(* The S2I forward simulation (FCC): match relation and diagram.

   Source is a CEK machine; the compiled code evaluates expressions leaving
   results in R_COM, spilling temporaries onto a per-activation stack frame.
   [match_states] relates a source state to a target state through
     - a block renaming (SimInject) for memories and values,
     - code anchoring (SimCode's [code_at]) for the pc,
     - a continuation/frame correspondence ([cont_match]) and a call-stack
       correspondence ([stack_match]).
   The diagram is [forward_simulation_star]: source steps map to target plus
   steps, except the administrative "descend" steps, which stutter under the
   [measure] below. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import S2I.SimCode.
Require Import S2I.Definitions.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype path.
From extructures Require Import ord fset fmap.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Import Intermediate.

Set Bullet Behavior "Strict Subproofs".

(* ==================== the stutter measure ==================== *)

(* Node weight 2: every "descend into a subexpression" source step strictly
   decreases [esize e + ksize k] while executing no target instruction. *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | E_val _ | E_arg | E_local | E_exit => 1
  | E_binop _ e1 e2 => (esize e1 + esize e2).+2
  | E_seq e1 e2 => (esize e1 + esize e2).+2
  | E_if e1 e2 e3 => (esize e1 + esize e2 + esize e3).+2
  | E_alloc e1 => (esize e1).+2
  | E_deref e1 => (esize e1).+2
  | E_assign e1 e2 => (esize e1 + esize e2).+2
  | E_call _ _ e1 => (esize e1).+2
  end.

Fixpoint ksize (k : cont) : nat :=
  match k with
  | Kstop => 0
  | Kbinop1 _ e2 k' => (esize e2).+1 + ksize k'
  | Kbinop2 _ _ k' => 1 + ksize k'
  | Kseq e2 k' => (esize e2).+1 + ksize k'
  | Kif e2 e3 k' => (esize e2 + esize e3).+1 + ksize k'
  | Kalloc k' => 1 + ksize k'
  | Kderef k' => 1 + ksize k'
  | Kassign1 e1 k' => (esize e1).+1 + ksize k'
  | Kassign2 _ k' => 1 + ksize k'
  | Kcall _ _ k' => 1 + ksize k'
  end.

Definition measure (s : S.CS.state) : nat :=
  esize (S.CS.s_expr s) + ksize (S.CS.s_cont s).

(* ==================== frame bookkeeping ==================== *)

(* canonical per-component pointers *)
Definition lbp (C : Component.id) : Pointer.t := (C, 0, 0%Z).
Definition scr (C : Component.id) : Pointer.t := (C, 1, 0%Z).

(* Peak in-frame slot usage (above the 3 linkage slots) of a continuation,
   given [t] currently live temporaries — from the moment the current
   expression has just delivered its value. Occupancy-aware: value-consuming
   continuations pop their temp before continuing, so the future need is
   measured against the SHRUNK temp count (a flat "temps + future" bound is
   not preserved across pushes). *)
Fixpoint kneed (k : cont) (t : nat) : nat :=
  match k with
  | Kstop => t
  | Kbinop1 _ e2 k' => maxn (t + 1 + stack_need e2) (kneed k' t)
  | Kbinop2 _ _ k' => kneed k' t.-1
  | Kseq e2 k' => maxn (t + stack_need e2) (kneed k' t)
  | Kif e2 e3 k' =>
      maxn (t + stack_need e2) (maxn (t + stack_need e3) (kneed k' t))
  | Kalloc k' => kneed k' t
  | Kderef k' => kneed k' t
  | Kassign1 e1 k' => maxn (t + 1 + stack_need e1) (kneed k' t)
  | Kassign2 _ k' => kneed k' t.-1
  | Kcall _ _ k' => maxn (t + 2) (kneed k' t)
  end.

(* the temporaries on the frame, top of stack first: with R_SP at offset
   2 + size temps, temp i sits at offset (1 + size temps) - i.
   (The body frame now has TWO linkage slots — the caller's R_SP and the saved
   R_ARG; the inherited-scratch slot moved to the wrapper's frame.) *)
Definition frame_temps (tmem : Memory.t) (C : Component.id) (fb : Block.id)
           (temps : seq value) : Prop :=
  forall i, i < size temps ->
    Memory.load tmem (C, fb, Z.of_nat (1 + size temps - i))
    = Some (nth Undef temps i).

(* every slot below [cap] is loadable (the frame was allocated that big) *)
Definition frame_cap (tmem : Memory.t) (C : Component.id) (fb : Block.id)
           (cap : nat) : Prop :=
  forall j : Z, (0 <= j < Z.of_nat cap)%Z ->
    exists v, Memory.load tmem (C, fb, j) = Some v.

(* Target-only-store discipline: blocks the compiled code writes raw (the
   current frame, the scratch cells at block 1) must not alias the injection's
   range, or target-only stores would break [mem_inject]
   (cf. [store_outside_inject]). These facts are established at allocation time
   ([alloc_outside_inject]) and preserved under [extend] because extensions map
   onto freshly allocated target blocks. *)
Definition scratch_priv (α : renaming) : Prop :=
  forall C' b0, α C' b0 <> Some 1.

Definition frame_priv (α : renaming) (C : Component.id) (fb : Block.id) : Prop :=
  fb <> 1 /\ forall b0, α C b0 <> Some fb.

(* ==================== the continuation relation ==================== *)

(* [cont_match α C plm k rest temps]: after the current fragment, the code
   [rest] implements the continuation [k]; [temps] are the target values
   currently spilled for the pending operations (top of stack first). *)
Inductive cont_match (α : renaming) (C : Component.id) (plm : NMap label)
  : cont -> code -> seq value -> Prop :=
| CM_stop :
    cont_match α C plm Kstop
      (pop R_ARG ++ pop R_SP ++ [:: IJump]) [::]
| CM_binop1 : forall op e2 k c2 rest temps s1 s2,
    compile_expr C (lbp C) (scr C) plm e2 s1 = Some (c2, s2) ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kbinop1 op e2 k)
      (push R_COM ++ c2 ++ pop R_AUX1
         ++ IBinOp op R_AUX1 R_COM R_COM :: rest) temps
| CM_binop2 : forall op v tv k rest temps,
    val_inject α v tv ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kbinop2 op v k)
      (pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest) (tv :: temps)
| CM_seq : forall e2 k c2 rest temps s1 s2,
    compile_expr C (lbp C) (scr C) plm e2 s1 = Some (c2, s2) ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kseq e2 k) (c2 ++ rest) temps
| CM_if : forall e2 e3 k c2 c3 lconseq lend rest temps s2a s2b s3a s3b,
    compile_expr C (lbp C) (scr C) plm e2 s2a = Some (c2, s2b) ->
    compile_expr C (lbp C) (scr C) plm e3 s3a = Some (c3, s3b) ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kif e2 e3 k)
      (IBnz R_COM lconseq :: c3 ++ [:: IBnz R_ONE lend; ILabel lconseq]
         ++ c2 ++ ILabel lend :: rest) temps
| CM_alloc : forall k rest temps,
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kalloc k) (IAlloc R_COM R_COM :: rest) temps
| CM_deref : forall k rest temps,
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kderef k) (ILoad R_COM R_COM :: rest) temps
| CM_assign1 : forall e1 k c1 rest temps s1 s2,
    compile_expr C (lbp C) (scr C) plm e1 s1 = Some (c1, s2) ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kassign1 e1 k)
      (push R_COM ++ c1 ++ pop R_AUX1
         ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest) temps
| CM_assign2 : forall v tv k rest temps,
    val_inject α v tv ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kassign2 v k)
      (pop R_AUX1 ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest)
      (tv :: temps)
| CM_call_int : forall C' P' k tl rest temps,
    C' = C ->
    getm plm P' = Some tl ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kcall C' P' k)
      (push R_RA ++ IJal tl :: pop R_RA ++ rest) temps
| CM_call_ext : forall C' P' k rest temps,
    C' <> C ->
    cont_matchJ α C plm k rest temps ->
    cont_match α C plm (Kcall C' P' k)
      (push R_RA ++ push R_ARG ++ store_arg (scr C) R_SP R_AUX2
         ++ ICall C' P' :: IConst (IInt 1) R_ONE
         :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest) temps

(* [cont_matchJ]: [cont_match] up to leading JOIN JUNK — the if-emission's
   glue (a join label; or the else-branch's jump-to-join over the then-code).
   The junk drains by silent administrative target steps (see
   [cont_matchJ_drain]); the canonical relation underneath stays
   syntax-directed. *)
with cont_matchJ (α : renaming) (C : Component.id) (plm : NMap label)
  : cont -> code -> seq value -> Prop :=
| CMJ_base : forall k rest temps,
    cont_match α C plm k rest temps ->
    cont_matchJ α C plm k rest temps
| CMJ_label : forall l k rest temps,
    cont_matchJ α C plm k rest temps ->
    cont_matchJ α C plm k (ILabel l :: rest) temps
| CMJ_bnzjoin : forall lend lconseq c2 k rest temps,
    cont_matchJ α C plm k (ILabel lend :: rest) temps ->
    cont_matchJ α C plm k
      (IBnz R_ONE lend :: ILabel lconseq :: c2 ++ ILabel lend :: rest) temps.

Scheme cont_match_mutind := Minimality for cont_match Sort Prop
  with cont_matchJ_mutind := Minimality for cont_matchJ Sort Prop.
Combined Scheme cont_match_combind from cont_match_mutind, cont_matchJ_mutind.

(* ==================== the stack relation ==================== *)

Section StackMatch.

Variable G : global_env.
Variable labelsP : NMap (NMap label).

(* The suspended EXTERNAL-entry activation of the callee: after the body's
   IJump, control lands in the external epilogue, pops the external frame
   [fbE], and IReturns. Main's dual entry has the extra context-marker pop
   (the marker is nonzero for a genuine cross-component call). *)
Inductive ext_frame_match (tmem : Memory.t) (C : Component.id)
  : Block.id -> Pointer.t -> Z -> Prop :=
(* The external frame now carries THREE linkage slots (four for main): the
   caller's R_SP, the INHERITED SCRATCH the wrapper saved on entry, and R_RA
   (plus main's context marker).  The scratch save/restore moved here from the
   body, so the epilogue also restores the cell before popping R_SP. *)
| EF_std : forall fbE jal_ret v0 v1 v2,
    Pointer.component jal_ret = C ->
    code_at G jal_ret (pop R_RA ++ pop R_AUX1
                         ++ store_arg (scr C) R_AUX1 R_AUX2
                         ++ pop R_SP ++ [:: IReturn]) ->
    Memory.load tmem (C, fbE, 0%Z) = Some v0 ->
    Memory.load tmem (C, fbE, 1%Z) = Some v1 ->
    Memory.load tmem (C, fbE, 2%Z) = Some v2 ->
    ext_frame_match tmem C fbE jal_ret 3%Z
| EF_main : forall fbE jal_ret lret v0 v1 v2 z,
    Pointer.component jal_ret = C ->
    code_at G jal_ret
      (pop R_ARG ++ pop R_RA ++ pop R_AUX1
         ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
    Memory.load tmem (C, fbE, 0%Z) = Some v0 ->
    Memory.load tmem (C, fbE, 1%Z) = Some v1 ->
    Memory.load tmem (C, fbE, 2%Z) = Some v2 ->
    Memory.load tmem (C, fbE, 3%Z) = Some (Int z) ->
    z <> 0%Z ->
    ext_frame_match tmem C fbE jal_ret 4%Z.

(* [stack_match α tmem scrs C fb prot stk gps]:
   the CURRENT activation runs in component [C] on frame [fb]; [stk]/[gps]
   are the suspended source/target stacks; [scrs] maps each externally
   suspended component to the scratch-cell content it relies upon; [prot]
   collects the frame blocks the relation's memory facts live in (the
   current [fb] is NOT protected: pushes write above its linkage slots). *)
Inductive stack_match (α : renaming) (tmem : Memory.t)
  : NMap value -> Component.id -> Block.id
    -> seq (Component.id * Block.id) -> S.CS.stack -> I.CS.stack -> Prop :=
| SM_init : forall scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1,
    (* current = main's initial activation; parent = main's dual entry,
       marker Int 0: after the body, control drains to IHalt *)
    Memory.load tmem (Component.main, fb, 0%Z)
      = Some (Ptr (Component.main, fb_ext, 4%Z)) ->
    Memory.load tmem (Component.main, fb, 1%Z) = Some vs1 ->
    Memory.load tmem (Component.main, fb_ext, 0%Z) = Some v0 ->
    Memory.load tmem (Component.main, fb_ext, 1%Z) = Some v1 ->
    Memory.load tmem (Component.main, fb_ext, 2%Z) = Some vx ->
    Memory.load tmem (Component.main, fb_ext, 3%Z) = Some (Int 0) ->
    frame_priv α Component.main fb_ext ->
    Pointer.component ret_ext = Component.main ->
    code_at G ret_ext
      (pop R_ARG ++ pop R_RA ++ pop R_AUX1
         ++ store_arg (scr Component.main) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
    fb <> fb_ext ->
    stack_match α tmem scrs0 Component.main fb
      [:: (Component.main, fb_ext)] [::] [:: ret_ext]
| SM_internal : forall scrs C fb fb' prot stk gps oldarg targ k' rest' temps'
                       plm ret junkRA cap',
    (* the caller: same component, suspended at an internal call site *)
    getm labelsP C = Some plm ->
    Pointer.component ret = C ->
    code_at G ret (pop R_RA ++ rest') ->
    cont_matchJ α C plm k' rest' temps' ->
    (* the callee's linkage slots: caller R_SP and the saved argument.  There is
       no scratch slot here — an INTRA-component activation neither saves nor
       restores the cell (the save/restore lives in the wrapper), which is why
       unwinding this frame leaves the transit map [scrs] untouched below. *)
    Memory.load tmem (C, fb, 0%Z)
      = Some (Ptr (C, fb', Z.of_nat (2 + size temps' + 1))) ->
    Memory.load tmem (C, fb, 1%Z) = Some targ ->
    val_inject α oldarg targ ->
    (* the caller's suspended frame *)
    frame_priv α C fb' ->
    frame_temps tmem C fb' temps' ->
    Memory.load tmem (C, fb', Z.of_nat (2 + size temps')) = Some junkRA ->
    frame_cap tmem C fb' cap' ->
    3 + kneed k' (size temps') <= cap' ->
    (C, fb') \notin prot ->
    fb <> fb' ->
    (* an intra return restores nothing: the map passes through *)
    stack_match α tmem scrs C fb' prot stk gps ->
    stack_match α tmem scrs C fb ((C, fb') :: prot)
      (S.CS.Frame C oldarg k' :: stk) (ret :: gps)
| SM_external : forall scrs C C'' fb fbE spE fb'' prot stk gps oldarg
                       targ k'' rest'' temps'' plm'' jal_ret icall_ret vscr
                       junkRA junkARG cap'',
    (* the caller: a DIFFERENT component, suspended at an ICall *)
    C'' <> C ->
    getm labelsP C'' = Some plm'' ->
    (* the callee-side external-entry activation *)
    ext_frame_match tmem C fbE jal_ret spE ->
    frame_priv α C fbE ->
    (* the callee's internal linkage slots: caller R_SP and the saved argument.
       The inherited scratch [vscr] now lives in the callee's WRAPPER frame
       [fbE] (slot 1), not in its body frame — that is where the wrapper saved
       it on entry and where its epilogue will read it back from. *)
    Memory.load tmem (C, fb, 0%Z) = Some (Ptr (C, fbE, spE)) ->
    Memory.load tmem (C, fbE, 1%Z) = Some vscr ->
    Memory.load tmem (C, fb, 1%Z) = Some junkARG ->
    (* the caller's return site and suspended state *)
    Pointer.component icall_ret = C'' ->
    code_at G icall_ret
      (IConst (IInt 1) R_ONE
         :: reload_sp (scr C'') ++ pop R_ARG ++ pop R_RA ++ rest'') ->
    cont_matchJ α C'' plm'' k'' rest'' temps'' ->
    frame_priv α C'' fb'' ->
    frame_temps tmem C'' fb'' temps'' ->
    Memory.load tmem (C'', fb'', Z.of_nat (2 + size temps'')) = Some junkRA ->
    Memory.load tmem (C'', fb'', Z.of_nat (2 + size temps'' + 1)) = Some targ ->
    val_inject α oldarg targ ->
    frame_cap tmem C'' fb'' cap'' ->
    3 + kneed k'' (size temps'') <= cap'' ->
    (* the caller's transit expectation is the map's current entry *)
    getm scrs C''
      = Some (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2))) ->
    (C'', fb'') \notin prot ->
    (C, fbE) \notin ((C'', fb'') :: prot) ->
    fb <> fbE ->
    (* unwinding restores [vscr] into C's scratch cell *)
    stack_match α tmem (setm scrs C vscr) C'' fb'' prot stk gps ->
    stack_match α tmem scrs C fb
      ((C, fbE) :: (C'', fb'') :: prot)
      (S.CS.Frame C'' oldarg k'' :: stk) (jal_ret :: icall_ret :: gps).

End StackMatch.

(* ==================== the state relation ==================== *)

Section MatchStates.

Variable p : Source.program.
Variable tp : Intermediate.program.

Let G : global_env := prepare_global_env tp.

Definition labelsP : NMap (NMap label) :=
  match gen_all_procedures_labels
          (elementsm (Source.prog_procedures p)) init_env with
  | Some (l, _) => l
  | None => emptym
  end.

(* The invariant pack behind MS_expr, as a record: diagram case lemmas take it
   as ONE premise and rebuild it field by field. *)
Record expr_inv (α : renaming) (scrs : NMap value) (C : Component.id)
       (stk : S.CS.stack) (mem : Memory.t) (k : cont) (e : expr) (arg : value)
       (gps : I.CS.stack) (tmem : Memory.t) (tregs : Register.t)
       (pc : Pointer.t) (fb : Block.id)
       (prot : seq (Component.id * Block.id)) (temps : seq value)
       (plm : NMap label) (c rest : code) (s1 s2 : comp_env) (cap : nat)
  : Prop := ExprInv {
  ei_plm    : getm labelsP C = Some plm;
  ei_dom    : C \in domm (Intermediate.prog_interface tp);
  ei_mem    : mem_inject α mem tmem;
  ei_scrs   : forall C' v, getm scrs C' = Some v ->
              Memory.load tmem (C', 1, 0%Z) = Some v;
  ei_flag   : Memory.load tmem (Component.main, 1, 1%Z) = Some (Int 1);
  ei_scr_all: forall C', C' \in domm (Intermediate.prog_interface tp) ->
              exists v, Memory.load tmem (C', 1, 0%Z) = Some v;
  ei_one    : Register.get R_ONE tregs = Int 1;
  ei_sp     : Register.get R_SP tregs = Ptr (C, fb, Z.of_nat (2 + size temps));
  ei_arg    : val_inject α arg (Register.get R_ARG tregs);
  ei_pc     : Pointer.component pc = C;
  ei_comp   : compile_expr C (lbp C) (scr C) plm e s1 = Some (c, s2);
  ei_code   : code_at G pc (c ++ rest);
  ei_cont   : cont_matchJ α C plm k rest temps;
  ei_uniq   : forall Cx C_procs b P_code,
              getm (genv_procedures G) Cx = Some C_procs ->
              getm C_procs b = Some P_code ->
              uniq (labels_of P_code);
  ei_priv   : frame_priv α C fb;
  ei_scrp   : scratch_priv α;
  ei_temps  : frame_temps tmem C fb temps;
  ei_cap    : frame_cap tmem C fb cap;
  ei_budget : 3 + maxn (size temps + stack_need e) (kneed k (size temps))
              <= cap;
  ei_prot   : (C, fb) \notin prot;
  ei_stack  : stack_match G labelsP α tmem scrs C fb prot stk gps;
  ei_mainnf : forall mexpr, Source.prog_main p = Some mexpr ->
              immediately_final mexpr = false
}.

(* The invariant pack behind MS_val: the value already sits in R_COM and the
   pc sits on the continuation's code. *)
Record val_inv (α : renaming) (scrs : NMap value) (C : Component.id)
       (stk : S.CS.stack) (mem : Memory.t) (k : cont) (v : value) (arg : value)
       (gps : I.CS.stack) (tmem : Memory.t) (tregs : Register.t)
       (pc : Pointer.t) (fb : Block.id)
       (prot : seq (Component.id * Block.id)) (temps : seq value)
       (plm : NMap label) (rest : code) (cap : nat)
  : Prop := ValInv {
  vi_plm    : getm labelsP C = Some plm;
  vi_dom    : C \in domm (Intermediate.prog_interface tp);
  vi_mem    : mem_inject α mem tmem;
  vi_scrs   : forall C' v0, getm scrs C' = Some v0 ->
              Memory.load tmem (C', 1, 0%Z) = Some v0;
  vi_flag   : Memory.load tmem (Component.main, 1, 1%Z) = Some (Int 1);
  vi_scr_all: forall C', C' \in domm (Intermediate.prog_interface tp) ->
              exists v0, Memory.load tmem (C', 1, 0%Z) = Some v0;
  vi_one    : Register.get R_ONE tregs = Int 1;
  vi_sp     : Register.get R_SP tregs = Ptr (C, fb, Z.of_nat (2 + size temps));
  vi_arg    : val_inject α arg (Register.get R_ARG tregs);
  vi_com    : val_inject α v (Register.get R_COM tregs);
  vi_pc     : Pointer.component pc = C;
  vi_code   : code_at G pc rest;
  vi_cont   : cont_matchJ α C plm k rest temps;
  vi_uniq   : forall Cx C_procs b P_code,
              getm (genv_procedures G) Cx = Some C_procs ->
              getm C_procs b = Some P_code ->
              uniq (labels_of P_code);
  vi_priv   : frame_priv α C fb;
  vi_scrp   : scratch_priv α;
  vi_temps  : frame_temps tmem C fb temps;
  vi_cap    : frame_cap tmem C fb cap;
  vi_budget : 3 + kneed k (size temps) <= cap;
  vi_prot   : (C, fb) \notin prot;
  vi_stack  : stack_match G labelsP α tmem scrs C fb prot stk gps;
  vi_mainnf : forall mexpr, Source.prog_main p = Some mexpr ->
              immediately_final mexpr = false
}.

Variant match_states : S.CS.state -> CS.state -> Prop :=
| MS_start :
    match_states (S.CS.initial_machine_state p) (CS.initial_machine_state tp)
| MS_expr : forall α scrs C stk mem k e arg gps tmem tregs pc fb prot temps
                   plm c rest s1 s2 cap,
    expr_inv α scrs C stk mem k e arg gps tmem tregs pc fb prot temps
             plm c rest s1 s2 cap ->
    (forall v, e = E_val v -> k = Kstop -> stk <> [::]) ->
    match_states (S.CS.State C stk mem k e arg) (gps, tmem, tregs, pc)
| MS_val : forall α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
                  plm rest cap,
    val_inv α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
            plm rest cap ->
    (k = Kstop -> stk <> [::]) ->
    match_states (S.CS.State C stk mem k (E_val v) arg) (gps, tmem, tregs, pc)
| MS_halted : forall α C mem v arg gps tmem tregs pc,
    mem_inject α mem tmem ->
    executing G pc IHalt ->
    match_states (S.CS.State C [::] mem Kstop (E_val v) arg)
                 (gps, tmem, tregs, pc).

End MatchStates.

Arguments ei_plm {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_dom {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_mem {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_scrs {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_flag {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_scr_all {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_one {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_sp {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_arg {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_pc {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_comp {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_code {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_cont {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_uniq {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_priv {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_scrp {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_temps {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_cap {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_budget {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_prot {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_stack {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.
Arguments ei_mainnf {p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c rest s1 s2 cap}.

(* ==================== diagram plumbing: descend steps ==================== *)

Module TReplumb.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Notation icode := Intermediate.Machine.code.

Section WithCodePred.

(* the only thing the seven proofs need of a code predicate: nothing *)
Variable P : icode -> Prop.

Variable a : renaming.
Variable C : Component.id.
Variable plm : NMap label.

Lemma binop1_replumb op e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_binop op e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kbinop1 op e2 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1,
    (push R_COM ++ c2 ++ pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest),
    s1, sA.
  split=> //.
  - move: Hcode. rewrite /push /pop.
    by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_binop1 E2 Hk.
Qed.

Lemma seq1_replumb e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_seq e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kseq e2 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1, (c2 ++ rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_seq E2 Hk.
Qed.

Lemma if1_replumb e1 e2 e3 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_if e1 e2 e3) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kif e2 e3 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=.
  case E3: (compile_expr C (lbp C) (scr C) plm e3 sB) => [[c3 sC]|]; last by [].
  rewrite /= !fresh_labelE /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1, (IBnz R_COM (odflt 0 (next_label sC C))
      :: c3 ++ [:: IBnz R_ONE (odflt 0 (setm (next_label sC) C
                                          (1 + odflt 0 (next_label sC C)) C));
                   ILabel (odflt 0 (next_label sC C))]
      ++ c2 ++ ILabel (odflt 0 (setm (next_label sC) C
                                  (1 + odflt 0 (next_label sC C)) C)) :: rest),
    s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_if E2 E3 Hk.
Qed.

Lemma alloc1_replumb e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_alloc e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c0 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (c0, sB),
        P (c0 ++ rest')
      & cont_matchJ a C plm (Kalloc k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[c0 sA]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c0, (IAlloc R_COM R_COM :: rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_alloc Hk.
Qed.

Lemma deref1_replumb e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_deref e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c0 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (c0, sB),
        P (c0 ++ rest')
      & cont_matchJ a C plm (Kderef k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[c0 sA]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c0, (ILoad R_COM R_COM :: rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_deref Hk.
Qed.

Lemma assign1_replumb e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_assign e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c2 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e2 sA = Some (c2, sB),
        P (c2 ++ rest')
      & cont_matchJ a C plm (Kassign1 e1 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c2, (push R_COM ++ c1 ++ pop R_AUX1
      ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest), sA, sB.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_assign1 E1 Hk.
Qed.

Lemma initcall_replumb C' P' e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_call C' P' e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists ce rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (ce, sB),
        P (ce ++ rest')
      & cont_matchJ a C plm (Kcall C' P' k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[ce sA]|]; last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  - (* internal call *)
    case EL: (getm plm P') => [tl|]; last by [].
    rewrite /=. move=> [Ec _] Hcode Hk. subst c.
    have EC : C' = C by apply/PeanoNat.Nat.eqb_eq.
    exists ce, (push R_RA ++ IJal tl :: pop R_RA ++ rest), s1, sA.
    split=> //.
    + move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    + apply: CMJ_base. exact: CM_call_int EC EL Hk.
  - (* external call *)
    move=> [Ec _] Hcode Hk. subst c.
    have HneC : C' <> C.
    { move=> E. by rewrite E /Component.eqb PeanoNat.Nat.eqb_refl in Heqb. }
    exists ce, (push R_RA ++ push R_ARG ++ store_arg (scr C) R_SP R_AUX2
        ++ ICall C' P' :: IConst (IInt 1) R_ONE
        :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest), s1, sA.
    split=> //.
    + move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    + apply: CMJ_base. exact: CM_call_ext HneC Hk.
Qed.

End WithCodePred.

End TReplumb.


(* ==================== cont_match inversion lemmas ==================== *)

Lemma cont_match_binop1_inv {α C plm op e2 k rest temps} :
  cont_match α C plm (Kbinop1 op e2 k) rest temps ->
  exists c2 rest' s1 s2,
    [/\ compile_expr C (lbp C) (scr C) plm e2 s1 = Some (c2, s2),
        rest = push R_COM ++ c2 ++ pop R_AUX1
               ++ IBinOp op R_AUX1 R_COM R_COM :: rest'
      & cont_matchJ α C plm k rest' temps].
Proof. move=> H. inversion H; subst. by exists c2, rest0, s1, s2. Qed.

Lemma cont_match_binop2_inv {α C plm op v k rest temps} :
  cont_match α C plm (Kbinop2 op v k) rest temps ->
  exists tv temps' rest',
    [/\ val_inject α v tv, temps = tv :: temps',
        rest = pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest'
      & cont_matchJ α C plm k rest' temps'].
Proof. move=> H. inversion H; subst. by exists tv, temps0, rest0. Qed.

Lemma cont_match_alloc_inv {α C plm k rest temps} :
  cont_match α C plm (Kalloc k) rest temps ->
  exists rest',
    rest = IAlloc R_COM R_COM :: rest' /\ cont_matchJ α C plm k rest' temps.
Proof. move=> H. inversion H; subst. by exists rest0. Qed.

Lemma cont_match_deref_inv {α C plm k rest temps} :
  cont_match α C plm (Kderef k) rest temps ->
  exists rest',
    rest = ILoad R_COM R_COM :: rest' /\ cont_matchJ α C plm k rest' temps.
Proof. move=> H. inversion H; subst. by exists rest0. Qed.

Lemma cont_match_assign1_inv {α C plm e1 k rest temps} :
  cont_match α C plm (Kassign1 e1 k) rest temps ->
  exists c1 rest' s1 s2,
    [/\ compile_expr C (lbp C) (scr C) plm e1 s1 = Some (c1, s2),
        rest = push R_COM ++ c1 ++ pop R_AUX1
               ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest'
      & cont_matchJ α C plm k rest' temps].
Proof. move=> H. inversion H; subst. by exists c1, rest0, s1, s2. Qed.

Lemma cont_match_assign2_inv {α C plm v k rest temps} :
  cont_match α C plm (Kassign2 v k) rest temps ->
  exists tv temps' rest',
    [/\ val_inject α v tv, temps = tv :: temps',
        rest = pop R_AUX1
               ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest'
      & cont_matchJ α C plm k rest' temps'].
Proof. move=> H. inversion H; subst. by exists tv, temps0, rest0. Qed.

Lemma cont_match_if_inv {α C plm e2 e3 k rest temps} :
  cont_match α C plm (Kif e2 e3 k) rest temps ->
  exists c2 c3 lconseq lend rest' s2a s2b s3a s3b,
    [/\ compile_expr C (lbp C) (scr C) plm e2 s2a = Some (c2, s2b),
        compile_expr C (lbp C) (scr C) plm e3 s3a = Some (c3, s3b),
        rest = IBnz R_COM lconseq :: c3 ++ [:: IBnz R_ONE lend; ILabel lconseq]
               ++ c2 ++ ILabel lend :: rest'
      & cont_matchJ α C plm k rest' temps].
Proof.
  move=> H. inversion H; subst.
  by exists c2, c3, lconseq, lend, rest0, s2a, s2b, s3a, s3b.
Qed.

Lemma cont_match_seq_inv {α C plm e2 k rest temps} :
  cont_match α C plm (Kseq e2 k) rest temps ->
  exists c2 rest' s1 s2,
    [/\ compile_expr C (lbp C) (scr C) plm e2 s1 = Some (c2, s2),
        rest = c2 ++ rest'
      & cont_matchJ α C plm k rest' temps].
Proof. move=> H. inversion H; subst. by exists c2, rest0, s1, s2. Qed.

Lemma cont_match_stop_inv {α C plm rest temps} :
  cont_match α C plm Kstop rest temps ->
  rest = pop R_ARG ++ pop R_SP ++ [:: IJump] /\ temps = [::].
Proof. move=> H. by inversion H. Qed.

Lemma cont_match_call_inv {α C plm C' P' k rest temps} :
  cont_match α C plm (Kcall C' P' k) rest temps ->
  (exists tl rest',
    [/\ C' = C, getm plm P' = Some tl,
        rest = push R_RA ++ IJal tl :: pop R_RA ++ rest'
      & cont_matchJ α C plm k rest' temps])
  \/
  (exists rest',
    [/\ C' <> C,
        rest = push R_RA ++ push R_ARG ++ store_arg (scr C) R_SP R_AUX2
               ++ ICall C' P' :: IConst (IInt 1) R_ONE
               :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest'
      & cont_matchJ α C plm k rest' temps]).
Proof.
  move=> H. inversion H; subst.
  - left. by exists tl, rest0.
  - right. by exists rest0.
Qed.

(* ==================== store-preservation toolkit ==================== *)

(* Loadability survives ANY store (the store may only overwrite a value). *)
Lemma frame_cap_store tmem tmem' C fb cap ptr w :
  frame_cap tmem C fb cap ->
  Memory.store tmem ptr w = Some tmem' ->
  frame_cap tmem' C fb cap.
Proof.
  move=> Hcap Hs j Hj.
  case: (Hcap j Hj) => v Hv.
  rewrite (Memory.load_after_store _ _ _ _ (C, fb, j) Hs) Hv.
  case: ifP => _; by eexists.
Qed.

Lemma frame_temps_store tmem tmem' C fb temps ptr w :
  frame_temps tmem C fb temps ->
  Memory.store tmem ptr w = Some tmem' ->
  (forall i, i < size temps -> ptr <> (C, fb, Z.of_nat (1 + size temps - i))) ->
  frame_temps tmem' C fb temps.
Proof.
  move=> Ht Hs Hne i Hi.
  rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne i Hi) Hs).
  exact: Ht Hi.
Qed.

Lemma ext_frame_match_store G0 tmem tmem' C fbE jal_ret spE ptr w :
  ext_frame_match G0 tmem C fbE jal_ret spE ->
  Memory.store tmem ptr w = Some tmem' ->
  (forall o : Z, ptr <> (C, fbE, o)) ->
  ext_frame_match G0 tmem' C fbE jal_ret spE.
Proof.
  move=> Hm Hs Hne.
  have L : forall o : Z,
      Memory.load tmem' (C, fbE, o) = Memory.load tmem (C, fbE, o).
  { move=> o. exact: Memory.load_after_store_neq (Hne o) Hs. }
  inversion Hm; subst.
  - eapply EF_std;
      [reflexivity | eassumption | rewrite L; eassumption
      | rewrite L; eassumption | rewrite L; eassumption].
  - eapply EF_main;
      [reflexivity | eassumption | rewrite L; eassumption
      | rewrite L; eassumption | rewrite L; eassumption
      | rewrite L; eassumption | assumption].
Qed.

(* A store outside the relation's footprint preserves [stack_match]: it must
   avoid the protected frames, the scratch blocks, and the linkage slots
   (offsets 0..2) of the current frame — pushes above them are fine. *)
Lemma stack_match_store G0 lP α tmem tmem' scrs C0 fb0 prot stk gps Cp bp op w :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  Memory.store tmem (Cp, bp, op) w = Some tmem' ->
  (Cp, bp) \notin prot ->
  ((Cp, bp) = (C0, fb0) -> (2 <= op)%Z) ->
  stack_match G0 lP α tmem' scrs C0 fb0 prot stk gps.
Proof.
  move=> Hsm Hs.
  have Lneq : forall C1 b1 (o : Z), (Cp, bp, op) <> (C1, b1, o) ->
      Memory.load tmem' (C1, b1, o) = Memory.load tmem (C1, b1, o).
  { move=> C1 b1 o Hd. exact: Memory.load_after_store_neq Hd Hs. }
  elim: Hsm => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
                  L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne Hprot Hcur
               |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
                  plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
                  Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail IH
                  Hprot Hcur
               |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
                  k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
                  junkARG cap''
                  HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
                  Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
                  Hnp'' HnpE HneE Htail IH Hprot Hcur].
  - (* SM_init *)
    have NEcur : forall o : Z, (o < 2)%Z ->
        (Cp, bp, op) <> (Component.main, fb, o).
    { move=> o Ho [E1' E2' E3']. subst Cp bp op.
      by move: (Hcur erefl); lia. }
    have NEext : forall o : Z, (Cp, bp, op) <> (Component.main, fb_ext, o).
    { move=> o [E1' E2' E3']. subst Cp bp.
      by move: Hprot; rewrite inE eqxx. }
    apply: SM_init; try eassumption.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L1.
    + rewrite Lneq; last by apply: NEext. exact: E0.
    + rewrite Lneq; last by apply: NEext. exact: E1.
    + rewrite Lneq; last by apply: NEext. exact: E2.
    + rewrite Lneq; last by apply: NEext. exact: E3.
  - (* SM_internal *)
    move: Hprot; rewrite inE negb_or => /andP [Hprot1 Hprot'].
    have NEcur : forall o : Z, (o < 2)%Z -> (Cp, bp, op) <> (C, fb, o).
    { move=> o Ho [E1' E2' E3']. subst Cp bp op.
      by move: (Hcur erefl); lia. }
    have NEsusp : forall o : Z, (Cp, bp, op) <> (C, fb', o).
    { move=> o [E1' E2' E3']. subst Cp bp.
      by move: Hprot1; rewrite eqxx. }
    apply: SM_internal; try eassumption.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L1.
    + apply: frame_temps_store Htemps Hs _ => i Hi. exact: NEsusp.
    + rewrite Lneq; last by apply: NEsusp. exact: LjRA.
    + exact: frame_cap_store Hcap Hs.
    + apply: IH => //. by move=> [E1' E2']; move: Hprot1; rewrite E1' E2' eqxx.
  - (* SM_external *)
    move: Hprot; rewrite !inE !negb_or => /andP [HprotE /andP [Hprot2 Hprot']].
    have NEcur : forall o : Z, (o < 2)%Z -> (Cp, bp, op) <> (C, fb, o).
    { move=> o Ho [E1' E2' E3']. subst Cp bp op.
      by move: (Hcur erefl); lia. }
    have NEE : forall o : Z, (Cp, bp, op) <> (C, fbE, o).
    { move=> o [E1' E2' E3']. subst Cp bp.
      by move: HprotE; rewrite eqxx. }
    have NEsusp : forall o : Z, (Cp, bp, op) <> (C'', fb'', o).
    { move=> o [E1' E2' E3']. subst Cp bp.
      by move: Hprot2; rewrite eqxx. }
    apply: SM_external; try eassumption.
    + apply: ext_frame_match_store Hext Hs _. exact: NEE.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    (* [vscr] now lives in the WRAPPER frame [fbE], so it is protected by [NEE] *)
    + rewrite Lneq; last by apply: NEE. exact: L1.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L2E.
    + apply: frame_temps_store Htemps'' Hs _ => i Hi. exact: NEsusp.
    + rewrite Lneq; last by apply: NEsusp. exact: LjRA''.
    + rewrite Lneq; last by apply: NEsusp. exact: Ltarg''.
    + exact: frame_cap_store Hcap'' Hs.
    + apply: IH => //. by move=> [E1' E2']; move: Hprot2; rewrite E1' E2' eqxx.
Qed.


(* ==================== alloc-preservation toolkit ==================== *)

(* Memory-level: allocation changes no existing cell. *)
Lemma memory_load_after_alloc tmem Ca n tmem' pt C1 b1 (o : Z) :
  Memory.alloc tmem Ca n = Some (tmem', pt) ->
  (C1, b1) <> (Ca, Pointer.block pt) ->
  Memory.load tmem' (C1, b1, o) = Memory.load tmem (C1, b1, o).
Proof.
  rewrite /Memory.alloc /Memory.load.
  case E: (getm tmem Ca) => [cm|] //.
  case E2: (ComponentMemory.alloc cm n) => [cm' b] [<- <-] /= Hne.
  rewrite setmE. case: (C1 =P Ca) => [EC|] //. subst C1.
  rewrite (ComponentMemory.load_after_alloc _ _ _ _ E2) ?E //.
  by move=> Eb; apply: Hne; rewrite Eb.
Qed.

(* The allocated block was not loadable before (needs the cursor invariant). *)
Lemma memory_alloc_fresh tmem Ca n tmem' pt :
  (forall C cm, getm tmem C = Some cm -> ComponentMemory.wf cm) ->
  Memory.alloc tmem Ca n = Some (tmem', pt) ->
  forall (o : Z) w,
    Memory.load tmem (Ca, Pointer.block pt, o) = Some w -> False.
Proof.
  move=> Hwf.
  rewrite /Memory.alloc /Memory.load.
  case E: (getm tmem Ca) => [cm|] //.
  case E2: (ComponentMemory.alloc cm n) => [cm' b] [_ <-] /= o w Hl.
  have Hfr := ComponentMemory.alloc_fresh _ _ _ _ (Hwf _ _ E) E2.
  move: Hfr. rewrite (ComponentMemory.load_domm _ _ _ _ Hl). by [].
Qed.

(* rle-monotonicity of the continuation relation *)
Lemma cont_match_rle_all α α' C plm :
  rle α α' ->
  (forall k rest temps, cont_match α C plm k rest temps ->
     cont_match α' C plm k rest temps)
  /\ (forall k rest temps, cont_matchJ α C plm k rest temps ->
     cont_matchJ α' C plm k rest temps).
Proof.
  move=> Hrle.
  apply: (cont_match_combind α C plm
    (fun k rest temps => cont_match α' C plm k rest temps)
    (fun k rest temps => cont_matchJ α' C plm k rest temps)).
  - by intros; eapply CM_stop.
  - by intros; eapply CM_binop1; eauto.
  - by intros; eapply CM_binop2; eauto using val_inject_rle.
  - by intros; eapply CM_seq; eauto.
  - by intros; eapply CM_if; eauto.
  - by intros; eapply CM_alloc; eauto.
  - by intros; eapply CM_deref; eauto.
  - by intros; eapply CM_assign1; eauto.
  - by intros; eapply CM_assign2; eauto using val_inject_rle.
  - by intros; eapply CM_call_int; eauto.
  - by intros; eapply CM_call_ext; eauto.
  - by intros; eapply CMJ_base; eauto.
  - by intros; eapply CMJ_label; eauto.
  - by intros; eapply CMJ_bnzjoin; eauto.
Qed.

Lemma cont_matchJ_rle α α' C plm k rest temps :
  rle α α' ->
  cont_matchJ α C plm k rest temps ->
  cont_matchJ α' C plm k rest temps.
Proof.
  move=> Hrle. exact: (proj2 (cont_match_rle_all _ _ C plm Hrle)).
Qed.

Lemma ext_frame_match_transport G0 tmem tmem' C fbE jal_ret spE :
  ext_frame_match G0 tmem C fbE jal_ret spE ->
  (forall (o : Z) w, Memory.load tmem (C, fbE, o) = Some w ->
     Memory.load tmem' (C, fbE, o) = Some w) ->
  ext_frame_match G0 tmem' C fbE jal_ret spE.
Proof.
  move=> Hm Ltr. inversion Hm; subst.
  - eapply EF_std;
      [reflexivity | eassumption | exact: Ltr H1 | exact: Ltr H2
      | exact: Ltr H3].
  - eapply EF_main;
      [reflexivity | eassumption | exact: Ltr H1 | exact: Ltr H2
      | exact: Ltr H3 | exact: Ltr H4 | assumption].
Qed.

(* Allocation (in any component) preserves the stack relation, along the
   extended renaming: no existing cell moves, and the extension maps onto the
   FRESH block, which cannot alias any protected frame (they all have loadable
   cells). *)
Lemma stack_match_alloc G0 lP α α' tmem tmem' scrs C0 fb0 prot stk gps Ca n
      bt pt :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  Memory.alloc tmem Ca n = Some (tmem', pt) ->
  Pointer.block pt = bt ->
  rle α α' ->
  (forall Cx b0 bx, α' Cx b0 = Some bx ->
     α Cx b0 = Some bx \/ (Cx = Ca /\ bx = bt)) ->
  (forall (o : Z) w, Memory.load tmem (Ca, bt, o) = Some w -> False) ->
  stack_match G0 lP α' tmem' scrs C0 fb0 prot stk gps.
Proof.
  move=> Hsm Halloc Ept Hrle Hnew Hfresh.
  have Ltr : forall C1 b1 (o : Z) w,
      Memory.load tmem (C1, b1, o) = Some w ->
      Memory.load tmem' (C1, b1, o) = Some w.
  { move=> C1 b1 o w Hl.
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halloc) //.
    rewrite Ept. move=> [E1 E2]. subst C1 b1. exact: Hfresh Hl. }
  have Hprv : forall Cx bx,
      (forall b0, α Cx b0 <> Some bx) ->
      (exists (o : Z) w, Memory.load tmem (Cx, bx, o) = Some w) ->
      forall b0, α' Cx b0 <> Some bx.
  { move=> Cx bx Hold [o [w Hl]] b0 HA.
    case: (Hnew _ _ _ HA) => [HA0 | [E1 E2]].
    - exact: Hold HA0.
    - subst Cx bx. exact: Hfresh Hl. }
  elim: Hsm => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
                  L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne
               |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
                  plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
                  Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail IH
               |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
                  k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
                  junkARG cap''
                  HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
                  Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
                  Hnp'' HnpE HneE Htail IH].
  - apply: SM_init; try eassumption.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + exact: Ltr E0.
    + exact: Ltr E1.
    + exact: Ltr E2.
    + exact: Ltr E3.
    + split; first by case: HprivE.
      apply: Hprv; first by case: HprivE.
      by exists 0%Z, v0.
  - apply: SM_internal; try eassumption.
    + apply: cont_matchJ_rle Hrle Hcont.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + exact: val_inject_rle Hrle Hvi.
    + split; first by case: Hpriv.
      apply: Hprv; first by case: Hpriv.
      by exists (Z.of_nat (2 + size temps')), junkRA.
    + move=> i Hi. apply: Ltr. exact: Htemps Hi.
    + exact: Ltr LjRA.
    + move=> j Hj. case: (Hcap j Hj) => w Hw. exists w. exact: Ltr Hw.
  - apply: SM_external; try eassumption.
    + apply: ext_frame_match_transport Hext _.
      move=> o w. exact: Ltr.
    + split; first by case: HprivE.
      apply: Hprv; first by case: HprivE.
      inversion Hext; subst; by exists 0%Z, v0.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + exact: Ltr L2E.
    + apply: cont_matchJ_rle Hrle Hcont''.
    + split; first by case: Hpriv''.
      apply: Hprv; first by case: Hpriv''.
      by exists (Z.of_nat (2 + size temps'')), junkRA.
    + move=> i Hi. apply: Ltr. exact: Htemps'' Hi.
    + exact: Ltr LjRA''.
    + exact: Ltr Ltarg''.
    + exact: val_inject_rle Hrle Hvi.
    + move=> j Hj. case: (Hcap'' j Hj) => w Hw. exists w. exact: Ltr Hw.
Qed.

(* Every protected frame carries recorded α-avoidance: α-image stores
   (source-program assignments) can never hit a protected frame. *)
Lemma stack_match_prot_priv G0 lP α tmem scrs C0 fb0 prot stk gps Cx bx :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  (Cx, bx) \in prot ->
  forall b0, α Cx b0 <> Some bx.
Proof.
  move=> Hsm; elim: Hsm => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
                  _ _ _ _ _ _ HprivE _ _ _ Hin
               |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
                  plm ret junkRA cap' _ _ _ _ _
                  _ _ Hpriv _ _ _ _ _ _ _ IH Hin
               |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
                  k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
                  junkARG cap''
                  _ _ _ HprivE _ _ _ _ _ _ Hpriv'' _ _ _ _ _ _ _
                  _ _ _ _ IH Hin].
  - move: Hin. rewrite inE => /eqP [E1 E2]. subst Cx bx.
    exact: (proj2 HprivE).
  - move: Hin. rewrite inE => /orP [/eqP [E1 E2] | Hin'].
    + subst Cx bx. exact: (proj2 Hpriv).
    + exact: IH Hin'.
  - move: Hin. rewrite inE => /orP [/eqP [E1 E2] | Hin2].
    + subst Cx bx. exact: (proj2 HprivE).
    + move: Hin2. rewrite inE => /orP [/eqP [E1 E2] | Hin'].
      * subst Cx bx. exact: (proj2 Hpriv'').
      * exact: IH Hin'.
Qed.

(* Every protected frame is disjoint from the scratch block. *)
Lemma stack_match_prot_not1 G0 lP α tmem scrs C0 fb0 prot stk gps Cx bx :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  (Cx, bx) \in prot ->
  bx <> 1.
Proof.
  move=> Hsm; elim: Hsm => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
                  _ _ _ _ _ _ HprivE _ _ _ Hin
               |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
                  plm ret junkRA cap' _ _ _ _ _
                  _ _ Hpriv _ _ _ _ _ _ _ IH Hin
               |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
                  k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
                  junkARG cap''
                  _ _ _ HprivE _ _ _ _ _ _ Hpriv'' _ _ _ _ _ _ _
                  _ _ _ _ IH Hin].
  - move: Hin. rewrite inE => /eqP [E1 E2]. subst Cx bx.
    exact: (proj1 HprivE).
  - move: Hin. rewrite inE => /orP [/eqP [E1 E2] | Hin'].
    + subst Cx bx. exact: (proj1 Hpriv).
    + exact: IH Hin'.
  - move: Hin. rewrite inE => /orP [/eqP [E1 E2] | Hin2].
    + subst Cx bx. exact: (proj1 HprivE).
    + move: Hin2. rewrite inE => /orP [/eqP [E1 E2] | Hin'].
      * subst Cx bx. exact: (proj1 Hpriv'').
      * exact: IH Hin'.
Qed.

(* fmap plumbing for the scratch tracker *)
Lemma setm_over (m : NMap value) k v w : setm (setm m k w) k v = setm m k v.
Proof. apply/eq_fmap => x. rewrite !setmE. by case: eqP. Qed.

Lemma setm_comm (m : NMap value) k1 k2 v1 v2 :
  k1 <> k2 -> setm (setm m k1 v1) k2 v2 = setm (setm m k2 v2) k1 v1.
Proof.
  move=> Hne. apply/eq_fmap => x. rewrite !setmE.
  case: (x =P k2) => [->|_] //. case: eqP => [E|//]. by case: Hne.
Qed.

(* Adding a FRESH entry to the scratch tracker preserves the stack relation
   (a fresh entry cannot be any suspended caller's transit expectation). *)
Lemma stack_match_scrs_extend G0 lP α tmem scrs C0 fb0 prot stk gps Cx w :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  getm scrs Cx = None ->
  stack_match G0 lP α tmem (setm scrs Cx w) C0 fb0 prot stk gps.
Proof.
  move=> Hsm; elim: Hsm
    => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
          L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne Hfresh
       |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
          plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
          Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail IH Hfresh
       |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
          k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
          junkARG cap''
          HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
          Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
          Hnp'' HnpE HneE Htail IH Hfresh].
  - by apply: SM_init; eassumption.
  (* SM_internal no longer rewrites [scrs], so the tail goal is exactly the IH *)
  - apply: SM_internal; try eassumption.
    by apply: IH.
  - have HneCx'' : Cx <> C''.
    { move=> E. subst Cx. by rewrite Hentry in Hfresh. }
    apply: SM_external; try eassumption.
    + rewrite setmE. case: eqP => [E|_]; last exact: Hentry.
      by case: HneCx''; rewrite E.
    + case: (Cx =P C) => [ECx | HneCx].
      * subst Cx. by rewrite setm_over.
      * rewrite (setm_comm _ _ _ _ _ HneCx). apply: IH.
        rewrite setmE. by case: eqP => [E|_] //.
Qed.

(* Fresh frames come Undef-initialized: every slot below the size loads. *)
Lemma memory_load_after_alloc_in tmem Ca n tmem' pt (o : Z) :
  Memory.alloc tmem Ca n = Some (tmem', pt) ->
  (0 <= o < Z.of_nat n)%Z ->
  Memory.load tmem' (Ca, Pointer.block pt, o) = Some Undef.
Proof.
  rewrite /Memory.alloc /Memory.load.
  case E: (getm tmem Ca) => [cm|] //.
  case E2: (ComponentMemory.alloc cm n) => [cm' b] [<- <-] /= Ho.
  rewrite setmE eqxx.
  rewrite (ComponentMemory.load_after_alloc_eq _ _ _ _ E2).
  suff -> : (0 <=? o)%Z && (o <? Z.of_nat n)%Z = true by [].
  lia.
Qed.

(* uniq of a decomposed label list: the label is not in the prefix *)
Lemma uniq_cat_cons_notin (l : label) ls1 ls2 :
  uniq (ls1 ++ l :: ls2) -> l \notin ls1.
Proof.
  rewrite cat_uniq /= => /and3P [_ Hh _].
  move: Hh. rewrite negb_or => /andP [Hn _]. exact: Hn.
Qed.

(* A label with a unique occurrence splits code uniquely. *)
Lemma label_split_unique (l : label) (A B ext rest : code) :
  A ++ ILabel l :: B = ext ++ ILabel l :: rest ->
  uniq (labels_of (A ++ ILabel l :: B)) ->
  A = ext /\ B = rest.
Proof.
  move=> Heq Huq.
  have HnA : l \notin labels_of A.
  { move: Huq. rewrite labels_of_cat /= => Hu.
    exact: uniq_cat_cons_notin Hu. }
  have HnE : l \notin labels_of ext.
  { move: Huq. rewrite Heq labels_of_cat /= => Hu.
    exact: uniq_cat_cons_notin Hu. }
  clear Huq.
  elim: A ext Heq HnA HnE => [|a A' IH] [|e ext'] /=.
  - by move=> [->] _ _.
  - move=> [Ea _] _ HnE. subst e. by move: HnE; rewrite /= inE eqxx.
  - move=> [Ea _] HnA _. subst a. by move: HnA; rewrite /= inE eqxx.
  - move=> [Ea Heq'] HnA HnE. subst e.
    have HnA' : l \notin labels_of A'.
    { move: HnA. case: (a) => //= l0. by rewrite inE negb_or => /andP [_ ?]. }
    have HnE' : l \notin labels_of ext'.
    { move: HnE. case: (a) => //= l0. by rewrite inE negb_or => /andP [_ ?]. }
    case: (IH _ Heq' HnA' HnE') => -> ->. by [].
Qed.

(* The code after a procedure's entry label: the internal prologue, the
   compiled body, and the [Kstop] epilogue. *)
Lemma compile_proc_after_label C0 plm P e s cd s' pl ext rest :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  cd = ext ++ ILabel pl :: rest ->
  uniq (labels_of cd) ->
  exists bodyc sA sB,
    compile_expr C0 (lbp C0) (scr C0) plm e sA = Some (bodyc, sB) /\
    rest = [:: IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP] ++
           push R_AUX1 ++
           push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
           (pop R_ARG ++ pop R_SP ++ [:: IJump]).
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] [Epl]. subst pl0.
  move=> Hdec Huq.
  exists pcode. do 2 eexists. split; first exact: EE.
  move: Ecd.
  case: (Component.eqb C0 Component.main && Procedure.eqb P Procedure.main).
  - case: (immediately_final e).
    + move=> Ecd.
      have Heq : ([:: IHalt] ++ [:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                 ++ ILabel pl ::
                 ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump]))
                 = ext ++ ILabel pl :: rest.
      { rewrite -Hdec -Ecd. by []. }
      have Huq2 : uniq (labels_of
                 (([:: IHalt] ++ [:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
      { suff -> : ([:: IHalt] ++ [:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])) = cd by [].
        by rewrite -Ecd. }
      by case: (label_split_unique _ _ _ _ _ Heq Huq2) => _ <-.
    + move=> Ecd.
      have Heq : ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                 ++ ILabel pl ::
                 ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump]))
                 = ext ++ ILabel pl :: rest.
      { rewrite -Hdec -Ecd. by []. }
      have Huq2 : uniq (labels_of
                 (([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
      { suff -> : ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
                [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                    ILoad R_AUX1 R_AUX2] ++
                push R_AUX2 ++
                [:: IBnz R_AUX2 (odflt 0 (next_label s C0));
                    IConst (IInt 0) R_COM;
                    ILabel (odflt 0 (next_label s C0));
                    IConst (IInt 1) R_AUX2;
                    IStore R_AUX1 R_AUX2; IJal pl] ++
                pop R_ARG ++ pop R_RA ++ pop R_AUX1
                  ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                [:: IBnz R_ARG
                      (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IHalt;
                    ILabel (odflt 0 (setm (next_label s) C0
                         (1 + odflt 0 (next_label s C0)) C0)); IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])) = cd by [].
        by rewrite -Ecd. }
      by case: (label_split_unique _ _ _ _ _ Heq Huq2) => _ <-.
  - move=> Ecd.
      have Heq : ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++ [:: IJal pl] ++
                pop R_RA ++ pop R_AUX1 ++ store_arg (scr C0) R_AUX1 R_AUX2
                  ++ pop R_SP ++ [:: IReturn])
                 ++ ILabel pl ::
                 ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump]))
                 = ext ++ ILabel pl :: rest.
      { rewrite -Hdec -Ecd. by []. }
      have Huq2 : uniq (labels_of
                 (([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++ [:: IJal pl] ++
                pop R_RA ++ pop R_AUX1 ++ store_arg (scr C0) R_AUX1 R_AUX2
                  ++ pop R_SP ++ [:: IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
      { suff -> : ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++ [:: IJal pl] ++
                pop R_RA ++ pop R_AUX1 ++ store_arg (scr C0) R_AUX1 R_AUX2
                  ++ pop R_SP ++ [:: IReturn])
                  ++ ILabel pl ::
                  ([:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                    IAlloc R_SP R_SP] ++
                push R_AUX1 ++
                push R_ARG ++ [:: IMov R_COM R_ARG] ++ pcode ++
                (pop R_ARG ++ pop R_SP ++ [:: IJump])) = cd by [].
        by rewrite -Ecd. }
      by case: (label_split_unique _ _ _ _ _ Heq Huq2) => _ <-.
Qed.

(* Every protected frame has a loadable cell (fresh blocks avoid prot). *)
Lemma stack_match_prot_loadable G0 lP α tmem scrs C0 fb0 prot stk gps Cx bx :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  (Cx, bx) \in prot ->
  exists (o : Z) w, Memory.load tmem (Cx, bx, o) = Some w.
Proof.
  move=> Hsm; elim: Hsm
    => [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
          L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne Hin
       |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
          plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
          Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail IH Hin
       |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
          k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
          junkARG cap''
          HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
          Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
          Hnp'' HnpE HneE Htail IH Hin].
  - move: Hin. rewrite inE => /eqP [E1' E2']. subst Cx bx.
    by exists 0%Z, v0.
  - move: Hin. rewrite inE => /orP [/eqP [E1' E2'] | Hin'].
    + subst Cx bx. by exists (Z.of_nat (2 + size temps')), junkRA.
    + exact: IH Hin'.
  - move: Hin. rewrite inE => /orP [/eqP [E1' E2'] | Hin2].
    + subst Cx bx. inversion Hext; subst; by exists 0%Z, v0.
    + move: Hin2. rewrite inE => /orP [/eqP [E1' E2'] | Hin'].
      * subst Cx bx. by exists (Z.of_nat (2 + size temps'')), junkRA.
      * exact: IH Hin'.
Qed.

(* Updating the RUNNING component's tracker entry preserves the stack relation.
   [SM_external] still shadows the current component's entry in its tail
   ([setm_over]).  [SM_internal] no longer rewrites [scrs] at all — an intra
   activation restores nothing — so the update has to be pushed down its tail
   INDUCTIVELY; hence [elim], not [case]. *)
Lemma stack_match_scrs_update G0 lP α tmem scrs C0 fb0 prot stk gps w :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  stack_match G0 lP α tmem (setm scrs C0 w) C0 fb0 prot stk gps.
Proof.
  elim=> [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
            L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne
         |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
            plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
            Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail IH
         |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
            k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
            junkARG cap''
            HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
            Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
            Hnp'' HnpE HneE Htail IH].
  - by apply: SM_init; eassumption.
  - by apply: SM_internal; eassumption.
  - apply: SM_external; try eassumption.
    + rewrite setmE. case: eqP => [E|_]; last exact: Hentry.
      by case: HneC; rewrite E.
    + by rewrite setm_over.
Qed.

(* The full shape of a compiled STANDARD procedure (callee side of ICall). *)
Lemma compile_proc_shape_std C0 plm P e s cd s' pl :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb C0 Component.main && Procedure.eqb P Procedure.main = false ->
  exists bodyc sA sB,
    compile_expr C0 (lbp C0) (scr C0) plm e sA = Some (bodyc, sB) /\
    cd = ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++ [:: IJal pl] ++
          pop R_RA ++ pop R_AUX1 ++ store_arg (scr C0) R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IReturn])
         ++ ILabel pl ::
         ([:: IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++
          push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
          (pop R_ARG ++ pop R_SP ++ [:: IJump])).
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] [Epl]. subst pl0.
  move=> Hmain.
  exists pcode. do 2 eexists. split; first exact: EE.
  rewrite -Ecd Hmain. by [].
Qed.

(* The full shape of compiled MAIN (dual entry) when its body is not
   immediately final (so no halt pad). *)
Lemma compile_proc_shape_main C0 plm P e s cd s' pl :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb C0 Component.main && Procedure.eqb P Procedure.main = true ->
  immediately_final e = false ->
  exists lm lr bodyc sA sB,
    compile_expr C0 (lbp C0) (scr C0) plm e sA = Some (bodyc, sB) /\
    cd = ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++ push R_RA ++
          [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
              ILoad R_AUX1 R_AUX2] ++
          push R_AUX2 ++
          [:: IBnz R_AUX2 lm; IConst (IInt 0) R_COM; ILabel lm;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
          pop R_ARG ++ pop R_RA ++ pop R_AUX1
            ++ store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
          [:: IBnz R_ARG lr; IHalt; ILabel lr; IReturn])
         ++ ILabel pl ::
         ([:: IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++
          push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
          (pop R_ARG ++ pop R_SP ++ [:: IJump])).
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] [Epl]. subst pl0.
  move=> Hmain Hfin.
  exists (odflt 0 (next_label s C0)),
         (odflt 0 (setm (next_label s) C0
            (1 + odflt 0 (next_label s C0)) C0)),
         pcode.
  do 2 eexists. split; first exact: EE.
  rewrite -Ecd Hmain Hfin. by [].
Qed.

(* main's halt pad: an immediately-final main compiles to IHalt-first code *)
Lemma compile_proc_shape_main_final C0 plm P e s cd s' pl :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb C0 Component.main && Procedure.eqb P Procedure.main = true ->
  immediately_final e = true ->
  exists restH, cd = IHalt :: restH.
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] _ Hmain Hfin.
  rewrite -Ecd Hmain Hfin /=.
  by eexists.
Qed.

(* ==================== diagram: leaf evaluations ==================== *)

Section Diagram.

Variable p : Source.program.
Variable tp : Intermediate.program.

Hypothesis Hwf_p : Source.well_formed_program p.
Hypothesis Hclosed_p : Source.closed_program p.
Hypothesis Hcompile : compile_program p = Some tp.

Let G : global_env := prepare_global_env tp.

(* Draining the join junk: silent administrative steps (labels, and the
   else-branch's taken IBnz over the then-code) lead from junk-wrapped code to
   the canonical continuation code. Registers, memory and the stack are
   untouched. *)
Lemma cont_matchJ_drain α C plm k temps pc jrest :
  cont_matchJ α C plm k jrest temps ->
  code_at G pc jrest ->
  Pointer.component pc = C ->
  (forall Cx C_procs b P_code,
      getm (genv_procedures G) Cx = Some C_procs ->
      getm C_procs b = Some P_code ->
      uniq (labels_of P_code)) ->
  forall gps tmem tregs,
  Register.get R_ONE tregs = Int 1 ->
  exists pc' rest,
    [/\ star CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs, pc'),
        pc' = pc \/ plus CS.step G (gps, tmem, tregs, pc) E0
                        (gps, tmem, tregs, pc'),
        code_at G pc' rest,
        Pointer.component pc' = C /\ Pointer.block pc' = Pointer.block pc
      & cont_match α C plm k rest temps].
Proof.
  move=> Hcm; elim: Hcm pc
    => [k0 rest0 temps0 Hc
       | l k0 rest0 temps0 _ IH
       | lend lc c2 k0 rest0 temps0 _ IH] pc Hcode Hpc Huniq gps tmem tregs
       HONE.
  - exists pc, rest0.
    split; [exact: star_refl | by left | exact: Hcode | by [] | exact: Hc].
  - have SB : CS.step G (gps, tmem, tregs, pc) E0
              (gps, tmem, tregs, Pointer.inc pc).
    { exact: step_label Hcode. }
    have HcT := code_at_tail Hcode.
    have HpcT : Pointer.component (Pointer.inc pc) = C
      by rewrite Pointer.inc_preserves_component.
    case: (IH _ HcT HpcT Huniq gps tmem tregs HONE)
      => [pc' [rest' [Sd Hor Hc' [Ec Eb] Hcm']]].
    exists pc', rest'.
    split.
    + eapply star_trans; [exact: star_one SB | exact: Sd | by []].
    + right. eapply plus_left; [exact: SB | exact: Sd | by []].
    + exact: Hc'.
    + split; [exact: Ec | by rewrite Eb Pointer.inc_preserves_block].
    + exact: Hcm'.
  - case: (Hcode) => [Cp [Pc [pre [post [HgC HgP Ecode Eoff]]]]].
    have Huq := Huniq _ _ _ _ HgC HgP.
    set pre' := pre ++ IBnz R_ONE lend :: ILabel lc :: c2.
    have Edec : Pc = pre' ++ ILabel lend :: (rest0 ++ post).
    { rewrite /pre' Ecode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have Hnotin : lend \notin labels_of pre'.
    { apply: uniq_cat_cons_notin (labels_of (rest0 ++ post)) _.
      move: Huq. rewrite Edec labels_of_cat /=. by []. }
    have Hfind : find_label_in_procedure G pc lend
                 = Some (Pointer.component pc, Pointer.block pc,
                         Z.of_nat (size pre')).
    { exact: find_label_in_procedure_at HgC HgP Edec Hnotin. }
    set pcL := ((Pointer.component pc, Pointer.block pc,
                 Z.of_nat (size pre')) : Pointer.t).
    have SB : CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs, pcL).
    { apply: step_bnz_nz Hcode HONE _ Hfind. by []. }
    have HcL : code_at G pcL (ILabel lend :: rest0).
    { exists Cp, Pc, pre', post.
      split.
      - exact: HgC.
      - exact: HgP.
      - rewrite Edec. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
      - by []. }
    have HpcL : Pointer.component pcL = C by rewrite /pcL /= Hpc.
    case: (IH pcL HcL HpcL Huniq gps tmem tregs HONE)
      => [pc' [rest' [Sd Hor Hc' [Ec Eb] Hcm']]].
    exists pc', rest'.
    split.
    + eapply star_trans; [exact: star_one SB | exact: Sd | by []].
    + right. eapply plus_left; [exact: SB | exact: Sd | by []].
    + exact: Hc'.
    + split; [exact: Ec | by rewrite Eb /pcL].
    + exact: Hcm'.
Qed.

(* plus-typed executors (mirrors of SimCode's exec_push/exec_pop) *)
Lemma exec_push_plus gps mem regs pc r c C0 fb0 sp mem' :
  code_at G pc (push r ++ c) ->
  Register.get R_SP regs = Ptr (C0, fb0, sp) ->
  Register.get R_ONE regs = Int 1 ->
  Pointer.component pc = C0 ->
  Memory.store mem (C0, fb0, sp) (Register.get r regs) = Some mem' ->
  plus CS.step G (gps, mem, regs, pc) E0
       (gps, mem', Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) regs,
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /push /= => Hcode HSP HONE Hcomp Hstore.
  eapply plus_left with (t1 := E0) (t2 := E0); [| |by []].
  - eapply step_store;
      [exact: Hcode | exact: HSP | by rewrite /= Hcomp | exact: Hstore].
  - apply: star_one.
    have Hb := step_binop G gps mem' regs (Pointer.inc pc) Add R_SP R_ONE R_SP
                 c (code_at_tail Hcode).
    by rewrite HSP HONE /= in Hb.
Qed.

Lemma exec_pop_plus gps mem regs pc r c C0 fb0 sp v :
  code_at G pc (pop r ++ c) ->
  Register.get R_SP regs = Ptr (C0, fb0, sp) ->
  Register.get R_ONE regs = Int 1 ->
  Pointer.component pc = C0 ->
  Memory.load mem (C0, fb0, (sp - 1)%Z) = Some v ->
  plus CS.step G (gps, mem, regs, pc) E0
       (gps, mem,
        Register.set r v (Register.set R_SP (Ptr (C0, fb0, (sp - 1)%Z)) regs),
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /pop /= => Hcode HSP HONE Hcomp Hload.
  eapply plus_left with (t1 := E0) (t2 := E0); [| |by []].
  - have Hb := step_binop G gps mem regs pc Minus R_SP R_ONE R_SP _ Hcode.
    rewrite HSP HONE /= in Hb. exact: Hb.
  - apply: star_one.
    eapply step_load;
      [ exact: (code_at_tail Hcode)
      | by rewrite register_get_set_eq
      | by rewrite /= Pointer.inc_preserves_component Hcomp
      | exact: Hload].
Qed.

(* Rebuild [val_inv] from [expr_inv] after the target ran the current
   expression's code: memory untouched, only R_COM and the pc moved (plus
   scratch registers), and the value now injects into R_COM. *)
Lemma expr_to_val α scrs C stk mem k e v arg gps tmem tregs pc fb prot temps
      plm c rest s1 s2 cap tregs' pc' :
  expr_inv p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps
           plm c rest s1 s2 cap ->
  Register.get R_ONE tregs' = Register.get R_ONE tregs ->
  Register.get R_SP tregs' = Register.get R_SP tregs ->
  Register.get R_ARG tregs' = Register.get R_ARG tregs ->
  val_inject α v (Register.get R_COM tregs') ->
  Pointer.component pc' = C ->
  Pointer.block pc' = Pointer.block pc ->
  code_at G pc' rest ->
  val_inv p tp α scrs C stk mem k v arg gps tmem tregs' pc' fb prot temps
          plm rest cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hpc Hcomp Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf
         EONE ESP EARG Hv Epc' Eb' Hcode'.
  split=> //.
  - by rewrite EONE.
  - by rewrite ESP.
  - by rewrite EARG.
  - by move: Hbud; lia.
Qed.

(* [E_val v] leaves: only integer literals compile. One IConst step. *)
Lemma leaf_val_run α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
      plm c rest s1 s2 cap :
  expr_inv p tp α scrs C stk mem k (E_val v) arg gps tmem tregs pc fb prot
           temps plm c rest s1 s2 cap ->
  exists i,
    [/\ v = Int i,
        CS.step G (gps, tmem, tregs, pc) E0
                (gps, tmem, Register.set R_COM (Int i) tregs, Pointer.inc pc)
      & code_at G (Pointer.inc pc) rest].
Proof.
  case=> _ _ _ _ _ _ _ _ _ _ Hcomp Hcode _ _ _ _ _ _ _ _ _ _.
  case: v Hcomp => [i|ptr|] /=; [move=> [Ec _] | by [] | by []].
  subst c.
  exists i. split=> //.
  - exact: step_const Hcode.
  - exact: code_at_tail Hcode.
Qed.

(* [E_arg]: one IMov step; the result is the injected argument. *)
Lemma leaf_arg_run α scrs C stk mem k arg gps tmem tregs pc fb prot temps
      plm c rest s1 s2 cap :
  expr_inv p tp α scrs C stk mem k E_arg arg gps tmem tregs pc fb prot
           temps plm c rest s1 s2 cap ->
  [/\ CS.step G (gps, tmem, tregs, pc) E0
             (gps, tmem,
              Register.set R_COM (Register.get R_ARG tregs) tregs,
              Pointer.inc pc),
      val_inject α arg (Register.get R_ARG tregs)
    & code_at G (Pointer.inc pc) rest].
Proof.
  case=> _ _ _ _ _ _ _ _ HARG _ Hcomp Hcode _ _ _ _ _ _ _ _ _ _.
  move: Hcomp => /= [Ec _]. subst c.
  split=> //.
  - exact: step_mov Hcode.
  - exact: code_at_tail Hcode.
Qed.

(* [E_local]: one IConst step loading the local-buffer pointer; it injects
   because renamings are the identity on [Block.local]. *)
Lemma leaf_local_run α scrs C stk mem k arg gps tmem tregs pc fb prot temps
      plm c rest s1 s2 cap :
  expr_inv p tp α scrs C stk mem k E_local arg gps tmem tregs pc fb prot
           temps plm c rest s1 s2 cap ->
  [/\ CS.step G (gps, tmem, tregs, pc) E0
             (gps, tmem, Register.set R_COM (Ptr (lbp C)) tregs,
              Pointer.inc pc),
      val_inject α (Ptr (C, Block.local, 0%Z)) (Ptr (lbp C))
    & code_at G (Pointer.inc pc) rest].
Proof.
  case=> _ _ Hmem _ _ _ _ _ _ _ Hcomp Hcode _ _ _ _ _ _ _ _ _ _.
  move: Hcomp => /= [Ec _]. subst c.
  split=> //.
  - exact: step_const Hcode.
  - apply: VI_ptr. exact: (inj_local _ (mi_ok _ _ _ Hmem)).
  - exact: code_at_tail Hcode.
Qed.

(* register bookkeeping through concrete set-chains *)
Ltac rget := rewrite /Register.get /Register.set /= !setmE /=.

Ltac is_arith T :=
  match T with
  | context [Z.lt] => idtac | context [Z.le] => idtac | context [@eq Z] => idtac
  | context [lt] => idtac | context [le] => idtac | context [@eq nat] => idtac
  | context [leq] => idtac | context [Z.of_nat] => idtac
  | context [@eq positive] => idtac | context [@eq N] => idtac
  end.

Ltac slia :=
  repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop => tryif is_arith T then fail else clear H end
  end; lia.

(* The [Kstop] epilogue: pop the saved argument, pop the caller's frame pointer,
   and stack-return. Five silent steps; R_COM (the produced value) rides through
   untouched.  The scratch restore that used to sit between the two pops now
   lives in the WRAPPER (see the note on [compile_proc]), so this epilogue no
   longer touches memory at all — hence no [tmem1]/[Memory.store] premise. *)
Lemma epilogue_run C0 gps' tmem tregs pc fb jt vs0 vs1 :
  code_at G pc (pop R_ARG ++ pop R_SP ++ [:: IJump]) ->
  Pointer.component pc = C0 ->
  Register.get R_SP tregs = Ptr (C0, fb, 2%Z) ->
  Register.get R_ONE tregs = Int 1 ->
  Memory.load tmem (C0, fb, 0%Z) = Some vs0 ->
  Memory.load tmem (C0, fb, 1%Z) = Some vs1 ->
  Pointer.component jt = C0 ->
  exists tregs1,
    [/\ star CS.step G (jt :: gps', tmem, tregs, pc) E0
             (gps', tmem, tregs1, jt),
        Register.get R_COM tregs1 = Register.get R_COM tregs,
        Register.get R_ONE tregs1 = Int 1,
        Register.get R_SP tregs1 = vs0
      & Register.get R_ARG tregs1 = vs1].
Proof.
  move=> Hcode Hpc HSP HONE Hl0 Hl1 Hjt.
  (* pop R_ARG : the saved argument (slot 1) *)
  have SA := exec_pop _ _ _ _ _ R_ARG _ _ _ _ _ Hcode HSP HONE Hpc Hl1.
  set regsA := Register.set R_ARG vs1 _ in SA.
  set pcA := Pointer.inc (Pointer.inc pc) in SA.
  have HpcA : Pointer.component pcA = C0
    by rewrite /pcA !Pointer.inc_preserves_component.
  have HcA := code_at_tail (code_at_tail Hcode).
  have HSPA : Register.get R_SP regsA = Ptr (C0, fb, 1%Z) by rget.
  have HONEA : Register.get R_ONE regsA = Int 1 by rget.
  (* pop R_SP : the caller's frame pointer (slot 0) *)
  have SD := exec_pop _ _ _ _ _ R_SP _ _ _ _ _ HcA HSPA HONEA HpcA Hl0.
  set regsD := Register.set R_SP vs0 _ in SD.
  set pcD := Pointer.inc (Pointer.inc pcA) in SD.
  have HpcD : Pointer.component pcD = C0
    by rewrite /pcD !Pointer.inc_preserves_component.
  have HcD := code_at_tail (code_at_tail HcA).
  (* IJump : stack return to [jt] *)
  have SE : star CS.step G (jt :: gps', tmem, regsD, pcD) E0
                 (gps', tmem, regsD, jt).
  { apply: star_one. apply: step_jump HcD _. by rewrite Hjt HpcD. }
  exists regsD.
  split.
  - exact: (star_trans (SA (jt :: gps'))
             (star_trans (SD (jt :: gps')) SE erefl) erefl).
  - by rget.
  - by rget.
  - by rget.
  - by rget.
Qed.

(* Main's dual-entry drain: pop the linkage and the Int-0 context marker,
   fall through the IBnz onto the IHalt. Seven silent steps. *)
Lemma main_drain_run gps tmem tmem1 tregs pc fbE lret v0m v1m v2m :
  code_at G pc (pop R_ARG ++ pop R_RA ++ pop R_AUX1
                ++ store_arg (scr Component.main) R_AUX1 R_AUX2 ++ pop R_SP
                ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
  Pointer.component pc = Component.main ->
  Register.get R_SP tregs = Ptr (Component.main, fbE, 4%Z) ->
  Register.get R_ONE tregs = Int 1 ->
  fbE <> 1 ->
  Memory.load tmem (Component.main, fbE, 0%Z) = Some v0m ->
  Memory.load tmem (Component.main, fbE, 1%Z) = Some v1m ->
  Memory.load tmem (Component.main, fbE, 2%Z) = Some v2m ->
  Memory.load tmem (Component.main, fbE, 3%Z) = Some (Int 0) ->
  Memory.store tmem (Component.main, 1, 0%Z) v1m = Some tmem1 ->
  exists tregs' pcH,
    star CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem1, tregs', pcH) /\
    executing G pcH IHalt.
Proof.
  move=> Hcode Hpc HSP HONE HfbE1 Hl0 Hl1 Hl2 Hl3 Hstore.
  (* pop R_ARG : the context marker (slot 3) *)
  have SA := exec_pop _ _ _ _ _ R_ARG _ _ _ _ _ Hcode HSP HONE Hpc Hl3.
  set regsA := Register.set R_ARG (Int 0) _ in SA.
  set pcA := Pointer.inc (Pointer.inc pc) in SA.
  have HpcA : Pointer.component pcA = Component.main
    by rewrite /pcA !Pointer.inc_preserves_component.
  have HcA := code_at_tail (code_at_tail Hcode).
  have HSPA : Register.get R_SP regsA = Ptr (Component.main, fbE, 3%Z) by rget.
  have HONEA : Register.get R_ONE regsA = Int 1 by rget.
  (* pop R_RA : the saved return (slot 2) *)
  have SB := exec_pop _ _ _ _ _ R_RA _ _ _ _ _ HcA HSPA HONEA HpcA Hl2.
  set regsB := Register.set R_RA v2m _ in SB.
  set pcB := Pointer.inc (Pointer.inc pcA) in SB.
  have HpcB : Pointer.component pcB = Component.main
    by rewrite /pcB !Pointer.inc_preserves_component.
  have HcB := code_at_tail (code_at_tail HcA).
  have HSPB : Register.get R_SP regsB = Ptr (Component.main, fbE, 2%Z) by rget.
  have HONEB : Register.get R_ONE regsB = Int 1 by rget.
  (* pop R_AUX1 : the INHERITED SCRATCH the wrapper saved on entry (slot 1) *)
  have SBB := exec_pop _ _ _ _ _ R_AUX1 _ _ _ _ _ HcB HSPB HONEB HpcB Hl1.
  set regsBB := Register.set R_AUX1 v1m _ in SBB.
  set pcBB := Pointer.inc (Pointer.inc pcB) in SBB.
  have HpcBB : Pointer.component pcBB = Component.main
    by rewrite /pcBB !Pointer.inc_preserves_component.
  have HcBB := code_at_tail (code_at_tail HcB).
  (* store_arg : put it back into the component's scratch cell *)
  have HgBB : Register.get R_AUX1 regsBB = v1m by rget.
  have Hstore' : Memory.store tmem (Component.main, 1, 0%Z)
                   (Register.get R_AUX1 regsBB) = Some tmem1 by rewrite HgBB.
  have SBC := exec_store_arg _ _ _ _ _ (scr Component.main) R_AUX1 R_AUX2 _ _
                HcBB (esym HpcBB) (ltac:(by [])) Hstore'.
  set regsBC := Register.set R_AUX2 (Ptr (scr Component.main)) _ in SBC.
  set pcBC := Pointer.inc (Pointer.inc pcBB) in SBC.
  have HpcBC : Pointer.component pcBC = Component.main
    by rewrite /pcBC !Pointer.inc_preserves_component.
  have HcBC := code_at_tail (code_at_tail HcBB).
  have HSPBC : Register.get R_SP regsBC = Ptr (Component.main, fbE, 1%Z) by rget.
  have HONEBC : Register.get R_ONE regsBC = Int 1 by rget.
  (* pop R_SP : the caller's frame pointer (slot 0), read AFTER the store *)
  have Hl0' : Memory.load tmem1 (Component.main, fbE, 0%Z) = Some v0m.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore) //.
    by move=> E; inversion E; apply: HfbE1. }
  have SC := exec_pop _ _ _ _ _ R_SP _ _ _ _ _ HcBC HSPBC HONEBC HpcBC Hl0'.
  set regsC := Register.set R_SP v0m _ in SC.
  set pcC := Pointer.inc (Pointer.inc pcBC) in SC.
  have HcC := code_at_tail (code_at_tail HcBC).
  have HgC : Register.get R_ARG regsC = Int 0 by rget.
  have SD : star CS.step G (gps, tmem1, regsC, pcC) E0
                 (gps, tmem1, regsC, Pointer.inc pcC).
  { apply: star_one. exact: step_bnz_z HcC HgC. }
  exists regsC, (Pointer.inc pcC).
  split.
  - exact: (star_trans (SA gps)
             (star_trans (SB gps)
               (star_trans (SBB gps)
                 (star_trans (SBC gps)
                   (star_trans (SC gps) SD erefl) erefl) erefl) erefl) erefl).
  - apply: executing_halt. exact: (code_at_tail HcC).
Qed.

(* The full final drain: a value sits in R_COM at [Kstop] with an empty source
   stack; the target runs the epilogue, stack-returns into main's dual entry,
   and drains onto the IHalt. Produces the MS_halted facts. *)
Lemma final_drain α scrs C mem gps tmem tregs pc fb prot temps plm rest :
  mem_inject α mem tmem ->
  scratch_priv α ->
  frame_priv α C fb ->
  (forall C', C' \in domm (Intermediate.prog_interface tp) ->
     exists w, Memory.load tmem (C', 1, 0%Z) = Some w) ->
  C \in domm (Intermediate.prog_interface tp) ->
  Register.get R_ONE tregs = Int 1 ->
  Register.get R_SP tregs = Ptr (C, fb, Z.of_nat (2 + size temps)) ->
  Pointer.component pc = C ->
  code_at G pc rest ->
  cont_match α C plm Kstop rest temps ->
  stack_match G (labelsP p) α tmem scrs C fb prot [::] gps ->
  exists tmem1 tregs1 pcH,
    [/\ star CS.step G (gps, tmem, tregs, pc) E0 ([::], tmem1, tregs1, pcH),
        executing G pcH IHalt
      & mem_inject α mem tmem1].
Proof.
  move=> Hmem Hscrp Hpriv Hscr_all Hdom HONE HSP Hpc Hcode Hcont Hsm.
  (* the continuation is [Kstop]: the code is the epilogue, no temps *)
  inversion Hcont; subst.
  (* the stack is empty: SM_init pins main's dual-entry linkage *)
  inversion Hsm; subst.
  rewrite -H in Hscr_all Hdom HSP Hcode.
  (* the epilogue no longer touches memory: the scratch restore moved to the
     wrapper, i.e. into [main_drain_run] below *)
  have [tregs1 [Sepi _ HONE1 HSP1 _]] :=
    epilogue_run _ [::] _ _ _ _ ret_ext _ _
                 Hcode (esym H) HSP HONE H0 H1 H7.
  (* the scratch store is now performed BY the drain (the wrapper's restore) *)
  have [w0 Hw0] := Hscr_all _ Hdom.
  have [tmem1 Hstore] := Memory.store_after_load _ _ _ v1 Hw0.
  (* the drain run *)
  have [tregs2 [pcH [Sdrain Hhalt]]] :=
    main_drain_run [::] tmem tmem1 tregs1 ret_ext fb_ext lret v0 v1 vx
                   H8 H7 HSP1 HONE1 (proj1 H6) H2 H3 H4 H5 Hstore.
  exists tmem1, tregs2, pcH.
  split=> //.
  - exact: (star_trans Sepi Sdrain erefl).
  - apply: store_outside_inject Hmem _ Hstore.
    move=> b0 /=. exact: Hscrp.
Qed.

(* ==================== diagram: value-consuming steps ==================== *)

(* KS_Seq2: drain any join junk, then a stutter — the source drops the value
   and moves into e2 with no further target step. *)
Lemma diagram_seq2 α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
      plm rest cap e2 :
  val_inv p tp α scrs C stk mem (Kseq e2 k) v arg gps tmem tregs pc fb prot
          temps plm rest cap ->
  exists pc' c2 rest' sA sB,
    [/\ star CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs, pc'),
        pc' = pc \/ plus CS.step G (gps, tmem, tregs, pc) E0
                        (gps, tmem, tregs, pc')
      & expr_inv p tp α scrs C stk mem k e2 arg gps tmem tregs pc' fb prot
                 temps plm c2 rest' sA sB cap].
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs HONE)
    => [pc' [rest1 [Sd Hor Hc' [Ec Eb] Hcm']]].
  case: (cont_match_seq_inv Hcm') => [c2 [rest0 [s1 [s2 [E2 Erest Hk]]]]].
  subst rest1.
  exists pc', c2, rest0, s1, s2.
  split; [exact: Sd | exact: Hor |].
  split.
  - exact: Hplm.
  - exact: Hdom.
  - exact: Hmem.
  - exact: Hscrs.
  - exact: Hflag.
  - exact: Hall.
  - exact: HONE.
  - exact: HSP.
  - exact: HARG.
  - exact: Ec.
  - exact: E2.
  - exact: Hc'.
  - exact: Hk.
  - exact: Huniq.
  - exact: Hpriv.
  - exact: Hscrp.
  - exact: Htemps.
  - exact: Hcap.
  - exact: Hbud.
  - exact: Hprot.
  - exact: Hstack.
  - exact: Hmnf.
Qed.

(* KS_Binop2: drain, then push the operand and descend. *)
Lemma diagram_binop2 α scrs C stk mem k v1 arg gps tmem tregs pc fb prot temps
      plm rest cap op e2 :
  val_inv p tp α scrs C stk mem (Kbinop1 op e2 k) v1 arg gps tmem tregs pc fb
          prot temps plm rest cap ->
  exists pcF tmem' cd rest' sA sB,
    plus CS.step G (gps, tmem, tregs, pc) E0
         (gps, tmem',
          Register.set R_SP
            (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)) tregs,
          pcF) /\
    expr_inv p tp α scrs C stk mem (Kbinop2 op v1 k) e2 arg gps tmem'
             (Register.set R_SP
                (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)) tregs)
             pcF fb prot
             (Register.get R_COM tregs :: temps) plm cd rest' sA sB cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs HONE)
    => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_binop1_inv Hcm') => [cd [rest0 [s1 [s2 [E2 Erest Hk]]]]].
  subst rest1.
  have [w Hw] : exists w,
      Memory.load tmem (C, fb, Z.of_nat (2 + size temps)) = Some w.
  { apply: Hcap. move: Hbud => /=. lia. }
  have [tmem' Hstore] :=
    Memory.store_after_load _ _ _ (Register.get R_COM tregs) Hw.
  have Hne1 : forall (C1 : Component.id) (o : Z),
      (C, fb, Z.of_nat (2 + size temps)) <> (C1, 1, o) :> Pointer.t.
  { move=> C1 o E. inversion E. by case: Hpriv => + _; apply. }
  have Pp := exec_push_plus gps tmem tregs pcD R_COM _ _ _ _ tmem'
               HcD HSP HONE Ec Hstore.
  exists (Pointer.inc (Pointer.inc pcD)), tmem', cd,
         (pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest0),
         s1, s2.
  split.
  - eapply star_plus_trans; [exact: Sd | exact: Pp | by []].
  - split.
    + exact: Hplm.
    + exact: Hdom.
    + apply: store_outside_inject Hmem _ Hstore.
      move=> b0 /=. exact: (proj2 Hpriv).
    + move=> C' w' /Hscrs Hl.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + move=> C' /Hall [w' Hl]. exists w'.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + by rget.
    + rget. congr Ptr. congr (_, _). rewrite /=. lia.
    + by rget.
    + by rewrite !Pointer.inc_preserves_component.
    + exact: E2.
    + exact: code_at_tail (code_at_tail HcD).
    + apply: CMJ_base. exact: CM_binop2 Hcom Hk.
    + exact: Huniq.
    + exact: Hpriv.
    + exact: Hscrp.
    + move=> i. case: i => [_|i Hi].
      * have -> : Z.of_nat (1 + size (Register.get R_COM tregs :: temps) - 0)
                = Z.of_nat (2 + size temps).
        { rewrite [size (_ :: _)]/=. lia. }
        exact: Memory.load_after_store_eq Hstore.
      * have -> : Z.of_nat (1 + size (Register.get R_COM tregs :: temps)
                            - i.+1)
                = Z.of_nat (1 + size temps - i).
        { rewrite [size (_ :: _)]/=. lia. }
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore); last first.
        { move=> E. inversion E. lia. }
        apply: Htemps. move: Hi. rewrite /=. lia.
    + exact: frame_cap_store Hcap Hstore.
    + move: Hbud => /=. lia.
    + exact: Hprot.
    + apply: stack_match_store Hstack Hstore Hprot _.
      move=> _. lia.
    + exact: Hmnf.
Qed.

(* KS_Assign2: drain, then push the operand and descend. *)
Lemma diagram_assign2 α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
      plm rest cap e1 :
  val_inv p tp α scrs C stk mem (Kassign1 e1 k) v arg gps tmem tregs pc fb
          prot temps plm rest cap ->
  exists pcF tmem' cd rest' sA sB,
    plus CS.step G (gps, tmem, tregs, pc) E0
         (gps, tmem',
          Register.set R_SP
            (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)) tregs,
          pcF) /\
    expr_inv p tp α scrs C stk mem (Kassign2 v k) e1 arg gps tmem'
             (Register.set R_SP
                (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)) tregs)
             pcF fb prot
             (Register.get R_COM tregs :: temps) plm cd rest' sA sB cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs HONE)
    => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_assign1_inv Hcm') => [cd [rest0 [s1 [s2 [E2 Erest Hk]]]]].
  subst rest1.
  have [w Hw] : exists w,
      Memory.load tmem (C, fb, Z.of_nat (2 + size temps)) = Some w.
  { apply: Hcap. move: Hbud => /=. lia. }
  have [tmem' Hstore] :=
    Memory.store_after_load _ _ _ (Register.get R_COM tregs) Hw.
  have Hne1 : forall (C1 : Component.id) (o : Z),
      (C, fb, Z.of_nat (2 + size temps)) <> (C1, 1, o) :> Pointer.t.
  { move=> C1 o E. inversion E. by case: Hpriv => + _; apply. }
  have Pp := exec_push_plus gps tmem tregs pcD R_COM _ _ _ _ tmem'
               HcD HSP HONE Ec Hstore.
  exists (Pointer.inc (Pointer.inc pcD)), tmem', cd,
         (pop R_AUX1 ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0),
         s1, s2.
  split.
  - eapply star_plus_trans; [exact: Sd | exact: Pp | by []].
  - split.
    + exact: Hplm.
    + exact: Hdom.
    + apply: store_outside_inject Hmem _ Hstore.
      move=> b0 /=. exact: (proj2 Hpriv).
    + move=> C' w' /Hscrs Hl.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + move=> C' /Hall [w' Hl]. exists w'.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstore).
    + by rget.
    + rget. congr Ptr. congr (_, _). rewrite /=. lia.
    + by rget.
    + by rewrite !Pointer.inc_preserves_component.
    + exact: E2.
    + exact: code_at_tail (code_at_tail HcD).
    + apply: CMJ_base. exact: CM_assign2 Hcom Hk.
    + exact: Huniq.
    + exact: Hpriv.
    + exact: Hscrp.
    + move=> i. case: i => [_|i Hi].
      * have -> : Z.of_nat (1 + size (Register.get R_COM tregs :: temps) - 0)
                = Z.of_nat (2 + size temps).
        { rewrite [size (_ :: _)]/=. lia. }
        exact: Memory.load_after_store_eq Hstore.
      * have -> : Z.of_nat (1 + size (Register.get R_COM tregs :: temps)
                            - i.+1)
                = Z.of_nat (1 + size temps - i).
        { rewrite [size (_ :: _)]/=. lia. }
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore); last first.
        { move=> E. inversion E. lia. }
        apply: Htemps. move: Hi. rewrite /=. lia.
    + exact: frame_cap_store Hcap Hstore.
    + move: Hbud => /=. lia.
    + exact: Hprot.
    + apply: stack_match_store Hstack Hstore Hprot _.
      move=> _. lia.
    + exact: Hmnf.
Qed.

(* KS_BinopEval: drain, pop the spilled operand, combine. *)
Lemma diagram_binop_eval α scrs C stk mem k v1 v2 arg gps tmem tregs pc fb
      prot temps plm rest cap op :
  val_inv p tp α scrs C stk mem (Kbinop2 op v1 k) v2 arg gps tmem tregs pc fb
          prot temps plm rest cap ->
  exists tregs' pcF rest' temps',
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs', pcF) /\
    val_inv p tp α scrs C stk mem k (eval_binop op v1 v2) arg gps tmem
            tregs' pcF fb prot temps' plm rest' cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_binop2_inv Hcm')
    => [tv [temps' [rest0 [Hvtv Etemps Erest Hk]]]].
  subst rest1 temps.
  have Hload : Memory.load tmem
      (C, fb, (Z.of_nat (2 + size (tv :: temps')) - 1)%Z) = Some tv.
  { have -> : (Z.of_nat (2 + size (tv :: temps')) - 1)%Z
            = Z.of_nat (1 + size (tv :: temps') - 0).
    { rewrite [size (_ :: _)]/=. lia. }
    exact: (Htemps 0 (ltn0Sn _)). }
  have Pp := exec_pop_plus gps tmem tregs pcD R_AUX1 _ _ _ _ _
               HcD HSP HONE Ec Hload.
  set regsA := Register.set R_AUX1 tv _ in Pp.
  set pcA := Pointer.inc (Pointer.inc pcD) in Pp.
  have HcA := code_at_tail (code_at_tail HcD).
  have SB : CS.step G (gps, tmem, regsA, pcA) E0
            (gps, tmem,
             Register.set R_COM
               (eval_binop op (Register.get R_AUX1 regsA)
                              (Register.get R_COM regsA)) regsA,
             Pointer.inc pcA).
  { exact: step_binop HcA. }
  exists (Register.set R_COM
            (eval_binop op (Register.get R_AUX1 regsA)
                           (Register.get R_COM regsA)) regsA),
         (Pointer.inc pcA), rest0, temps'.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_star_trans; [exact: Pp | exact: star_one SB | by []].
  - have HA1 : Register.get R_AUX1 regsA = tv by rget.
    have HCM : Register.get R_COM regsA = Register.get R_COM tregs by rget.
    split.
    + exact: Hplm.
    + exact: Hdom.
    + exact: Hmem.
    + exact: Hscrs.
    + exact: Hflag.
    + exact: Hall.
    + by rget.
    + have -> : Z.of_nat (2 + size temps')
              = (Z.of_nat (2 + size (tv :: temps')) - 1)%Z.
      { rewrite [size (_ :: _)]/=. lia. }
      by rget.
    + by rget.
    + rewrite register_get_set_eq HA1 HCM.
      exact: eval_binop_inject (mi_ok _ _ _ Hmem) Hvtv Hcom.
    + by rewrite !Pointer.inc_preserves_component Ec.
    + exact: code_at_tail HcA.
    + exact: Hk.
    + exact: Huniq.
    + exact: Hpriv.
    + exact: Hscrp.
    + move=> i Hi.
      have -> : Z.of_nat (1 + size temps' - i)
              = Z.of_nat (1 + size (tv :: temps') - i.+1).
      { rewrite [size (_ :: _)]/=. lia. }
      have -> : nth Undef temps' i = nth Undef (tv :: temps') i.+1 by [].
      apply: Htemps. rewrite /=. lia.
    + exact: Hcap.
    + move: Hbud => /=. lia.
    + exact: Hprot.
    + exact: Hstack.
    + exact: Hmnf.
Qed.

(* KS_DerefEval: drain, then one ILoad step via [mi_load]. *)
Lemma diagram_deref_eval α scrs C stk mem k arg gps tmem tregs pc fb
      prot temps plm rest cap bp op' v :
  val_inv p tp α scrs C stk mem (Kderef k) (Ptr (C, bp, op')) arg gps tmem
          tregs pc fb prot temps plm rest cap ->
  Memory.load mem (C, bp, op') = Some v ->
  exists tregs' pcF rest',
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs', pcF) /\
    val_inv p tp α scrs C stk mem k v arg gps tmem tregs' pcF
            fb prot temps plm rest' cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf Hld.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_deref_inv Hcm') => [rest0 [Erest Hk]]. subst rest1.
  case: (val_inject_ptr_l _ _ _ _ _ Hcom) => [b'' [Hα Ecom]].
  case: (load_inject Hmem Hα Hld) => [tv [Hldt Hvtv]].
  have SB : CS.step G (gps, tmem, tregs, pcD) E0
            (gps, tmem, Register.set R_COM tv tregs, Pointer.inc pcD).
  { apply: step_load HcD Ecom _ Hldt. by rewrite /= Ec. }
  exists (Register.set R_COM tv tregs), (Pointer.inc pcD), rest0.
  split.
  - eapply star_plus_trans; [exact: Sd | exact: plus_one SB | by []].
  - split.
    + exact: Hplm.
    + exact: Hdom.
    + exact: Hmem.
    + exact: Hscrs.
    + exact: Hflag.
    + exact: Hall.
    + by rget.
    + by rget.
    + by rget.
    + rewrite register_get_set_eq. exact: Hvtv.
    + by rewrite Pointer.inc_preserves_component Ec.
    + exact: code_at_tail HcD.
    + exact: Hk.
    + exact: Huniq.
    + exact: Hpriv.
    + exact: Hscrp.
    + exact: Htemps.
    + exact: Hcap.
    + exact: Hbud.
    + exact: Hprot.
    + exact: Hstack.
    + exact: Hmnf.
Qed.

(* KS_AssignEval: drain, pop the spilled value, store through the α-image
   of the address, restore R_COM. *)
Lemma diagram_assign_eval α scrs C stk mem mem' k v arg gps tmem tregs pc fb
      prot temps plm rest cap bp op' :
  val_inv p tp α scrs C stk mem (Kassign2 v k) (Ptr (C, bp, op')) arg gps tmem
          tregs pc fb prot temps plm rest cap ->
  Memory.store mem (C, bp, op') v = Some mem' ->
  exists tmem' tregs' pcF rest' temps',
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem', tregs', pcF) /\
    val_inv p tp α scrs C stk mem' k v arg gps tmem' tregs' pcF
            fb prot temps' plm rest' cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf Hst.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_assign2_inv Hcm')
    => [tv [temps' [rest0 [Hvtv Etemps Erest Hk]]]].
  subst rest1 temps.
  case: (val_inject_ptr_l _ _ _ _ _ Hcom) => [b'' [Hα Ecom]].
  case: (store_inject Hmem Hα Hvtv Hst) => [tmem' [Hstt Hmem']].
  have Hn1 : b'' <> 1.
  { move=> E. subst b''. exact: (Hscrp _ _ Hα). }
  have Hnefb : b'' <> fb.
  { move=> E. subst b''. exact: (proj2 Hpriv _ Hα). }
  have Hne1 : forall (C1 : Component.id) (o : Z),
      (C, b'', op') <> (C1, 1, o) :> Pointer.t.
  { move=> C1 o E. inversion E. by apply: Hn1. }
  have Hnef : forall (o : Z),
      (C, b'', op') <> (C, fb, o) :> Pointer.t.
  { move=> o E. inversion E. by apply: Hnefb. }
  have Hload : Memory.load tmem
      (C, fb, (Z.of_nat (2 + size (tv :: temps')) - 1)%Z) = Some tv.
  { have -> : (Z.of_nat (2 + size (tv :: temps')) - 1)%Z
            = Z.of_nat (1 + size (tv :: temps') - 0).
    { rewrite [size (_ :: _)]/=. lia. }
    exact: (Htemps 0 (ltn0Sn _)). }
  have Pp := exec_pop_plus gps tmem tregs pcD R_AUX1 _ _ _ _ _
               HcD HSP HONE Ec Hload.
  set regsA := Register.set R_AUX1 tv _ in Pp.
  set pcA := Pointer.inc (Pointer.inc pcD) in Pp.
  have HcA := code_at_tail (code_at_tail HcD).
  have HCA : Register.get R_COM regsA = Ptr (C, b'', op') by rget.
  have HA1 : Register.get R_AUX1 regsA = tv by rget.
  have Hstt' : Memory.store tmem (C, b'', op') (Register.get R_AUX1 regsA)
               = Some tmem' by rewrite HA1.
  have SB : CS.step G (gps, tmem, regsA, pcA) E0
            (gps, tmem', regsA, Pointer.inc pcA).
  { apply: step_store HcA HCA _ Hstt'.
    by rewrite /= /pcA !Pointer.inc_preserves_component Ec. }
  have HcB := code_at_tail HcA.
  have SC : CS.step G (gps, tmem', regsA, Pointer.inc pcA) E0
            (gps, tmem',
             Register.set R_COM (Register.get R_AUX1 regsA) regsA,
             Pointer.inc (Pointer.inc pcA)).
  { exact: step_mov HcB. }
  exists tmem',
         (Register.set R_COM (Register.get R_AUX1 regsA) regsA),
         (Pointer.inc (Pointer.inc pcA)), rest0, temps'.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_star_trans; [exact: Pp | | by []].
    eapply star_trans; [exact: star_one SB | exact: star_one SC | by []].
  - split.
    + exact: Hplm.
    + exact: Hdom.
    + exact: Hmem'.
    + move=> C' w' /Hscrs Hl.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstt).
    + by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstt).
    + move=> C' /Hall [w' Hl]. exists w'.
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hne1 _ _) Hstt).
    + by rget.
    + have -> : Z.of_nat (2 + size temps')
              = (Z.of_nat (2 + size (tv :: temps')) - 1)%Z.
      { rewrite [size (_ :: _)]/=. lia. }
      by rget.
    + by rget.
    + rewrite register_get_set_eq HA1. exact: Hvtv.
    + by rewrite !Pointer.inc_preserves_component Ec.
    + exact: code_at_tail HcB.
    + exact: Hk.
    + exact: Huniq.
    + exact: Hpriv.
    + exact: Hscrp.
    + move=> i Hi.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hnef _) Hstt).
      have -> : Z.of_nat (1 + size temps' - i)
              = Z.of_nat (1 + size (tv :: temps') - i.+1).
      { rewrite [size (_ :: _)]/=. lia. }
      have -> : nth Undef temps' i = nth Undef (tv :: temps') i.+1 by [].
      apply: Htemps. rewrite /=. lia.
    + exact: frame_cap_store Hcap Hstt.
    + move: Hbud => /=. lia.
    + exact: Hprot.
    + have Hnp : (C, b'') \notin prot.
      { apply/negP => Hin.
        exact: (stack_match_prot_priv _ _ _ _ _ _ _ _ _ _ _ _
                  Hstack Hin bp Hα). }
      apply: stack_match_store Hstack Hstt Hnp _.
      move=> E. exfalso. inversion E. by apply: Hnefb.
    + exact: Hmnf.
Qed.

(* KS_AllocEval: drain, then one IAlloc step; lock-step allocation extends
   the renaming onto the fresh blocks. *)
Lemma diagram_alloc_eval α scrs C stk mem mem' k arg gps tmem tregs pc fb
      prot temps plm rest cap size ptr :
  val_inv p tp α scrs C stk mem (Kalloc k) (Int size) arg gps tmem
          tregs pc fb prot temps plm rest cap ->
  (size > 0)%Z ->
  Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
  exists α' tmem' tregs' pcF rest',
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem', tregs', pcF) /\
    val_inv p tp α' scrs C stk mem' k (Ptr ptr) arg gps tmem' tregs'
            pcF fb prot temps plm rest' cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf Hpos Hal.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_alloc_inv Hcm') => [rest0 [Erest Hk]]. subst rest1.
  have Ecom := val_inject_int_l _ _ _ Hcom.
  case: (alloc_inject Hmem Hal)
    => [tmem' [ptrt [bs [bt [Halt [[Eps Ept] Hrle Hext Hmem']]]]]].
  have Hfresh : forall (o : Z) w,
      Memory.load tmem (C, bt, o) = Some w -> False.
  { have := memory_alloc_fresh _ _ _ _ _ (mi_wf_t _ _ _ Hmem) Halt.
    by rewrite Ept. }
  have Hnew : forall Cx b0 bx,
      extend α C bs bt Cx b0 = Some bx ->
      α Cx b0 = Some bx \/ (Cx = C /\ bx = bt).
  { move=> Cx b0 bx. rewrite /extend.
    case: ifP => [/andP [/eqP -> _] [<-] | _ H]; [by right | by left]. }
  have Ltr : forall C1 b1 (o : Z) w,
      Memory.load tmem (C1, b1, o) = Some w ->
      Memory.load tmem' (C1, b1, o) = Some w.
  { move=> C1 b1 o w Hl.
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halt) //.
    rewrite Ept. move=> [E1 E2]. subst C1 b1. exact: Hfresh Hl. }
  have SB : CS.step G (gps, tmem, tregs, pcD) E0
            (gps, tmem', Register.set R_COM (Ptr ptrt) tregs,
             Pointer.inc pcD).
  { apply: step_alloc HcD Ecom Hpos _. by rewrite Ec. }
  exists (extend α C bs bt), tmem',
         (Register.set R_COM (Ptr ptrt) tregs), (Pointer.inc pcD), rest0.
  split.
  - eapply star_plus_trans; [exact: Sd | exact: plus_one SB | by []].
  - split.
    + exact: Hplm.
    + exact: Hdom.
    + exact: Hmem'.
    + move=> C' w' /Hscrs Hl. exact: Ltr Hl.
    + exact: Ltr Hflag.
    + move=> C' /Hall [w' Hl]. exists w'. exact: Ltr Hl.
    + by rget.
    + by rget.
    + have HARG' := val_inject_rle _ _ _ _ Hrle HARG.
      by rget.
    + rewrite register_get_set_eq Eps Ept.
      exact: VI_ptr Hext.
    + by rewrite Pointer.inc_preserves_component Ec.
    + exact: code_at_tail HcD.
    + exact: cont_matchJ_rle Hrle Hk.
    + exact: Huniq.
    + split; first by case: Hpriv.
      move=> b0 HA. case: (Hnew _ _ _ HA) => [HA0 | [_ E2]].
      * exact: (proj2 Hpriv) HA0.
      * subst bt.
        have [w0 Hw0] : exists w0, Memory.load tmem (C, fb, 0%Z) = Some w0.
        { apply: Hcap. move: Hbud. lia. }
        exact: Hfresh Hw0.
    + move=> C' b0 HA. case: (Hnew _ _ _ HA) => [HA0 | [E1 E2]].
      * exact: Hscrp HA0.
      * subst C' bt.
        have [w0 Hw0] := Hall _ Hdom.
        exact: Hfresh Hw0.
    + move=> i Hi. apply: Ltr. exact: Htemps Hi.
    + move=> j Hj. case: (Hcap j Hj) => w Hw. exists w. exact: Ltr Hw.
    + move: Hbud => /=. lia.
    + exact: Hprot.
    + have Ebt : Pointer.block ptrt = bt by rewrite Ept.
      exact: stack_match_alloc Hstack Halt Ebt Hrle Hnew Hfresh.
    + exact: Hmnf.
Qed.

(* KS_If2: drain, then the branch. Taken (i<>0): IBnz to the then-label plus
   the label step; the then-code runs against a label-junk continuation.
   Fallthrough (i=0): one IBnz step; the else-code runs against the
   jump-over-then junk continuation. *)
Lemma diagram_if2 α scrs C stk mem k arg gps tmem tregs pc fb prot temps
      plm rest cap e2 e3 i :
  val_inv p tp α scrs C stk mem (Kif e2 e3 k) (Int i) arg gps tmem tregs pc
          fb prot temps plm rest cap ->
  exists pcF cd rest' sA sB,
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps, tmem, tregs, pcF) /\
    expr_inv p tp α scrs C stk mem k (if i != 0%Z then e2 else e3) arg gps
             tmem tregs pcF fb prot temps plm cd rest' sA sB cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_if_inv Hcm')
    => [c2 [c3 [lconseq [lend [rest0 [s2a [s2b [s3a [s3b
       [E2 E3 Erest Hk]]]]]]]]]].
  subst rest1.
  have Ecom := val_inject_int_l _ _ _ Hcom.
  case Hi: (i != 0%Z).
  - (* then-branch *)
    case: (HcD) => [Cp [Pc [pre [post [HgC HgP Ecode Eoff]]]]].
    have Huq := Huniq _ _ _ _ HgC HgP.
    set pre' := pre ++ IBnz R_COM lconseq :: c3 ++ [:: IBnz R_ONE lend].
    have Edec : Pc = pre'
                     ++ ILabel lconseq :: (c2 ++ ILabel lend :: rest0 ++ post).
    { rewrite /pre' Ecode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have Hnotin : lconseq \notin labels_of pre'.
    { apply: uniq_cat_cons_notin
        (labels_of (c2 ++ ILabel lend :: rest0 ++ post)) _.
      move: Huq. rewrite Edec labels_of_cat /=. by []. }
    have Hfind : find_label_in_procedure G pcD lconseq
                 = Some (Pointer.component pcD, Pointer.block pcD,
                         Z.of_nat (size pre')).
    { exact: find_label_in_procedure_at HgC HgP Edec Hnotin. }
    set pcL := ((Pointer.component pcD, Pointer.block pcD,
                 Z.of_nat (size pre')) : Pointer.t).
    have SB : CS.step G (gps, tmem, tregs, pcD) E0 (gps, tmem, tregs, pcL).
    { apply: step_bnz_nz HcD Ecom _ Hfind. by move/eqP: Hi. }
    have HcL : code_at G pcL (ILabel lconseq :: c2 ++ ILabel lend :: rest0).
    { exists Cp, Pc, pre', post. split.
      - exact: HgC.
      - exact: HgP.
      - rewrite Edec. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
      - by []. }
    have SC : CS.step G (gps, tmem, tregs, pcL) E0
              (gps, tmem, tregs, Pointer.inc pcL).
    { exact: step_label HcL. }
    exists (Pointer.inc pcL), c2, (ILabel lend :: rest0), s2a, s2b.
    split.
    + eapply star_plus_trans; [exact: Sd | | by []].
      eapply plus_left with (t1 := E0) (t2 := E0);
        [exact: SB | exact: star_one SC | by []].
    + split.
      * exact: Hplm.
      * exact: Hdom.
      * exact: Hmem.
      * exact: Hscrs.
      * exact: Hflag.
      * exact: Hall.
      * exact: HONE.
      * exact: HSP.
      * exact: HARG.
      * by rewrite Pointer.inc_preserves_component /pcL /= Ec.
      * exact: E2.
      * exact: code_at_tail HcL.
      * apply: CMJ_label. exact: Hk.
      * exact: Huniq.
      * exact: Hpriv.
      * exact: Hscrp.
      * exact: Htemps.
      * exact: Hcap.
      * move: Hbud => /=. lia.
      * exact: Hprot.
      * exact: Hstack.
      * exact: Hmnf.
  - (* else-branch: fallthrough *)
    have Hi0 : i = 0%Z by move: Hi => /negbFE /eqP.
    have SB : CS.step G (gps, tmem, tregs, pcD) E0
              (gps, tmem, tregs, Pointer.inc pcD).
    { apply: step_bnz_z HcD _. by rewrite Ecom Hi0. }
    exists (Pointer.inc pcD), c3,
           (IBnz R_ONE lend :: ILabel lconseq :: c2 ++ ILabel lend :: rest0),
           s3a, s3b.
    split.
    + eapply star_plus_trans; [exact: Sd | exact: plus_one SB | by []].
    + split.
      * exact: Hplm.
      * exact: Hdom.
      * exact: Hmem.
      * exact: Hscrs.
      * exact: Hflag.
      * exact: Hall.
      * exact: HONE.
      * exact: HSP.
      * exact: HARG.
      * by rewrite Pointer.inc_preserves_component Ec.
      * exact: E3.
      * exact: code_at_tail HcD.
      * apply: CMJ_bnzjoin. apply: CMJ_label. exact: Hk.
      * exact: Huniq.
      * exact: Hpriv.
      * exact: Hscrp.
      * exact: Htemps.
      * exact: Hcap.
      * move: Hbud => /=. lia.
      * exact: Hprot.
      * exact: Hstack.
      * exact: Hmnf.
Qed.

(* The current frame always has a loadable linkage cell. *)
Lemma stack_match_cur_loadable G0 lP α tmem scrs C0 fb0 prot stk gps :
  stack_match G0 lP α tmem scrs C0 fb0 prot stk gps ->
  exists (o : Z) w, Memory.load tmem (C0, fb0, o) = Some w.
Proof.
  case=> [scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
            L0 L1 E0 E1 E2 E3 HprivE Hrc Hcode Hne
         |scrs' C fb fb' prot' stk' gps' oldarg targ k' rest' temps'
            plm ret junkRA cap' HgetP Hrc Hcode Hcont L0 L1
            Hvi Hpriv Htemps LjRA Hcap Hbud Hnp Hne Htail
         |scrs1 C C'' fb fbE spE fb'' prot' stk' gps' oldarg targ
            k'' rest'' temps'' plm'' jal_ret icall_ret vscr junkRA
            junkARG cap''
            HneC HgetP'' Hext HprivE L0 L1 L2E Hic Hcode'' Hcont''
            Hpriv'' Htemps'' LjRA'' Ltarg'' Hvi Hcap'' Hbud'' Hentry
            Hnp'' HnpE HneE Htail].
  - by exists 0%Z, (Ptr (Component.main, fb_ext, 4%Z)).
  - by exists 0%Z,
       (Ptr (C, fb', Z.of_nat (2 + size temps' + 1))).
  - by exists 0%Z, (Ptr (C, fbE, spE)).
Qed.

(* The internal-entry prologue, from the entry label: allocate a fresh frame,
   save the caller linkage (old SP, the scratch cell, the old argument), move
   the argument into place. Thirteen silent steps; reusable by both call
   flavours and the initial bridge. *)
Lemma internal_prologue_run Cf gps2 tmemIn (regsIn : Register.t) pc0 plf ne
      bodyc restE α0 mem0 :
  code_at G pc0 (ILabel plf ::
     ([:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
          IAlloc R_SP R_SP] ++
      push R_AUX1 ++
      push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++ restE)) ->
  Pointer.component pc0 = Cf ->
  Register.get R_ONE regsIn = Int 1 ->
  mem_inject α0 mem0 tmemIn ->
  (exists w, Memory.load tmemIn (Cf, 1, 0%Z) = Some w) ->
  exists tmemOut regsOut fbN pcF wscr,
    [/\ star CS.step G (gps2, tmemIn, regsIn, pc0) E0
             (gps2, tmemOut, regsOut, pcF),
        [/\ mem_inject α0 mem0 tmemOut,
            Memory.load tmemIn (Cf, 1, 0%Z) = Some wscr,
            (forall (o : Z) w', Memory.load tmemIn (Cf, fbN, o) = Some w'
                                -> False),
            forall b0, α0 Cf b0 <> Some fbN
          & fbN <> 1],
        (* the body frame now has TWO linkage slots: the caller's R_SP and the
           saved argument.  The inherited scratch is saved by the WRAPPER. *)
        [/\ Memory.load tmemOut (Cf, fbN, 0%Z)
              = Some (Register.get R_SP regsIn),
            Memory.load tmemOut (Cf, fbN, 1%Z)
              = Some (Register.get R_ARG regsIn)
          & forall C1 b1 (o : Z) w,
              Memory.load tmemIn (C1, b1, o) = Some w ->
              (C1, b1) <> (Cf, fbN) :> (Component.id * Block.id) ->
              Memory.load tmemOut (C1, b1, o) = Some w],
        [/\ Register.get R_ONE regsOut = Int 1,
            Register.get R_SP regsOut = Ptr (Cf, fbN, (0 + 1 + 1)%Z),
            Register.get R_ARG regsOut = Register.get R_COM regsIn
          & Register.get R_COM regsOut = Register.get R_COM regsIn]
      & [/\ Pointer.component pcF = Cf,
            code_at G pcF (bodyc ++ restE),
            (forall j : Z, (0 <= j < Z.of_nat (4 + ne))%Z ->
              exists w, Memory.load tmemOut (Cf, fbN, j) = Some w)
          & forall lP0 scrs0 C0 fb0 prot0 stk0 gps0,
              stack_match G lP0 α0 tmemIn scrs0 C0 fb0 prot0 stk0 gps0 ->
              stack_match G lP0 α0 tmemOut scrs0 C0 fb0 prot0 stk0 gps0]].
Proof.
  move=> Hc0 Hpc0 HONE0 Hmem0 [wscr Hwscr].
  have SL : CS.step G (gps2, tmemIn, regsIn, pc0) E0
            (gps2, tmemIn, regsIn, Pointer.inc pc0).
  { exact: step_label Hc0. }
  have HcP := code_at_tail Hc0.
  have S1 := step_mov G gps2 tmemIn regsIn _ R_SP R_AUX1 _ HcP.
  set regs3 := Register.set R_AUX1 (Register.get R_SP regsIn) regsIn in S1.
  have Hc1 := code_at_tail HcP.
  have S2 := step_const G gps2 tmemIn regs3 _ (IInt (Z.of_nat (4 + ne)))
               R_SP _ Hc1.
  set regs4 := Register.set R_SP (Int (Z.of_nat (4 + ne))) regs3 in S2.
  have Hc2 := code_at_tail Hc1.
  have [cm1 Hcm1] : exists cm, getm tmemIn Cf = Some cm.
  { move: Hwscr. rewrite /Memory.load /=.
    case: (getm tmemIn Cf) => // cm _. by exists cm. }
  have [tmem2 [ptrN Halloc]] : exists tmem2 ptrN,
      Memory.alloc tmemIn Cf (Z.to_nat (Z.of_nat (4 + ne)))
      = Some (tmem2, ptrN).
  { rewrite /Memory.alloc Hcm1.
    case: (ComponentMemory.alloc cm1 _) => cm' b. by do 2 eexists. }
  case: (alloc_outside_inject Hmem0 Halloc) => [Hmem2 EcompN EoffN Havoid].
  set fbN := Pointer.block ptrN.
  have EptrN : ptrN = (Cf, fbN, 0%Z).
  { rewrite /fbN. case: (ptrN) EcompN EoffN => [[pC pB] pO] /= EC EO.
    by rewrite EC EO. }
  have Hfresh : forall (o : Z) w,
      Memory.load tmemIn (Cf, fbN, o) = Some w -> False.
  { exact: memory_alloc_fresh (mi_wf_t _ _ _ Hmem0) Halloc. }
  have HfbN1 : fbN <> 1.
  { move=> E. rewrite E in Hfresh. exact: Hfresh Hwscr. }
  have HgSP4 : Register.get R_SP regs4 = Int (Z.of_nat (4 + ne))
    by rewrite /regs4; rget.
  have S3 : CS.step G (gps2, tmemIn, regs4,
                       Pointer.inc (Pointer.inc (Pointer.inc pc0))) E0
            (gps2, tmem2, Register.set R_SP (Ptr ptrN) regs4,
             Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc pc0)))).
  { apply: step_alloc Hc2 HgSP4 _ _.
    - lia.
    - rewrite /=. rewrite !Pointer.inc_preserves_component Hpc0.
      exact: Halloc. }
  set regs5 := Register.set R_SP (Ptr ptrN) regs4 in S3.
  have Hc3 := code_at_tail Hc2.
  have HldN : forall o : Z, (0 <= o < Z.of_nat (4 + ne))%Z ->
      Memory.load tmem2 (Cf, fbN, o) = Some Undef.
  { move=> o Ho. apply: memory_load_after_alloc_in Halloc _.
    rewrite Nat2Z.id. exact: Ho. }
  (* push R_AUX1 : slot 0 := saved SP *)
  have [tmem3 Hst3] := Memory.store_after_load _ _ _
      (Register.get R_AUX1 regs5) (HldN 0%Z (ltac:(lia))).
  have HSP5 : Register.get R_SP regs5 = Ptr (Cf, fbN, 0%Z)
    by rewrite /regs5 EptrN; rget.
  have HONE5 : Register.get R_ONE regs5 = Int 1
    by rewrite /regs5 /regs4 /regs3; rget.
  have HpcX : forall n, Pointer.component (iter n Pointer.inc pc0) = Cf.
  { elim=> [|n IH] //=. by rewrite Pointer.inc_preserves_component. }
  have S45 := exec_push _ gps2 tmem2 regs5 _ R_AUX1 _ _ _ _ tmem3
                Hc3 HSP5 HONE5 (HpcX 4) Hst3.
  set regs6 := Register.set R_SP (Ptr (Cf, fbN, (0 + 1)%Z)) regs5 in S45.
  have Hc4 := code_at_tail (code_at_tail Hc3).
  (* push R_ARG : slot 1 := saved argument.  The body no longer saves the
     component's scratch cell — that moved to the wrapper — so the frame has
     TWO linkage slots and R_SP lands at [0+1+1]. *)
  have Hld2 : Memory.load tmem3 (Cf, fbN, (0 + 1)%Z) = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst3);
      last by move=> EE; inversion EE.
    apply: HldN. lia. }
  have [tmem5 Hst5] := Memory.store_after_load _ _ _
      (Register.get R_ARG regs6) Hld2.
  have HSP6 : Register.get R_SP regs6 = Ptr (Cf, fbN, (0 + 1)%Z)
    by rewrite /regs6; rget.
  have HONE6 : Register.get R_ONE regs6 = Int 1
    by rewrite /regs6 /regs5 /regs4 /regs3; rget.
  have S1011 := exec_push _ gps2 tmem3 regs6 _ R_ARG _ _ _ _ tmem5
                  Hc4 HSP6 HONE6 (HpcX 6) Hst5.
  set regs9 := Register.set R_SP (Ptr (Cf, fbN, (0 + 1 + 1)%Z)) regs6
    in S1011.
  have Hc10 := code_at_tail (code_at_tail Hc4).
  (* IMov R_COM R_ARG *)
  have S12 := step_mov G gps2 tmem5 regs9 _ R_COM R_ARG _ Hc10.
  set regsF := Register.set R_ARG (Register.get R_COM regs9) regs9 in S12.
  have HgARG8 : Register.get R_ARG regs6 = Register.get R_ARG regsIn
    by rewrite /regs6 /regs5 /regs4 /regs3; rget.
  have HgAUX5 : Register.get R_AUX1 regs5 = Register.get R_SP regsIn
    by rewrite /regs5 /regs4 /regs3; rget.
  exists tmem5, regsF, fbN, (iter 9 Pointer.inc pc0), wscr.
  split.
  - rewrite [iter 9 Pointer.inc pc0]/=.
    eapply star_trans; [exact: star_one SL | | by []].
    eapply star_trans; [exact: star_one S1 | | by []].
    eapply star_trans; [exact: star_one S2 | | by []].
    eapply star_trans; [exact: star_one S3 | | by []].
    eapply star_trans; [exact: S45 | | by []].
    eapply star_trans; [exact: S1011 | exact: star_one S12 | by []].
  - split.
    + have Hmem3 : mem_inject α0 mem0 tmem3.
      { apply: store_outside_inject Hmem2 _ Hst3.
        move=> b0 /=. exact: Havoid. }
      apply: store_outside_inject Hmem3 _ Hst5.
      move=> b0 /=. exact: Havoid.
    + exact: Hwscr.
    + exact: Hfresh.
    + exact: Havoid.
    + exact: HfbN1.
  - split.
    + rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst5);
        last by move=> EE; inversion EE.
      by rewrite -HgAUX5 (Memory.load_after_store_eq _ _ _ _ Hst3).
    + have -> : (1%Z) = (0 + 1)%Z by [].
      by rewrite -HgARG8 (Memory.load_after_store_eq _ _ _ _ Hst5).
    + move=> C1 b1 o w Hl HneN.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst5);
        last by move=> EE; inversion EE; case: HneN; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst3);
        last by move=> EE; inversion EE; case: HneN; rewrite -H0 -H1.
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halloc HneN).
  - split.
    + by rewrite /regsF /regs9 /regs6 /regs5 /regs4 /regs3; rget.
    + by rewrite /regsF /regs9; rget.
    + rewrite /regsF register_get_set_eq /regs9 /regs6 /regs5
              /regs4 /regs3. rget. by [].
    + by rewrite /regsF /regs9 /regs6 /regs5 /regs4 /regs3; rget.
  - split.
    + exact: (HpcX 9).
    + exact: code_at_tail Hc10.
    + move=> j Hj.
      rewrite (Memory.load_after_store _ _ _ _ (Cf, fbN, j) Hst5).
      case: ifP => _; first by eexists.
      rewrite (Memory.load_after_store _ _ _ _ (Cf, fbN, j) Hst3).
      case: ifP => _; first by eexists.
      exists Undef. exact: HldN Hj.
    + move=> lP0 scrs0 C0 fb0 prot0 stk0 gps0 Hsm0.
      have HnpN : (Cf, fbN) \notin prot0.
      { apply/negP => Hin.
        case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
                 Hsm0 Hin) => [o [w Hl]].
        exact: Hfresh Hl. }
      have HneCur : ((Cf, fbN) = (C0, fb0) :> (Component.id * Block.id))
                    -> False.
      { move=> E.
        case: (stack_match_cur_loadable _ _ _ _ _ _ _ _ _ _ Hsm0)
          => [o [w Hl]].
        apply: (Hfresh o w). by rewrite E. }
      have Hsm2 : stack_match G lP0 α0 tmem2 scrs0 C0 fb0 prot0 stk0 gps0.
      { apply: stack_match_alloc Hsm0 Halloc erefl (rle_refl α0) _ _.
        - move=> Cx b0 bx HA. by left.
        - move=> o w Hl. exact: Hfresh Hl. }
      have Hsm3 : stack_match G lP0 α0 tmem3 scrs0 C0 fb0 prot0 stk0 gps0.
      { apply: stack_match_store Hsm2 Hst3 HnpN _.
        move=> E. by case: (HneCur E). }
      apply: stack_match_store Hsm3 Hst5 HnpN _.
      move=> E. by case: (HneCur E).
Qed.

(* KS_InternalReturn: drain, run the epilogue (restores the caller's scratch
   cell), stack-return to the internal call site, pop the saved R_RA. *)
Lemma diagram_return_int α scrs C stk mem k' v oldarg arg gps tmem tregs pc fb
      prot temps plm rest cap :
  val_inv p tp α scrs C (S.CS.Frame C oldarg k' :: stk) mem Kstop v arg
          gps tmem tregs pc fb prot temps plm rest cap ->
  exists scrs1 tmem1 tregs1 pcF gps' rest' temps' fb' prot' cap',
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps', tmem1, tregs1, pcF) /\
    val_inv p tp α scrs1 C stk mem k' v oldarg gps' tmem1 tregs1 pcF fb'
            prot' temps' plm rest' cap'.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_stop_inv Hcm') => [Erest Etemps]. subst rest1 temps.
  inversion Hstack; subst; last by congruence.
  move: H2. rewrite Hplm. case=> Eplm. subst plm0.
  (* NO scratch writeback here any more: an INTRA return restores nothing (the
     save/restore lives in the wrapper), so the epilogue leaves memory alone. *)
  (* the epilogue: 5 steps, lands at the internal return site *)
  have [tregs1 [Sepi HCOM1 HONE1 HSP1 HARG1]] :=
    epilogue_run _ gps0 _ _ _ _ ret _ _
                 HcD Ec HSP HONE H6 H7 H3.
  (* pop the saved (junk) R_RA *)
  have Hjunk1 : Memory.load tmem (Pointer.component pc, fb',
                  (Z.of_nat (2 + size temps' + 1) - 1)%Z) = Some junkRA.
  { have -> : (Z.of_nat (2 + size temps' + 1) - 1)%Z
            = Z.of_nat (2 + size temps') by lia.
    assumption. }
  have Ppop := exec_pop_plus gps0 tmem tregs1 ret R_RA _ _ _ _ _
                 H4 HSP1 HONE1 H3 Hjunk1.
  (* the transit map passes through UNCHANGED: an intra return restores nothing *)
  exists scrs, tmem,
         (Register.set R_RA junkRA
            (Register.set R_SP
               (Ptr (Pointer.component pc, fb',
                     (Z.of_nat (2 + size temps' + 1) - 1)%Z)) tregs1)),
         (Pointer.inc (Pointer.inc ret)), gps0, rest', temps', fb', prot0,
         cap'.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply star_plus_trans; [exact: Sepi | exact: Ppop | by []].
  - have HAv : val_inject α oldarg (Register.get R_ARG tregs1)
      by rewrite HARG1.
    have HCv : val_inject α v (Register.get R_COM tregs1)
      by rewrite HCOM1.
    split.
    + exact: Hplm.
    + exact: Hdom.
    + exact: Hmem.
    + move=> C' v0 Hv0. exact: Hscrs Hv0.
    + by [].
    + move=> C' /Hall [w' Hl]. by exists w'.
    + by rget.
    + have -> : Z.of_nat (2 + size temps')
              = (Z.of_nat (2 + size temps' + 1) - 1)%Z by lia.
      by rget.
    + by rget.
    + by rget.
    + by rewrite !Pointer.inc_preserves_component H3.
    + exact: code_at_tail (code_at_tail H4).
    (* NB [SM_internal]'s inversion auto-names all shifted down by one when it
       lost its scratch load, so these are matched by TYPE, not by number. *)
    + assumption.
    + exact: Huniq.
    + assumption.
    + exact: Hscrp.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + exact: Hmnf.
Qed.

(* Resuming a suspended EXTERNAL caller after IReturn lands on its ICall
   continuation: re-establish R_ONE, reload R_SP from the scratch transit
   cell, pop the saved argument and the junk R_RA. Seven silent steps. *)
Lemma icall_resume_run C'' gps' tmem1 regs0 icall_ret rest'' fb''
      (temps'' : seq value) targ junkRA'' :
  code_at G icall_ret
    (IConst (IInt 1) R_ONE
       :: reload_sp (scr C'') ++ pop R_ARG ++ pop R_RA ++ rest'') ->
  Pointer.component icall_ret = C'' ->
  Memory.load tmem1 (C'', 1, 0%Z)
    = Some (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2))) ->
  Memory.load tmem1 (C'', fb'', Z.of_nat (2 + size temps'' + 1)) = Some targ ->
  Memory.load tmem1 (C'', fb'', Z.of_nat (2 + size temps'')) = Some junkRA'' ->
  exists regsF pcF,
    [/\ star CS.step G (gps', tmem1, regs0, icall_ret) E0
             (gps', tmem1, regsF, pcF),
        Register.get R_ONE regsF = Int 1,
        Register.get R_SP regsF
          = Ptr (C'', fb'', Z.of_nat (2 + size temps'')),
        [/\ Register.get R_ARG regsF = targ
          & Register.get R_COM regsF = Register.get R_COM regs0]
      & [/\ Pointer.component pcF = C''
          & code_at G pcF rest'']].
Proof.
  move=> Hcode Hic Htr Hta Hjk.
  have SA : CS.step G (gps', tmem1, regs0, icall_ret) E0
            (gps', tmem1, Register.set R_ONE (Int 1) regs0,
             Pointer.inc icall_ret).
  { exact: step_const Hcode. }
  set regs1 := Register.set R_ONE (Int 1) regs0.
  have Hc1 := code_at_tail Hcode.
  have SB := exec_reload_sp _ gps' tmem1 regs1 _ (scr C'') _ _
               Hc1 _ Htr.
  have SB' := SB (ltac:(by rewrite /= Pointer.inc_preserves_component Hic)).
  set regs2 := Register.set R_SP
                 (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2)))
                 (Register.set R_AUX2 (Ptr (scr C'')) regs1) in SB'.
  set pc2 := Pointer.inc (Pointer.inc (Pointer.inc icall_ret)) in SB'.
  have Hc2 : code_at G pc2 (pop R_ARG ++ pop R_RA ++ rest'').
  { exact: code_at_tail (code_at_tail Hc1). }
  have Hpc2 : Pointer.component pc2 = C''
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have HSP2 : Register.get R_SP regs2
              = Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2)) by rget.
  have HONE2 : Register.get R_ONE regs2 = Int 1 by rget.
  have Hta' : Memory.load tmem1
      (C'', fb'', (Z.of_nat (2 + size temps'' + 2) - 1)%Z) = Some targ.
  { have -> : (Z.of_nat (2 + size temps'' + 2) - 1)%Z
            = Z.of_nat (2 + size temps'' + 1) by lia.
    exact: Hta. }
  have SC := exec_pop _ _ _ _ _ R_ARG _ _ _ _ _ Hc2 HSP2 HONE2 Hpc2 Hta'.
  set regs3 := Register.set R_ARG targ _ in SC.
  set pc3 := Pointer.inc (Pointer.inc pc2) in SC.
  have Hc3 : code_at G pc3 (pop R_RA ++ rest'').
  { exact: code_at_tail (code_at_tail Hc2). }
  have Hpc3 : Pointer.component pc3 = C''
    by rewrite /pc3 !Pointer.inc_preserves_component.
  have HSP3 : Register.get R_SP regs3
              = Ptr (C'', fb'', (Z.of_nat (2 + size temps'' + 2) - 1)%Z)
    by rget.
  have HONE3 : Register.get R_ONE regs3 = Int 1 by rget.
  have Hjk' : Memory.load tmem1
      (C'', fb'', ((Z.of_nat (2 + size temps'' + 2) - 1) - 1)%Z)
      = Some junkRA''.
  { have -> : ((Z.of_nat (2 + size temps'' + 2) - 1) - 1)%Z
            = Z.of_nat (2 + size temps'') by lia.
    exact: Hjk. }
  have SD := exec_pop _ _ _ _ _ R_RA _ _ _ _ _ Hc3 HSP3 HONE3 Hpc3 Hjk'.
  set regs4 := Register.set R_RA junkRA'' _ in SD.
  set pc4 := Pointer.inc (Pointer.inc pc3) in SD.
  exists regs4, pc4.
  split.
  - eapply star_trans; [exact: star_one SA | | by []].
    eapply star_trans; [exact: SB' | | by []].
    eapply star_trans; [exact: (SC gps') | exact: (SD gps') | by []].
  - by rget.
  - have -> : Z.of_nat (2 + size temps'')
            = ((Z.of_nat (2 + size temps'' + 2) - 1) - 1)%Z by lia.
    by rget.
  - split; by rget.
  - split.
    + by rewrite /pc4 /pc3 /pc2 !Pointer.inc_preserves_component.
    + exact: code_at_tail (code_at_tail Hc3).
Qed.

(* Crossing the external-entry glue on return: pop its linkage and IReturn
   with the ERet event. Handles both the standard and main's dual entry. *)
(* The wrapper's epilogue now RESTORES the inherited scratch before popping the
   frame, so this run writes memory: [tmem1] → [tmem2].  Mirror image of the
   internal-return diagram, which lost exactly this store. *)
Lemma ef_cross_run Cc gps1 tmem1 tmem2 regs1 jal_ret fbE spE (i : Z) pc' vscr :
  ext_frame_match G tmem1 Cc fbE jal_ret spE ->
  Register.get R_SP regs1 = Ptr (Cc, fbE, spE) ->
  Register.get R_ONE regs1 = Int 1 ->
  Register.get R_COM regs1 = Int i ->
  (forall Cx C_procs b P_code,
      getm (genv_procedures G) Cx = Some C_procs ->
      getm C_procs b = Some P_code ->
      uniq (labels_of P_code)) ->
  Cc <> Pointer.component pc' ->
  fbE <> 1 ->
  Memory.load tmem1 (Cc, fbE, 1%Z) = Some vscr ->
  Memory.store tmem1 (Cc, 1, 0%Z) vscr = Some tmem2 ->
  exists regs2,
    star CS.step G (pc' :: gps1, tmem1, regs1, jal_ret)
         [:: ERet Cc i (Pointer.component pc')]
         (gps1, tmem2, Register.invalidate regs2, pc') /\
    Register.get R_COM regs2 = Int i.
Proof.
  move=> Hef HSP HONE HCOM Huniq Hne HfbE1 Hlv Hstore.
  inversion Hef as [fbE0 jr0 v0 v1 v2 Hjc0 HcodeE Hl0 Hl1 Hl2
                   |fbE0 jr0 lret v0 v1 v2 z Hjc0 HcodeE Hl0 Hl1 Hl2 Hl3 Hz];
    subst.
  - (* EF_std: pop R_RA (slot 2) ; pop R_AUX1 (slot 1) ; store_arg ;
       pop R_SP (slot 0, after the store) ; IReturn *)
    have Evs : vscr = v1 by congruence.
    subst vscr.
    have SA := exec_pop _ _ _ _ _ R_RA _ _ _ _ _ HcodeE HSP HONE erefl Hl2.
    set regsA := Register.set R_RA v2 _ in SA.
    set pcA := Pointer.inc (Pointer.inc jal_ret) in SA.
    have HcA := code_at_tail (code_at_tail HcodeE).
    have HSPA : Register.get R_SP regsA
                = Ptr (Pointer.component jal_ret, fbE, (3 - 1)%Z) by rget.
    have HONEA : Register.get R_ONE regsA = Int 1 by rget.
    have HpcA : Pointer.component pcA = Pointer.component jal_ret
      by rewrite /pcA !Pointer.inc_preserves_component.
    (* pop R_AUX1 : the inherited scratch this wrapper saved on entry *)
    have SB := exec_pop _ _ _ _ _ R_AUX1 _ _ _ _ _ HcA HSPA HONEA HpcA Hl1.
    set regsB := Register.set R_AUX1 v1 _ in SB.
    set pcB := Pointer.inc (Pointer.inc pcA) in SB.
    have HcB := code_at_tail (code_at_tail HcA).
    have HpcB : Pointer.component pcB = Pointer.component jal_ret
      by rewrite /pcB /pcA !Pointer.inc_preserves_component.
    (* store_arg : put it back into the component's scratch cell *)
    have HgB : Register.get R_AUX1 regsB = v1 by rget.
    have Hst' : Memory.store tmem1 (Pointer.component jal_ret, 1, 0%Z)
                  (Register.get R_AUX1 regsB) = Some tmem2 by rewrite HgB.
    have SC := exec_store_arg _ _ _ _ _ (scr (Pointer.component jal_ret))
                 R_AUX1 R_AUX2 _ _ HcB (esym HpcB) (ltac:(by [])) Hst'.
    set regsC := Register.set R_AUX2 (Ptr (scr (Pointer.component jal_ret))) _ in SC.
    set pcC := Pointer.inc (Pointer.inc pcB) in SC.
    have HcC := code_at_tail (code_at_tail HcB).
    have HSPC : Register.get R_SP regsC
                = Ptr (Pointer.component jal_ret, fbE, (3 - 1 - 1)%Z) by rget.
    have HONEC : Register.get R_ONE regsC = Int 1 by rget.
    have HpcC : Pointer.component pcC = Pointer.component jal_ret
      by rewrite /pcC /pcB /pcA !Pointer.inc_preserves_component.
    (* pop R_SP : the caller's frame pointer, read AFTER the store *)
    have Hl0' : Memory.load tmem2 (Pointer.component jal_ret, fbE, 0%Z) = Some v0.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore) //.
      by move=> E; inversion E; apply: HfbE1. }
    have SD := exec_pop _ _ _ _ _ R_SP _ _ _ _ _ HcC HSPC HONEC HpcC Hl0'.
    set regsD := Register.set R_SP v0 _ in SD.
    set pcD := Pointer.inc (Pointer.inc pcC) in SD.
    have HcD := code_at_tail (code_at_tail HcC).
    have EcD : Pointer.component pcD = Pointer.component jal_ret
      by rewrite /pcD /pcC /pcB /pcA !Pointer.inc_preserves_component.
    have HCOMD : Register.get R_COM regsD = Int i by rget.
    have SE : CS.step G (pc' :: gps1, tmem2, regsD, pcD)
              [:: ERet (Pointer.component pcD) i (Pointer.component pc')]
              (gps1, tmem2, Register.invalidate regsD, pc').
    { apply: step_return HcD _ HCOMD. by rewrite EcD. }
    exists regsD. split; last exact: HCOMD.
    rewrite -EcD.
    eapply star_trans; [exact: (SA (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SB (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SC (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SD (pc' :: gps1)) | exact: star_one SE | by []].
  - (* EF_main: pop R_ARG (marker, slot 3) ; pop R_RA (slot 2) ;
       pop R_AUX1 (slot 1) ; store_arg ; pop R_SP (slot 0, after the store) ;
       then the taken IBnz R_ARG over the IHalt *)
    have Evs : vscr = v1 by congruence.
    subst vscr.
    have SA := exec_pop _ _ _ _ _ R_ARG _ _ _ _ _ HcodeE HSP HONE erefl Hl3.
    set regsA := Register.set R_ARG (Int z) _ in SA.
    set pcA := Pointer.inc (Pointer.inc jal_ret) in SA.
    have HcA := code_at_tail (code_at_tail HcodeE).
    have HSPA : Register.get R_SP regsA
                = Ptr (Pointer.component jal_ret, fbE, (4 - 1)%Z) by rget.
    have HONEA : Register.get R_ONE regsA = Int 1 by rget.
    have HpcA : Pointer.component pcA = Pointer.component jal_ret
      by rewrite /pcA !Pointer.inc_preserves_component.
    have SB := exec_pop _ _ _ _ _ R_RA _ _ _ _ _ HcA HSPA HONEA HpcA Hl2.
    set regsB := Register.set R_RA v2 _ in SB.
    set pcB := Pointer.inc (Pointer.inc pcA) in SB.
    have HcB := code_at_tail (code_at_tail HcA).
    have HSPB : Register.get R_SP regsB
                = Ptr (Pointer.component jal_ret, fbE, (4 - 1 - 1)%Z) by rget.
    have HONEB : Register.get R_ONE regsB = Int 1 by rget.
    have HpcB : Pointer.component pcB = Pointer.component jal_ret
      by rewrite /pcB /pcA !Pointer.inc_preserves_component.
    (* pop R_AUX1 : the inherited scratch *)
    have SBB := exec_pop _ _ _ _ _ R_AUX1 _ _ _ _ _ HcB HSPB HONEB HpcB Hl1.
    set regsBB := Register.set R_AUX1 v1 _ in SBB.
    set pcBB := Pointer.inc (Pointer.inc pcB) in SBB.
    have HcBB := code_at_tail (code_at_tail HcB).
    have HpcBB : Pointer.component pcBB = Pointer.component jal_ret
      by rewrite /pcBB /pcB /pcA !Pointer.inc_preserves_component.
    (* store_arg : put it back *)
    have HgBB : Register.get R_AUX1 regsBB = v1 by rget.
    have Hst' : Memory.store tmem1 (Pointer.component jal_ret, 1, 0%Z)
                  (Register.get R_AUX1 regsBB) = Some tmem2 by rewrite HgBB.
    have SBC := exec_store_arg _ _ _ _ _ (scr (Pointer.component jal_ret))
                  R_AUX1 R_AUX2 _ _ HcBB (esym HpcBB) (ltac:(by [])) Hst'.
    set regsBC := Register.set R_AUX2 (Ptr (scr (Pointer.component jal_ret))) _ in SBC.
    set pcBC := Pointer.inc (Pointer.inc pcBB) in SBC.
    have HcBC := code_at_tail (code_at_tail HcBB).
    have HSPBC : Register.get R_SP regsBC
                 = Ptr (Pointer.component jal_ret, fbE, (4 - 1 - 1 - 1)%Z) by rget.
    have HONEBC : Register.get R_ONE regsBC = Int 1 by rget.
    have HpcBC : Pointer.component pcBC = Pointer.component jal_ret
      by rewrite /pcBC /pcBB /pcB /pcA !Pointer.inc_preserves_component.
    (* pop R_SP : read AFTER the store *)
    have Hl0' : Memory.load tmem2 (Pointer.component jal_ret, fbE, 0%Z) = Some v0.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore) //.
      by move=> E; inversion E; apply: HfbE1. }
    have SC := exec_pop _ _ _ _ _ R_SP _ _ _ _ _ HcBC HSPBC HONEBC HpcBC Hl0'.
    set regsC := Register.set R_SP v0 _ in SC.
    set pcC := Pointer.inc (Pointer.inc pcBC) in SC.
    have HcC := code_at_tail (code_at_tail HcBC).
    (* the taken IBnz over the IHalt onto the ILabel lret *)
    case: (HcC) => [CpE [PcE [preE [postE [HgC HgP Ecode Eoff]]]]].
    have Huq := Huniq _ _ _ _ HgC HgP.
    set pre'' := preE ++ [:: IBnz R_ARG lret; IHalt].
    have Edec : PcE = pre'' ++ ILabel lret :: ([:: IReturn] ++ postE).
    { rewrite /pre'' Ecode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have Hnotin : lret \notin labels_of pre''.
    { apply: uniq_cat_cons_notin (labels_of ([:: IReturn] ++ postE)) _.
      move: Huq. rewrite Edec labels_of_cat /=. by []. }
    have Hfind : find_label_in_procedure G pcC lret
                 = Some (Pointer.component pcC, Pointer.block pcC,
                         Z.of_nat (size pre'')).
    { exact: find_label_in_procedure_at HgC HgP Edec Hnotin. }
    have HA1C : Register.get R_ARG regsC = Int z by rget.
    set pcL := ((Pointer.component pcC, Pointer.block pcC,
                 Z.of_nat (size pre'')) : Pointer.t).
    have SD : CS.step G (pc' :: gps1, tmem2, regsC, pcC) E0
              (pc' :: gps1, tmem2, regsC, pcL).
    { exact: step_bnz_nz HcC HA1C Hz Hfind. }
    have HcL : code_at G pcL (ILabel lret :: [:: IReturn]).
    { exists CpE, PcE, pre'', postE.
      split.
      - exact: HgC.
      - exact: HgP.
      - rewrite Edec. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
      - by []. }
    have SE : CS.step G (pc' :: gps1, tmem2, regsC, pcL) E0
              (pc' :: gps1, tmem2, regsC, Pointer.inc pcL).
    { exact: step_label HcL. }
    have HcR := code_at_tail HcL.
    have EcR : Pointer.component (Pointer.inc pcL) = Pointer.component jal_ret
      by rewrite Pointer.inc_preserves_component /pcL /pcC /pcB /pcA /=
                 !Pointer.inc_preserves_component.
    have HCOMC : Register.get R_COM regsC = Int i by rget.
    have SF : CS.step G (pc' :: gps1, tmem2, regsC, Pointer.inc pcL)
              [:: ERet (Pointer.component (Pointer.inc pcL)) i
                       (Pointer.component pc')]
              (gps1, tmem2, Register.invalidate regsC, pc').
    { apply: step_return HcR _ HCOMC. by rewrite EcR. }
    exists regsC. split; last exact: HCOMC.
    rewrite -EcR.
    eapply star_trans; [exact: (SA (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SB (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SBB (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SBC (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: (SC (pc' :: gps1)) | | by []].
    eapply star_trans; [exact: star_one SD | | by []].
    eapply star_trans; [exact: star_one SE | exact: star_one SF | by []].
Qed.

(* KS_ExternalReturn: drain, epilogue, cross the EF entry (std or main
   flavour), IReturn with the ERet event, resume the suspended caller. *)
Lemma diagram_return_ext α scrs C Cf stk mem k'' i oldarg arg gps tmem tregs
      pc fb prot temps plm rest cap :
  val_inv p tp α scrs C (S.CS.Frame Cf oldarg k'' :: stk) mem Kstop (Int i)
          arg gps tmem tregs pc fb prot temps plm rest cap ->
  C <> Cf ->
  exists scrs1 tmem1 tregs1 pcF gps1 rest1 temps1 fb1 prot1 cap1 plm1,
    plus CS.step G (gps, tmem, tregs, pc) [:: ERet C i Cf]
         (gps1, tmem1, tregs1, pcF) /\
    val_inv p tp α scrs1 Cf stk mem k'' (Int i) oldarg gps1 tmem1 tregs1 pcF
            fb1 prot1 temps1 plm1 rest1 cap1.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf HneCf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_stop_inv Hcm') => [Erest Etemps]. subst rest1 temps.
  inversion Hstack; subst; first by congruence.
  have Hjc : Pointer.component jal_ret = Pointer.component pc
    by inversion H5.
  (* the scratch writeback is now performed by the WRAPPER, inside
     [ef_cross_run] — the body epilogue leaves memory alone *)
  have [w0 Hw0] := Hall _ Hdom.
  have [tmem1 Hstore] := Memory.store_after_load _ _ _ vscr Hw0.
  (* the epilogue: lands at jal_ret with the EF-frame pointer in R_SP.
     [H7]/[H9] are the BODY frame's slots 0 and 1; [H8] is the WRAPPER's slot 1
     (the inherited scratch), which [ef_cross_run] consumes below. *)
  have [tregs1 [Sepi HCOM1 HONE1 HSP1 HARG1]] :=
    epilogue_run _ (icall_ret :: gps0) _ _ _ _ jal_ret _ _
                 HcD Ec HSP HONE H7 H9 Hjc.
  have Ecom := val_inject_int_l _ _ _ Hcom.
  have HCOMi : Register.get R_COM tregs1 = Int i by rewrite HCOM1.
  have [regs2 [Scross HCOM2]] :=
    ef_cross_run (Pointer.component pc) gps0 tmem tmem1 tregs1 jal_ret fbE spE
                 i icall_ret vscr H5 HSP1 HONE1 HCOMi Huniq HneCf
                 (proj1 H6) H8 Hstore.
  (* resume the caller *)
  have HCOMinv : Register.get R_COM (Register.invalidate regs2) = Int i.
  { by rewrite /Register.invalidate HCOM2 /Register.get mkfmapE /=. }
  have Htr1 : Memory.load tmem1 (Pointer.component icall_ret, 1, 0%Z)
              = Some (Ptr (Pointer.component icall_ret, fb'',
                           Z.of_nat (2 + size temps'' + 2))).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore);
      last by move=> E; inversion E; apply: HneCf.
    exact: Hscrs H20. }
  have Hta1 : Memory.load tmem1 (Pointer.component icall_ret, fb'',
                Z.of_nat (2 + size temps'' + 1)) = Some targ.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore);
      last by move=> E; inversion E; apply: HneCf.
    exact: H16. }
  have Hjk1 : Memory.load tmem1 (Pointer.component icall_ret, fb'',
                Z.of_nat (2 + size temps'')) = Some junkRA.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore);
      last by move=> E; inversion E; apply: HneCf.
    exact: H15. }
  have [regsF [pcF [Sres RONEF RSPF [RARGF RCOMF] [EpcF HcF]]]] :=
    icall_resume_run (Pointer.component icall_ret) gps0 tmem1
                     (Register.invalidate regs2) icall_ret rest'' fb''
                     temps'' targ junkRA H11 erefl Htr1 Hta1 Hjk1.
  (* assemble the run; its trace is the single ERet event *)
  have Stotal : star CS.step G
      ([:: jal_ret, icall_ret & gps0], tmem, tregs, pc)
      [:: ERet (Pointer.component pc) i (Pointer.component icall_ret)]
      (gps0, tmem1, regsF, pcF).
  { eapply star_trans; [exact: Sd | | by []].
    eapply star_trans; [exact: Sepi | | by []].
    eapply star_trans; [exact: Scross | exact: Sres | by []]. }
  have Hplus : plus CS.step G
      ([:: jal_ret, icall_ret & gps0], tmem, tregs, pc)
      [:: ERet (Pointer.component pc) i (Pointer.component icall_ret)]
      (gps0, tmem1, regsF, pcF).
  { case: (star_inv Stotal) => [[_ Habs] | //]. discriminate Habs. }
  exists (setm scrs (Pointer.component pc) vscr), tmem1, regsF, pcF, gps0,
         rest'', temps'', fb'', prot0, cap'', plm''.
  split; first exact: Hplus.
  have HAv : val_inject α oldarg (Register.get R_ARG regsF)
    by rewrite RARGF.
  have HCv : val_inject α (Int i) (Register.get R_COM regsF)
    by rewrite RCOMF HCOMinv; exact: VI_int.
  split.
  - exact: H4.
  - case: (H11) => [Cp' [Pc' [pre' [post' [HgC' _ _ _]]]]].
    rewrite -domm_genv_procedures. by rewrite mem_domm HgC'.
  - apply: store_outside_inject Hmem _ Hstore.
    move=> b0 /=. exact: Hscrp.
  - move=> C' v0. rewrite setmE.
    case: eqP => [-> [<-] | HneC Hv0].
    + exact: Memory.load_after_store_eq Hstore.
    + rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore);
        last by move=> E; inversion E; apply: HneC.
      exact: Hscrs Hv0.
  - by rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore).
  - move=> C' /Hall [w' Hl].
    rewrite (Memory.load_after_store _ _ _ _ (C', 1, 0%Z) Hstore).
    case: ifP => _; [by exists vscr | by exists w'].
  - exact: RONEF.
  - exact: RSPF.
  - exact: HAv.
  - exact: HCv.
  - exact: EpcF.
  - exact: HcF.
  - exact: H12.
  - exact: Huniq.
  - exact: H13.
  - exact: Hscrp.
  - apply: frame_temps_store H14 Hstore _.
    move=> i0 Hi0 E. inversion E. by apply: HneCf.
  - exact: frame_cap_store H18 Hstore.
  - exact: H19.
  - exact: H25.
  - have Hnp1 : (Pointer.component pc, 1) \notin prot0.
    { apply/negP => Hin.
      exact: (stack_match_prot_not1 _ _ _ _ _ _ _ _ _ _ _ _
                H29 Hin erefl). }
    apply: stack_match_store H29 Hstore Hnp1 _.
    move=> E. exfalso. inversion E. by apply: HneCf.
  - exact: Hmnf.
Qed.

(* KS_InternalCall: drain, push the return address, IJal to the callee's
   entry label (label resolution across the compiled program), run the
   internal prologue on a fresh frame, and suspend the caller. *)
Lemma diagram_call_int α scrs C stk mem k P v arg gps tmem tregs pc fb prot
      temps plm rest cap P_expr :
  val_inv p tp α scrs C stk mem (Kcall C P k) (Int v) arg gps tmem tregs pc
          fb prot temps plm rest cap ->
  Source.find_procedure (Source.prog_procedures p) C P = Some P_expr ->
  exists tmem5 tregs5 pcF gps1 c1 rest1 sA sB fbN,
    plus CS.step G (gps, tmem, tregs, pc) E0 (gps1, tmem5, tregs5, pcF) /\
    expr_inv p tp α scrs C (S.CS.Frame C arg k :: stk) mem Kstop P_expr
             (Int v) gps1 tmem5 tregs5 pcF fbN ((C, fb) :: prot) [::] plm
             c1 rest1 sA sB (4 + stack_need P_expr).
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf Hfind.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_call_inv Hcm') => [[tl [rest0 [_ Htl Erest Hk]]]
                                      |[rest0 [Hne _ _]]]; last by [].
  subst rest1.
  (* the label resolution *)
  case: (compiled_jal_resolution Hwf_p Hcompile) => [labels [cenv1 [Egen HRES]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  move: Hfind. rewrite /Source.find_procedure.
  case HgC: (getm (Source.prog_procedures p) C) => [Cprocs|] //. move=> HgP.
  rewrite Elab in Hplm.
  have HRES' := HRES _ _ _ _ _ _ HgC HgP Hplm Htl Hdom.
  (* push the return address *)
  have [wRA HwRA] : exists w,
      Memory.load tmem (C, fb, Z.of_nat (2 + size temps)) = Some w.
  { apply: Hcap. move: Hbud => /=. lia. }
  have [tmem1 Hst1] :=
    Memory.store_after_load _ _ _ (Register.get R_RA tregs) HwRA.
  have Ppush := exec_push_plus gps tmem tregs pcD R_RA _ _ _ _ tmem1
                  HcD HSP HONE Ec Hst1.
  set regs1 := Register.set R_SP _ tregs in Ppush.
  set pcJ := Pointer.inc (Pointer.inc pcD) in Ppush.
  have HpcJ : Pointer.component pcJ = C
    by rewrite /pcJ !Pointer.inc_preserves_component Ec.
  have HcJ : code_at G pcJ (IJal tl :: pop R_RA ++ rest0).
  { exact: code_at_tail (code_at_tail HcD). }
  case: (HRES' pcJ HpcJ)
    => [bP [cd [ext [restP [CprocsB [HgB HgCd Hdec Hex Hfl]]]]]].
  case: Hex => [s1 [s2 Hcp]].
  have SJ : CS.step G (gps, tmem1, regs1, pcJ) E0
            (Pointer.inc pcJ :: gps, tmem1,
             Register.set R_RA Undef regs1, (C, bP, Z.of_nat (size ext))).
  { apply: step_jal HcJ _. by rewrite /find_label_in_component -HpcJ in Hfl *. }
  set pcE := ((C, bP, Z.of_nat (size ext)) : Pointer.t) in SJ.
  set regs2 := Register.set R_RA Undef regs1 in SJ.
  have HcE : code_at G pcE (ILabel tl :: restP).
  { exists CprocsB, cd, ext, [::]. split.
    - exact: HgB.
    - exact: HgCd.
    - by rewrite Hdec cats0.
    - by []. }
  have SL : CS.step G (Pointer.inc pcJ :: gps, tmem1, regs2, pcE) E0
            (Pointer.inc pcJ :: gps, tmem1, regs2, Pointer.inc pcE).
  { exact: step_label HcE. }
  have Huq := Huniq _ _ _ _ HgB HgCd.
  case: (compile_proc_after_label _ _ _ _ _ _ _ _ _ _ Hcp Htl Hdec Huq)
    => [bodyc [sA [sB [Ebody Erest]]]].
  subst restP.
  have HcP := code_at_tail HcE.
  (* register facts entering the prologue *)
  have Ecom := val_inject_int_l _ _ _ Hcom.
  have HSP2 : Register.get R_SP regs2
              = Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)
    by rewrite /regs2 /regs1; rget.
  have HONE2 : Register.get R_ONE regs2 = Int 1
    by rewrite /regs2 /regs1; rget.
  have HCOM2 : Register.get R_COM regs2 = Int v
    by rewrite /regs2 /regs1; rget.
  have HARG2 : Register.get R_ARG regs2 = Register.get R_ARG tregs
    by rewrite /regs2 /regs1; rget.
  (* IMov R_SP R_AUX1 *)
  have S1 : CS.step G (Pointer.inc pcJ :: gps, tmem1, regs2, Pointer.inc pcE)
            E0 (Pointer.inc pcJ :: gps, tmem1,
                Register.set R_AUX1 (Register.get R_SP regs2) regs2,
                Pointer.inc (Pointer.inc pcE)).
  { exact: step_mov HcP. }
  set regs3 := Register.set R_AUX1 (Register.get R_SP regs2) regs2 in S1.
  have Hc1 := code_at_tail HcP.
  (* IConst frame-size R_SP *)
  have S2 : CS.step G (Pointer.inc pcJ :: gps, tmem1, regs3,
                       Pointer.inc (Pointer.inc pcE)) E0
            (Pointer.inc pcJ :: gps, tmem1,
             Register.set R_SP
               (Int (Z.of_nat (4 + stack_need P_expr))) regs3,
             Pointer.inc (Pointer.inc (Pointer.inc pcE))).
  { exact: step_const Hc1. }
  set regs4 := Register.set R_SP (Int (Z.of_nat (4 + stack_need P_expr)))
                 regs3 in S2.
  have Hc2 := code_at_tail Hc1.
  (* the fresh frame *)
  have Hmem1 : mem_inject α mem tmem1.
  { apply: store_outside_inject Hmem _ Hst1.
    move=> b0 /=. exact: (proj2 Hpriv). }
  have Hn1RA : forall (C1 : Component.id) (o : Z),
      (C, fb, Z.of_nat (2 + size temps)) <> (C1, 1, o) :> Pointer.t.
  { move=> C1 o E. inversion E. by case: Hpriv => + _; apply. }
  have [w1 Hw1] := Hall _ Hdom.
  have Hw1' : Memory.load tmem1 (C, 1, 0%Z) = Some w1.
  { by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1RA _ _) Hst1). }
  have [cm1 Hcm1] : exists cm, getm tmem1 C = Some cm.
  { move: Hw1'. rewrite /Memory.load /=.
    case: (getm tmem1 C) => // cm _. by exists cm. }
  have [tmem2 [ptrN Halloc]] : exists tmem2 ptrN,
      Memory.alloc tmem1 C (Z.to_nat (Z.of_nat (4 + stack_need P_expr)))
      = Some (tmem2, ptrN).
  { rewrite /Memory.alloc Hcm1.
    case: (ComponentMemory.alloc cm1 _) => cm' b. by do 2 eexists. }
  case: (alloc_outside_inject Hmem1 Halloc) => [Hmem2 EcompN EoffN Havoid].
  set fbN := Pointer.block ptrN.
  have EptrN : ptrN = (C, fbN, 0%Z).
  { rewrite /fbN. case: (ptrN) EcompN EoffN => [[pC pB] pO] /= EC EO.
    by rewrite EC EO. }
  have Hfresh1 : forall (o : Z) w,
      Memory.load tmem1 (C, fbN, o) = Some w -> False.
  { exact: memory_alloc_fresh (mi_wf_t _ _ _ Hmem1) Halloc. }
  have HfbN1 : fbN <> 1.
  { move=> E. rewrite E in Hfresh1. exact: Hfresh1 Hw1'. }
  have HfbNfb : fbN <> fb.
  { move=> E.
    apply: (Hfresh1 (Z.of_nat (2 + size temps))
                    (Register.get R_RA tregs)).
    rewrite E. exact: Memory.load_after_store_eq Hst1. }
  have HgSP4 : Register.get R_SP regs4
               = Int (Z.of_nat (4 + stack_need P_expr))
    by rewrite /regs4; rget.
  have S3 : CS.step G (Pointer.inc pcJ :: gps, tmem1, regs4,
                       Pointer.inc (Pointer.inc (Pointer.inc pcE))) E0
            (Pointer.inc pcJ :: gps, tmem2,
             Register.set R_SP (Ptr ptrN) regs4,
             Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc pcE)))).
  { apply: step_alloc Hc2 HgSP4 _ _.
    - lia.
    - rewrite /=. exact: Halloc. }
  set regs5 := Register.set R_SP (Ptr ptrN) regs4 in S3.
  have Hc3 := code_at_tail Hc2.
  (* frame cells are loadable *)
  have HldN : forall (o : Z), (0 <= o < Z.of_nat (4 + stack_need P_expr))%Z ->
      Memory.load tmem2 (C, fbN, o) = Some Undef.
  { move=> o Ho. apply: memory_load_after_alloc_in Halloc _.
    rewrite Nat2Z.id. exact: Ho. }
  (* push R_AUX1 : slot 0 := saved SP *)
  have [tmem3 Hst3] := Memory.store_after_load _ _ _
      (Register.get R_AUX1 regs5) (HldN 0%Z (ltac:(lia))).
  have HSP5 : Register.get R_SP regs5 = Ptr (C, fbN, 0%Z)
    by rewrite /regs5 EptrN; rget.
  have HONE5 : Register.get R_ONE regs5 = Int 1
    by rewrite /regs5 /regs4 /regs3; rget.
  have HpcE4 : Pointer.component
      (Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc pcE)))) = C
    by rewrite !Pointer.inc_preserves_component.
  have Hst3' : Memory.store tmem2 (C, fbN, 0%Z)
                 (Register.get R_AUX1 regs5) = Some tmem3 by [].
  have S45 := exec_push _ (Pointer.inc pcJ :: gps) tmem2 regs5 _ R_AUX1 _
                _ _ _ tmem3 Hc3 HSP5 HONE5 HpcE4 Hst3'.
  set regs6 := Register.set R_SP (Ptr (C, fbN, (0 + 1)%Z)) regs5 in S45.
  have Hc4 := code_at_tail (code_at_tail Hc3).
  (* push R_ARG : slot 1 := saved argument.  The body no longer saves the
     component's scratch cell here — [load_arg scr R_AUX1; push R_AUX1] moved to
     the wrapper (see the note on [compile_proc]), so the frame has just TWO
     linkage slots and R_SP lands at [0+1+1]. *)
  have Hld2 : Memory.load tmem3 (C, fbN, (0 + 1)%Z) = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst3);
      last by move=> E; inversion E.
    apply: HldN. lia. }
  have [tmem5 Hst5] := Memory.store_after_load _ _ _
      (Register.get R_ARG regs6) Hld2.
  have HSP6 : Register.get R_SP regs6 = Ptr (C, fbN, (0 + 1)%Z)
    by rewrite /regs6; rget.
  have HONE6 : Register.get R_ONE regs6 = Int 1
    by rewrite /regs6 /regs5 /regs4 /regs3; rget.
  have S1011 := exec_push _ (Pointer.inc pcJ :: gps) tmem3 regs6 _ R_ARG _
                _ _ _ tmem5 Hc4 HSP6 HONE6
                (ltac:(by rewrite !Pointer.inc_preserves_component)) Hst5.
  set regs9 := Register.set R_SP (Ptr (C, fbN, (0 + 1 + 1)%Z)) regs6
    in S1011.
  have Hc10 := code_at_tail (code_at_tail Hc4).
  (* IMov R_COM R_ARG *)
  have S12 := step_mov G (Pointer.inc pcJ :: gps) tmem5 regs9 _ R_COM R_ARG
                _ Hc10.
  set regsF := Register.set R_ARG (Register.get R_COM regs9) regs9 in S12.
  (* preservation of old cells across the whole prologue *)
  have HneN : forall C1 b1, Memory.load tmem (C1, b1, 0%Z) = Some w1 \/ True ->
      True by [].
  clear HneN.
  have Ltr5 : forall C1 b1 (o : Z) w,
      Memory.load tmem (C1, b1, o) = Some w ->
      (C1, b1, o) <> (C, fb, Z.of_nat (2 + size temps)) :> Pointer.t ->
      (C1, b1) <> (C, fbN) :> (Component.id * Block.id) ->
      Memory.load tmem5 (C1, b1, o) = Some w.
  { move=> C1 b1 o w Hl Hne HneN.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst5);
      last by move=> EE; inversion EE; case: HneN; rewrite -H0 -H1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst3);
      last by move=> EE; inversion EE; case: HneN; rewrite -H0 -H1.
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halloc HneN).
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst1);
      last by move=> EE; rewrite EE in Hne; case: (Hne erefl).
    exact: Hl. }
  have HneOld : forall C1 b1, Memory.load tmem (C1, b1, 0%Z) = Some w1 ->
      True by [].
  clear HneOld.
  (* fresh-frame disjointness from everything old *)
  have HfrN : forall C1 b1 (o : Z) w,
      Memory.load tmem (C1, b1, o) = Some w ->
      (C1, b1) <> (C, fbN) :> (Component.id * Block.id).
  { move=> C1 b1 o w Hl [E1 E2]. subst C1 b1.
    apply: (Hfresh1 o w).
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst1);
      last by move=> EE; inversion EE; case: HfbNfb.
    exact: Hl. }
  (* the new frame's linkage cells *)
  have Hslot0 : Memory.load tmem5 (C, fbN, 0%Z)
                = Some (Ptr (C, fb, Z.of_nat (2 + size temps + 1))).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst5);
      last by move=> EE; inversion EE.
    have -> : Ptr (C, fb, Z.of_nat (2 + size temps + 1))
              = Register.get R_AUX1 regs5.
    { rewrite /regs5 /regs4 /regs3 HSP2. rget.
      congr Ptr. congr (_, _). lia. }
    exact: Memory.load_after_store_eq Hst3. }
  (* slot 1 is now the saved ARGUMENT (the scratch slot moved to the wrapper) *)
  have Hslot1 : Memory.load tmem5 (C, fbN, 1%Z)
                = Some (Register.get R_ARG tregs).
  { have -> : Register.get R_ARG tregs = Register.get R_ARG regs6.
    { by rewrite /regs6 /regs5 /regs4 /regs3 /regs2 /regs1; rget. }
    have -> : (1%Z) = (0 + 1)%Z by [].
    exact: Memory.load_after_store_eq Hst5. }
  (* final register facts *)
  have HONEF : Register.get R_ONE regsF = Int 1.
  { by rewrite /regsF /regs9 /regs6 /regs5 /regs4 /regs3
            /regs2 /regs1; rget. }
  have HSPF : Register.get R_SP regsF = Ptr (C, fbN, (0 + 1 + 1)%Z).
  { by rewrite /regsF /regs9; rget. }
  have HARGF : Register.get R_ARG regsF = Int v.
  { rewrite /regsF register_get_set_eq /regs9 /regs6 /regs5
            /regs4 /regs3 /regs2 /regs1. rget. exact: Ecom. }
  (* assemble *)
  eexists tmem5, regsF, _, (Pointer.inc pcJ :: gps), bodyc,
          (pop R_ARG ++ pop R_SP ++ [:: IJump]), sA, sB, fbN.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_star_trans; [exact: Ppush | | by []].
    eapply star_trans; [exact: star_one SJ | | by []].
    eapply star_trans; [exact: star_one SL | | by []].
    eapply star_trans; [exact: star_one S1 | | by []].
    eapply star_trans; [exact: star_one S2 | | by []].
    eapply star_trans; [exact: star_one S3 | | by []].
    eapply star_trans; [exact: S45 | | by []].
    eapply star_trans; [exact: S1011 | exact: star_one S12 | by []].
  - have Hplm' : getm (labelsP p) C = Some plm by rewrite Elab.
    split.
    + exact: Hplm'.
    + exact: Hdom.
    + have Hmem3 : mem_inject α mem tmem3.
      { apply: store_outside_inject Hmem2 _ Hst3.
        move=> b0 /=. exact: Havoid. }
      apply: store_outside_inject Hmem3 _ Hst5.
      move=> b0 /=. exact: Havoid.
    + move=> C' v0 Hv0.
      apply: Ltr5 (Hscrs _ _ Hv0) _ _.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * move=> [E1 E2]. exact: (HfbN1 (esym E2)).
    + apply: Ltr5 Hflag _ _.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * move=> [E1 E2]. exact: (HfbN1 (esym E2)).
    + move=> C' /Hall [w' Hl]. exists w'.
      apply: Ltr5 Hl _ _.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * move=> [E1 E2]. exact: (HfbN1 (esym E2)).
    + exact: HONEF.
    + by rewrite HSPF.
    + rewrite HARGF. exact: VI_int.
    + by rewrite !Pointer.inc_preserves_component.
    + exact: Ebody.
    + exact: code_at_tail Hc10.
    + apply: CMJ_base. exact: CM_stop.
    + exact: Huniq.
    + split; [exact: HfbN1 | exact: Havoid].
    + exact: Hscrp.
    + by move=> i.
    + move=> j Hj.
      have Hj' : (0 <= j < Z.of_nat (4 + stack_need P_expr))%Z.
      { move: Hj. rewrite /=. lia. }
      rewrite (Memory.load_after_store _ _ _ _ (C, fbN, j) Hst5).
      case: ifP => _; first by eexists.
      rewrite (Memory.load_after_store _ _ _ _ (C, fbN, j) Hst3).
      case: ifP => _; first by eexists.
      exists Undef. exact: HldN Hj'.
    + rewrite /=. lia.
    + rewrite inE negb_or. apply/andP. split.
      * apply/eqP => -[E2]. exact: (HfbNfb E2).
      * apply/negP => Hin.
        case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
                 Hstack Hin) => [o [w Hl]].
        exact: (HfrN _ _ _ _ Hl erefl).
    + (* the pushed SM_internal level *)
      apply: (SM_internal _ _ _ _ _ _ _ fb _ _ _ arg
                (Register.get R_ARG tregs) k rest0 temps plm
                (Pointer.inc pcJ) (Register.get R_RA tregs) cap).
      * exact: Hplm'.
      * by rewrite Pointer.inc_preserves_component HpcJ.
      * exact: code_at_tail HcJ.
      * exact: Hk.
      * exact: Hslot0.
      * exact: Hslot1.
      * exact: HARG.
      * exact: Hpriv.
      * (* the caller's temps survive *)
        move=> i Hi. apply: Ltr5 (Htemps i Hi) _ _.
        -- move=> EE.
           have := f_equal (fun q : Pointer.t => Pointer.offset q) EE.
           rewrite /=. lia.
        -- case=> E2. exact: (HfbNfb (esym E2)).
      * (* the pushed R_RA *)
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst5);
          last by move=> EE; inversion EE; case: HfbNfb.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hst3);
          last by move=> EE; inversion EE; case: HfbNfb.
        have HpairN : (C, fb) <> (C, Pointer.block ptrN)
                      :> (Component.id * Block.id).
        { case=> E2. exact: (HfbNfb (esym E2)). }
        rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halloc HpairN).
        exact: Memory.load_after_store_eq Hst1.
      * (* the caller's cap *)
        move=> j Hj. case: (Hcap j Hj) => w Hw.
        (* the RA slot may have been overwritten: use loadability *)
        rewrite (Memory.load_after_store _ _ _ _ (C, fb, j) Hst5).
        case: ifP => _; first by eexists.
        rewrite (Memory.load_after_store _ _ _ _ (C, fb, j) Hst3).
        case: ifP => _; first by eexists.
        rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Halloc);
          last by move=> [E2]; exact: (HfbNfb (esym E2)).
        rewrite (Memory.load_after_store _ _ _ _ (C, fb, j) Hst1).
        case: ifP => _; [by eexists | by exists w].
      * move: Hbud => /=. lia.
      * exact: Hprot.
      * exact: HfbNfb.
      * (* the tail, at the recorded-write map *)
        have Hstk5 : stack_match G (labelsP p) α tmem5 scrs C fb prot stk gps.
        { have Hs1 : stack_match G (labelsP p) α tmem1 scrs C fb prot stk gps.
          { apply: stack_match_store Hstack Hst1 Hprot _.
            move=> _. lia. }
          have Hs2 : stack_match G (labelsP p) α tmem2 scrs C fb prot stk gps.
          { apply: stack_match_alloc Hs1 Halloc erefl (rle_refl α) _ _.
            - move=> Cx b0 bx HA. by left.
            - move=> o w Hl. exact: Hfresh1 Hl. }
          have HnpN : (C, fbN) \notin prot.
          { apply/negP => Hin.
            case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
                     Hs1 Hin) => [o [w Hl]].
            exact: Hfresh1 Hl. }
          have HcurN : ((C, fbN) = (C, fb) :> (Component.id * Block.id))
                       -> False.
          { move=> [E2]. exact: (HfbNfb E2). }
          have Hs3 : stack_match G (labelsP p) α tmem3 scrs C fb prot stk gps.
          { apply: stack_match_store Hs2 Hst3 HnpN _.
            move=> E. by case: (HcurN E). }
          apply: stack_match_store Hs3 Hst5 HnpN _.
          move=> E. by case: (HcurN E). }
        (* [SM_internal] no longer rewrites [scrs], so the tail is verbatim *)
        exact: Hstk5.
    + exact: Hmnf.
Qed.

(* KS_ExternalCall: drain, push the linkage, store the transit pointer,
   ICall (the ECall event), cross the callee's external entry, run the
   internal prologue, and suspend the caller externally. *)
Lemma diagram_call_ext α scrs C Cf stk mem k P v arg gps tmem tregs pc fb
      prot temps plm rest cap P_expr :
  val_inv p tp α scrs C stk mem (Kcall Cf P k) (Int v) arg gps tmem tregs pc
          fb prot temps plm rest cap ->
  C <> Cf ->
  imported_procedure (Source.prog_interface p) C Cf P ->
  Source.find_procedure (Source.prog_procedures p) Cf P = Some P_expr ->
  exists scrs1 tmem9 tregs9 pcF gps1 c1 rest1 sA sB fbN prot1 plm1,
    plus CS.step G (gps, tmem, tregs, pc) [:: ECall C P v Cf]
         (gps1, tmem9, tregs9, pcF) /\
    expr_inv p tp α scrs1 Cf (S.CS.Frame C arg k :: stk) mem Kstop P_expr
             (Int v) gps1 tmem9 tregs9 pcF fbN prot1 [::] plm1
             c1 rest1 sA sB (4 + stack_need P_expr).
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf HneCf Himp
         Hfind.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pcD [rest1 [Sd _ HcD [Ec Eb] Hcm']]].
  case: (cont_match_call_inv Hcm') => [[tl [rest0 [EC _ _ _]]]
                                      |[rest0 [_ Erest Hk]]];
    first by case: HneCf; rewrite EC.
  subst rest1.
  have Ecom := val_inject_int_l _ _ _ Hcom.
  (* push R_RA *)
  have [wRA HwRA] : exists w,
      Memory.load tmem (C, fb, Z.of_nat (2 + size temps)) = Some w.
  { apply: Hcap. move: Hbud => /=. slia. }
  have [tmemA HstA] :=
    Memory.store_after_load _ _ _ (Register.get R_RA tregs) HwRA.
  have PpushRA := exec_push_plus gps tmem tregs pcD R_RA _ _ _ _ tmemA
                    HcD HSP HONE Ec HstA.
  set regs1 := Register.set R_SP _ tregs in PpushRA.
  set pcA := Pointer.inc (Pointer.inc pcD) in PpushRA.
  have HpcA : Pointer.component pcA = C
    by rewrite /pcA !Pointer.inc_preserves_component Ec.
  have HcA : code_at G pcA
      (push R_ARG ++ store_arg (scr C) R_SP R_AUX2
         ++ ICall Cf P :: IConst (IInt 1) R_ONE
         :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0).
  { exact: code_at_tail (code_at_tail HcD). }
  (* push R_ARG *)
  have HcapA : frame_cap tmemA C fb cap.
  { exact: frame_cap_store Hcap HstA. }
  have [wAR HwAR] : exists w,
      Memory.load tmemA (C, fb, (Z.of_nat (2 + size temps) + 1)%Z) = Some w.
  { apply: HcapA. move: Hbud => /=. slia. }
  have [tmemB HstB] :=
    Memory.store_after_load _ _ _ (Register.get R_ARG regs1) HwAR.
  have HSP1 : Register.get R_SP regs1
              = Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)
    by rewrite /regs1; rget.
  have HONE1 : Register.get R_ONE regs1 = Int 1 by rewrite /regs1; rget.
  have SpushAR := exec_push _ gps tmemA regs1 _ R_ARG _ _ _ _ tmemB
                    HcA HSP1 HONE1 HpcA HstB.
  set regs2 := Register.set R_SP
                 (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1 + 1)%Z)) regs1
    in SpushAR.
  set pcB := Pointer.inc (Pointer.inc pcA) in SpushAR.
  have HpcB : Pointer.component pcB = C
    by rewrite /pcB !Pointer.inc_preserves_component Ec.
  have HcB := code_at_tail (code_at_tail HcA).
  (* store_arg : the transit pointer *)
  have Hn1fb : forall (C1 : Component.id) (o1 o2 : Z),
      (C, fb, o1) <> (C1, 1, o2) :> Pointer.t.
  { move=> C1 o1 o2 E. inversion E. by case: Hpriv => + _; apply. }
  have Hn1fb' : forall (o1 o2 : Z), (C, 1, o1) <> (C, fb, o2) :> Pointer.t.
  { move=> o1 o2 E. inversion E. by case: Hpriv => + _; apply. }
  have [wS HwS] := Hall _ Hdom.
  have HwS' : Memory.load tmemB (C, 1, 0%Z) = Some wS.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstB).
    by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstA). }
  have [tmemC HstC] :=
    Memory.store_after_load _ _ _ (Register.get R_SP regs2) HwS'.
  have SstoreT := exec_store_arg _ gps tmemB regs2 _ (scr C) R_SP R_AUX2 _
                    tmemC HcB (esym HpcB) (ltac:(by [])) HstC.
  set regs3 := Register.set R_AUX2 (Ptr (scr C)) regs2 in SstoreT.
  set pcC := Pointer.inc (Pointer.inc pcB) in SstoreT.
  have HpcC : Pointer.component pcC = C
    by rewrite /pcC !Pointer.inc_preserves_component Ec.
  have HcC := code_at_tail (code_at_tail HcB).
  set transit := Register.get R_SP regs2 in HstC.
  have Etransit : transit
                  = Ptr (C, fb, (Z.of_nat (2 + size temps) + 1 + 1)%Z)
    by rewrite /transit /regs2; rget.
  (* the ICall: interface and entry point *)
  have Eintf : genv_interface G = Source.prog_interface p.
  { by rewrite /G /prepare_global_env /=
       (compilation_preserves_interface _ _ Hcompile). }
  have HimpT : imported_procedure (genv_interface G) C Cf P
    by rewrite Eintf.
  have Hexp : exported_procedure (Source.prog_interface p) Cf P.
  { exact: (Source.cprog_closed_interface Hclosed_p) Himp. }
  have HCfdom : Cf \in domm (Intermediate.prog_interface tp).
  { case: Hexp => CI' [HhasC' _].
    rewrite (compilation_preserves_interface _ _ Hcompile).
    by rewrite mem_domm HhasC'. }
  (* the callee's compiled code and entry point *)
  move: (Hfind). rewrite /Source.find_procedure.
  case HgCf: (getm (Source.prog_procedures p) Cf) => [CprocsF|] //.
  move=> HgPf.
  case: (compile_prog_procedures_spec Hwf_p Hcompile)
    => [labels [cenv1 [Egen HSPEC]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  case: (HSPEC _ _ _ _ HgCf HgPf)
    => [plmf [CprocsT [cd [s1 [s2 [Hplmf HgT HgTP Hcp]]]]]].
  case: (compiled_code_anchor _ _ _ _ _ HCfdom HgT HgTP)
    => [bE [CprocsB [HgB HgBE Hentrypt Hother]]].
  have HEP : EntryPoint.get Cf P (genv_entrypoints G) = Some bE.
  { case: (Hexp) => CI' [HhasC' Hexporting].
    apply: (Hentrypt CI').
    - by rewrite (compilation_preserves_interface _ _ Hcompile).
    - by apply/orP; left. }
  have HCOM3 : Register.get R_COM regs3 = Int v
    by rewrite /regs3 /regs2 /regs1; rget.
  have Scall : CS.step G (gps, tmemC, regs3, pcC)
               [:: ECall (Pointer.component pcC) P v Cf]
               (Pointer.inc pcC :: gps, tmemC, Register.invalidate regs3,
                (Cf, bE, 0%Z)).
  { apply: step_call HcC _ _ HEP HCOM3.
    - by rewrite HpcC.
    - by rewrite HpcC. }
  (* the callee's entry label exists *)
  have [plf Hplf] : exists plf, getm plmf P = Some plf.
  { move: Hcp.
    rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
    case: (getm plmf P) => [x|] //=. by exists x. }
  have HcE0 : code_at G (Cf, bE, 0%Z) cd.
  { exists CprocsB, cd, [::], [::]. split=> //. by rewrite cats0. }
  have HCOMinv : Register.get R_COM (Register.invalidate regs3) = Int v.
  { by rewrite /Register.invalidate HCOM3 /Register.get mkfmapE /=. }
  case: (compiled_jal_resolution Hwf_p Hcompile)
    => [labels2 [cenv2 [Egen2 HRES]]].
  move: Egen2. rewrite Egen. case=> E1' E2'. subst labels2 cenv2.
  have HRES' := HRES _ _ _ _ _ _ HgCf HgPf Hplmf Hplf HCfdom.
  (* the caller-side memory relation and preserved loads up to tmemC *)
  have HmemC : mem_inject α mem tmemC.
  { have HmemA : mem_inject α mem tmemA.
    { apply: store_outside_inject Hmem _ HstA.
      move=> b0 /=. exact: (proj2 Hpriv). }
    have HmemB : mem_inject α mem tmemB.
    { apply: store_outside_inject HmemA _ HstB.
      move=> b0 /=. exact: (proj2 Hpriv). }
    apply: store_outside_inject HmemB _ HstC.
    move=> b0 /=. exact: Hscrp. }
  have [wf HwfC] : exists wf, Memory.load tmemC (Cf, 1, 0%Z) = Some wf.
  { have [wf Hwf0] := Hall _ HCfdom.
    exists wf.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstC);
      last by move=> EE; inversion EE; apply: HneCf.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstB).
    by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstA). }
  (* transport of arbitrary old cells to tmemC (outside the two frame slots
     and the caller's scratch cell) *)
  have LtrC : forall C1 b1 (o : Z) w,
      Memory.load tmem (C1, b1, o) = Some w ->
      (C1, b1, o) <> (C, fb, Z.of_nat (2 + size temps)) ->
      (C1, b1, o) <> (C, fb, (Z.of_nat (2 + size temps) + 1)%Z) ->
      (C1, b1, o) <> (C, 1, 0%Z) ->
      Memory.load tmemC (C1, b1, o) = Some w.
  { move=> C1 b1 o w Hl Hne1 Hne2 Hne3.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstC);
      last by move=> EE; rewrite EE in Hne3; case: (Hne3 erefl).
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstB);
      last by move=> EE; rewrite EE in Hne2; case: (Hne2 erefl).
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstA);
      last by move=> EE; rewrite EE in Hne1; case: (Hne1 erefl).
    exact: Hl. }
  case Hmain: (Component.eqb Cf Component.main && Procedure.eqb P
                 Procedure.main).
  - (* main-callee: dual entry with the flag *)
    move: (Hmain) => /andP [/PeanoNat.Nat.eqb_eq ECf /PeanoNat.Nat.eqb_eq EP].
    subst Cf P.
    have Hfin : immediately_final P_expr = false.
    { apply: Hmnf. by rewrite /Source.prog_main. }
    case: (compile_proc_shape_main _ _ _ _ _ _ _ _ Hcp Hplf Hmain Hfin)
      => [lm [lr [bodyc0 [sA0 [sB0 [Ebody0 Ecd]]]]]].
    rewrite Ecd in HcE0.
    set regsI := Register.invalidate regs3 in Scall HCOMinv.
    have F1 := step_const G (Pointer.inc pcC :: gps) tmemC regsI _ (IInt 1)
                 R_ONE _ HcE0.
    set regsG1 := Register.set R_ONE (Int 1) regsI in F1.
    have Hd1 := code_at_tail HcE0.
    have F2 := step_mov G (Pointer.inc pcC :: gps) tmemC regsG1 _ R_SP R_AUX1
                 _ Hd1.
    set regsG2 := Register.set R_AUX1 (Register.get R_SP regsG1) regsG1 in F2.
    have Hd2 := code_at_tail Hd1.
    have F3 := step_const G (Pointer.inc pcC :: gps) tmemC regsG2 _
                 (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP _ Hd2.
    set regsG3 := Register.set R_SP
                    (Int (Z.of_nat (4 + stack_need P_expr))) regsG2 in F3.
    have Hd3 := code_at_tail Hd2.
    have [cmf Hcmf] : exists cm, getm tmemC Component.main = Some cm.
    { move: HwfC. rewrite /Memory.load /=.
      case: (getm tmemC Component.main) => // cm _. by exists cm. }
    have [tmemD [ptrE HallocE]] : exists tmemD ptrE,
        Memory.alloc tmemC Component.main
          (Z.to_nat (Z.of_nat (4 + stack_need P_expr)))
        = Some (tmemD, ptrE).
    { rewrite /Memory.alloc Hcmf.
      case: (ComponentMemory.alloc cmf _) => cm' b. by do 2 eexists. }
    case: (alloc_outside_inject HmemC HallocE)
      => [HmemD EcompE EoffE HavoidE].
    set fbE := Pointer.block ptrE.
    have EptrE : ptrE = (Component.main, fbE, 0%Z).
    { rewrite /fbE. case: (ptrE) EcompE EoffE => [[pC pB] pO] /= EC EO.
      by rewrite EC EO. }
    have HfreshE : forall (o : Z) w,
        Memory.load tmemC (Component.main, fbE, o) = Some w -> False.
    { exact: memory_alloc_fresh (mi_wf_t _ _ _ HmemC) HallocE. }
    have HfbE1 : fbE <> 1.
    { move=> E. rewrite E in HfreshE. exact: HfreshE HwfC. }
    have HgSP3 : Register.get R_SP regsG3
                 = Int (Z.of_nat (4 + stack_need P_expr))
      by rewrite /regsG3 /Register.get /Register.set setmE /=.
    have F4 : CS.step G (Pointer.inc pcC :: gps, tmemC, regsG3,
                Pointer.inc (Pointer.inc (Pointer.inc
                  (Component.main, bE, 0%Z)))) E0
              (Pointer.inc pcC :: gps, tmemD,
               Register.set R_SP (Ptr ptrE) regsG3,
               Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc
                 (Component.main, bE, 0%Z))))).
    { apply: step_alloc Hd3 HgSP3 _ _.
      - slia.
      - rewrite /=. exact: HallocE. }
    set regsG4 := Register.set R_SP (Ptr ptrE) regsG3 in F4.
    have Hd4 := code_at_tail Hd3.
    have HldE : forall o : Z,
        (0 <= o < Z.of_nat (4 + stack_need P_expr))%Z ->
        Memory.load tmemD (Component.main, fbE, o) = Some Undef.
    { move=> o Ho. apply: memory_load_after_alloc_in HallocE _.
      rewrite Nat2Z.id. exact: Ho. }
    have [tmemE1 HstE1] := Memory.store_after_load _ _ _
        (Register.get R_AUX1 regsG4) (HldE 0%Z (ltac:(slia))).
    have HSPG4 : Register.get R_SP regsG4 = Ptr (Component.main, fbE, 0%Z)
      by rewrite /regsG4 EptrE /Register.get /Register.set setmE /=.
    have HONEG4 : Register.get R_ONE regsG4 = Int 1
      by rewrite /regsG4 /regsG3 /regsG2 /regsG1 /Register.get
                 /Register.set !setmE /=.
    have F56 := exec_push _ (Pointer.inc pcC :: gps) tmemD regsG4 _ R_AUX1
                  _ _ _ _ tmemE1 Hd4 HSPG4 HONEG4 (ltac:(by [])) HstE1.
    set regsG5 := Register.set R_SP (Ptr (Component.main, fbE, (0 + 1)%Z))
                    regsG4 in F56.
    have Hd6 := code_at_tail (code_at_tail Hd4).
    (* load_arg scr R_AUX1 : the WRAPPER now saves the inherited scratch (this
       moved here from the body's prologue — see the note on [compile_proc]) *)
    have HwE1 : Memory.load tmemE1 (Component.main, 1, 0%Z) = Some wf.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; exact: HfbE1.
      have Hpair : (Component.main, 1) <> (Component.main, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
      exact: HwfC. }
    have F67 := exec_load_arg _ (Pointer.inc pcC :: gps) tmemE1 regsG5 _
                  (scr Component.main) R_AUX1 _ _ Hd6 (ltac:(by [])) HwE1.
    set regsG5b := Register.set R_AUX1 wf
                     (Register.set R_AUX1 (Ptr (scr Component.main)) regsG5)
      in F67.
    have Hd6b := code_at_tail (code_at_tail Hd6).
    (* push R_AUX1 : slot 1 := the inherited scratch *)
    have HldE1 : Memory.load tmemE1 (Component.main, fbE, (0 + 1)%Z)
                 = Some Undef.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE.
      apply: HldE. slia. }
    have [tmemE1b HstE1b] := Memory.store_after_load _ _ _
        (Register.get R_AUX1 regsG5b) HldE1.
    have HSPG5b : Register.get R_SP regsG5b
                  = Ptr (Component.main, fbE, (0 + 1)%Z)
      by rewrite /regsG5b /regsG5 /Register.get /Register.set !setmE /=.
    have HONEG5b : Register.get R_ONE regsG5b = Int 1
      by rewrite /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
                 /Register.get /Register.set !setmE /=.
    have F67b := exec_push _ (Pointer.inc pcC :: gps) tmemE1 regsG5b _ R_AUX1
                   _ _ _ _ tmemE1b Hd6b HSPG5b HONEG5b (ltac:(by [])) HstE1b.
    set regsG5c := Register.set R_SP
                     (Ptr (Component.main, fbE, (0 + 1 + 1)%Z)) regsG5b in F67b.
    have Hd6c := code_at_tail (code_at_tail Hd6b).
    (* push R_RA : slot 2 *)
    have HldE2ra : Memory.load tmemE1b (Component.main, fbE, (0 + 1 + 1)%Z)
                   = Some Undef.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; slia.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; slia.
      apply: HldE. slia. }
    have [tmemE2 HstE2] := Memory.store_after_load _ _ _
        (Register.get R_RA regsG5c) HldE2ra.
    have HSPG5 : Register.get R_SP regsG5c
                 = Ptr (Component.main, fbE, (0 + 1 + 1)%Z)
      by rewrite /regsG5c /Register.get /Register.set setmE /=.
    have HONEG5 : Register.get R_ONE regsG5c = Int 1
      by rewrite /regsG5c /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
                 /Register.get /Register.set !setmE /=.
    have F78 := exec_push _ (Pointer.inc pcC :: gps) tmemE1b regsG5c _ R_RA
                  _ _ _ _ tmemE2 Hd6c HSPG5 HONEG5 (ltac:(by [])) HstE2.
    set regsG6 := Register.set R_SP
                    (Ptr (Component.main, fbE, (0 + 1 + 1 + 1)%Z))
                    regsG5c in F78.
    have Hd8 := code_at_tail (code_at_tail Hd6c).
    (* the flag test: IConst flag-ptr; ILoad; push the marker *)
    have M9 := step_const G (Pointer.inc pcC :: gps) tmemE2 regsG6 _
                 (IPtr (flag_buf_ptr (scr Component.main))) R_AUX1 _ Hd8.
    set regsM9 := Register.set R_AUX1
                    (Ptr (flag_buf_ptr (scr Component.main))) regsG6 in M9.
    have Hd9 := code_at_tail Hd8.
    have HflagE2 : Memory.load tmemE2 (Component.main, 1, (0 + 1)%Z)
                   = Some (Int 1).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; apply: HfbE1.
      have Hpair : (Component.main, 1) <> (Component.main, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
      apply: LtrC Hflag _ _ _.
      - by move=> EE; inversion EE; case: Hpriv => + _; apply.
      - by move=> EE; inversion EE; case: Hpriv => + _; apply.
      - by move=> EE; inversion EE; apply: HneCf. }
    have HA1M9 : Register.get R_AUX1 regsM9
                 = Ptr (flag_buf_ptr (scr Component.main))
      by rewrite /regsM9 /Register.get /Register.set setmE /=.
    have HldFl : Memory.load tmemE2 (flag_buf_ptr (scr Component.main))
                 = Some (Int 1).
    { exact: HflagE2. }
    have M10 := step_load G (Pointer.inc pcC :: gps) tmemE2 regsM9 _
                  R_AUX1 R_AUX2 _ _ _ Hd9 HA1M9 (ltac:(by [])) HldFl.
    set regsM10 := Register.set R_AUX2 (Int 1) regsM9 in M10.
    have Hd10 := code_at_tail Hd9.
    have HldE2 : Memory.load tmemE2 (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
                 = Some Undef.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; slia.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; slia.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; slia.
      apply: HldE. slia. }
    have [tmemE3 HstE3] := Memory.store_after_load _ _ _
        (Register.get R_AUX2 regsM10) HldE2.
    have HSPM10 : Register.get R_SP regsM10
                  = Ptr (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
      by rewrite /regsM10 /regsM9 /regsG6 /Register.get /Register.set
                 !setmE /=.
    have HONEM10 : Register.get R_ONE regsM10 = Int 1
      by rewrite /regsM10 /regsM9 /regsG6 /regsG5c /regsG5b /regsG5 /regsG4
                 /regsG3 /regsG2 /regsG1 /Register.get /Register.set !setmE /=.
    have M1112 := exec_push _ (Pointer.inc pcC :: gps) tmemE2 regsM10 _
                    R_AUX2 _ _ _ _ tmemE3 Hd10 HSPM10 HONEM10
                    (ltac:(by [])) HstE3.
    set regsM12 := Register.set R_SP
                     (Ptr (Component.main, fbE, (0 + 1 + 1 + 1 + 1)%Z)) regsM10
      in M1112.
    have Hd12 := code_at_tail (code_at_tail Hd10).
    (* the taken IBnz over the initial-run constant *)
    have Huq0 := Huniq _ _ _ _ HgB HgBE.
    set pre14 := ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                      IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                      IAlloc R_SP R_SP] ++
                  push R_AUX1 ++
                  load_arg (scr Component.main) R_AUX1 ++ push R_AUX1 ++
                  push R_RA ++
                  [:: IConst (IPtr (flag_buf_ptr (scr Component.main)))
                        R_AUX1;
                      ILoad R_AUX1 R_AUX2] ++
                  push R_AUX2 ++
                  [:: IBnz R_AUX2 lm; IConst (IInt 0) R_COM]).
    set rest14 := ([:: IConst (IInt 1) R_AUX2;
                       IStore R_AUX1 R_AUX2; IJal plf] ++
                   pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
                   store_arg (scr Component.main) R_AUX1 R_AUX2 ++
                   pop R_SP ++
                   [:: IBnz R_ARG lr; IHalt; ILabel lr; IReturn] ++
                   ILabel plf ::
                   ([:: IMov R_SP R_AUX1;
                        IConst (IInt (Z.of_nat (4 + stack_need P_expr)))
                          R_SP;
                        IAlloc R_SP R_SP] ++
                    push R_AUX1 ++
                    push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc0 ++
                    (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
    have Edec14 : cd = pre14 ++ ILabel lm :: rest14.
    { rewrite Ecd /pre14 /rest14.
      by do 14!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have Hnotin14 : lm \notin labels_of pre14.
    { apply: uniq_cat_cons_notin (labels_of rest14) _.
      move: Huq0. rewrite Edec14 labels_of_cat /=. by []. }
    have HgB13 : getm (genv_procedures G) (Pointer.component
        (iter 16 Pointer.inc (Component.main, bE, 0%Z))) = Some CprocsB.
    { exact: HgB. }
    have HgBE13 : getm CprocsB (Pointer.block
        (iter 16 Pointer.inc (Component.main, bE, 0%Z))) = Some cd.
    { exact: HgBE. }
    have Hfind14 : find_label_in_procedure G
        (iter 16 Pointer.inc (Component.main, bE, 0%Z)) lm
        = Some (Component.main, bE, Z.of_nat (size pre14)).
    { exact: (find_label_in_procedure_at _ _ _ _ _ _ _
                HgB13 HgBE13 Edec14 Hnotin14). }
    have HA2M12 : Register.get R_AUX2 regsM12 = Int 1
      by rewrite /regsM12 /regsM10 /Register.get /Register.set !setmE /=.
    have M13 : CS.step G (Pointer.inc pcC :: gps, tmemE3, regsM12,
                 iter 16 Pointer.inc (Component.main, bE, 0%Z)) E0
               (Pointer.inc pcC :: gps, tmemE3, regsM12,
                (Component.main, bE, Z.of_nat (size pre14))).
    { apply: step_bnz_nz _ HA2M12 _ Hfind14.
      - exact: Hd12.
      - by []. }
    have HcL : code_at G (Component.main, bE, Z.of_nat (size pre14))
                 (ILabel lm :: rest14).
    { exists CprocsB, cd, pre14, [::]. split=> //.
      - by rewrite Edec14 cats0.
    }
    have M14 : CS.step G (Pointer.inc pcC :: gps, tmemE3, regsM12,
                 (Component.main, bE, Z.of_nat (size pre14))) E0
               (Pointer.inc pcC :: gps, tmemE3, regsM12,
                Pointer.inc (Component.main, bE, Z.of_nat (size pre14))).
    { exact: step_label HcL. }
    have HdL1 := code_at_tail HcL.
    have M15 := step_const G (Pointer.inc pcC :: gps) tmemE3 regsM12 _
                  (IInt 1) R_AUX2 _ HdL1.
    set regsM15 := Register.set R_AUX2 (Int 1) regsM12 in M15.
    have HdL2 := code_at_tail HdL1.
    (* re-store the flag *)
    have HflagE3 : Memory.load tmemE3 (Component.main, 1, (0 + 1)%Z)
                   = Some (Int 1).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE; apply: HfbE1.
      exact: HflagE2. }
    have [tmemE4 HstE4] := Memory.store_after_load _ _ _
        (Register.get R_AUX2 regsM15) HflagE3.
    have HgA1M15 : Register.get R_AUX1 regsM15
                   = Ptr (flag_buf_ptr (scr Component.main))
      by rewrite /regsM15 /regsM12 /regsM10 /regsM9 /Register.get
                 /Register.set !setmE /=.
    have HstE4' : Memory.store tmemE3 (flag_buf_ptr (scr Component.main))
                    (Register.get R_AUX2 regsM15) = Some tmemE4.
    { exact: HstE4. }
    have M16 := step_store G (Pointer.inc pcC :: gps) tmemE3 regsM15 _
                  R_AUX1 R_AUX2 _ (flag_buf_ptr (scr Component.main)) tmemE4
                  HdL2 HgA1M15 (ltac:(by [])) HstE4'.
    have HdL3 := code_at_tail HdL2.
    (* IJal pl *)
    case: (HRES' (Pointer.inc (Pointer.inc (Pointer.inc
             (Component.main, bE, Z.of_nat (size pre14)))))
             (ltac:(by rewrite !Pointer.inc_preserves_component)))
      => [bPJ [cdJ [extJ [restJ [CprocsBJ [HgBJ HgCdJ HdecJ HexJ HflJ]]]]]].
    case: HexJ => [s1J [s2J HcpJ]].
    have MJ : CS.step G (Pointer.inc pcC :: gps, tmemE4, regsM15,
                Pointer.inc (Pointer.inc (Pointer.inc
                  (Component.main, bE, Z.of_nat (size pre14))))) E0
              (Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc
                 (Component.main, bE, Z.of_nat (size pre14)))))
                 :: Pointer.inc pcC :: gps, tmemE4,
               Register.set R_RA Undef regsM15,
               (Component.main, bPJ, Z.of_nat (size extJ))).
    { apply: step_jal _ HflJ. exact: HdL3. }
    set regsM17 := Register.set R_RA Undef regsM15 in MJ.
    set jal_ret := Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc
                     (Component.main, bE, Z.of_nat (size pre14))))) in MJ.
    have Hjrc : code_at G jal_ret
        (pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
         store_arg (scr Component.main) R_AUX1 R_AUX2 ++ pop R_SP ++
         [:: IBnz R_ARG lr; IHalt; ILabel lr; IReturn]).
    { apply: (code_at_app_l (c2 := ILabel plf ::
        ([:: IMov R_SP R_AUX1;
             IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
             IAlloc R_SP R_SP] ++
         push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc0 ++
         (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
      move: (code_at_tail HdL3).
      rewrite /jal_ret.
      by do 12!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    (* the landing and the internal prologue *)
    have Huq := Huniq _ _ _ _ HgBJ HgCdJ.
    case: (compile_proc_after_label _ _ _ _ _ _ _ _ _ _ HcpJ Hplf HdecJ Huq)
      => [bodycJ [sAJ [sBJ [EbodyJ ErestJ]]]].
    subst restJ.
    have HcLand : code_at G (Component.main, bPJ, Z.of_nat (size extJ))
        (ILabel plf ::
           ([:: IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                IAlloc R_SP R_SP] ++
            push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodycJ ++
            (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
    { exists CprocsBJ, cdJ, extJ, [::]. split=> //.
      rewrite HdecJ. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have HONEM17 : Register.get R_ONE regsM17 = Int 1
      by rewrite /regsM17 /regsM15 /regsM12 /regsM10 /regsM9 /regsG6 /regsG5c
                 /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
                 /Register.get /Register.set !setmE /=.
    have HwfE4 : exists w,
        Memory.load tmemE4 (Component.main, 1, 0%Z) = Some w.
    { exists wf.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; inversion EE.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; apply: HfbE1.
      have Hpair : (Component.main, 1)
                   <> (Component.main, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair). }
    have HmemE4 : mem_inject α mem tmemE4.
    { have HmemE1 : mem_inject α mem tmemE1.
      { apply: store_outside_inject HmemD _ HstE1.
        move=> b0 /=. exact: HavoidE. }
      have HmemE1b : mem_inject α mem tmemE1b.
      { apply: store_outside_inject HmemE1 _ HstE1b.
        move=> b0 /=. exact: HavoidE. }
      have HmemE2' : mem_inject α mem tmemE2.
      { apply: store_outside_inject HmemE1b _ HstE2.
        move=> b0 /=. exact: HavoidE. }
      have HmemE3 : mem_inject α mem tmemE3.
      { apply: store_outside_inject HmemE2' _ HstE3.
        move=> b0 /=. exact: HavoidE. }
      apply: store_outside_inject HmemE3 _ HstE4.
      move=> b0 /=. exact: Hscrp. }
    case: (internal_prologue_run Component.main
             (jal_ret :: Pointer.inc pcC :: gps) tmemE4 regsM17
             (Component.main, bPJ, Z.of_nat (size extJ)) plf
             (stack_need P_expr) bodycJ _ α mem HcLand (ltac:(by []))
             HONEM17 HmemE4 HwfE4)
      => [tmemF [regsF [fbN [pcF [wscr
           [Sprol [HmemF Hwscr HfreshN HavoidN HfbN1]
             [Hslot0 Hslot1 LtrN]
             [RONEF RSPF RARGF RCOMF] [HpcF HcF HcapN Hsmtr]]]]]]].
    (* register values entering the prologue *)
    have HgSP17 : Register.get R_SP regsM17
                  = Ptr (Component.main, fbE, (0 + 1 + 1 + 1 + 1)%Z)
      by rewrite /regsM17 /regsM15 /regsM12 /Register.get /Register.set
                 !setmE /=.
    have HgCOM17 : Register.get R_COM regsM17 = Int v.
    { rewrite -HCOMinv /regsM17 /regsM15 /regsM12 /regsM10 /regsM9 /regsG6
              /regsG5c /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
              /Register.get /Register.set !setmE /=. by []. }
    (* the callee's EF-frame slots survive into tmemF.  FOUR of them now:
       caller R_SP, the INHERITED SCRATCH, R_RA, and the context marker. *)
    have HldEF0 : Memory.load tmemE4 (Component.main, fbE, 0%Z)
                  = Some (Register.get R_AUX1 regsG4).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE.
      exact: Memory.load_after_store_eq HstE1. }
    have HldEF1 : Memory.load tmemE4 (Component.main, fbE, (0 + 1)%Z)
                  = Some (Register.get R_AUX1 regsG5b).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE; slia.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; slia.
      exact: Memory.load_after_store_eq HstE1b. }
    have HldEF2 : Memory.load tmemE4 (Component.main, fbE, (0 + 1 + 1)%Z)
                  = Some (Register.get R_RA regsG5c).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE; slia.
      exact: Memory.load_after_store_eq HstE2. }
    have HldEF3 : Memory.load tmemE4
                    (Component.main, fbE, (0 + 1 + 1 + 1)%Z) = Some (Int 1).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; inversion EE; apply: HfbE1.
      have -> : (Int 1) = Register.get R_AUX2 regsM10
        by rewrite /regsM10 /Register.get /Register.set setmE /=.
      exact: Memory.load_after_store_eq HstE3. }
    have HnefbEN : fbE <> fbN.
    { move=> E. apply: (HfreshN 0%Z (Register.get R_AUX1 regsG4)).
      by rewrite -E. }
    have HpairEN : (Component.main, fbE) <> (Component.main, fbN)
                   :> (Component.id * Block.id).
    { case=> E2. exact: (HnefbEN E2). }
    have HldF0 : Memory.load tmemF (Component.main, fbE, 0%Z)
                 = Some (Register.get R_AUX1 regsG4).
    { exact: LtrN HldEF0 HpairEN. }
    have HldF1 : Memory.load tmemF (Component.main, fbE, (0 + 1)%Z)
                 = Some (Register.get R_AUX1 regsG5b).
    { exact: LtrN HldEF1 HpairEN. }
    have HldF2 : Memory.load tmemF (Component.main, fbE, (0 + 1 + 1)%Z)
                 = Some (Register.get R_RA regsG5c).
    { exact: LtrN HldEF2 HpairEN. }
    have HldF3 : Memory.load tmemF (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
                 = Some (Int 1).
    { exact: LtrN HldEF3 HpairEN. }
    (* transports of old cells to tmemF; the flag cell is special-cased *)
    have LtrEF : forall C1 b1 (o : Z) w,
        Memory.load tmemC (C1, b1, o) = Some w ->
        (C1, b1) <> (Component.main, fbE) :> (Component.id * Block.id) ->
        (C1, b1) <> (Component.main, fbN) :> (Component.id * Block.id) ->
        (C1, b1, o) <> (Component.main, 1, (0 + 1)%Z) :> Pointer.t ->
        Memory.load tmemF (C1, b1, o) = Some w.
    { move=> C1 b1 o w Hl HneE HneN Hnefl.
      apply: LtrN _ HneN.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
        last by move=> EE; rewrite EE in Hnefl; case: (Hnefl erefl).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE HneE). }
    have HpCfb : forall bx, (C, fb) <> (Component.main, bx)
                            :> (Component.id * Block.id).
    { move=> bx. case=> E1 _. by apply: HneCf; rewrite E1. }
    have HpCfl : forall (o : Z),
        (C, fb, o) <> (Component.main, 1, (0 + 1)%Z) :> Pointer.t.
    { move=> o E. inversion E. by case: Hpriv => + _; apply. }
    have LtrCfb : forall (o : Z) w,
        Memory.load tmem (C, fb, o) = Some w ->
        o <> Z.of_nat (2 + size temps) ->
        o <> (Z.of_nat (2 + size temps) + 1)%Z ->
        Memory.load tmemF (C, fb, o) = Some w.
    { move=> o w Hl Hne1 Hne2.
      apply: LtrEF _ (HpCfb fbE) (HpCfb fbN) (HpCfl o).
      apply: LtrC Hl _ _ _.
      - move=> EE. case: Hne1.
        exact: (f_equal (fun q : Pointer.t => Pointer.offset q) EE).
      - move=> EE. case: Hne2.
        exact: (f_equal (fun q : Pointer.t => Pointer.offset q) EE).
      - by move=> EE; inversion EE; case: Hpriv => + _; apply. }
    have HljRA : Memory.load tmemF (C, fb, Z.of_nat (2 + size temps))
                 = Some (Register.get R_RA tregs).
    { apply: LtrEF _ (HpCfb fbE) (HpCfb fbN) (HpCfl _).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb' _ _) HstC).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstB);
        last by move=> EE; inversion EE; slia.
      exact: Memory.load_after_store_eq HstA. }
    have HltARG : Memory.load tmemF
                    (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)
                  = Some (Register.get R_ARG tregs).
    { apply: LtrEF _ (HpCfb fbE) (HpCfb fbN) (HpCfl _).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb' _ _) HstC).
      have -> : Register.get R_ARG tregs = Register.get R_ARG regs1
        by rewrite /regs1; rget.
      exact: Memory.load_after_store_eq HstB. }
    have Etransit' : transit
                     = Ptr (C, fb, Z.of_nat (2 + size temps + 2)).
    { rewrite Etransit. congr Ptr. congr (_, _). slia. }
    have HldTr : Memory.load tmemF (C, 1, 0%Z) = Some transit.
    { have HneCfp : forall bx, (C, 1) <> (Component.main, bx)
                               :> (Component.id * Block.id).
      { move=> bx. case=> E1 _. by apply: HneCf; rewrite E1. }
      have Hnefl : (C, 1, 0%Z) <> (Component.main, 1, (0 + 1)%Z)
                   :> Pointer.t.
      { move=> E. inversion E. }
      apply: LtrEF _ (HneCfp fbE) (HneCfp fbN) Hnefl.
      exact: Memory.load_after_store_eq HstC. }
    have HldFlag : Memory.load tmemF (Component.main, 1, 1%Z) = Some (Int 1).
    { have HgA2M15 : Register.get R_AUX2 regsM15 = Int 1
        by rewrite /regsM15 /Register.get /Register.set setmE /=.
      have Hne : (Component.main, 1) <> (Component.main, fbN)
                 :> (Component.id * Block.id).
      { case=> E2. exact: (HfbN1 (esym E2)). }
      apply: LtrN _ Hne.
      have -> : (Int 1) = Register.get R_AUX2 regsM15 by rewrite HgA2M15.
      exact: Memory.load_after_store_eq HstE4. }
    have HwfE4' : Memory.load tmemE4 (Component.main, 1, 0%Z) = Some wf.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
          last by move=> EE; inversion EE.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
          last by move=> EE; inversion EE; apply: HfbE1.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
          last by move=> EE; inversion EE; apply: HfbE1.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
          last by move=> EE; inversion EE; apply: HfbE1.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
          last by move=> EE; inversion EE; apply: HfbE1.
        have Hpair : (Component.main, 1)
                     <> (Component.main, Pointer.block ptrE)
                     :> (Component.id * Block.id).
        { case=> E2. exact: (HfbE1 (esym E2)). }
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE
                    Hpair). }
    have Ew : wscr = wf.
    { move: Hwscr. rewrite HwfE4'. by case. }
    have Ewscr : Memory.load tmem (Component.main, 1, 0%Z) = Some wscr.
    { rewrite Ew.
      move: HwfC.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstC);
        last by move=> EE; inversion EE; apply: HneCf.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstB).
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _)
                    HstA). }
    (* the assembled run *)
    have Hplus : plus CS.step G (gps, tmem, tregs, pc)
        [:: ECall (Pointer.component pcC) Procedure.main v Component.main]
        (jal_ret :: Pointer.inc pcC :: gps, tmemF, regsF, pcF).
    { eapply star_plus_trans; [exact: Sd | | by []].
      eapply plus_star_trans; [exact: PpushRA | | by []].
      eapply star_trans; [exact: SpushAR | | by []].
      eapply star_trans; [exact: SstoreT | | by []].
      eapply star_trans; [exact: star_one Scall | | by []].
      eapply star_trans; [exact: star_one F1 | | by []].
      eapply star_trans; [exact: star_one F2 | | by []].
      eapply star_trans; [exact: star_one F3 | | by []].
      eapply star_trans; [exact: star_one F4 | | by []].
      eapply star_trans; [exact: F56 | | by []].
      eapply star_trans; [exact: F67 | | by []].
      eapply star_trans; [exact: F67b | | by []].
      eapply star_trans; [exact: F78 | | by []].
      eapply star_trans; [exact: star_one M9 | | by []].
      eapply star_trans; [exact: star_one M10 | | by []].
      eapply star_trans; [exact: M1112 | | by []].
      eapply star_trans; [exact: star_one M13 | | by []].
      eapply star_trans; [exact: star_one M14 | | by []].
      eapply star_trans; [exact: star_one M15 | | by []].
      eapply star_trans; [exact: star_one M16 | | by []].
      eapply star_trans; [exact: star_one MJ | exact: Sprol | by []]. }
    rewrite HpcC in Hplus.
    exists (setm scrs C transit), tmemF, regsF, pcF,
           (jal_ret :: Pointer.inc pcC :: gps), bodycJ,
           (pop R_ARG ++ pop R_SP ++ [:: IJump]), sAJ, sBJ, fbN,
           ((Component.main, fbE) :: (C, fb) :: prot), plmf.
    split; first exact: Hplus.
    have HnpE' : (Component.main, fbE) \notin prot.
    { apply/negP => Hin.
      case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
               Hstack Hin) => [o [w Hl]].
      apply: (HfreshE o w).
      apply: LtrC Hl _ _ _; by move=> EE; inversion EE; apply: HneCf. }
    split.
    + by rewrite Elab.
    + exact: HCfdom.
    + exact: HmemF.
    + move=> C' v0. rewrite setmE.
      case: eqP => [-> [<-] | HneC' Hv0]; first exact: HldTr.
      have Hp : forall bx, bx <> 1 ->
          (C', 1) <> (Component.main, bx) :> (Component.id * Block.id).
      { move=> bx Hbx. case=> _ E2. by case: (Hbx (esym E2)). }
      have Hnefl : (C', 1, 0%Z) <> (Component.main, 1, (0 + 1)%Z)
                   :> Pointer.t.
      { move=> E. inversion E. }
      apply: LtrEF _ (Hp _ HfbE1) (Hp _ HfbN1) Hnefl.
      apply: LtrC (Hscrs _ _ Hv0) _ _ _.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * by move=> EE; inversion EE; apply: HneC'.
    + exact: HldFlag.
    + move=> C' HC'dom.
      have [w' Hw'] := Hall _ HC'dom.
      have Hp : forall bx, bx <> 1 ->
          (C', 1) <> (Component.main, bx) :> (Component.id * Block.id).
      { move=> bx Hbx. case=> _ E2. by case: (Hbx (esym E2)). }
      have Hnefl : (C', 1, 0%Z) <> (Component.main, 1, (0 + 1)%Z)
                   :> Pointer.t.
      { move=> E. inversion E. }
      case: (C' =P C) => [EC' | HneC'].
      * subst C'. exists transit. exact: HldTr.
      * exists w'.
        apply: LtrEF _ (Hp _ HfbE1) (Hp _ HfbN1) Hnefl.
        apply: LtrC Hw' _ _ _.
        -- by move=> EE; inversion EE; case: Hpriv => + _; apply.
        -- by move=> EE; inversion EE; case: Hpriv => + _; apply.
        -- by move=> EE; inversion EE; apply: HneC'.
    + exact: RONEF.
    + by rewrite RSPF.
    + rewrite RARGF HgCOM17. exact: VI_int.
    + exact: HpcF.
    + exact: EbodyJ.
    + exact: HcF.
    + apply: CMJ_base. exact: CM_stop.
    + exact: Huniq.
    + split; [exact: HfbN1 | exact: HavoidN].
    + exact: Hscrp.
    + by [].
    + exact: HcapN.
    + rewrite /=. slia.
    + rewrite !inE !negb_or. apply/and3P. split.
      * apply/eqP. case=> E2. exact: (HnefbEN (esym E2)).
      * apply/eqP. case=> E1 _. by apply: HneCf; rewrite E1.
      * apply/negP => Hin.
        case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
                 Hstack Hin) => [o [w Hl]].
        have HlC : Memory.load tmemC (Component.main, fbN, o) = Some w.
        { apply: LtrC Hl _ _ _;
            by move=> EE; inversion EE; apply: HneCf. }
        case: (fbN =P fbE) => [EfbNE | HnefbNE'].
        -- apply: (HfreshE o w). by rewrite -EfbNE.
        -- apply: (HfreshN o w).
           have Hpair' : (Component.main, fbN) <> (Component.main, fbE)
                         :> (Component.id * Block.id).
           { case=> E2. exact: (HnefbNE' E2). }
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
             last by move=> EE; inversion EE; apply: HfbN1.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
             last by move=> EE; inversion EE; case: HnefbNE'.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
             last by move=> EE; inversion EE; case: HnefbNE'.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
             last by move=> EE; inversion EE; case: HnefbNE'.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
             last by move=> EE; inversion EE; case: HnefbNE'.
           by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE
                         Hpair').
    + apply: (SM_external _ _ _ _ _ Component.main C fbN fbE
                ((0 + 1 + 1 + 1 + 1)%Z) fb _ _ _
                arg (Register.get R_ARG tregs) k rest0 temps plm jal_ret
                (Pointer.inc pcC) wscr (Register.get R_RA tregs)
                (Register.get R_ARG regsM17) cap).
      * move=> E. by apply: HneCf; rewrite E.
      * exact: Hplm.
      * apply: (EF_main _ _ _ _ _ lr (Register.get R_AUX1 regsG4)
                  (Register.get R_AUX1 regsG5b) (Register.get R_RA regsG5c) 1)
          => //.
      * split; [exact: HfbE1 | exact: HavoidE].
      * by rewrite Hslot0 HgSP17.
      (* the WRAPPER frame's slot 1 is the inherited scratch [wscr] *)
      * have -> : (1%Z) = (0 + 1)%Z by [].
        rewrite HldF1 Ew /regsG5b /Register.get /Register.set setmE /=.
        by [].
      * exact: Hslot1.
      * by rewrite Pointer.inc_preserves_component HpcC.
      * exact: code_at_tail HcC.
      * exact: Hk.
      * exact: Hpriv.
      * move=> i Hi. apply: LtrCfb (Htemps i Hi) _ _; slia.
      * exact: HljRA.
      * have -> : Z.of_nat (2 + size temps + 1)
                = (Z.of_nat (2 + size temps) + 1)%Z by slia.
        exact: HltARG.
      * exact: HARG.
      * move=> j Hj.
        case: (Z.eqb_spec j (Z.of_nat (2 + size temps))) => [-> | Hne1].
        { eexists. exact: HljRA. }
        case: (Z.eqb_spec j (Z.of_nat (2 + size temps) + 1)%Z)
          => [-> | Hne2].
        { eexists. exact: HltARG. }
        case: (Hcap j Hj) => w Hw. exists w.
        exact: LtrCfb Hw Hne1 Hne2.
      * move: Hbud => /=. slia.
      * by rewrite setmE eqxx Etransit'.
      * exact: Hprot.
      * rewrite inE negb_or. apply/andP. split.
        -- apply/eqP. case=> E1 _. by apply: HneCf; rewrite E1.
        -- exact: HnpE'.
      * move=> E. exact: (HnefbEN (esym E)).
      * have HcurN1 : ((C, 1) = (C, fb) :> (Component.id * Block.id))
                      -> False.
        { case=> E2. by case: Hpriv => + _; apply; rewrite -E2. }
        have Hnp1 : (C, 1) \notin prot.
        { apply/negP => Hin.
          exact: (stack_match_prot_not1 _ _ _ _ _ _ _ _ _ _ _ _
                    Hstack Hin erefl). }
        have Hnpm1 : (Component.main, 1) \notin prot.
        { apply/negP => Hin.
          exact: (stack_match_prot_not1 _ _ _ _ _ _ _ _ _ _ _ _
                    Hstack Hin erefl). }
        have Hs1 : stack_match G (labelsP p) α tmemA scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hstack HstA Hprot _.
          move=> _. slia. }
        have Hs2 : stack_match G (labelsP p) α tmemB scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs1 HstB Hprot _.
          move=> _. slia. }
        have Hs3 : stack_match G (labelsP p) α tmemC scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs2 HstC Hnp1 _.
          move=> E. by case: (HcurN1 E). }
        have Hs4 : stack_match G (labelsP p) α tmemD scrs C fb prot stk
                     gps.
        { apply: stack_match_alloc Hs3 HallocE erefl (rle_refl α) _ _.
          - move=> Cx b0 bx HA. by left.
          - move=> o w Hl. exact: HfreshE Hl. }
        have HcurE : ((Component.main, fbE) = (C, fb)
                      :> (Component.id * Block.id)) -> False.
        { case=> E1 _. by apply: HneCf; rewrite E1. }
        have Hs5 : stack_match G (labelsP p) α tmemE1 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs4 HstE1 HnpE' _.
          move=> E. by case: (HcurE E). }
        have Hs5b : stack_match G (labelsP p) α tmemE1b scrs C fb prot stk
                      gps.
        { apply: stack_match_store Hs5 HstE1b HnpE' _.
          move=> E. by case: (HcurE E). }
        have Hs6 : stack_match G (labelsP p) α tmemE2 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs5b HstE2 HnpE' _.
          move=> E. by case: (HcurE E). }
        have Hs7 : stack_match G (labelsP p) α tmemE3 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs6 HstE3 HnpE' _.
          move=> E. by case: (HcurE E). }
        have HcurM1 : ((Component.main, 1) = (C, fb)
                       :> (Component.id * Block.id)) -> False.
        { case=> E1 _. by apply: HneCf; rewrite E1. }
        have Hs8 : stack_match G (labelsP p) α tmemE4 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs7 HstE4 Hnpm1 _.
          move=> E. by case: (HcurM1 E). }
        have HsF := Hsmtr _ _ _ _ _ _ _ Hs8.
        have Hup := stack_match_scrs_update _ _ _ _ _ _ _ _ _ _ transit
                      HsF.
        case Hget: (getm scrs Component.main) => [w0|].
        -- have Ew0 : wscr = w0.
           { have := Hscrs _ _ Hget. rewrite Ewscr. by case. }
           have -> : setm (setm scrs C transit) Component.main wscr
                     = setm scrs C transit.
           { apply/eq_fmap => x. rewrite !setmE.
             case: (x =P Component.main) => [->|_] //.
             have /negbTE -> : Component.main != C
               by apply/eqP => E; apply: HneCf; rewrite E.
             by rewrite Hget Ew0. }
           exact: Hup.
        -- apply: stack_match_scrs_extend Hup _.
           rewrite setmE.
           have /negbTE -> : Component.main != C
             by apply/eqP => E; apply: HneCf; rewrite E.
           exact: Hget.
    + by [].
  - (* standard callee *)
    case: (compile_proc_shape_std _ _ _ _ _ _ _ _ Hcp Hplf Hmain)
      => [bodyc0 [sA0 [sB0 [Ebody0 Ecd]]]].
    rewrite Ecd in HcE0.
    set regsI := Register.invalidate regs3 in Scall HCOMinv.
    (* IConst 1 R_ONE *)
    have F1 := step_const G (Pointer.inc pcC :: gps) tmemC regsI _ (IInt 1)
                 R_ONE _ HcE0.
    set regsG1 := Register.set R_ONE (Int 1) regsI in F1.
    have Hd1 := code_at_tail HcE0.
    (* IMov R_SP R_AUX1 *)
    have F2 := step_mov G (Pointer.inc pcC :: gps) tmemC regsG1 _ R_SP R_AUX1
                 _ Hd1.
    set regsG2 := Register.set R_AUX1 (Register.get R_SP regsG1) regsG1 in F2.
    have Hd2 := code_at_tail Hd1.
    (* IConst frame R_SP *)
    have F3 := step_const G (Pointer.inc pcC :: gps) tmemC regsG2 _
                 (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP _ Hd2.
    set regsG3 := Register.set R_SP
                    (Int (Z.of_nat (4 + stack_need P_expr))) regsG2 in F3.
    have Hd3 := code_at_tail Hd2.
    (* IAlloc : the EF frame *)
    have [cmf Hcmf] : exists cm, getm tmemC Cf = Some cm.
    { move: HwfC. rewrite /Memory.load /=.
      case: (getm tmemC Cf) => // cm _. by exists cm. }
    have [tmemD [ptrE HallocE]] : exists tmemD ptrE,
        Memory.alloc tmemC Cf (Z.to_nat (Z.of_nat (4 + stack_need P_expr)))
        = Some (tmemD, ptrE).
    { rewrite /Memory.alloc Hcmf.
      case: (ComponentMemory.alloc cmf _) => cm' b. by do 2 eexists. }
    case: (alloc_outside_inject HmemC HallocE)
      => [HmemD EcompE EoffE HavoidE].
    set fbE := Pointer.block ptrE.
    have EptrE : ptrE = (Cf, fbE, 0%Z).
    { rewrite /fbE. case: (ptrE) EcompE EoffE => [[pC pB] pO] /= EC EO.
      by rewrite EC EO. }
    have HfreshE : forall (o : Z) w,
        Memory.load tmemC (Cf, fbE, o) = Some w -> False.
    { exact: memory_alloc_fresh (mi_wf_t _ _ _ HmemC) HallocE. }
    have HfbE1 : fbE <> 1.
    { move=> E. rewrite E in HfreshE. exact: HfreshE HwfC. }
    have HgSP3 : Register.get R_SP regsG3
                 = Int (Z.of_nat (4 + stack_need P_expr))
      by rewrite /regsG3 /Register.get /Register.set setmE /=.
    have F4 : CS.step G (Pointer.inc pcC :: gps, tmemC, regsG3,
                Pointer.inc (Pointer.inc (Pointer.inc (Cf, bE, 0%Z)))) E0
              (Pointer.inc pcC :: gps, tmemD,
               Register.set R_SP (Ptr ptrE) regsG3,
               Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc
                 (Cf, bE, 0%Z))))).
    { apply: step_alloc Hd3 HgSP3 _ _.
      - slia.
      - rewrite /=. exact: HallocE. }
    set regsG4 := Register.set R_SP (Ptr ptrE) regsG3 in F4.
    have Hd4 := code_at_tail Hd3.
    have HldE : forall o : Z,
        (0 <= o < Z.of_nat (4 + stack_need P_expr))%Z ->
        Memory.load tmemD (Cf, fbE, o) = Some Undef.
    { move=> o Ho. apply: memory_load_after_alloc_in HallocE _.
      rewrite Nat2Z.id. exact: Ho. }
    (* push R_AUX1 : slot 0 *)
    have [tmemE1 HstE1] := Memory.store_after_load _ _ _
        (Register.get R_AUX1 regsG4) (HldE 0%Z (ltac:(slia))).
    have HSPG4 : Register.get R_SP regsG4 = Ptr (Cf, fbE, 0%Z)
      by rewrite /regsG4 EptrE /Register.get /Register.set setmE /=.
    have HONEG4 : Register.get R_ONE regsG4 = Int 1
      by rewrite /regsG4 /regsG3 /regsG2 /regsG1 /Register.get
                 /Register.set !setmE /=.
    have F56 := exec_push _ (Pointer.inc pcC :: gps) tmemD regsG4 _ R_AUX1
                  _ _ _ _ tmemE1 Hd4 HSPG4 HONEG4 (ltac:(by [])) HstE1.
    set regsG5 := Register.set R_SP (Ptr (Cf, fbE, (0 + 1)%Z)) regsG4 in F56.
    have Hd6 := code_at_tail (code_at_tail Hd4).
    (* load_arg scr R_AUX1 : the wrapper saves the inherited scratch *)
    have HwE1 : Memory.load tmemE1 (Cf, 1, 0%Z) = Some wf.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; exact: HfbE1.
      have Hpair : (Cf, 1) <> (Cf, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
      exact: HwfC. }
    have F67 := exec_load_arg _ (Pointer.inc pcC :: gps) tmemE1 regsG5 _
                  (scr Cf) R_AUX1 _ _ Hd6 (ltac:(by [])) HwE1.
    set regsG5b := Register.set R_AUX1 wf
                     (Register.set R_AUX1 (Ptr (scr Cf)) regsG5) in F67.
    have Hd6b := code_at_tail (code_at_tail Hd6).
    (* push R_AUX1 : slot 1 := the inherited scratch *)
    have HldE1 : Memory.load tmemE1 (Cf, fbE, (0 + 1)%Z) = Some Undef.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE.
      apply: HldE. slia. }
    have [tmemE1b HstE1b] := Memory.store_after_load _ _ _
        (Register.get R_AUX1 regsG5b) HldE1.
    have HSPG5b : Register.get R_SP regsG5b = Ptr (Cf, fbE, (0 + 1)%Z)
      by rewrite /regsG5b /regsG5 /Register.get /Register.set !setmE /=.
    have HONEG5b : Register.get R_ONE regsG5b = Int 1
      by rewrite /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
                 /Register.get /Register.set !setmE /=.
    have F67b := exec_push _ (Pointer.inc pcC :: gps) tmemE1 regsG5b _ R_AUX1
                   _ _ _ _ tmemE1b Hd6b HSPG5b HONEG5b (ltac:(by [])) HstE1b.
    set regsG5c := Register.set R_SP (Ptr (Cf, fbE, (0 + 1 + 1)%Z)) regsG5b
      in F67b.
    have Hd6c := code_at_tail (code_at_tail Hd6b).
    (* push R_RA : slot 2 *)
    have HldE2ra : Memory.load tmemE1b (Cf, fbE, (0 + 1 + 1)%Z) = Some Undef.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; slia.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; slia.
      apply: HldE. slia. }
    have [tmemE2 HstE2] := Memory.store_after_load _ _ _
        (Register.get R_RA regsG5c) HldE2ra.
    have HSPG5 : Register.get R_SP regsG5c = Ptr (Cf, fbE, (0 + 1 + 1)%Z)
      by rewrite /regsG5c /Register.get /Register.set setmE /=.
    have HONEG5 : Register.get R_ONE regsG5c = Int 1
      by rewrite /regsG5c /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
                 /Register.get /Register.set !setmE /=.
    have F78 := exec_push _ (Pointer.inc pcC :: gps) tmemE1b regsG5c _ R_RA
                  _ _ _ _ tmemE2 Hd6c HSPG5 HONEG5 (ltac:(by [])) HstE2.
    set regsG6 := Register.set R_SP (Ptr (Cf, fbE, (0 + 1 + 1 + 1)%Z)) regsG5c
      in F78.
    have Hd8 := code_at_tail (code_at_tail Hd6c).
    (* IJal plf *)
    case: (HRES' (iter 12 Pointer.inc (Cf, bE, 0%Z)) (ltac:(by [])))
      => [bPJ [cdJ [extJ [restJ [CprocsBJ [HgBJ HgCdJ HdecJ HexJ HflJ]]]]]].
    case: HexJ => [s1J [s2J HcpJ]].
    have FJ : CS.step G (Pointer.inc pcC :: gps, tmemE2, regsG6,
                iter 12 Pointer.inc (Cf, bE, 0%Z)) E0
              (Pointer.inc (iter 12 Pointer.inc (Cf, bE, 0%Z))
                 :: Pointer.inc pcC :: gps, tmemE2,
               Register.set R_RA Undef regsG6,
               (Cf, bPJ, Z.of_nat (size extJ))).
    { apply: step_jal _ HflJ. exact: Hd8. }
    set regsG7 := Register.set R_RA Undef regsG6 in FJ.
    set jal_ret := Pointer.inc (iter 12 Pointer.inc (Cf, bE, 0%Z)) in FJ.
    have Hjrc : code_at G jal_ret
        (pop R_RA ++ pop R_AUX1 ++ store_arg (scr Cf) R_AUX1 R_AUX2
           ++ pop R_SP ++ [:: IReturn]).
    { apply: (code_at_app_l (c2 := ILabel plf ::
        ([:: IMov R_SP R_AUX1;
             IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
             IAlloc R_SP R_SP] ++
         push R_AUX1 ++
         push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc0 ++
         (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
      move: (code_at_tail Hd8).
      by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    (* the landing and the internal prologue *)
    have Huq := Huniq _ _ _ _ HgBJ HgCdJ.
    case: (compile_proc_after_label _ _ _ _ _ _ _ _ _ _ HcpJ Hplf HdecJ Huq)
      => [bodycJ [sAJ [sBJ [EbodyJ ErestJ]]]].
    subst restJ.
    have HcLand : code_at G (Cf, bPJ, Z.of_nat (size extJ))
        (ILabel plf ::
           ([:: IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                IAlloc R_SP R_SP] ++
            push R_AUX1 ++
            push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodycJ ++
            (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
    { exists CprocsBJ, cdJ, extJ, [::]. split=> //.
      rewrite HdecJ. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
    have HONEG7 : Register.get R_ONE regsG7 = Int 1
      by rewrite /regsG7 /regsG6 /regsG5c /regsG5b /regsG5 /regsG4 /regsG3
                 /regsG2 /regsG1 /Register.get /Register.set !setmE /=.
    have HwfE2 : exists w, Memory.load tmemE2 (Cf, 1, 0%Z) = Some w.
    { exists wf.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; apply: HfbE1.
      have Hpair : (Cf, 1) <> (Cf, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair). }
    have HmemE2 : mem_inject α mem tmemE2.
    { have HmemE1 : mem_inject α mem tmemE1.
      { apply: store_outside_inject HmemD _ HstE1.
        move=> b0 /=. exact: HavoidE. }
      have HmemE1b : mem_inject α mem tmemE1b.
      { apply: store_outside_inject HmemE1 _ HstE1b.
        move=> b0 /=. exact: HavoidE. }
      apply: store_outside_inject HmemE1b _ HstE2.
      move=> b0 /=. exact: HavoidE. }
    case: (internal_prologue_run Cf
             (jal_ret :: Pointer.inc pcC :: gps) tmemE2 regsG7
             (Cf, bPJ, Z.of_nat (size extJ)) plf (stack_need P_expr)
             bodycJ _ α mem HcLand (ltac:(by [])) HONEG7 HmemE2 HwfE2)
      => [tmemF [regsF [fbN [pcF [wscr
           [Sprol [HmemF Hwscr HfreshN HavoidN HfbN1]
             [Hslot0 Hslot1 LtrN]
             [RONEF RSPF RARGF RCOMF] [HpcF HcF HcapN Hsmtr]]]]]]].
    (* register values entering the prologue *)
    have HgSP7 : Register.get R_SP regsG7 = Ptr (Cf, fbE, (0 + 1 + 1 + 1)%Z)
      by rewrite /regsG7 /regsG6 /Register.get /Register.set !setmE /=.
    have HgCOM7 : Register.get R_COM regsG7 = Int v.
    { rewrite -HCOMinv /regsG7 /regsG6 /regsG5c /regsG5b /regsG5 /regsG4
              /regsG3 /regsG2 /regsG1 /Register.get /Register.set !setmE /=.
      by []. }
    (* the callee's EF-frame slots survive into tmemF: caller R_SP, the
       INHERITED SCRATCH, and R_RA *)
    have HldEF0 : Memory.load tmemE2 (Cf, fbE, 0%Z)
                  = Some (Register.get R_AUX1 regsG4).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE.
      exact: Memory.load_after_store_eq HstE1. }
    have HldEF1 : Memory.load tmemE2 (Cf, fbE, (0 + 1)%Z)
                  = Some (Register.get R_AUX1 regsG5b).
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; slia.
      exact: Memory.load_after_store_eq HstE1b. }
    have HldEF2 : Memory.load tmemE2 (Cf, fbE, (0 + 1 + 1)%Z)
                  = Some (Register.get R_RA regsG5c).
    { exact: Memory.load_after_store_eq HstE2. }
    have HnefbEN : fbE <> fbN.
    { move=> E. apply: (HfreshN 0%Z (Register.get R_AUX1 regsG4)).
      by rewrite -E. }
    have HpairEN : (Cf, fbE) <> (Cf, fbN) :> (Component.id * Block.id).
    { case=> E2. exact: (HnefbEN E2). }
    have HldF0 : Memory.load tmemF (Cf, fbE, 0%Z)
                 = Some (Register.get R_AUX1 regsG4).
    { exact: LtrN HldEF0 HpairEN. }
    have HldF1 : Memory.load tmemF (Cf, fbE, (0 + 1)%Z)
                 = Some (Register.get R_AUX1 regsG5b).
    { exact: LtrN HldEF1 HpairEN. }
    have HldF2 : Memory.load tmemF (Cf, fbE, (0 + 1 + 1)%Z)
                 = Some (Register.get R_RA regsG5c).
    { exact: LtrN HldEF2 HpairEN. }
    (* transports of caller cells to tmemF *)
    have LtrEF : forall C1 b1 (o : Z) w,
        Memory.load tmemC (C1, b1, o) = Some w ->
        (C1, b1) <> (Cf, fbE) :> (Component.id * Block.id) ->
        (C1, b1) <> (Cf, fbN) :> (Component.id * Block.id) ->
        Memory.load tmemF (C1, b1, o) = Some w.
    { move=> C1 b1 o w Hl HneE HneN.
      apply: LtrN _ HneN.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE HneE). }
    have HpCfb : forall bx, (C, fb) <> (Cf, bx)
                            :> (Component.id * Block.id).
    { move=> bx. case=> E1 _. by apply: HneCf; rewrite E1. }
    have LtrCfb : forall (o : Z) w,
        Memory.load tmem (C, fb, o) = Some w ->
        o <> Z.of_nat (2 + size temps) ->
        o <> (Z.of_nat (2 + size temps) + 1)%Z ->
        Memory.load tmemF (C, fb, o) = Some w.
    { move=> o w Hl Hne1 Hne2.
      apply: LtrEF _ (HpCfb fbE) (HpCfb fbN).
      apply: LtrC Hl _ _ _.
      - move=> EE. case: Hne1.
        exact: (f_equal (fun q : Pointer.t => Pointer.offset q) EE).
      - move=> EE. case: Hne2.
        exact: (f_equal (fun q : Pointer.t => Pointer.offset q) EE).
      - by move=> EE; inversion EE; case: Hpriv => + _; apply. }
    have HljRA : Memory.load tmemF (C, fb, Z.of_nat (2 + size temps))
                 = Some (Register.get R_RA tregs).
    { apply: LtrEF _ (HpCfb fbE) (HpCfb fbN).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb' _ _) HstC).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstB);
        last by move=> EE; inversion EE; slia.
      exact: Memory.load_after_store_eq HstA. }
    have HltARG : Memory.load tmemF
                    (C, fb, (Z.of_nat (2 + size temps) + 1)%Z)
                  = Some (Register.get R_ARG tregs).
    { apply: LtrEF _ (HpCfb fbE) (HpCfb fbN).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb' _ _) HstC).
      have -> : Register.get R_ARG tregs = Register.get R_ARG regs1
        by rewrite /regs1; rget.
      exact: Memory.load_after_store_eq HstB. }
    have Etransit' : transit
                     = Ptr (C, fb, Z.of_nat (2 + size temps + 2)).
    { rewrite Etransit. congr Ptr. congr (_, _). slia. }
    have HldTr : Memory.load tmemF (C, 1, 0%Z) = Some transit.
    { have HneCfp : forall bx, (C, 1) <> (Cf, bx)
                               :> (Component.id * Block.id).
      { move=> bx. case=> E1 _. by apply: HneCf; rewrite E1. }
      apply: LtrEF _ (HneCfp fbE) (HneCfp fbN).
      exact: Memory.load_after_store_eq HstC. }
    have HwfE2' : Memory.load tmemE2 (Cf, 1, 0%Z) = Some wf.
    { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
        last by move=> EE; inversion EE; apply: HfbE1.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
        last by move=> EE; inversion EE; apply: HfbE1.
      have Hpair : (Cf, 1) <> (Cf, Pointer.block ptrE)
                   :> (Component.id * Block.id).
      { case=> E2. exact: (HfbE1 (esym E2)). }
      by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE
                    Hpair). }
    have Ew : wscr = wf.
    { move: Hwscr. rewrite HwfE2'. by case. }
    have Ewscr : Memory.load tmem (Cf, 1, 0%Z) = Some wscr.
    { rewrite Ew.
      move: HwfC.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstC);
        last by move=> EE; inversion EE; apply: HneCf.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstB).
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _)
                    HstA). }
    (* the assembled run *)
    have Hplus : plus CS.step G (gps, tmem, tregs, pc)
        [:: ECall (Pointer.component pcC) P v Cf]
        (jal_ret :: Pointer.inc pcC :: gps, tmemF, regsF, pcF).
    { eapply star_plus_trans; [exact: Sd | | by []].
      eapply plus_star_trans; [exact: PpushRA | | by []].
      eapply star_trans; [exact: SpushAR | | by []].
      eapply star_trans; [exact: SstoreT | | by []].
      eapply star_trans; [exact: star_one Scall | | by []].
      eapply star_trans; [exact: star_one F1 | | by []].
      eapply star_trans; [exact: star_one F2 | | by []].
      eapply star_trans; [exact: star_one F3 | | by []].
      eapply star_trans; [exact: star_one F4 | | by []].
      eapply star_trans; [exact: F56 | | by []].
      eapply star_trans; [exact: F67 | | by []].
      eapply star_trans; [exact: F67b | | by []].
      eapply star_trans; [exact: F78 | | by []].
      eapply star_trans; [exact: star_one FJ | exact: Sprol | by []]. }
    rewrite HpcC in Hplus.
    exists (setm scrs C transit), tmemF, regsF, pcF,
           (jal_ret :: Pointer.inc pcC :: gps), bodycJ,
           (pop R_ARG ++ pop R_SP ++ [:: IJump]), sAJ, sBJ, fbN,
           ((Cf, fbE) :: (C, fb) :: prot), plmf.
    split; first exact: Hplus.
    have HnpE' : (Cf, fbE) \notin prot.
    { apply/negP => Hin.
      case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
               Hstack Hin) => [o [w Hl]].
      apply: (HfreshE o w).
      apply: LtrC Hl _ _ _; by move=> EE; inversion EE; apply: HneCf. }
    split.
    + by rewrite Elab.
    + exact: HCfdom.
    + exact: HmemF.
    + move=> C' v0. rewrite setmE.
      case: eqP => [-> [<-] | HneC' Hv0]; first exact: HldTr.
      have Hp : forall bx, bx <> 1 ->
          (C', 1) <> (Cf, bx) :> (Component.id * Block.id).
      { move=> bx Hbx. case=> _ E2. by case: (Hbx (esym E2)). }
      apply: LtrEF _ (Hp _ HfbE1) (Hp _ HfbN1).
      apply: LtrC (Hscrs _ _ Hv0) _ _ _.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * by move=> EE; inversion EE; case: Hpriv => + _; apply.
      * by move=> EE; inversion EE; apply: HneC'.
    + have Hp : forall bx, bx <> 1 ->
          (Component.main, 1) <> (Cf, bx) :> (Component.id * Block.id).
      { move=> bx Hbx. case=> _ E2. by case: (Hbx (esym E2)). }
      apply: LtrEF _ (Hp _ HfbE1) (Hp _ HfbN1).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstC);
        last by move=> EE; inversion EE.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _) HstB).
      by rewrite (Memory.load_after_store_neq _ _ _ _ _ (Hn1fb _ _ _)
                    HstA).
    + move=> C' HC'dom.
      have [w' Hw'] := Hall _ HC'dom.
      have Hp : forall bx, bx <> 1 ->
          (C', 1) <> (Cf, bx) :> (Component.id * Block.id).
      { move=> bx Hbx. case=> _ E2. by case: (Hbx (esym E2)). }
      case: (C' =P C) => [EC' | HneC'].
      * subst C'. exists transit. exact: HldTr.
      * exists w'.
        apply: LtrEF _ (Hp _ HfbE1) (Hp _ HfbN1).
        apply: LtrC Hw' _ _ _.
        -- by move=> EE; inversion EE; case: Hpriv => + _; apply.
        -- by move=> EE; inversion EE; case: Hpriv => + _; apply.
        -- by move=> EE; inversion EE; apply: HneC'.
    + exact: RONEF.
    + by rewrite RSPF.
    + rewrite RARGF HgCOM7. exact: VI_int.
    + exact: HpcF.
    + exact: EbodyJ.
    + exact: HcF.
    + apply: CMJ_base. exact: CM_stop.
    + exact: Huniq.
    + split; [exact: HfbN1 | exact: HavoidN].
    + exact: Hscrp.
    + by [].
    + exact: HcapN.
    + rewrite /=. slia.
    + rewrite !inE !negb_or. apply/and3P. split.
      * apply/eqP. case=> E2. exact: (HnefbEN (esym E2)).
      * apply/eqP. case=> E1 _. by apply: HneCf; rewrite E1.
      * apply/negP => Hin.
        case: (stack_match_prot_loadable _ _ _ _ _ _ _ _ _ _ _ _
                 Hstack Hin) => [o [w Hl]].
        have HlC : Memory.load tmemC (Cf, fbN, o) = Some w.
        { apply: LtrC Hl _ _ _;
            by move=> EE; inversion EE; apply: HneCf. }
        case: (fbN =P fbE) => [EfbNE | HnefbNE'].
        -- apply: (HfreshE o w). by rewrite -EfbNE.
        -- apply: (HfreshN o w).
           have Hpair' : (Cf, fbN) <> (Cf, fbE)
                         :> (Component.id * Block.id).
           { case=> E2. exact: (HnefbNE' E2). }
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
             last by move=> EE; inversion EE; case: HnefbNE'.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
             last by move=> EE; inversion EE; case: HnefbNE'.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
             last by move=> EE; inversion EE; case: HnefbNE'.
           by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE
                         Hpair').
    + apply: (SM_external _ _ _ _ _ Cf C fbN fbE ((0 + 1 + 1 + 1)%Z) fb _ _ _
                arg (Register.get R_ARG tregs) k rest0 temps plm jal_ret
                (Pointer.inc pcC) wscr (Register.get R_RA tregs)
                (Register.get R_ARG regsG7) cap).
      * move=> E. by apply: HneCf; rewrite E.
      * exact: Hplm.
      * apply: (EF_std _ _ _ _ _ (Register.get R_AUX1 regsG4)
                  (Register.get R_AUX1 regsG5b)
                  (Register.get R_RA regsG5c)) => //.
      * split; [exact: HfbE1 | exact: HavoidE].
      * by rewrite Hslot0 HgSP7.
      (* the WRAPPER frame's slot 1 is the inherited scratch [wscr] *)
      * have -> : (1%Z) = (0 + 1)%Z by [].
        rewrite HldF1 Ew /regsG5b /Register.get /Register.set setmE /=.
        by [].
      * exact: Hslot1.
      * by rewrite Pointer.inc_preserves_component HpcC.
      * exact: code_at_tail HcC.
      * exact: Hk.
      * exact: Hpriv.
      * move=> i Hi. apply: LtrCfb (Htemps i Hi) _ _; slia.
      * exact: HljRA.
      * have -> : Z.of_nat (2 + size temps + 1)
                = (Z.of_nat (2 + size temps) + 1)%Z by slia.
        exact: HltARG.
      * exact: HARG.
      * move=> j Hj.
        case: (Z.eqb_spec j (Z.of_nat (2 + size temps))) => [-> | Hne1].
        { eexists. exact: HljRA. }
        case: (Z.eqb_spec j (Z.of_nat (2 + size temps) + 1)%Z)
          => [-> | Hne2].
        { eexists. exact: HltARG. }
        case: (Hcap j Hj) => w Hw. exists w.
        exact: LtrCfb Hw Hne1 Hne2.
      * move: Hbud => /=. slia.
      * by rewrite setmE eqxx Etransit'.
      * exact: Hprot.
      * rewrite inE negb_or. apply/andP. split.
        -- apply/eqP. case=> E1 _. by apply: HneCf; rewrite E1.
        -- exact: HnpE'.
      * move=> E. exact: (HnefbEN (esym E)).
      * have HcurN1 : ((C, 1) = (C, fb) :> (Component.id * Block.id))
                      -> False.
        { case=> E2. by case: Hpriv => + _; apply; rewrite -E2. }
        have Hnp1 : (C, 1) \notin prot.
        { apply/negP => Hin.
          exact: (stack_match_prot_not1 _ _ _ _ _ _ _ _ _ _ _ _
                    Hstack Hin erefl). }
        have Hs1 : stack_match G (labelsP p) α tmemA scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hstack HstA Hprot _.
          move=> _. slia. }
        have Hs2 : stack_match G (labelsP p) α tmemB scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs1 HstB Hprot _.
          move=> _. slia. }
        have Hs3 : stack_match G (labelsP p) α tmemC scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs2 HstC Hnp1 _.
          move=> E. by case: (HcurN1 E). }
        have Hs4 : stack_match G (labelsP p) α tmemD scrs C fb prot stk
                     gps.
        { apply: stack_match_alloc Hs3 HallocE erefl (rle_refl α) _ _.
          - move=> Cx b0 bx HA. by left.
          - move=> o w Hl. exact: HfreshE Hl. }
        have HcurE : ((Cf, fbE) = (C, fb) :> (Component.id * Block.id))
                     -> False.
        { case=> E1 _. by apply: HneCf; rewrite E1. }
        have Hs5 : stack_match G (labelsP p) α tmemE1 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs4 HstE1 HnpE' _.
          move=> E. by case: (HcurE E). }
        have Hs5b : stack_match G (labelsP p) α tmemE1b scrs C fb prot stk
                      gps.
        { apply: stack_match_store Hs5 HstE1b HnpE' _.
          move=> E. by case: (HcurE E). }
        have Hs6 : stack_match G (labelsP p) α tmemE2 scrs C fb prot stk
                     gps.
        { apply: stack_match_store Hs5b HstE2 HnpE' _.
          move=> E. by case: (HcurE E). }
        have HsF := Hsmtr _ _ _ _ _ _ _ Hs6.
        have Hup := stack_match_scrs_update _ _ _ _ _ _ _ _ _ _ transit
                      HsF.
        case Hget: (getm scrs Cf) => [w0|].
        -- have Ew0 : wscr = w0.
           { have := Hscrs _ _ Hget. rewrite Ewscr. by case. }
           have -> : setm (setm scrs C transit) Cf wscr
                     = setm scrs C transit.
           { apply/eq_fmap => x. rewrite !setmE.
             case: (x =P Cf) => [->|_] //.
             have /negbTE -> : Cf != C
               by apply/eqP => E; apply: HneCf; rewrite E.
             by rewrite Hget Ew0. }
           exact: Hup.
        -- apply: stack_match_scrs_extend Hup _.
           rewrite setmE.
           have /negbTE -> : Cf != C
             by apply/eqP => E; apply: HneCf; rewrite E.
           exact: Hget.
    + by [].
Qed.

(* ==================== the initial bridge ==================== *)

(* every block of the compiled global environment holds a procedure body of
   the compiled program *)
Lemma genv_block_code_inv Cx CprocsB b cd :
  getm (genv_procedures G) Cx = Some CprocsB ->
  getm CprocsB b = Some cd ->
  exists P, getm (odflt emptym (getm (Intermediate.prog_procedures tp) Cx)) P
            = Some cd.
Proof.
  rewrite /G genv_procedures_getm.
  case HCx: (Cx \in domm (Intermediate.prog_interface tp)) => //.
  rewrite /Intermediate.reserve_component_blocks.
  case Erb: (ComponentMemoryExtra.reserve_blocks _ _) => [cm' bs] /=.
  move=> [<-] Hb.
  set Cprocs := odflt emptym (getm (Intermediate.prog_procedures tp) Cx)
    in Erb Hb *.
  have Hlen := ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Erb.
  have Hsz2 : size bs = size (unzip2 (elementsm Cprocs)).
  { rewrite /unzip2 size_map. move: Hlen.
    rewrite /length -/(size _) -/(size _). by move=> ->. }
  have [i [Hi Hbnth Hcdnth]] := getm_zip_inv _ _ _ _ Hsz2 Hb.
  have Hie : i < size (elementsm Cprocs).
  { move: Hi. move: Hlen. rewrite /length -/(size _) -/(size _).
    by move=> ->. }
  exists (nth Procedure.main (unzip1 (elementsm Cprocs)) i).
  have HIn := nth_assoc_In (elementsm Cprocs) Procedure.main cd i Hie.
  rewrite Hcdnth in HIn.
  exact: In_elementsm_getm HIn.
Qed.

(* every compiled procedure's labels are pairwise distinct: the entry label
   was generated before the body's counter window opened *)
Lemma compiled_uniq_labels Cx C_procs b P_code :
  getm (genv_procedures G) Cx = Some C_procs ->
  getm C_procs b = Some P_code ->
  uniq (labels_of P_code).
Proof.
  move=> HgC HgB.
  have [P HgP] := genv_block_code_inv _ _ _ _ HgC HgB.
  case HgT: (getm (Intermediate.prog_procedures tp) Cx) => [Cprocs'|];
    last by rewrite HgT /= emptymE in HgP.
  rewrite HgT /= in HgP.
  have HCxdom : Cx \in domm (Intermediate.prog_interface tp).
  { move: HgC. rewrite /G genv_procedures_getm.
    by case: (Cx \in domm (Intermediate.prog_interface tp)). }
  have HCxsrc : Cx \in domm (Source.prog_procedures p).
  { move: HCxdom.
    rewrite (compilation_preserves_interface _ _ Hcompile).
    by rewrite (Source.wfprog_defined_procedures Hwf_p). }
  case/dommP: HCxsrc => CprocsS HgS.
  have [labels [cenv1 [Egen Hcc]]] := compiled_component_labels Hwf_p Hcompile.
  have [plm [lo [Cprocs'' [Hml HCp' [Hbnd Hinj] Hfwd Hrev]]]] := Hcc _ _ HgS.
  have E : Cprocs'' = Cprocs'. { move: HCp'. rewrite HgT. by case. }
  subst Cprocs''.
  case: (Hrev _ _ HgP) => [[_ ->] //
                          |[e0 [s1 [s2 [pl0 [Hge0 Hpl0 Hrun Hlo]]]]]].
  have [_ _ Hu] := compile_proc_labels _ _ _ _ _ _ _ _ _ _ Hrun Hpl0.
  apply: Hu.
  have Hlt := Hbnd _ _ Hpl0. lia.
Qed.

(* the initial renaming touches no scratch block *)
Lemma init_scratch_priv : scratch_priv init_renaming.
Proof.
  by move=> C' b0; rewrite /init_renaming; case: ifP.
Qed.

(* the compiled program's initial scratch and flag cells *)
Lemma initial_scratch_cells C' :
  C' \in domm (Intermediate.prog_interface tp) ->
  Memory.load (Intermediate.prepare_procedures_memory tp) (C', 1, 0%Z)
    = Some Undef
  /\ Memory.load (Intermediate.prepare_procedures_memory tp) (C', 1, 1%Z)
     = Some (Int 0).
Proof.
  move=> HC'.
  have HC'b : C' \in domm (Source.prog_buffers p).
  { move: HC'. rewrite (compilation_preserves_interface _ _ Hcompile).
    by rewrite (Source.wfprog_defined_buffers Hwf_p). }
  case/dommP: HC'b => ib Eb.
  split.
  - rewrite /Memory.load /= prepare_procedures_memory_getm HC'.
    case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
    rewrite (reserve_blocks_load E) ComponentMemory.load_prealloc /=.
    rewrite (compilation_preserves_buffers Hcompile) /gen_buffers mapmE Eb /=.
    by rewrite ?setmE /=.
  - rewrite /Memory.load /= prepare_procedures_memory_getm HC'.
    case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
    rewrite (reserve_blocks_load E) ComponentMemory.load_prealloc /=.
    rewrite (compilation_preserves_buffers Hcompile) /gen_buffers mapmE Eb /=.
    by rewrite ?setmE /=.
Qed.

(* THE bridge: main's compiled dual entry runs from the target's initial
   state, takes the initial (flag = Int 0) fall-through path, sets the flag,
   jumps into the internal prologue, and lands on main's compiled body in a
   state matching the source's initial state. *)
Lemma start_bridge mexpr :
  Source.prog_main p = Some mexpr ->
  immediately_final mexpr = false ->
  exists scrs1 tmemF tregsF pcF gps1 c1 rest1 sA sB fbN prot1 plm1,
    plus CS.step G (CS.initial_machine_state tp) E0
         (gps1, tmemF, tregsF, pcF)
    /\ expr_inv p tp init_renaming scrs1 Component.main [::]
         (Source.prepare_buffers p) Kstop mexpr (Int 0) gps1 tmemF tregsF
         pcF fbN prot1 [::] plm1 c1 rest1 sA sB (4 + stack_need mexpr).
Proof.
  move=> Hmain Hfin.
  (* main's procedure, compiled code, and entry block *)
  move: (Hmain). rewrite /Source.prog_main /Source.find_procedure.
  case HgCm: (getm (Source.prog_procedures p) Component.main)
    => [CprocsM|] //= HgPm.
  case: (compile_prog_procedures_spec Hwf_p Hcompile)
    => [labels [cenv1 [Egen HSPEC]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  case: (HSPEC _ _ _ _ HgCm HgPm)
    => [plmf [CprocsT [cd [s1 [s2 [Hplmf HgT HgTP Hcp]]]]]].
  have Hdom : Component.main \in domm (Intermediate.prog_interface tp).
  { rewrite (compilation_preserves_interface _ _ Hcompile).
    apply/(proj2 (Source.wfprog_main_existence Hwf_p)).
    by rewrite Hmain. }
  case: (compiled_code_anchor _ _ _ _ _ Hdom HgT HgTP)
    => [bE [CprocsB [HgB HgBE Hentrypt Hother]]].
  have Hmaintp : Intermediate.prog_main tp = true.
  { by rewrite (compilation_preserves_main_flag _ _ Hcompile) Hmain. }
  have [CI HgCI] : exists CI,
      getm (Intermediate.prog_interface tp) Component.main = Some CI.
  { by case/dommP: Hdom => CI HCI; exists CI. }
  have HEP : EntryPoint.get Component.main Procedure.main
               (genv_entrypoints G) = Some bE.
  { apply: (Hentrypt CI HgCI).
    apply/orP; right.
    by rewrite Hmaintp !PeanoNat.Nat.eqb_refl. }
  (* the initial state, unfolded *)
  have Einit : CS.initial_machine_state tp
    = ([::], Intermediate.prepare_procedures_memory tp, Register.init,
       (Component.main, bE, 0%Z)).
  { rewrite /CS.initial_machine_state Hmaintp.
    move: HEP.
    rewrite /G /prepare_global_env /Intermediate.prepare_procedures_memory.
    case: (Intermediate.prepare_procedures_initial_memory tp)
      => [[mem procs] eps] /=.
    by move=> ->. }
  rewrite Einit.
  (* the entry shape *)
  have [plf Hplf] : exists plf, getm plmf Procedure.main = Some plf.
  { move: Hcp.
    rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
    case: (getm plmf Procedure.main) => [x|] //=. by exists x. }
  have Hguard : Component.eqb Component.main Component.main
                && Procedure.eqb Procedure.main Procedure.main = true.
  { by rewrite /Component.eqb /Procedure.eqb !PeanoNat.Nat.eqb_refl. }
  case: (compile_proc_shape_main _ _ _ _ _ _ _ _ Hcp Hplf Hguard Hfin)
    => [lm [lr [bodyc0 [sA0 [sB0 [Ebody0 Ecd]]]]]].
  have HcE0 : code_at G (Component.main, bE, 0%Z) cd.
  { exists CprocsB, cd, [::], [::]. split=> //. by rewrite cats0. }
  rewrite Ecd in HcE0.
  (* the memory relation and the initial cells *)
  have Hmem0 := initial_mem_inject _ _ Hwf_p Hcompile.
  have [HwfM0 Hflag0] := initial_scratch_cells _ Hdom.
  (* the shared 8-instruction entry: IConst R_ONE, frame alloc, two pushes *)
  have F1 := step_const G [::] (Intermediate.prepare_procedures_memory tp)
               Register.init _ (IInt 1) R_ONE _ HcE0.
  set regsG1 := Register.set R_ONE (Int 1) Register.init in F1.
  have Hd1 := code_at_tail HcE0.
  have F2 := step_mov G [::] (Intermediate.prepare_procedures_memory tp)
               regsG1 _ R_SP R_AUX1 _ Hd1.
  set regsG2 := Register.set R_AUX1 (Register.get R_SP regsG1) regsG1 in F2.
  have Hd2 := code_at_tail Hd1.
  have F3 := step_const G [::] (Intermediate.prepare_procedures_memory tp)
               regsG2 _ (IInt (Z.of_nat (4 + stack_need mexpr))) R_SP _ Hd2.
  set regsG3 := Register.set R_SP
                  (Int (Z.of_nat (4 + stack_need mexpr))) regsG2 in F3.
  have Hd3 := code_at_tail Hd2.
  have [cmf Hcmf] : exists cm,
      getm (Intermediate.prepare_procedures_memory tp) Component.main
      = Some cm.
  { move: HwfM0. rewrite /Memory.load /=.
    case: (getm (Intermediate.prepare_procedures_memory tp) Component.main)
      => // cm _. by exists cm. }
  have [tmemD [ptrE HallocE]] : exists tmemD ptrE,
      Memory.alloc (Intermediate.prepare_procedures_memory tp) Component.main
        (Z.to_nat (Z.of_nat (4 + stack_need mexpr)))
      = Some (tmemD, ptrE).
  { rewrite /Memory.alloc Hcmf.
    case: (ComponentMemory.alloc cmf _) => cm' b. by do 2 eexists. }
  case: (alloc_outside_inject Hmem0 HallocE)
    => [HmemD EcompE EoffE HavoidE].
  set fbE := Pointer.block ptrE.
  have EptrE : ptrE = (Component.main, fbE, 0%Z).
  { rewrite /fbE. case: (ptrE) EcompE EoffE => [[pC pB] pO] /= EC EO.
    by rewrite EC EO. }
  have HfreshE : forall (o : Z) w,
      Memory.load (Intermediate.prepare_procedures_memory tp)
        (Component.main, fbE, o) = Some w -> False.
  { exact: memory_alloc_fresh (mi_wf_t _ _ _ Hmem0) HallocE. }
  have HfbE1 : fbE <> 1.
  { move=> E. rewrite E in HfreshE. exact: HfreshE HwfM0. }
  have HgSP3 : Register.get R_SP regsG3
               = Int (Z.of_nat (4 + stack_need mexpr))
    by rewrite /regsG3 /Register.get /Register.set setmE /=.
  have F4 : CS.step G ([::], Intermediate.prepare_procedures_memory tp,
              regsG3,
              Pointer.inc (Pointer.inc (Pointer.inc
                (Component.main, bE, 0%Z)))) E0
            ([::], tmemD, Register.set R_SP (Ptr ptrE) regsG3,
             Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc
               (Component.main, bE, 0%Z))))).
  { apply: step_alloc Hd3 HgSP3 _ _.
    - lia.
    - rewrite /=. exact: HallocE. }
  set regsG4 := Register.set R_SP (Ptr ptrE) regsG3 in F4.
  have Hd4 := code_at_tail Hd3.
  have HldE : forall o : Z,
      (0 <= o < Z.of_nat (4 + stack_need mexpr))%Z ->
      Memory.load tmemD (Component.main, fbE, o) = Some Undef.
  { move=> o Ho. apply: memory_load_after_alloc_in HallocE _.
    rewrite Nat2Z.id. exact: Ho. }
  have [tmemE1 HstE1] := Memory.store_after_load _ _ _
      (Register.get R_AUX1 regsG4) (HldE 0%Z (ltac:(lia))).
  have HSPG4 : Register.get R_SP regsG4 = Ptr (Component.main, fbE, 0%Z)
    by rewrite /regsG4 EptrE /Register.get /Register.set setmE /=.
  have HONEG4 : Register.get R_ONE regsG4 = Int 1
    by rewrite /regsG4 /regsG3 /regsG2 /regsG1 /Register.get
               /Register.set !setmE /=.
  have F56 := exec_push _ [::] tmemD regsG4 _ R_AUX1
                _ _ _ _ tmemE1 Hd4 HSPG4 HONEG4 (ltac:(by [])) HstE1.
  set regsG5 := Register.set R_SP (Ptr (Component.main, fbE, (0 + 1)%Z))
                  regsG4 in F56.
  have Hd6 := code_at_tail (code_at_tail Hd4).
  (* load_arg scr R_AUX1 : the wrapper saves the inherited scratch (Undef at
     the initial state) *)
  have HwE1 : Memory.load tmemE1 (Component.main, 1, 0%Z) = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; exact: HfbE1.
    have Hpair : (Component.main, 1) <> (Component.main, Pointer.block ptrE)
                 :> (Component.id * Block.id).
    { case=> E2. exact: (HfbE1 (esym E2)). }
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
    exact: HwfM0. }
  have F67 := exec_load_arg _ [::] tmemE1 regsG5 _
                (scr Component.main) R_AUX1 _ _ Hd6 (ltac:(by [])) HwE1.
  set regsG5b := Register.set R_AUX1 Undef
                   (Register.set R_AUX1 (Ptr (scr Component.main)) regsG5)
    in F67.
  have Hd6b := code_at_tail (code_at_tail Hd6).
  (* push R_AUX1 : slot 1 := the inherited scratch *)
  have HldE1 : Memory.load tmemE1 (Component.main, fbE, (0 + 1)%Z)
               = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE.
    apply: HldE. lia. }
  have [tmemE1b HstE1b] := Memory.store_after_load _ _ _
      (Register.get R_AUX1 regsG5b) HldE1.
  have HSPG5b : Register.get R_SP regsG5b
                = Ptr (Component.main, fbE, (0 + 1)%Z)
    by rewrite /regsG5b /regsG5 /Register.get /Register.set !setmE /=.
  have HONEG5b : Register.get R_ONE regsG5b = Int 1
    by rewrite /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
               /Register.get /Register.set !setmE /=.
  have F67b := exec_push _ [::] tmemE1 regsG5b _ R_AUX1
                 _ _ _ _ tmemE1b Hd6b HSPG5b HONEG5b (ltac:(by [])) HstE1b.
  set regsG5c := Register.set R_SP (Ptr (Component.main, fbE, (0 + 1 + 1)%Z))
                   regsG5b in F67b.
  have Hd6c := code_at_tail (code_at_tail Hd6b).
  (* push R_RA : slot 2 *)
  have HldE2ra : Memory.load tmemE1b (Component.main, fbE, (0 + 1 + 1)%Z)
                 = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE; lia.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; lia.
    apply: HldE. lia. }
  have [tmemE2 HstE2] := Memory.store_after_load _ _ _
      (Register.get R_RA regsG5c) HldE2ra.
  have HSPG5 : Register.get R_SP regsG5c
               = Ptr (Component.main, fbE, (0 + 1 + 1)%Z)
    by rewrite /regsG5c /Register.get /Register.set setmE /=.
  have HONEG5 : Register.get R_ONE regsG5c = Int 1
    by rewrite /regsG5c /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
               /Register.get /Register.set !setmE /=.
  have F78 := exec_push _ [::] tmemE1b regsG5c _ R_RA
                _ _ _ _ tmemE2 Hd6c HSPG5 HONEG5 (ltac:(by [])) HstE2.
  set regsG6 := Register.set R_SP
                  (Ptr (Component.main, fbE, (0 + 1 + 1 + 1)%Z))
                  regsG5c in F78.
  have Hd8 := code_at_tail (code_at_tail Hd6c).
  (* the flag test: IConst flag-ptr; ILoad (Int 0); push the marker *)
  have M9 := step_const G [::] tmemE2 regsG6 _
               (IPtr (flag_buf_ptr (scr Component.main))) R_AUX1 _ Hd8.
  set regsM9 := Register.set R_AUX1
                  (Ptr (flag_buf_ptr (scr Component.main))) regsG6 in M9.
  have Hd9 := code_at_tail Hd8.
  have HflagE2 : Memory.load tmemE2 (Component.main, 1, (0 + 1)%Z)
                 = Some (Int 0).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; apply: HfbE1.
    have Hpair : (Component.main, 1) <> (Component.main, Pointer.block ptrE)
                 :> (Component.id * Block.id).
    { case=> E2. exact: (HfbE1 (esym E2)). }
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
    exact: Hflag0. }
  have HA1M9 : Register.get R_AUX1 regsM9
               = Ptr (flag_buf_ptr (scr Component.main))
    by rewrite /regsM9 /Register.get /Register.set setmE /=.
  have HldFl : Memory.load tmemE2 (flag_buf_ptr (scr Component.main))
               = Some (Int 0).
  { exact: HflagE2. }
  have M10 := step_load G [::] tmemE2 regsM9 _ R_AUX1 R_AUX2 _ _ _
                Hd9 HA1M9 (ltac:(by [])) HldFl.
  set regsM10 := Register.set R_AUX2 (Int 0) regsM9 in M10.
  have Hd10 := code_at_tail Hd9.
  have HldE2 : Memory.load tmemE2 (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
               = Some Undef.
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE; lia.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE; lia.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; lia.
    apply: HldE. lia. }
  have [tmemE3 HstE3] := Memory.store_after_load _ _ _
      (Register.get R_AUX2 regsM10) HldE2.
  have HSPM10 : Register.get R_SP regsM10
                = Ptr (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
    by rewrite /regsM10 /regsM9 /regsG6 /Register.get /Register.set
               !setmE /=.
  have HONEM10 : Register.get R_ONE regsM10 = Int 1
    by rewrite /regsM10 /regsM9 /regsG6 /regsG5c /regsG5b /regsG5 /regsG4
               /regsG3 /regsG2 /regsG1 /Register.get /Register.set !setmE /=.
  have M1112 := exec_push _ [::] tmemE2 regsM10 _ R_AUX2 _ _ _ _ tmemE3
                  Hd10 HSPM10 HONEM10 (ltac:(by [])) HstE3.
  set regsM12 := Register.set R_SP
                   (Ptr (Component.main, fbE, (0 + 1 + 1 + 1 + 1)%Z)) regsM10
    in M1112.
  have Hd12 := code_at_tail (code_at_tail Hd10).
  (* the UNtaken IBnz: this is the initial run, the flag was Int 0 *)
  have HA2M12 : Register.get R_AUX2 regsM12 = Int 0
    by rewrite /regsM12 /regsM10 /Register.get /Register.set !setmE /=.
  have M13 := step_bnz_z G [::] tmemE3 regsM12 _ R_AUX2 lm _ Hd12 HA2M12.
  have Hd13 := code_at_tail Hd12.
  (* main's initial argument *)
  have M14 := step_const G [::] tmemE3 regsM12 _ (IInt 0) R_COM _ Hd13.
  set regsM14 := Register.set R_COM (Int 0) regsM12 in M14.
  have Hd14 := code_at_tail Hd13.
  have M15 := step_label G [::] tmemE3 regsM14 _ lm _ Hd14.
  have Hd15 := code_at_tail Hd14.
  have M16 := step_const G [::] tmemE3 regsM14 _ (IInt 1) R_AUX2 _ Hd15.
  set regsM16 := Register.set R_AUX2 (Int 1) regsM14 in M16.
  have Hd16 := code_at_tail Hd15.
  (* flag := Int 1 *)
  have HflagE3 : Memory.load tmemE3 (Component.main, 1, (0 + 1)%Z)
                 = Some (Int 0).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE; apply: HfbE1.
    exact: HflagE2. }
  have [tmemE4 HstE4] := Memory.store_after_load _ _ _
      (Register.get R_AUX2 regsM16) HflagE3.
  have HgA1M16 : Register.get R_AUX1 regsM16
                 = Ptr (flag_buf_ptr (scr Component.main))
    by rewrite /regsM16 /regsM14 /regsM12 /regsM10 /regsM9 /Register.get
               /Register.set !setmE /=.
  have HstE4' : Memory.store tmemE3 (flag_buf_ptr (scr Component.main))
                  (Register.get R_AUX2 regsM16) = Some tmemE4.
  { exact: HstE4. }
  have M17 := step_store G [::] tmemE3 regsM16 _ R_AUX1 R_AUX2 _
                (flag_buf_ptr (scr Component.main)) tmemE4
                Hd16 HgA1M16 (ltac:(by [])) HstE4'.
  have Hd17 := code_at_tail Hd16.
  (* IJal to the internal entry *)
  case: (compiled_jal_resolution Hwf_p Hcompile)
    => [labels2 [cenv2 [Egen2 HRES]]].
  move: Egen2. rewrite Egen. case=> E1' E2'. subst labels2 cenv2.
  have HRES' := HRES _ _ _ _ _ _ HgCm HgPm Hplmf Hplf Hdom.
  case: (HRES' (iter 21 Pointer.inc (Component.main, bE, 0%Z))
           (ltac:(by [])))
    => [bPJ [cdJ [extJ [restJ [CprocsBJ [HgBJ HgCdJ HdecJ HexJ HflJ]]]]]].
  case: HexJ => [s1J [s2J HcpJ]].
  have MJ : CS.step G ([::], tmemE4, regsM16,
              iter 21 Pointer.inc (Component.main, bE, 0%Z)) E0
            ([:: iter 22 Pointer.inc (Component.main, bE, 0%Z)], tmemE4,
             Register.set R_RA Undef regsM16,
             (Component.main, bPJ, Z.of_nat (size extJ))).
  { apply: step_jal _ HflJ. exact: Hd17. }
  set regsM17 := Register.set R_RA Undef regsM16 in MJ.
  set jal_ret := iter 22 Pointer.inc (Component.main, bE, 0%Z) in MJ.
  have Hjrc : code_at G jal_ret
      (pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
       store_arg (scr Component.main) R_AUX1 R_AUX2 ++ pop R_SP ++
       [:: IBnz R_ARG lr; IHalt; ILabel lr; IReturn]).
  { apply: (code_at_app_l (c2 := ILabel plf ::
      ([:: IMov R_SP R_AUX1;
           IConst (IInt (Z.of_nat (4 + stack_need mexpr))) R_SP;
           IAlloc R_SP R_SP] ++
       push R_AUX1 ++
       push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc0 ++
       (pop R_ARG ++ pop R_SP ++ [:: IJump])))).
    move: (code_at_tail Hd17).
    rewrite /jal_ret.
    by do 12!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
  (* the landing and the internal prologue *)
  have Huq := compiled_uniq_labels _ _ _ _ HgBJ HgCdJ.
  case: (compile_proc_after_label _ _ _ _ _ _ _ _ _ _ HcpJ Hplf HdecJ Huq)
    => [bodycJ [sAJ [sBJ [EbodyJ ErestJ]]]].
  subst restJ.
  have HcLand : code_at G (Component.main, bPJ, Z.of_nat (size extJ))
      (ILabel plf ::
         ([:: IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need mexpr))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++
          push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodycJ ++
          (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
  { exists CprocsBJ, cdJ, extJ, [::]. split=> //.
    rewrite HdecJ. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0. }
  have HONEM17 : Register.get R_ONE regsM17 = Int 1
    by rewrite /regsM17 /regsM16 /regsM14 /regsM12 /regsM10 /regsM9 /regsG6
               /regsG5c /regsG5b /regsG5 /regsG4 /regsG3 /regsG2 /regsG1
               /Register.get /Register.set !setmE /=.
  have HwfE4 : exists w,
      Memory.load tmemE4 (Component.main, 1, 0%Z) = Some w.
  { exists Undef.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; inversion EE.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; apply: HfbE1.
    have Hpair : (Component.main, 1)
                 <> (Component.main, Pointer.block ptrE)
                 :> (Component.id * Block.id).
    { case=> E2. exact: (HfbE1 (esym E2)). }
    rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE Hpair).
    exact: HwfM0. }
  have HmemE4 : mem_inject init_renaming (Source.prepare_buffers p) tmemE4.
  { have HmemE1 : mem_inject init_renaming (Source.prepare_buffers p) tmemE1.
    { apply: store_outside_inject HmemD _ HstE1.
      move=> b0 /=. exact: HavoidE. }
    have HmemE1b : mem_inject init_renaming (Source.prepare_buffers p)
                     tmemE1b.
    { apply: store_outside_inject HmemE1 _ HstE1b.
      move=> b0 /=. exact: HavoidE. }
    have HmemE2' : mem_inject init_renaming (Source.prepare_buffers p)
                     tmemE2.
    { apply: store_outside_inject HmemE1b _ HstE2.
      move=> b0 /=. exact: HavoidE. }
    have HmemE3 : mem_inject init_renaming (Source.prepare_buffers p) tmemE3.
    { apply: store_outside_inject HmemE2' _ HstE3.
      move=> b0 /=. exact: HavoidE. }
    apply: store_outside_inject HmemE3 _ HstE4.
    move=> b0 /=. exact: init_scratch_priv. }
  case: (internal_prologue_run Component.main [:: jal_ret] tmemE4 regsM17
           (Component.main, bPJ, Z.of_nat (size extJ)) plf
           (stack_need mexpr) bodycJ _ init_renaming
           (Source.prepare_buffers p) HcLand (ltac:(by []))
           HONEM17 HmemE4 HwfE4)
    => [tmemF [regsF [fbN [pcF [wscr
         [Sprol [HmemF Hwscr HfreshN HavoidN HfbN1]
           [Hslot0 Hslot1 LtrN]
           [RONEF RSPF RARGF RCOMF] [HpcF HcF HcapN Hsmtr]]]]]]].
  (* register values entering the prologue *)
  have HgSP17 : Register.get R_SP regsM17
                = Ptr (Component.main, fbE, (0 + 1 + 1 + 1 + 1)%Z)
    by rewrite /regsM17 /regsM16 /regsM14 /regsM12 /Register.get
               /Register.set !setmE /=.
  have HgCOM17 : Register.get R_COM regsM17 = Int 0
    by rewrite /regsM17 /regsM16 /regsM14 /Register.get /Register.set
               !setmE /=.
  (* the EF-frame slots survive into tmemF: caller R_SP, the INHERITED
     SCRATCH, R_RA, and the context marker *)
  have HldEF0 : Memory.load tmemE4 (Component.main, fbE, 0%Z)
                = Some (Register.get R_AUX1 regsG4).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE.
    exact: Memory.load_after_store_eq HstE1. }
  have HldEF1 : Memory.load tmemE4 (Component.main, fbE, (0 + 1)%Z)
                = Some (Register.get R_AUX1 regsG5b).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE; lia.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE; lia.
    exact: Memory.load_after_store_eq HstE1b. }
  have HldEF2 : Memory.load tmemE4 (Component.main, fbE, (0 + 1 + 1)%Z)
                = Some (Register.get R_RA regsG5c).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; inversion EE; apply: HfbE1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE; lia.
    exact: Memory.load_after_store_eq HstE2. }
  have HldEF3 : Memory.load tmemE4 (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
                = Some (Int 0).
  { rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; inversion EE; apply: HfbE1.
    have -> : (Int 0) = Register.get R_AUX2 regsM10
      by rewrite /regsM10 /Register.get /Register.set setmE /=.
    exact: Memory.load_after_store_eq HstE3. }
  have HnefbEN : fbE <> fbN.
  { move=> E. apply: (HfreshN 0%Z (Register.get R_AUX1 regsG4)).
    by rewrite -E. }
  have HpairEN : (Component.main, fbE) <> (Component.main, fbN)
                 :> (Component.id * Block.id).
  { case=> E2. exact: (HnefbEN E2). }
  have HldF0 : Memory.load tmemF (Component.main, fbE, 0%Z)
               = Some (Register.get R_AUX1 regsG4).
  { exact: LtrN HldEF0 HpairEN. }
  have HldF1 : Memory.load tmemF (Component.main, fbE, (0 + 1)%Z)
               = Some (Register.get R_AUX1 regsG5b).
  { exact: LtrN HldEF1 HpairEN. }
  have HldF2 : Memory.load tmemF (Component.main, fbE, (0 + 1 + 1)%Z)
               = Some (Register.get R_RA regsG5c).
  { exact: LtrN HldEF2 HpairEN. }
  have HldF3 : Memory.load tmemF (Component.main, fbE, (0 + 1 + 1 + 1)%Z)
               = Some (Int 0).
  { exact: LtrN HldEF3 HpairEN. }
  (* transport of untouched initial cells to tmemF *)
  have LtrEF : forall C1 b1 (o : Z) w,
      Memory.load (Intermediate.prepare_procedures_memory tp) (C1, b1, o)
        = Some w ->
      (C1, b1) <> (Component.main, fbE) :> (Component.id * Block.id) ->
      (C1, b1) <> (Component.main, fbN) :> (Component.id * Block.id) ->
      (C1, b1, o) <> (Component.main, 1, (0 + 1)%Z) :> Pointer.t ->
      Memory.load tmemF (C1, b1, o) = Some w.
  { move=> C1 b1 o w Hl HneE HneN Hnefl.
    apply: LtrN _ HneN.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE4);
      last by move=> EE; rewrite EE in Hnefl; case: (Hnefl erefl).
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE3);
      last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE2);
      last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1b);
      last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ HstE1);
      last by move=> EE; inversion EE; case: HneE; rewrite -H0 -H1.
    by rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ HallocE HneE). }
  have HldFlag : Memory.load tmemF (Component.main, 1, 1%Z) = Some (Int 1).
  { have HgA2M16 : Register.get R_AUX2 regsM16 = Int 1
      by rewrite /regsM16 /Register.get /Register.set setmE /=.
    have Hne : (Component.main, 1) <> (Component.main, fbN)
               :> (Component.id * Block.id).
    { case=> E2. exact: (HfbN1 (esym E2)). }
    apply: LtrN _ Hne.
    have -> : (Int 1) = Register.get R_AUX2 regsM16 by rewrite HgA2M16.
    exact: Memory.load_after_store_eq HstE4. }
  (* the assembled run *)
  have Hplus : plus CS.step G
      ([::], Intermediate.prepare_procedures_memory tp, Register.init,
       (Component.main, bE, 0%Z)) E0
      ([:: jal_ret], tmemF, regsF, pcF).
  { eapply plus_star_trans; [exact: plus_one F1 | | by []].
    eapply star_trans; [exact: star_one F2 | | by []].
    eapply star_trans; [exact: star_one F3 | | by []].
    eapply star_trans; [exact: star_one F4 | | by []].
    eapply star_trans; [exact: F56 | | by []].
    eapply star_trans; [exact: F67 | | by []].
    eapply star_trans; [exact: F67b | | by []].
    eapply star_trans; [exact: F78 | | by []].
    eapply star_trans; [exact: star_one M9 | | by []].
    eapply star_trans; [exact: star_one M10 | | by []].
    eapply star_trans; [exact: M1112 | | by []].
    eapply star_trans; [exact: star_one M13 | | by []].
    eapply star_trans; [exact: star_one M14 | | by []].
    eapply star_trans; [exact: star_one M15 | | by []].
    eapply star_trans; [exact: star_one M16 | | by []].
    eapply star_trans; [exact: star_one M17 | | by []].
    eapply star_trans; [exact: star_one MJ | exact: Sprol | by []]. }
  exists emptym, tmemF, regsF, pcF, [:: jal_ret], bodycJ,
         (pop R_ARG ++ pop R_SP ++ [:: IJump]), sAJ, sBJ, fbN,
         [:: (Component.main, fbE)], plmf.
  split; first exact: Hplus.
  split.
  + by rewrite Elab.
  + exact: Hdom.
  + exact: HmemF.
  + by move=> C' v0'; rewrite emptymE.
  + exact: HldFlag.
  + move=> C' HC'dom.
    have [Hu0 _] := initial_scratch_cells _ HC'dom.
    exists Undef.
    apply: LtrEF Hu0 _ _ _.
    * by move=> [_ E2]; apply: (HfbE1 (esym E2)).
    * by move=> [_ E2]; apply: (HfbN1 (esym E2)).
    * by move=> EE; inversion EE.
  + exact: RONEF.
  + by rewrite RSPF.
  + rewrite RARGF HgCOM17. exact: VI_int.
  + exact: HpcF.
  + exact: EbodyJ.
  + exact: HcF.
  + apply: CMJ_base. exact: CM_stop.
  + exact: compiled_uniq_labels.
  + split; [exact: HfbN1 | exact: HavoidN].
  + exact: init_scratch_priv.
  + by [].
  + exact: HcapN.
  + rewrite /=. lia.
  + rewrite inE. apply/eqP. case=> E. exact: (HnefbEN (esym E)).
  + apply: (SM_init _ _ _ _ emptym fbN fbE jal_ret lr
              (Register.get R_AUX1 regsG4) (Register.get R_AUX1 regsG5b)
              (Register.get R_RA regsG5c) (Register.get R_ARG regsM17)).
    * by rewrite Hslot0 HgSP17.
    * exact: Hslot1.
    * exact: HldF0.
    * exact: HldF1.
    * exact: HldF2.
    * exact: HldF3.
    * split; [exact: HfbE1 | exact: HavoidE].
    * by [].
    * exact: Hjrc.
    * by move=> E; apply: HnefbEN; rewrite E.
  + by move=> m0; rewrite Hmain; case=> <-.
Qed.

(* ==================== master-diagram plumbing ==================== *)

(* deciding finality of a (cont, stack) pair *)
Lemma nofin_dec (k : cont) (stk : S.CS.stack) :
  (k = Kstop /\ stk = [::]) \/ (k = Kstop -> stk <> [::]).
Proof.
  case: k; try by right.
  case: stk; [by left | by move=> f s; right].
Qed.

Lemma exprval_dec (e : expr) :
  (exists v0, e = E_val v0) \/ (forall v0, e <> E_val v0).
Proof.
  case: e; try by right.
  move=> v0. left. by exists v0.
Qed.

(* immediately-final expressions never step at (Kstop, [::]) *)
Lemma final_expr_nostep GS0 C mem e arg t s' :
  immediately_final e = true ->
  S.CS.kstep GS0 (S.CS.State C [::] mem Kstop e arg) t s' -> False.
Proof.
  case: e => //= => [v|] _ Hstep; by inversion Hstep.
Qed.

(* a matched final value state drains onto main's IHalt *)
Lemma val_inv_final_drain α scrs C mem v arg gps tmem tregs pc fb prot temps
      plm rest cap :
  val_inv p tp α scrs C [::] mem Kstop v arg gps tmem tregs pc fb prot temps
          plm rest cap ->
  exists tmem1 tregs1 pcH,
    [/\ star CS.step G (gps, tmem, tregs, pc) E0 ([::], tmem1, tregs1, pcH),
        executing G pcH IHalt
      & mem_inject α mem tmem1].
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hcom Hpc Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf.
  case: (cont_matchJ_drain _ _ _ _ _ _ _ Hcont Hcode Hpc Huniq gps tmem tregs
           HONE) => [pc' [rest1 [Sd _ Hc' [Ec _] Hcm']]].
  case: (final_drain α scrs C mem gps tmem tregs pc' fb prot temps plm rest1
           Hmem Hscrp Hpriv Hall Hdom HONE HSP Ec Hc' Hcm' Hstack)
    => [tmem1 [tregs1 [pcH [Sf Hh Hm1]]]].
  exists tmem1, tregs1, pcH.
  split=> //.
  eapply star_trans; [exact: Sd | exact: Sf | by []].
Qed.

(* re-anchoring an expression invariant after a zero-step administrative
   descend: everything survives except the compiled fragment, the code
   anchor, the continuation and the budget *)
Lemma expr_inv_replumb {α scrs C stk mem k k' e e' arg gps tmem tregs pc fb
      prot temps plm c rest sA sB cap c' rest' sA' sB'} :
  expr_inv p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm
           c rest sA sB cap ->
  compile_expr C (lbp C) (scr C) plm e' sA' = Some (c', sB') ->
  code_at G pc (c' ++ rest') ->
  cont_matchJ α C plm k' rest' temps ->
  3 + maxn (size temps + stack_need e') (kneed k' (size temps)) <= cap ->
  expr_inv p tp α scrs C stk mem k' e' arg gps tmem tregs pc fb prot temps
           plm c' rest' sA' sB' cap.
Proof.
  case=> Hplm Hdom Hmem Hscrs Hflag Hall HONE HSP HARG Hpc Hcomp Hcode Hcont
         Huniq Hpriv Hscrp Htemps Hcap Hbud Hprot Hstack Hmnf
         Hcomp' Hcode' Hcont' Hbud'.
  by split.
Qed.

(* packaging a result state: either it is final (drain onto IHalt) or it
   matches in place *)
Lemma expr_pack α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm
      c rest sA sB cap :
  expr_inv p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm
           c rest sA sB cap ->
  (exists ts', plus CS.step G (gps, tmem, tregs, pc) E0 ts'
               /\ match_states p tp (S.CS.State C stk mem k e arg) ts')
  \/ match_states p tp (S.CS.State C stk mem k e arg) (gps, tmem, tregs, pc).
Proof.
  move=> He.
  case: (exprval_dec e) => [[v0 Ev0] | Hnev]; last first.
  { right. apply: MS_expr; [exact: He | by move=> v1 /Hnev]. }
  subst e.
  case: (nofin_dec k stk) => [[Ek Estk] | Hnf']; last first.
  { right. apply: MS_expr; [exact: He | by move=> v1 _; exact: Hnf']. }
  subst k stk.
  left.
  case/leaf_val_run: (He) => [i [Ev S0 Hc0]].
  subst v0.
  have Hval2 : val_inv p tp α scrs C [::] mem Kstop (Int i) arg gps tmem
                 (Register.set R_COM (Int i) tregs) (Pointer.inc pc) fb prot
                 temps plm rest cap.
  { apply: expr_to_val (He) _ _ _ _ _ _ _.
    - by rewrite register_get_set_neq.
    - by rewrite register_get_set_neq.
    - by rewrite register_get_set_neq.
    - rewrite register_get_set_eq. exact: VI_int.
    - rewrite Pointer.inc_preserves_component. exact: ei_pc He.
    - by rewrite Pointer.inc_preserves_block.
    - exact: Hc0. }
  case: (val_inv_final_drain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval2)
    => [tmem1 [tregs1 [pcH [Sf Hh Hm1]]]].
  exists ([::], tmem1, tregs1, pcH).
  split.
  - eapply plus_left; [exact: S0 | exact: Sf | by []].
  - apply: MS_halted Hm1 Hh.
Qed.

Lemma val_pack α scrs C stk mem k v arg gps tmem tregs pc fb prot temps plm
      rest cap :
  val_inv p tp α scrs C stk mem k v arg gps tmem tregs pc fb prot temps plm
          rest cap ->
  exists ts', star CS.step G (gps, tmem, tregs, pc) E0 ts'
              /\ match_states p tp (S.CS.State C stk mem k (E_val v) arg) ts'.
Proof.
  move=> Hv.
  case: (nofin_dec k stk) => [[Ek Estk] | Hnf']; last first.
  { exists (gps, tmem, tregs, pc). split; first exact: star_refl.
    apply: MS_val; [exact: Hv | exact: Hnf']. }
  subst k stk.
  case: (val_inv_final_drain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv)
    => [tmem1 [tregs1 [pcH [Sf Hh Hm1]]]].
  exists ([::], tmem1, tregs1, pcH).
  split; first exact: Sf.
  apply: MS_halted Hm1 Hh.
Qed.

(* the value-consuming dispatcher: a source step out of a value state *)
Lemma val_consume {α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
      plm rest cap t s1'} :
  S.CS.kstep (Source.GlobalEnv.prepare_global_env p)
    (S.CS.State C stk mem k (E_val v) arg) t s1' ->
  val_inv p tp α scrs C stk mem k v arg gps tmem tregs pc fb prot temps plm
          rest cap ->
  (exists ts', plus CS.step G (gps, tmem, tregs, pc) t ts'
               /\ match_states p tp s1' ts')
  \/ [/\ measure s1' < measure (S.CS.State C stk mem k (E_val v) arg),
         t = E0
       & match_states p tp s1' (gps, tmem, tregs, pc)].
Proof.
  move=> Hstep Hval.
  inversion Hstep; subst.
  - (* KS_Binop2 *)
    case/diagram_binop2: Hval
      => [pcF [tmem' [cd [rest' [sAx [sBx [Hp He2]]]]]]].
    left.
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hp | exact: P2 | by []].
    + eexists. split; [exact: Hp | exact: Hm2].
  - (* KS_BinopEval *)
    case/diagram_binop_eval: Hval
      => [tregs' [pcF [rest' [temps' [Hp Hv2]]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by []].
  - (* KS_Seq2 *)
    case/diagram_seq2: Hval => [pc' [c2 [rest' [sAx [sBx [Sd Hor He2]]]]]].
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + left. exists ts'. split; last exact: Hm2.
      eapply star_plus_trans; [exact: Sd | exact: P2 | by []].
    + case: Hor => [Epc | Hpl].
      * right. split.
        -- by rewrite /measure /=; lia.
        -- by [].
        -- by rewrite -Epc.
      * left. eexists. split; [exact: Hpl | exact: Hm2].
  - (* KS_If2 *)
    case/diagram_if2: Hval => [pcF [cd [rest' [sAx [sBx [Hp He2]]]]]].
    left.
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hp | exact: P2 | by []].
    + eexists. split; [exact: Hp | exact: Hm2].
  - (* KS_AllocEval *)
    case: (diagram_alloc_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval
             (ltac:(eassumption)) (ltac:(eassumption)))
      => [α' [tmem' [tregs' [pcF [rest' [Hp Hv2]]]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by []].
  - (* KS_DerefEval *)
    case: (diagram_deref_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval (ltac:(eassumption)))
      => [tregs' [pcF [rest' [Hp Hv2]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by []].
  - (* KS_Assign2 *)
    case/diagram_assign2: Hval
      => [pcF [tmem' [cd [rest' [sAx [sBx [Hp He2]]]]]]].
    left.
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hp | exact: P2 | by []].
    + eexists. split; [exact: Hp | exact: Hm2].
  - (* KS_AssignEval *)
    case: (diagram_assign_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval (ltac:(eassumption)))
      => [tmem2 [tregs' [pcF [rest' [temps' [Hp Hv2]]]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by []].
  - (* KS_InternalCall *)
    case: (diagram_call_int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval (ltac:(eassumption)))
      => [tmem5 [tregs5 [pcF [gps1 [c1 [rest1 [sAx [sBx [fbN [Hp
          He2]]]]]]]]]].
    left.
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hp | exact: P2 | by []].
    + eexists. split; [exact: Hp | exact: Hm2].
  - (* KS_ExternalCall *)
    case: (diagram_call_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval (ltac:(eassumption))
             (ltac:(eassumption)) (ltac:(eassumption)))
      => [scrs1 [tmem9 [tregs9 [pcF [gps1 [c1 [rest1 [sAx [sBx [fbN
          [prot1 [plm1 [Hp He2]]]]]]]]]]]]].
    left.
    case/expr_pack: He2 => [[ts' [P2 Hm2]] | Hm2].
    + exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hp | exact: P2 | by rewrite E0_right].
    + eexists. split; [exact: Hp | exact: Hm2].
  - (* KS_InternalReturn *)
    case/diagram_return_int: Hval
      => [scrs1 [tmem1 [tregs1 [pcF [gps' [rest' [temps' [fb' [prot' [cap'
          [Hp Hv2]]]]]]]]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by []].
  - (* KS_ExternalReturn *)
    case: (diagram_return_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hval (ltac:(eassumption)))
      => [scrs1 [tmem1 [tregs1 [pcF [gps1 [rest1 [temps1 [fb1 [prot1
          [cap1 [plm1 [Hp Hv2]]]]]]]]]]]].
    left.
    case/val_pack: Hv2 => [ts' [Sp Hm2]].
    exists ts'. split; last exact: Hm2.
    eapply plus_star_trans; [exact: Hp | exact: Sp | by rewrite E0_right].
Qed.

(* the expression dispatcher: a source step out of an expression state *)
Lemma step_diagram_expr {α scrs C stk mem k e arg gps tmem tregs pc fb prot
      temps plm c rest sA sB cap t s1'} :
  S.CS.kstep (Source.GlobalEnv.prepare_global_env p)
    (S.CS.State C stk mem k e arg) t s1' ->
  expr_inv p tp α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm
           c rest sA sB cap ->
  (forall v, e = E_val v -> k = Kstop -> stk <> [::]) ->
  (exists ts', plus CS.step G (gps, tmem, tregs, pc) t ts'
               /\ match_states p tp s1' ts')
  \/ [/\ measure s1' < measure (S.CS.State C stk mem k e arg), t = E0
       & match_states p tp s1' (gps, tmem, tregs, pc)].
Proof.
  move=> Hstep He Hnf.
  case: (exprval_dec e) => [[v0 Ev0] | Hnev].
  - (* a value: one IConst step, then consume *)
    subst e.
    case/leaf_val_run: (He) => [i [Ev S0 Hc0]].
    subst v0.
    have Hval2 : val_inv p tp α scrs C stk mem k (Int i) arg gps tmem
                   (Register.set R_COM (Int i) tregs) (Pointer.inc pc) fb
                   prot temps plm rest cap.
    { apply: expr_to_val (He) _ _ _ _ _ _ _.
      - by rewrite register_get_set_neq.
      - by rewrite register_get_set_neq.
      - by rewrite register_get_set_neq.
      - rewrite register_get_set_eq. exact: VI_int.
      - rewrite Pointer.inc_preserves_component. exact: ei_pc He.
      - by rewrite Pointer.inc_preserves_block.
      - exact: Hc0. }
    case: (val_consume Hstep Hval2) => [[ts' [P2 Hm2]] | [Hme Ht Hm2]].
    + left. exists ts'. split; last exact: Hm2.
      eapply star_plus_trans; [exact: star_one S0 | exact: P2 | by []].
    + left. eexists. split; last exact: Hm2.
      rewrite Ht. exact: plus_one S0.
  - (* administrative descends and non-value leaves *)
    inversion Hstep; subst; try by case: (Hnev _ erefl).
    + (* KS_Binop1 *)
      right.
      case: (TReplumb.binop1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_Seq1 *)
      right.
      case: (TReplumb.seq1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_If1 *)
      right.
      case: (TReplumb.if1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_Arg *)
      case/leaf_arg_run: (He) => [S0 Hvinj Hc0].
      have Hval2 := expr_to_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Register.set R_COM (Register.get R_ARG tregs) tregs)
        (Pointer.inc pc) He
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(rewrite register_get_set_eq; exact: Hvinj))
        (ltac:(rewrite Pointer.inc_preserves_component; exact: ei_pc He))
        (ltac:(by rewrite Pointer.inc_preserves_block))
        Hc0.
      case/val_pack: Hval2 => [ts' [Sp Hm2]].
      left. exists ts'. split; last exact: Hm2.
      eapply plus_left; [exact: S0 | exact: Sp | by []].
    + (* KS_LocalBuffer *)
      case/leaf_local_run: (He) => [S0 Hvinj Hc0].
      have Hval2 := expr_to_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Register.set R_COM (Ptr (lbp C)) tregs)
        (Pointer.inc pc) He
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(by rewrite register_get_set_neq))
        (ltac:(rewrite register_get_set_eq; exact: Hvinj))
        (ltac:(rewrite Pointer.inc_preserves_component; exact: ei_pc He))
        (ltac:(by rewrite Pointer.inc_preserves_block))
        Hc0.
      case/val_pack: Hval2 => [ts' [Sp Hm2]].
      left. exists ts'. split; last exact: Hm2.
      eapply plus_left; [exact: S0 | exact: Sp | by []].
    + (* KS_Alloc1 *)
      right.
      case: (TReplumb.alloc1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_Deref1 *)
      right.
      case: (TReplumb.deref1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_Assign1 *)
      right.
      case: (TReplumb.assign1_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
    + (* KS_InitCall *)
      right.
      case: (TReplumb.initcall_replumb (P := code_at _ _) (ei_comp He)
               (ei_code He) (ei_cont He))
        => [c1 [rest' [sA' [sB' [E1 Hc1 Hk1]]]]].
      have He' := expr_inv_replumb He E1 Hc1 Hk1
                    (ltac:(by move: (ei_budget He); rewrite /=; lia)).
      split.
      * by rewrite /measure /=; lia.
      * by [].
      * apply: MS_expr; [exact: He' | by []].
Qed.

(* THE master simulation diagram *)
Lemma step_diagram s1 t s1' :
  S.CS.kstep (Source.GlobalEnv.prepare_global_env p) s1 t s1' ->
  forall s2, match_states p tp s1 s2 ->
  (exists s2', plus CS.step G s2 t s2' /\ match_states p tp s1' s2')
  \/ [/\ measure s1' < measure s1, t = E0 & match_states p tp s1' s2].
Proof.
  move=> Hstep s2 Hmatch.
  move: Hstep.
  case: s1 s2 / Hmatch.
  - (* MS_start *)
    move=> Hstep.
    have [mexpr Em] : exists mexpr, Source.prog_main p = Some mexpr.
    { case E: (Source.prog_main p) => [m|]; first by exists m.
      move: (Source.cprog_main_existence Hclosed_p). by rewrite E. }
    rewrite /S.CS.initial_machine_state Em /= in Hstep *.
    have Hfin : immediately_final mexpr = false.
    { case Ef: (immediately_final mexpr) => //.
      by case: (final_expr_nostep _ _ _ _ _ _ _ Ef Hstep). }
    case: (start_bridge _ Em Hfin)
      => [scrs1 [tmemF [tregsF [pcF [gps1 [c1 [rest1 [sAx [sBx [fbN [prot1
          [plm1 [Hplusb Hinv1]]]]]]]]]]]]].
    have Hnf1 : forall v, mexpr = E_val v -> (Kstop : cont) = Kstop ->
                ([::] : S.CS.stack) <> [::].
    { by move=> v1 Ev1; move: Hfin; rewrite Ev1. }
    case: (step_diagram_expr Hstep Hinv1 Hnf1)
      => [[ts' [P2 Hm2]] | [Hme Ht Hm2]].
    + left. exists ts'. split; last exact: Hm2.
      eapply plus_trans; [exact: Hplusb | exact: P2 | by []].
    + left. exists (gps1, tmemF, tregsF, pcF). split; last exact: Hm2.
      rewrite Ht. exact: Hplusb.
  - (* MS_expr *)
    move=> α scrs C stk mem k e arg gps tmem tregs pc fb prot temps plm c0
           rest0 sA0 sB0 cap Hinv Hnf Hstep.
    exact: (step_diagram_expr Hstep Hinv Hnf).
  - (* MS_val *)
    move=> α scrs C stk mem k v arg gps tmem tregs pc fb prot temps plm
           rest0 cap Hinv Hnf Hstep.
    exact: (val_consume Hstep Hinv).
  - (* MS_halted *)
    move=> α C mem v arg gps tmem tregs pc Hmem Hexec Hstep.
    by inversion Hstep.
Qed.

(* ==================== initial and final states ==================== *)

Lemma match_initial_states s1 :
  S.CS.initial_state p s1 ->
  exists s2, I.CS.initial_state tp s2 /\ match_states p tp s1 s2.
Proof.
  move=> Hini.
  exists (CS.initial_machine_state tp).
  split; first by [].
  rewrite Hini. exact: MS_start.
Qed.

Lemma match_final_states s1 s2 :
  match_states p tp s1 s2 ->
  S.CS.final_state s1 ->
  I.CS.final_state G s2.
Proof.
  case: s1 s2 / => [ | α scrs C stk mem k e arg gps tmem tregs pc fb prot
                     temps plm c0 rest0 sA0 sB0 cap Hinv Hnf
                   | α scrs C stk mem k v arg gps tmem tregs pc fb prot temps
                     plm rest0 cap Hinv Hnf
                   | α C mem v arg gps tmem tregs pc Hmem Hexec] Hfin.
  - (* MS_start: the halt pad sits under the initial pc *)
    have [mexpr Em] : exists mexpr, Source.prog_main p = Some mexpr.
    { case E: (Source.prog_main p) => [m|]; first by exists m.
      move: (Source.cprog_main_existence Hclosed_p). by rewrite E. }
    move: Hfin. rewrite /S.CS.initial_machine_state Em /= => Hfin.
    have Hfinal : immediately_final mexpr = true.
    { by case: Hfin => [-> | [v [-> _]]]. }
    move: (Em). rewrite /Source.prog_main /Source.find_procedure.
    case HgCm: (getm (Source.prog_procedures p) Component.main)
      => [CprocsM|] //= HgPm.
    case: (compile_prog_procedures_spec Hwf_p Hcompile)
      => [labels [cenv1 [Egen HSPEC]]].
    case: (HSPEC _ _ _ _ HgCm HgPm)
      => [plmf [CprocsT [cd [s1x [s2x [Hplmf HgT HgTP Hcp]]]]]].
    have Hdom : Component.main \in domm (Intermediate.prog_interface tp).
    { rewrite (compilation_preserves_interface _ _ Hcompile).
      apply/(proj2 (Source.wfprog_main_existence Hwf_p)).
      by rewrite Em. }
    case: (compiled_code_anchor _ _ _ _ _ Hdom HgT HgTP)
      => [bE [CprocsB [HgB HgBE Hentrypt Hother]]].
    have Hmaintp : Intermediate.prog_main tp = true.
    { by rewrite (compilation_preserves_main_flag _ _ Hcompile) Em. }
    have [CI HgCI] : exists CI,
        getm (Intermediate.prog_interface tp) Component.main = Some CI.
    { by case/dommP: Hdom => CI HCI; exists CI. }
    have HEP : EntryPoint.get Component.main Procedure.main
                 (genv_entrypoints G) = Some bE.
    { apply: (Hentrypt CI HgCI).
      apply/orP; right.
      by rewrite Hmaintp !PeanoNat.Nat.eqb_refl. }
    have Einit : CS.initial_machine_state tp
      = ([::], Intermediate.prepare_procedures_memory tp, Register.init,
         (Component.main, bE, 0%Z)).
    { rewrite /CS.initial_machine_state Hmaintp.
      move: HEP.
      rewrite /G /prepare_global_env /Intermediate.prepare_procedures_memory.
      case: (Intermediate.prepare_procedures_initial_memory tp)
        => [[mem0 procs] eps] /=.
      by move=> ->. }
    have [plf Hplf] : exists plf, getm plmf Procedure.main = Some plf.
    { move: Hcp.
      rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
      case: (getm plmf Procedure.main) => [x|] //=. by exists x. }
    have Hguard : Component.eqb Component.main Component.main
                  && Procedure.eqb Procedure.main Procedure.main = true.
    { by rewrite /Component.eqb /Procedure.eqb !PeanoNat.Nat.eqb_refl. }
    case: (compile_proc_shape_main_final _ _ _ _ _ _ _ _ Hcp Hplf Hguard
             Hfinal) => [restH EcdH].
    rewrite Einit /=.
    have HcE0 : code_at G (Component.main, bE, 0%Z) cd.
    { exists CprocsB, cd, [::], [::]. split=> //. by rewrite cats0. }
    rewrite EcdH in HcE0.
    exact: code_at_head HcE0.
  - (* MS_expr: only E_exit is final here *)
    case: Hfin => [Ee | [v [Ee [Ek Estk]]]]; last first.
    { by case: (Hnf _ Ee Ek Estk). }
    subst e.
    move: (ei_comp Hinv) => /= [Ec _]. subst c0.
    move: (ei_code Hinv) => Hcode.
    exact: code_at_head Hcode.
  - (* MS_val: value final states are excluded by the side condition *)
    case: Hfin => [Ee | [v1 [Ee [Ek Estk]]]]; first by [].
    by case: (Hnf Ek Estk).
  - (* MS_halted *)
    exact: Hexec.
Qed.

(* ==================== the forward simulation ==================== *)

Theorem fcc_sim : forward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
  apply forward_simulation_star with
    (match_states := match_states p tp) (measure := measure).
  - exact: match_initial_states.
  - exact: match_final_states.
  - move=> s1 t s1' Hstep s2 Hm.
    case: (step_diagram _ _ _ Hstep _ Hm) => [[s2' [Hp Hm']] | [Hme Ht Hm']].
    + left. by exists s2'.
    + right. split; [by apply/ltP | by []].
Qed.

End Diagram.

(* ==================== THE compiler correctness theorem ==================== *)

(* FCC: the compiled program forward-simulates the source. This discharges
   the axiom formerly assumed in S2I/Compiler.v. *)
Theorem I_simulates_S :
  forall {p},
    Source.closed_program p ->
    Source.well_formed_program p ->
  forall {tp},
    compile_program p = Some tp ->
    forward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
  move=> p Hclosed Hwf tp Hcompile.
  exact: (fcc_sim p tp Hwf Hclosed Hcompile).
Qed.

(* BCC *)
(* We derive BCC from FCC as in CompCert *)
Corollary S_simulates_I:
  forall {p},
    Source.closed_program p ->
    Source.well_formed_program p ->
  forall {tp},
    compile_program p = Some tp ->
    backward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
  intros.
  apply forward_to_backward_simulation.
  - apply I_simulates_S; auto.
  - apply S.CS.receptiveness.
  - apply I.CS.determinacy.
Qed.

Lemma forward_simulation_same_safe_prefix:
  forall p p_compiled m,
    Source.closed_program p ->
    Source.well_formed_program p ->
    does_prefix (Source.CS.CS.sem p) m ->
    not_wrong_finpref m ->
    compile_program p = Some p_compiled ->
    does_prefix (Intermediate.CS.CS.sem p_compiled) m.
Proof.
  intros p p_compiled m Hcp Hwfp [b [Hb Hmb]] Hsafem Hcmp.
  assert(Hbs : forward_simulation (Source.CS.CS.sem p) (Intermediate.CS.CS.sem p_compiled)).
    apply I_simulates_S; assumption.
  apply (forward_simulation_behavior_improves Hbs) in Hb. clear Hbs.
  destruct Hb as [b' [Hb' [Hbb' | [t [H1 H2]]]]]; unfold does_prefix.
  - exists b. split; [| tauto]. subst. assumption.
  - exists b'. split. assumption. subst.
    destruct m as [| | t']; simpl in Hmb, Hsafem. tauto. tauto.
    simpl. eapply behavior_prefix_goes_wrong_trans; eassumption.
Qed.
Lemma backward_simulation_behavior_improves_prefix :
  forall p p_compiled m,
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    does_prefix (Intermediate.CS.CS.sem p_compiled) m ->
  exists b,
    program_behaves (Source.CS.CS.sem p) b /\
    (CompCertExtensions.prefix m b \/ behavior_improves_finpref b m).
Proof.
  intros p p_compiled m Hcp Hwfp Hcmp [b [Hb Hmb]].
  assert(Hbs : backward_simulation (Source.CS.CS.sem p) (Intermediate.CS.CS.sem p_compiled)).
    apply S_simulates_I; assumption.
  apply (backward_simulation_behavior_improves Hbs) in Hb. clear Hbs.
  destruct Hb as [b' [Hb' Hb'b]]. exists b'. split. assumption.
  destruct Hb'b as [Hb'b | [t [Hb't Htb]]].
  - left. now subst.
  - unfold behavior_improves_finpref. subst b'.
    (* right. exists t. split. assumption. -- committing too early *)
    (* we start by combining behavior_prefix t b and prefix m b to get
       that t and m must be in the prefix relation one way or the other *)
    eapply behavior_prefix_comp' in Htb; [| exact Hmb].
    destruct Htb.
    + left. destruct m as [| |t']; simpl in H. tauto. tauto. simpl.
      destruct H as [t'' ?]. subst.
      exists (Goes_wrong t''). reflexivity.
    + right. exists t. split. reflexivity. assumption.
Qed.


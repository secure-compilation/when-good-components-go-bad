Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.Blame.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.
Require Import Lib.Monads.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Inductive cont : Type :=
| Kstop
| Kbinop1 (op: binop) (re: expr) (k: cont)
| Kbinop2 (op: binop) (lv: value) (k: cont)
| Kseq (e: expr) (k: cont)
| Kif (e1: expr) (e2: expr) (k: cont)
| Kalloc (k: cont)
| Kderef (k: cont)
(* Seems not possible to use *)
(* | KderefExt (k: cont) *)
| Kassign1 (e: expr) (k: cont)
| Kassign2 (v: value) (k: cont)
| Kcall (C: Component.id) (P: Procedure.id) (k: cont).

Lemma continuation_absurd : forall k e1 e2,
    Kseq (E_seq e1 e2) k <> k.
Proof.
  elim => // e k IHk e1 e2 Hkseq.
  inversion Hkseq as [[He Hind]]. by apply IHk in Hind.
Qed.

Module CS.

CoInductive frame : Type := Frame {
  f_component : Component.id;
  f_arg       : value;
  f_cont      : cont
}.

Definition stack : Type := list frame.

CoInductive state : Type := State {
  s_component : Component.id;
  s_stack     : stack;
  s_memory    : Memory.t;
  s_cont      : cont;
  s_expr      : expr;
  s_arg       : value
}.

Notation "[ 'State' C , stk , mem , k , e , arg ]" :=
  (State C stk mem k e arg)
  (at level 0, format "[ 'State'  C ,  stk ,  mem ,  k ,  e ,  arg ]").

Ltac unfold_state st :=
  let C := fresh "C" in
  let s := fresh "s" in
  let mem := fresh "mem" in
  let k := fresh "k" in
  let e := fresh "e" in
  let arg := fresh "arg" in
  destruct st as [C s mem k e arg].

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Instance state_turn : HasTurn state := {
  turn_of s iface := s_component s \in domm iface
}.

Import MonadNotations.
Open Scope monad_scope.

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | Some main_expr => State Component.main [::] (prepare_buffers p) Kstop main_expr (Int 0)
  | None =>
    (* this case shouldn't happen for a well formed p *)
    State Component.main [::] emptym Kstop E_exit (Int 0)
  end.

(* transition system *)

Definition initial_state (p: program) (st: state) : Prop :=
  st = initial_machine_state p.

Definition final_state (st: state) : Prop :=
  let: State C s mem k e arg := st in
  e = E_exit \/ (exists v, e = E_val v /\ k = Kstop /\ s = []).

Inductive kstep (G: global_env) : state -> trace -> state -> Prop :=
| KS_Binop1 : forall C s mem k op e1 e2 arg,
    kstep G [State C, s, mem, k, E_binop op e1 e2, arg] E0
            [State C, s, mem, Kbinop1 op e2 k, e1, arg]
| KS_Binop2 : forall C s mem k op v1 e2 arg,
    kstep G [State C, s, mem, Kbinop1 op e2 k, E_val v1, arg] E0
            [State C, s, mem, Kbinop2 op v1 k, e2, arg]
| KS_BinopEval : forall C s mem k op v1 v2 arg,
    kstep G [State C, s, mem, Kbinop2 op v1 k, E_val v2, arg] E0
            [State C, s, mem, k, E_val (eval_binop op v1 v2), arg]
| KS_Seq1 :  forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_seq e1 e2, arg] E0
            [State C, s, mem, Kseq e2 k, e1, arg]
| KS_Seq2 : forall C s mem k v e2 arg,
    kstep G [State C, s, mem, Kseq e2 k, E_val v, arg] E0
            [State C, s, mem, k, e2, arg]
| KS_If1 : forall C s mem k e1 e2 e3 arg,
    kstep G [State C, s, mem, k, E_if e1 e2 e3, arg] E0
            [State C, s, mem, Kif e2 e3 k, e1, arg]
| KS_If2 : forall C s mem k e2 e3 i arg,
    kstep G [State C, s, mem, Kif e2 e3 k, E_val (Int i), arg] E0
            [State C, s, mem, k, if i != 0%Z then e2 else e3, arg]
| KS_Arg : forall C s mem k i,
    kstep G [State C, s, mem, k, E_arg, Int i] E0
            [State C, s, mem, k, E_val (Int i), Int i]
| KS_LocalBufferPublic : forall C s mem k arg,
    kstep G [State C, s, mem, k, E_local Block.pub, arg] E0
            [State C, s, mem, k, E_val (Ptr (C,Block.public,0%Z)), arg]
| KS_LocalBufferPrivate : forall C s mem k arg,
    kstep G [State C, s, mem, k, E_local Block.priv, arg] E0
          [State C, s, mem, k, E_val (Ptr (C,Block.private,0%Z)), arg]
| KS_ComponentBuffer : forall C s mem k C' arg,
    kstep G [State C, s, mem, k, E_component_buf C', arg] E0
            [State C, s, mem, k, E_val (Ptr (C',Block.public,0%Z)), arg]
| KS_Alloc1 : forall C s mem k e arg,
    kstep G [State C, s, mem, k, E_alloc e, arg] E0
            [State C, s, mem, Kalloc k, e, arg]
| KS_AllocEval : forall C s mem mem' k size ptr arg,
    (size > 0) % Z ->
    Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
    kstep G [State C, s, mem, Kalloc k, E_val (Int size), arg] E0
            [State C, s, mem', k, E_val (Ptr ptr), arg]
| KS_Deref1 : forall C s mem k e arg,
    kstep G [State C, s, mem, k, E_deref e, arg] E0
            [State C, s, mem, Kderef k, e, arg]
| KS_DerefEval : forall C s mem k C' b' o' v arg,
    C = C' ->
    Memory.load mem (C',b',o') = Some v ->
    kstep G [State C, s, mem, Kderef k, E_val (Ptr (C',b',o')), arg] E0
            [State C, s, mem, k, E_val v, arg]
(* If done automatically via take_step, the rule above is chosen instead of this
   one *)
(* Should we have another continuation for dereferencing a foreign pointer ?
   Since e is not evaluated at the point where we create the continuation, I
   guess it's not possible *)
| KS_DerefComponentEval : forall C s mem k C' b' o' v arg,
    C <> C' ->
    b' = Block.public -> (* for now, only allowing the preallocated public buffer *)
    Memory.load mem (C',b',o') = Some v ->
    (* for now, only allowing int and undef to be passed *)
    is_transferable_value v ->
    (* or this can be even enforced as Memory.load(C',Block.public,o') *)
    kstep G [State C, s, mem, Kderef k, E_val (Ptr (C',b',o')), arg]
            [:: ELoad C  o' v C']
            [State C, s, mem, k, E_val v, arg]
| KS_Assign1 : forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_assign e1 e2, arg] E0
            [State C, s, mem, Kassign1 e1 k, e2, arg]
| KS_Assign2 : forall C s mem k v e1 arg,
    kstep G [State C, s, mem, Kassign1 e1 k, E_val v, arg] E0
            [State C, s, mem, Kassign2 v k, e1, arg]
| KS_AssignEval : forall C s mem mem' k v C' b' o' arg,
    C = C' ->
    Memory.store mem (C', b', o') v = Some mem' ->
    kstep G [State C, s, mem, Kassign2 v k, E_val (Ptr (C', b', o')), arg] E0
            [State C, s, mem', k, E_val v, arg]
| KS_InitCall : forall C s mem k C' P e arg,
    kstep G [State C, s, mem, k, E_call C' P e, arg] E0
            [State C, s, mem, Kcall C' P k, e, arg]
| KS_InternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C = C' ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val (Int v), old_call_arg] E0
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, Int v]
| KS_ExternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C <> C' ->
    (* check permission *)
    imported_procedure (genv_interface G) C C' P  ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val (Int v), old_call_arg]
            [:: ECall C P v C']
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, Int v]
| KS_InternalReturn: forall C s mem k v arg C' old_call_arg,
    C = C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val (Int v), arg] E0
            [State C', s, mem, k, E_val (Int v), old_call_arg]
| KS_ExternalReturn: forall C s mem k v arg C' old_call_arg,
    C <> C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val (Int v), arg]
            [:: ERet C v C']
            [State C', s, mem, k, E_val (Int v), old_call_arg].

Lemma kstep_component G s t s' :
  kstep G s t s' ->
  s_component s' =
  if t is e :: _ then next_comp_of_event e
  else s_component s.
Proof. by case: s t s' /. Qed.

Lemma final_state_stuck G (st: state) :
  final_state st ->
  forall t st', ~ kstep G st t st'.
Proof.
move=> Hfinal t st' Hstep.
case: st t st' / Hstep Hfinal => //= *;
by repeat match goal with
| H : _ \/ _ |- _ => case: H=> ?
| H : exists _, _ |- _ => case: H => ??
| H : _ /\ _ |- _ => case: H => ??
end.
Qed.

(* functional kstep *)

Definition eval_kstep (G : global_env) (st : state) : option (trace * state) :=
  let: State C s mem k e arg := st in
  match e with
  (* pushing a new continuation *)
  | E_binop b_op e1 e2 =>
    ret (E0, [State C, s, mem, Kbinop1 b_op e2 k, e1, arg])
  | E_seq e1 e2 =>
    ret (E0, [State C, s, mem, Kseq e2 k, e1, arg])
  | E_if e1 e2 e3 =>
    ret (E0, [State C, s, mem, Kif e2 e3 k, e1, arg])
  | E_arg =>
    if arg is Int v then
      ret (E0, [State C, s, mem, k, E_val (Int v), arg])
    else None
  | E_local bk =>
    let block_id := Block.buffer_kind_to_block_id bk in
    ret (E0, [State C, s, mem, k, E_val (Ptr (C, block_id, 0%Z)), arg])
  | E_component_buf C' =>
    ret (E0, [State C, s, mem, k, E_val (Ptr (C', Block.public, 0%Z)), arg])
  | E_alloc e =>
    ret (E0, [State C, s, mem, Kalloc k, e, arg])
  | E_deref e =>
    ret (E0, [State C, s, mem, Kderef k, e, arg])
  | E_assign e1 e2 =>
    ret (E0, [State C, s, mem, Kassign1 e1 k, e2, arg])
  | E_call C' P e =>
    ret (E0, [State C, s, mem, Kcall C' P k, e, arg])
  (* evaluating current continuation *)
  | E_val v =>
    match k with
    | Kbinop1 b_op e2 k' =>
      ret (E0, [State C, s, mem, Kbinop2 b_op v k', e2, arg])
    | Kbinop2 b_op v1 k' =>
      ret (E0, [State C, s, mem, k', E_val (eval_binop b_op v1 v), arg])
    | Kseq e2 k' =>
      ret (E0, [State C, s, mem, k', e2, arg])
    | Kif e2 e3 k' =>
      match v with
      | Int z => ret (E0, [State C, s, mem, k', if z != 0%Z then e2 else e3, arg])
      | _ => None
      end
    | Kalloc k' =>
      match v with
      | Int size =>
        if (size >? 0) % Z then
          do (mem',ptr) <- Memory.alloc mem C (Z.to_nat size);
          ret (E0, [State C, s, mem', k', E_val (Ptr ptr), arg])
        else
          None
      | _ => None
      end
    | Kderef k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do v <- Memory.load mem (C',b',o');
          ret (E0, [State C, s, mem, k', E_val v, arg])
        else
          (* component buffer load *)
          do v <- Memory.load mem (C', b', o');
          (* match Block.block_id_to_buffer_kind b' with *)
          (* | Some pub => *)
          match b' with
          | (* public *) 0 =>
            if is_transferable_value v then
              (* For now, only allowing ints *)
              ret ([:: ELoad C o' v C'],
                                   [State C, s, mem, k', E_val v, arg])
            else None
          | _ => None
          end
      | _ => None
      end
    | Kassign1 e1 k' =>
      ret (E0, [State C, s, mem, Kassign2 v k', e1, arg])
    | Kassign2 v' k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do mem' <- Memory.store mem (C',b',o') v';
          ret (E0, [State C, s, mem', k', E_val v', arg])
        else
          None
      | _ => None
      end
    | Kcall C' P k' =>
      match v with
      | Int i =>
        if C == C' then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          ret (E0, [State C', Frame C arg k' :: s, mem, Kstop, P_expr, Int i])
        else if imported_procedure_b (genv_interface G) C C' P then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          ret ([ECall C P i C'], [State C', Frame C arg k' :: s, mem, Kstop, P_expr, Int i])
        else
          None
      | _ => None
      end
    | Kstop =>
      match v, s with
      | Int i, Frame C' old_call_arg k' :: s' =>
        let t := if C == C' then E0 else [:: ERet C i C'] in
        ret (t, [State C', s', mem, k', E_val (Int i), old_call_arg])
      | _, _ => None
      end
    end
  | _ => None
  end.

Hint Unfold eval_kstep.

Fixpoint execN (n: nat) (G: global_env) (st: state) : option state :=
  match n with
  | O => None
  | S n' =>
    match eval_kstep G st with
    | None => Some st
    | Some (_, st') => execN n' G st'
    end
  end.

Close Scope monad_scope.

(* Semantics Properties *)

Theorem eval_kstep_complete:
  forall G st t st',
    kstep G st t st' -> eval_kstep G st = Some (t, st').
Proof.
  intros G st t st' Hkstep.
  inversion Hkstep as [ | | | | | | | | | | |
                        | ?C ?s ?mem ?mem' ?k size ?ptr ?arg Hsize Halloc | |
                        (* DerefComponentEval *)
                        | ?C ?s ?mem ?k ?C' ?b' ?o' v ?arg HCC' Hpub Hload Htransf | | | | |
                        | | | ];
    subst; simpl; auto;
    try (unfold Memory.store, Memory.load, Memory.alloc in *;
         repeat simplify_nat_equalities;
         repeat simplify_option;
         reflexivity);
    try move/eqP/negbTE: H => -> ;
    try done.
  (* alloc eval *)
  - assert (HsizeBool: (size >? 0) % Z). {
      destruct size ; inversion Hsize ; auto.
    }
    rewrite HsizeBool.
    by rewrite Halloc.
  (* KS_DerefComponentEval -> _ *)
  - case: eqP; first done.
    by rewrite Hload Htransf.
  (* external calls *)
  - apply imported_procedure_iff in H0.
    by rewrite H0 H1.
Qed.

Theorem eval_kstep_sound:
  forall G st t st',
    eval_kstep G st = Some (t, st') -> kstep G st t st'.
Proof.
  intros.
  unfold_states.
  match goal with
  | H: eval_kstep _ _ = Some _ |- kstep _ [State _, _, _, _, ?E, _] _ [State _, _, _, _, _, _] =>
    destruct E; simpl in H;
      try discriminate;
      try (repeat simplify_option;
           econstructor; eauto;
           repeat simplify_nat_equalities;
           reflexivity)
  end.
  - repeat simplify_option.
    + case: (_ =P _) => [->|?]; econstructor; eauto.
    + econstructor.
    + econstructor.
    + econstructor.
    + destruct z ; econstructor; eauto; discriminate.
    + econstructor; eauto.
      * apply Zgt_is_gt_bool. assumption.
    + by econstructor; eauto; apply/eqP.
    + (* _ -> KS_DerefComponentEval *)
    constructor ; [by apply /eqP/negbT | reflexivity | assumption | assumption ].
    + econstructor.
    + by econstructor; eauto; apply/eqP.
    + econstructor; eauto; exact/eqP.
    + econstructor; eauto; first exact/eqP/negbT.
      apply imported_procedure_iff. assumption.
  - unfold Block.buffer_kind_to_block_id in H. destruct b ; inversion H ; constructor.
Qed.

Theorem eval_kstep_correct:
  forall G st t st',
    eval_kstep G st = Some (t, st') <-> kstep G st t st'.
Proof.
  split.
  apply eval_kstep_sound.
  apply eval_kstep_complete.
Qed.

Corollary kstep_deterministic:
  forall G st t st1 st2,
    kstep G st t st1 -> kstep G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hkstep1 Hkstep2.
  apply eval_kstep_correct in Hkstep1.
  apply eval_kstep_correct in Hkstep2.
  rewrite Hkstep1 in Hkstep2.
  inversion Hkstep2.
  reflexivity.
Qed.

Section Semantics.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem :=
    @Semantics_gen state global_env kstep (initial_state p) final_state G.

  Lemma receptiveness_step:
    forall s t1 s1 t2,
      kstep G s t1 s1 -> match_traces t1 t2 ->
      exists s2, kstep G s t2 s2.
  Proof.
    intros s t1 s1 t2.
    intros Hkstep Hmatch_traces.
    inversion Hkstep; subst;
    inversion Hmatch_traces; subst;
      try (eexists; apply Hkstep).
  Qed.

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; subst; simpl; auto.
  Qed.

  Theorem receptiveness:
    receptive sem.
  Proof.
    constructor.
    - apply receptiveness_step.
    - apply singleton_traces.
  Qed.

  Local Open Scope fset_scope.

  Definition stack_components (cs: state) : {fset Component.id} :=
    s_component cs |: fset [seq f_component f | f <- s_stack cs].

  Lemma stack_components_step cs t cs' :
    Step sem cs t cs' ->
    fsubset (stack_components cs) (domm (prog_interface p)) ->
    fsubset (stack_components cs') (domm (prog_interface p)).
  Proof.
  case: cs t cs' / => //=.
  - (* Internal Call *)
    move=> C stk mem k _ P v P_expr arg <-; rewrite /stack_components /=.
    by rewrite fset_cons fsetUA fsetUid.
  - (* External Call *)
    move=> C stk mem k C' P v P_expr arg _; rewrite /stack_components /=.
    rewrite (fsubU1set C') mem_domm fset_cons.
    by case/(cprog_closed_interface complete_program)=> CI [->].
  - (* Internal Return *)
    move=> C stk mem k v arg _ old <-; rewrite /stack_components /=.
    by rewrite fset_cons fsetUA fsetUid.
  - (* External Return *)
    move=> C stk mem k v arg C' old _; rewrite /stack_components /=.
    by rewrite (fsubU1set C) fset_cons; case/andP.
  Qed.

  Lemma stack_components_star cs t cs' :
    initial_state p cs ->
    Star sem cs t cs' ->
    fsubset (stack_components cs') (domm (prog_interface p)).
  Proof.
  move=> init star.
  have main_ok : Component.main \in domm (prog_interface p).
    have := cprog_main_existence complete_program.
    rewrite wfprog_defined_procedures // mem_domm /prog_main /find_procedure.
    by case: getm.
  have {init main_ok} cs_ok : fsubset (stack_components cs) (domm (prog_interface p)).
    rewrite init /initial_machine_state /stack_components.
    by case e_main: (prog_main p)=> [mainP|] /=; rewrite -fset0E fsetU0 fsub1set.
  elim: cs t cs' / star cs_ok=> // cs1 t1 cs2 t2 cs3 t step _ IH _ cs1_ok.
  by apply: IH; apply: stack_components_step cs1_ok; eauto.
  Qed.

  Fixpoint unstutter (T : eqType) (x : T) (s : seq T) :=
    if s is x' :: s' then
      if x == x' then unstutter x s'
      else x' :: unstutter x' s'
    else [::].

  Definition stack_state_of (cs: state) : stack_state :=
    let: State curr stk _ _ _ _ := cs in
    StackState curr (unstutter curr (map f_component stk)).

  Lemma trace_wb t cs cs' :
    Star sem cs t cs' ->
    well_bracketed_trace (stack_state_of cs) t.
  Proof.
    elim: cs t cs' / => //= s1 t1 s2 t2 s3 t Hstep Hstar IH -> {t}.
    case: s1 t1 s2 / Hstep Hstar IH=> //=.
    - (* Component buffer load *)
      by move => C stk mem k C' b' o' v arg; rewrite eqxx.
    - (* Internal Return *)
      by move=> C stk mem k _ P v P_expr old <-; rewrite eqxx.
    - (* External Return *)
      move=> C stk mem k C' P v P_expr old.
      by rewrite eq_sym eqxx=> /eqP/negbTE -> /=.
    - (* Internal Call *)
      by move=> C stk mem k v _ _ old <-; rewrite eqxx.
    - (* External Call *)
      by move=> C stk mem k v _ C' old /eqP/negbTE ->; rewrite !eqxx.
  Qed.

  Lemma events_wf st t st' :
    Star sem st t st' ->
    all (well_formed_event (prog_interface p)) t.
  Proof.
    (* have valid_program explicit in signature so that we don't have to use
       closed_program *)
    clear complete_program.
    elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
    rewrite all_cat; case: st1 t1 st2 / Hstep {Hstar} => //=.
    - move=> ?? mem ? C' ? o' ?? /eqP -> -> => mem_load transf. rewrite transf IH /= !andbT.
      move: mem_load ; rewrite /Memory.load/in_bounds/=.
      inversion valid_program as
          [ _ _ _ _ wf_defined_buffers [wf_valid_buffers wf_has_req_buffers] _].
      move: wf_defined_buffers ; rewrite -eq_fset.
      rewrite /valid_buffers in wf_valid_buffers.
      destruct (mem C') eqn:memC => //.
      (* rewrite /ComponentMemory.load. *) (* opaque here *)
      move => wf_defined_buffers Comp_load.

      (* we have pretty much everything, we just need to plug things from here : *)
      (* show that the size of the content of the component's memory is the same as the public_buffer_size in the program interface,
          or the size of the buffers in the program buffers *)
      (* explicit the link between the buffers and the memory content, ...*)
      (* eapply load_in_bounds *)
      (* rewrite -mem_domm in wf_defined_buffers. *)

      (* rewrite /prepare_global_env in G. *)
      (* Maybe use initial_state to get prepare_buffers, which could allow us to link the buffers and the memory *)
      admit.
    - by move=> ????????? /eqP -> /imported_procedure_iff ->.
    - by move=> ????????  /eqP ->.
  Admitted.

  Lemma trace_wf mainP t cs cs' :
    Star sem cs t cs' ->
    initial_state p cs ->
    prog_main p = Some mainP ->
    well_formed_trace (prog_interface p) t.
  Proof.
    move=> Hstar Hinitial Hmain; rewrite /well_formed_trace.
    rewrite (events_wf Hstar) andbT.
    suffices <- : stack_state_of cs = stack_state0 by apply: trace_wb; eauto.
    by move: Hinitial; rewrite /initial_state /initial_machine_state Hmain => ->.
  Qed.

  (* Several alternative formulations are possible. One may include the ERet event
     in the star, express the inclusion of ECall in the trace via In, etc. *)
  Lemma eret_from_initial_star_goes_after_ecall_cs s0 t s1 s2 C' v C :
    CS.initial_state p s0 ->
    Star sem s0 t s1 ->
    Step sem s1 [:: ERet C' v C] s2 ->
    exists t1 s s' t2 P v',
      Star sem s0 t1 s /\
      Step sem s [ECall C P v' C'] s' /\
      Star sem s' t2 s1 /\
      t = t1 ** [ECall C P v' C'] ** t2.
  Proof.
    move=> Hinitial Hstar Hstep.
    have {Hstep} /trace_wb : Star sem s0 (t ++ [:: ERet C' v C]) s2.
      apply: star_trans; eauto; exact: star_one.
    have -> : stack_state_of s0 = stack_state0.
      by rewrite Hinitial /= /CS.initial_machine_state /=; case: prog_main.
    case/well_bracketed_trace_inv=> t1 [P [arg [t2 e]]].
    move: Hstar; rewrite {}e -[seq.cat]/Eapp.
    case/(star_middle1_inv singleton_traces)=> s1' [s2' [Hstar1 [Hstep2 Hstar3]]].
    by exists t1, s1', s2', t2, P, arg; repeat split=> //.
  Qed.

  Lemma star_component s1 t s2 :
    Star sem s1 t s2 ->
    s_component s2 =
    last (s_component s1) [seq next_comp_of_event e | e <- t].
  Proof.
  elim: s1 t s2 / => //= s1 t1 s2 t2 s3 _ Hstep _ -> ->.
  rewrite map_cat last_cat (kstep_component Hstep).
  move/singleton_traces: Hstep.
  by case: t1=> [|e [|e' t1]] //= *; omega.
  Qed.

  Lemma initial_state_exists:
    exists s, initial_state p s.
  Proof.
    unfold initial_state, initial_machine_state;
      by eauto.
  Qed.
  Lemma memory_linked mem :
    prepare_buffers p = mem ->
    domm mem = domm (prog_interface p).
  Proof.
    rewrite /prepare_buffers.
    inversion valid_program as [_ _ _ _ def_bufs wf_bufs _]. rewrite def_bufs. move => <-. by apply domm_map.
  Qed.

  Lemma memory_linked_star cs_i t cs_f ptr v :
    Star sem cs_i t cs_f ->
    Memory.load (s_memory cs_i) ptr = Some v ->
    exists v', Memory.load (s_memory cs_f) ptr = Some v'.
  Proof.
    destruct ptr as [[C b] o].
    move => Hstar Hload.
    induction Hstar as [|cs_i t1 cs_int t2 cs_f t Hstep Hstar IHstar Htrace] ;
      first (by exists v).
    induction Hstep as [ |  | | | | | | | | | | |
                         C_ s mem mem' k size [[C' b'] o'] arg Hsize Halloc | | | | | |
                         C_ s mem mem' k v' C' b' o' arg HCC' Hstore | | | | | ] ;
      subst ; try (simpl in Hload, IHstar ; by apply (IHstar Hload)) ; apply IHstar ; clear IHstar.
    - move: Hload Halloc. rewrite /Memory.load/Memory.alloc/=.
      destruct (C == C_) eqn: HCC_ ; move:HCC_ => /eqP HCC_ ; first subst C_.
      + destruct (mem C) eqn:C_in_mem => //.

        (* rewrite setmE. *)

      (* case:(mem C) => //= memC Hload. case: (mem C_) => //= memC_ Halloc. *)
      (* rewrite -Hload. case: (mem' C) => // [mem'C|]. *)
      (* eapply ComponentMemory.load_after_alloc. *)
      (* rewrite /Memory.load/= in Hload, IHstar. rewrite /Memory.alloc in Halloc. case (mem C) => //. *)
  Admitted.


  Lemma memory_reachable cs_i t_i C s (mem : Memory.t) (t : ComponentMemory.t) bufs k e arg Cmem Omem v :
    prog_main p ->
    initial_state p cs_i -> (* necessary ? *)

    (* Component existing statically and dynamically, better way to enforce ? *)
    mem Cmem = Some t ->
    (prog_buffers p) Cmem = Some bufs ->

    Star sem cs_i t_i [State C, s, mem, k, e, arg] ->
    Z.to_nat Omem < buffer_size (get_buffer bufs Block.pub)
    <->  ComponentMemory.load t Block.public Omem = Some v.
  (* wow, such tedious *)
  Proof.
    rewrite /initial_state/initial_machine_state/=.
    case (prog_main p) => // main_expr.
    move => _ init Hmem Hbufs. subst => Hstar.
    split => [Hstat | Hdyn].


  Admitted.

  Lemma all_expressions_evaluate (* cs_i t_i *) C s mem k e arg :

    (* Is this the right way to state that e is well typed ? (you can get from
       the initial state of the program to the expr e, and p is well typed so is
       e) *)
    (* initial_state p cs_i -> *)
    (* Star sem cs_i t_i [State C, s, mem, k, e, arg] -> *)

    (* Or maybe is there a more usable way to say that e is well_typed ? *)
    well_formed_expr p C e ->

    exists mem' t v,
      Star sem
           [State C, s, mem,  k, e,       arg] t
           [State C, s, mem', k, E_val v, arg].
  Proof.
    (* intro Hinitial. *)
    move: (* t_i *) C s mem k arg.
    induction e as [ v | b | |
                     bin e1 IHe1 e2 IHe2 |
                     e1 IHe1 e2 IHe2 |
                     e__if IHe__if e__then IHe__then e__else IHe__else |
                     e__alloc IHe__alloc |
                     e__deref IHe__deref |
                     e__assign IHe__assign e__val IHe__val |
                     Cid Pid P__expr IHP__expr |
                     Cid | ]=> C s mem k arg Hwf_e.
      - (* E_val *)
        exists mem, E0, v ; by apply star_refl.
      - (* E_arg *)
        exists mem, E0 ; eexists ; eapply star_one.
        (* eapply KS_Arg *)
        destruct arg ; simpl ; rewrite -eval_kstep_correct ; simpl ;
          first done ; exfalso ;
        (* simpl in Hstep. rewrite <- eval_kstep_correct in Hstep. *)
        (* inversion valid_program as [? ? ? wf_proc ? ? ?]. *)
        (* inversion complete_program. simpl in Hstar. *)
        (* (* simpl in Hstar. *) *)
        (* (* generalize dependent e3 ; generalize dependent e2. *) *)
        (* (* unfold prepare_global_env in G. simpl. unfold G. intro z. *) *)
        (* (* simpl. *) *)
        (* admit. *)
        (** Should be stuck (cannot have Ptr or Undef as arg in a wf_prog and more precisely in a wf_expr), how to show it ? *)
            admit.
      - (* E_local *)
        exists mem, E0 ;
          by destruct b ; eexists ; eapply star_one ; constructor.
      - (* E_binop *)
        destruct Hwf_e as [Hvalid_calls Hval_int ]. simpl in Hvalid_calls, Hval_int.
        move:Hval_int => /andP[Hval_int_e1 Hval_int_e2].
        have Hvalid_equiv: valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e1 :|: called_procedures e2) ->
              valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e1) /\
              valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e2) by admit.
        apply Hvalid_equiv in Hvalid_calls.
        move: Hvalid_calls {Hvalid_equiv} => [Hvalid_calls_e1 Hvalid_calls_e2].
        have Hwf_e1: well_formed_expr p C e1 by split.
        have Hwf_e2: well_formed_expr p C e2 by split.
        specialize (IHe1 C s mem (Kbinop1 bin e2 k) arg Hwf_e1).
        (* inversion Hstar_initial ; subst. inversion Hinitial. unfold initial_machine_state in H0. *)
        destruct IHe1 as [mem1 [?t [v1 star_e1]]].
        specialize (IHe2 C s mem1  (Kbinop2 bin v1 k) arg Hwf_e2).
        destruct IHe2 as [?mem [t2 [v2 star_e2]]].
        do 3 eexists.
        eapply star_step with (t1:=E0) ; last by rewrite E0_left.
        apply KS_Binop1. (* specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *)
        (* destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *)
        eapply star_trans ; first by apply star_e1.
        eapply star_step with (t1:=E0) ; last by rewrite E0_left.
        apply KS_Binop2. (* specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *)
        (* destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *)
        eapply star_trans with (t1:=t2) (t2:=E0) ;
          last rewrite E0_right ;
          first by apply star_e2.
        apply star_one. by apply KS_BinopEval. done. done.
      - (* E_seq *)

        admit.
      - (* E_if *)
        admit.
      - (* E_alloc *)
        admit.
      - (* E_deref *)
        admit.
      - (* E_assign *)
        admit.
      - (* E_call *)
        admit.
      - (* E_component_buf *)
  Admitted.

  (*
| KS_Seq1 :  forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_seq e1 e2, arg] E0
            [State C, s, mem, Kseq e2 k, e1, arg]
| KS_Seq2 : forall C s mem k v e2 arg,
    kstep G [State C, s, mem, Kseq e2 k, E_val v, arg] E0
            [State C, s, mem, k, e2, arg]
   *)

(** we should have something like :
(Left side)
 Plus sem [State C, s, mem0, k, E_seq (E_seq e1 e2) e3, arg] evs
          [State C, s, mem__final, k, e3, arg]
          ≜
 (KS_Seq1)
 Step sem [State C, s, mem0, k, E_seq (E_seq e1 e2) e3, arg] E0
          [State C, s, mem0, Kseq e3 k, E_seq e1 e2, arg]
 **
 (KS_Seq1)
 Step sem [State C, s, mem0, Kseq e3 k, E_seq e1 e2, arg] E0
          [State C, s, mem0, Kseq e2 (Kseq e3 k), e1, arg]
 **
 (This is the part where case analysis/induction on e1 happens )
 Star sem [State C, s, mem0, Kseq e2 (Kseq e3 k), e1, arg] t1
          [State C, s, mem1, Kseq e2 (Kseq e3 k), E_val v, arg]
 (mem1 may be different from mem0, and t1 may be non empty)
 **
 (KS_Seq2)
 Step sem [State C, s, mem1, Kseq e2 (Kseq e3 k), E_val v, arg] E0
          [State C, s, mem1, Kseq e3 k, e2, arg]
 (case analysis/induction on e2)
 Star sem [State C, s, mem1, Kseq e3 k, e2, arg] t2
          [State C, s, mem__final, Kseq e3 k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem__final, Kseq e3 k, E_val v, arg] E0
          [State C, s, mem__final, k, e3, arg]

And (Right side)
 Plus sem [State C, s, mem0, k, E_seq e1 (E_seq e2 e3), arg] evs
          [State C, s, mem__final, k, e3, arg]
          ≜
 (KS_Seq1)
 Step sem [State C, s, mem0, k, E_seq e1 (E_seq e2 e3), arg] E0
          [State C, s, mem0, Kseq (E_seq e2 e3) k, e1, arg]
 **
 (case analysis/induction on e1)
 Star sem [State C, s, mem0, Kseq (E_seq e2 e3) k, e1, arg] t1
          [State C, s, mem1, Kseq (E_seq e2 e3) k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem1, Kseq (E_seq e2 e3) k, E_val v, arg] E0
          [State C, s, mem1, k, E_seq e2 e3, arg]
 **
 (KS_Seq1)
 Step sem [State C, s, mem1, k, E_seq e2 e3, arg] E0
          [State C, s, mem1, Kseq e3 k, e2, arg]
 **
 (case analysis/induction on e2)
 Star sem [State C, s, mem1, Kseq e3 k, e2, arg] t2
          [State C, s, mem2, Kseq e3 k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem2, Kseq e3 k, E_val v, arg] E0
          [State C, s, mem2, k, e3, arg]

We can even draw the finish line right before the case/ind on e2 since it's exactly the same from here *)
  (* Conjecture seq_associative : associative E_seq. *)
  (* Ltac inversion_star_and_subst := *)
  (*   match goal with *)
  (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
  (*     inversion_clear H as [H H' H'' [H''' Hcontra H'''1]|] ; subst *)
  (*   | _  => idtac *)
  (*   end. *)

  Lemma seq_assoc_in_CS_aux_left_seq C s mem mem' k e1 e2 e3 arg evs:
      Plus sem
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           (* [State C, s, mem', Kseq e3 k, e2, arg] *)
           (* Or *)
           [State C, s, mem', k, e3, arg]
      -> Plus sem
           [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
           [State C, s, mem', Kseq e3 k, e2, arg].
  Proof.
    intro H.
    apply plus_trans with (t1:=E0)
                          (t2:=evs)
                          (s2:= [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg]);
      last by rewrite E0_left.
    apply plus_one, KS_Seq1.
    have:  exists mem' t v,
        Star sem
             [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg] t
             [State C, s, mem', Kseq (E_seq e2 e3) k, E_val v, arg]
    (* \/ *)
        (* Plus sem *)
        (*      [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg] t *)
        (*      [State C, s, mem', Kseq (E_seq e2 e3) k, E_val v, arg] *).
    {
      apply all_expressions_evaluate. admit.
      (* inversion_clear H as [? ? ? ? ? ? Hstep Hstar (* ... *)] ; subst ; *)
      (*   inversion Hstep ; subst. *)
      (* inversion Hstar as [state Hstate Htrace [Hmem Hcontra Hexp]| state1 trace1 state2 trace2 state3 trace3 Hstep' Hstar' Htrace] ; subst ; *)
      (*   (* inversion_star_and_subst *) *)
      (*   (* [>by apply continuation_absurd in Hcontra| ..] *) *)
      (*   (** Not strong enough since we know that all the first goals generated by *)
      (*    inversion Hstar must be solved by this, but the 'subst' in between cannot *)
      (*    allow us to use 'first' *) *)
      (*   (* try by apply continuation_absurd in Hcontra. *) *)
      (*   match goal with *)
      (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
      (*       by apply continuation_absurd in H ; idtac "boup" *)
      (*   | _  => idtac *)
      (*   end. *)
      (* (* move: Hstar Hstep Hstep' Hstar'. *) *)
      (* generalize (Kseq (E_seq e2 e3) k). *)
      (* clear Hstar Hstep Hstar' Hstep'. generalize dependent mem. *)
      (* (* generalize dependent e3 ; generalize dependent e2. generalize dependent k. *) *)
      (* induction e1 => mem c (* => k e2 e3 *) (* H Hstar Hstep *) *)
      (* (* ; exists mem, E0 *) (* . eexists *) *)
      (* (*       inversion Hstar as [H0 H' H'' [H''' Hcontra H'''1]|] ; subst ; *)
      (*   (* inversion_star_and_subst *) *)
      (*   (* [>by apply continuation_absurd in Hcontra| ..] *) *)
      (*   (** Not strong enough since we know that all the first goals generated by *)
      (*    inversion Hstar must be solved by this, but the 'subst' in between cannot *)
      (*    allow us to use 'first' *) *)
      (*   (* try by apply continuation_absurd in Hcontra. *) *)
      (*   match goal with *)
      (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
      (*       by apply continuation_absurd in H *)
      (*   | _  => idtac *)
      (*   end. *) *)
      (* . *)
      (* - (* E_val *) *)
      (*   exists mem, E0, v ; by apply star_refl. *)
      (* - (* E_arg *) *)
      (*   exists mem, E0 ; eexists ; eapply star_one. *)
      (*   (* eapply KS_Arg *) *)
      (*   destruct arg ; simpl ; rewrite -eval_kstep_correct ; simpl ; *)
      (*     first done ; exfalso ; *)
      (*   (* simpl in Hstep. rewrite <- eval_kstep_correct in Hstep. *) *)
      (*   (* inversion valid_program as [? ? ? wf_proc ? ? ?]. *) *)
      (*   (* inversion complete_program. simpl in Hstar. *) *)
      (*   (* (* simpl in Hstar. *) *) *)
      (*   (* (* generalize dependent e3 ; generalize dependent e2. *) *) *)
      (*   (* (* unfold prepare_global_env in G. simpl. unfold G. intro z. *) *) *)
      (*   (* (* simpl. *) *) *)
      (*   (* admit. *) *)
      (*   (** Should be stuck (cannot have Ptr or Undef as arg in a wf_prog and more precisely in a wf_expr), how to show it ? *) *)
      (*       admit. *)
      (* - (* E_local *) *)
      (*   exists mem, E0 ; *)
      (*     by destruct b ; eexists ; eapply star_one ; constructor. *)
      (* - (* E_binop *) *)
      (*   specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *)
      (*   destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *)
      (*   specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *)
      (*   destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *)
      (*   do 3 eexists. *)
      (*   eapply star_step with (t1:=E0) ; last by rewrite E0_left. *)
      (*   apply KS_Binop1. (* specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *) *)
      (*   (* destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *) *)
      (*   eapply star_trans ; first by apply star_e1_1. *)
      (*   eapply star_step with (t1:=E0) ; last by rewrite E0_left. *)
      (*   apply KS_Binop2. (* specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *) *)
      (*   (* destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *) *)
      (*   eapply star_trans with (t1:=t2) (t2:=E0) ; *)
      (*     last rewrite E0_right ; *)
      (*     first by apply star_e1_2. *)
      (*   apply star_one. by apply KS_BinopEval. done. done. *)

    }
        (* intro. destruct x. destruct H ; destruct H. *)
    intros [mem1 [t1 [v1 Hstar]]].
    inversion H as [? ? ? ? ? ? Hstep Hstar' (* ... *)] ; subst.
    inversion Hstep ; subst.
    (* inversion Hstar' as [|] ; subst. *)
    (*   eapply star_plus_trans with (t1:=t1) *)
    (*                               (t2:=E0) ; *)
    (*     last (rewrite E0_right) ; *)
    (*     first (by apply Hstar) ; clear Hstar. *)
    (*   apply plus_trans with (t1:=E0) *)
    (*                         (t2:=E0) *)
    (*                         (s2:= [State C, s, mem', k, E_seq e2 e3, arg]); *)
    (*     last by rewrite E0_left. *)
    (*   apply plus_one, KS_Seq2. *)
    (*   apply plus_one, KS_Seq1. *)
  Admitted.

  Lemma seq_assoc_in_CS_aux_right_seq C s mem mem' k e1 e2 e3 arg evs:
      Plus sem
           [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
           (* [State C, s, mem', Kseq e3 k, e2, arg] *)
           (* Or *)
           [State C, s, mem', k, e3, arg]
      -> Plus sem
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           [State C, s, mem', Kseq e3 k, e2, arg].
  Proof.
  Admitted.

  (* Not well stated at all, not true in general *)
  Lemma seq_assoc_in_CS_aux_common:
    forall C s mem mem' k e1 e2 e3 arg evs,
      Plus sem
           (* direction doesn't really matter at this point I guess *)
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           [State C, s, mem', k, e3, arg] ->
      Plus sem
           [State C, s, mem, Kseq e3 k, e2, arg] evs
           [State C, s, mem', k, e3, arg].
  Proof.
    intros.
    have: exists v,
        Star sem
             [State C, s, mem, Kseq e3 k, e2, arg] evs
             [State C, s, mem', Kseq e3 k, E_val v, arg].
    induction e2 ; admit.
    intros [v Hstar].
    apply plus_right with (s2:=[State C, s, mem', Kseq e3 k, E_val v, arg])
                           (t1:=evs)
                           (t2:=E0) ;
      last (by rewrite E0_right) ;
      first (by apply Hstar) ; clear Hstar.
    apply KS_Seq2.
    Admitted.

  Lemma seq_assoc_in_CS:
  forall C s mem mem' k e1 e2 e3 arg evs,
    (* If we can go from e1 to e3 ("legal" expressions) *)
    (* Star *) Plus sem [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
             [State C, s, mem', k, e3, arg] <->
            (* then the sequencing doesn't matter, we have ((e1;e2); e3) <-> (e1;(e2;e3)) *)
    (* Star *) Plus sem [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
                    [State C, s, mem', k, e3, arg].

    (* step kstep (prepare_global_env p) [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs *)
    (*      [State C, s, mem', k, e3, arg] <-> *)
    (* step kstep (prepare_global_env p) [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs *)
    (*      [State C, s, mem', k, e3, arg]. *)

  (*   (* NB : no need to have different `s` or `arg` since we sequence expressions in the same stack frame (if we make a function call, we should return from it before ending the sequence) *) *)
Proof.
  split ; intro Dir1.
  (* - (* -> *) *)
  (*   eapply plus_trans. *)
  (*   eapply plus_trans in Dir1. *)
  (*   eapply plus_trans ; [|eapply seq_assoc_in_CS_aux_common |]. *)
  (*    apply seq_trans_in_CS_aux_left_seq. *)
  (*   eapply (plus_trans seq_trans_in_CS_aux_left_seq seq_trans_in_CS_aux_common). *)
  (* - (* <- *) *)
  (*   inversion Dir1 as [? ? ? ? ? ? Hstep Hstar (* ... *)] ; subst. *)
  (*   inversion Hstep ; subst. *)
  (*   eapply plus_trans. repeat econstructor. 2: by rewrite !E0_left. *)
  (*   eapply plus_trans. repeat econstructor. 2: by rewrite !E0_left. *)
  (*   induction e1. *)
  (*   + eapply plus_trans. *)
  (*   (* have: Kseq e2 (Kseq e3 k) = Kseq (E_seq e2 e3) k. *) *)
  (*   (* induction e1 => //. *) *)
  (*   (* eapply plus_left'. *) *)
  (*   apply star_inv in Hstar ; destruct Hstar as [[HcontraState ?] | Hstar] ; subst. *)
  (*   + inversion HcontraState ; subst. *)
  (*   (* inversion Hstar ; subst. *) *)
  (*   + (* Dead-end, cannot have star_refl *) *)
  (*     admit. *)
  (*   + *)
  (*   (* econstructor. constructor. econstructor. constructor. econstructor. *) *)
  (*   repeat econstructor ; last rewrite !E0_left E0_right. *)
  (*   (* inversion Hstep ; subst. *) *)
  (*   induction e1 => //=. *)
  (*   +  apply KS_Seq2. *)

  (*   ; simpl in Dir1, Hstep, Hstar. *)
  (* econstructor. *)
Admitted.

End Semantics.

End CS.

Notation "[ 'CState' C , stk , mem , k , e , arg ]" :=
  (CS.State C stk mem k e arg)
  (at level 0, format "[ 'CState'  C ,  stk ,  mem ,  k ,  e ,  arg ]").

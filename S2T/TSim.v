(** * Stage 4, part 13 — [match_states] and the step diagram at T.

    See plan-i2t-redo.md §4 (Stage 4).

    Port of `S2I/Simulation.v:482` (`match_states`), `:5760` (`val_consume`),
    `:6044` (`step_diagram_expr`) and `:6190` (`step_diagram`). This is the
    ROUTING layer: every case is "read off which source rule fired, hand the
    matching diagram its invariant, and repackage the result". No new content
    about the machine — all of that is in `TDiagram`.

    Two things differ from the I version, and both are inherited rather than
    new:

    - the target state is `(mem, regs, pc, pct)` — there is no `gps`, the call
      stack having been replaced by the spilled chain `Sl` inside the
      invariant;
    - `rtag` is pinned to `InternalJump` throughout (a procedure BODY is always
      entered by an `IJal`), so the constructors do not quantify over it.

    `measure` and the `measure_descend_*` arithmetic are reused verbatim from
    `S2I/Simulation.v`: they are statements about SOURCE states only. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TStack.
Require Import S2T.TInject.
Require Import S2T.TLabel.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.
Require Import S2T.TMatch.
Require Import S2T.TDrain.
Require Import S2T.TLeaf.
Require Import S2T.TProlog.
Require Import S2T.TDiagram.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import zify.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TSim.

Notation icode := Intermediate.Machine.code.

Section WithProgram.

Variable cde : Transitional.code.
Variable iface : Program.interface.
Variable labelsP : NMap (NMap label).

Local Notation expr_inv := (TMatch.expr_inv cde iface labelsP).
Local Notation val_inv := (TMatch.val_inv cde iface labelsP).

(** The relation. `MS_start` is deliberately absent: the initial state needs
    the COMPILED program (Stage 5's job), and everything below is stated over
    the abstract `cde`/`iface`/`labelsP` triple. *)
Variant match_states : S.CS.state -> TS.state -> Prop :=
| MS_expr : forall a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb prot
                   temps plm c rest s1 s2 cap,
    expr_inv a scrs C stk mem k e arg ret InternalJump Sl tmem tregs pct pc fb
             prot temps plm c rest s1 s2 cap ->
    (forall v, e = E_val v -> k = Kstop -> stk <> [::]) ->
    match_states (S.CS.State C stk mem k e arg) (tmem, tregs, pc, pct)
| MS_val : forall a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb prot
                  temps plm rest cap,
    val_inv a scrs C stk mem k v arg ret InternalJump Sl tmem tregs pct pc fb
            prot temps plm rest cap ->
    (k = Kstop -> stk <> [::]) ->
    match_states (S.CS.State C stk mem k (E_val v) arg) (tmem, tregs, pc, pct)
| MS_halted : forall a C mem e arg tmem tregs pct pc i tni,
    TInject.minj a mem tmem ->
    Transitional.executing cde pc i tni (Pointer.component pc) ->
    i = Transitional.TrHalt ->
    (* ★ [E_val v] OR [E_exit]. Both are stuck at the source and both make
       [compile_proc] emit main's HALT PAD, so both are matched by a target
       sitting on an [IHalt] — and [E_exit] has no other constructor to fall
       into, [expr_inv] being unavailable before the frame exists. *)
    immediately_final e = true ->
    match_states (S.CS.State C [::] mem Kstop e arg)
                 (tmem, tregs, pc, pct).

(* ================================================================== *)
(* Stage 3's interface: where a call lands                             *)
(* ================================================================== *)

Variable p : Source.program.

Local Notation G := (Source.GlobalEnv.prepare_global_env p).

(** The two entry-resolution facts the call diagrams consume, gathered as
    named predicates so the routing lemmas can take them as ordinary premises.
    Stage 3 discharges both by computation on compiled programs; they are the
    T analogues of `S2I/SimCode.v:1637` (`compiled_jal_resolution`) and of the
    entry-point lemmas behind it. *)
Definition entry_int : Prop :=
  forall C P P_expr plm tl,
    Source.find_procedure (Source.GlobalEnv.genv_procedures G) C P
      = Some P_expr ->
    getm labelsP C = Some plm ->
    getm plm P = Some tl ->
    exists pcE sA sB cbody,
      [/\ Pointer.component pcE = C,
          compile_expr C (lbp C) (scr C) plm P_expr sA = Some (cbody, sB)
        & TMacros.code_at_I cde C pcE
            ([:: ILabel tl; IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                 IAlloc R_SP R_SP]
             ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
             ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].

(** ★ The IMPORT premise is not decoration: `entry_ext`'s conclusion carries
    the LRC `check_pc_call` — "C is allowed to call Cf.P" — and no amount of
    well-formedness turns "Cf has a procedure P" into that. The fact is
    available wherever this is used: `Source/CS.v`'s `KS_ExternalCall` carries
    it as a premise of the source step. *)
Definition entry_ext : Prop :=
  forall C Cf P P_expr,
    C <> Cf ->
    imported_procedure (Source.GlobalEnv.genv_interface G) C Cf P ->
    Source.find_procedure (Source.GlobalEnv.genv_procedures G) Cf P
      = Some P_expr ->
    Cf \in domm iface /\
    exists pcW tniW plmf plf pcE sA sB cbody,
      [/\ [/\ Transitional.find_plabel_in_code cde Cf P = Some pcW,
              Transitional.executing cde pcW
                (Transitional.TrLabel (inr (Cf, P))) tniW Cf,
              Transitional.check_pc_call C tniW P
            & getm labelsP Cf = Some plmf],
          (* ★ EITHER wrapper: `(main, main)` gets `compile_proc`'s DUAL entry *)
          (TMacros.code_at_I cde Cf (Pointer.inc pcW)
             (IConst (IInt 1) R_ONE
              :: [:: IMov R_SP R_AUX1;
                     IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                     IAlloc R_SP R_SP]
                 ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
                 ++ push R_RA
                 ++ IJal plf
                    :: pop R_RA ++ pop R_AUX1
                       ++ store_arg (scr Cf) R_AUX1 R_AUX2
                       ++ pop R_SP ++ [:: IReturn])
           \/ (Cf = Component.main /\ exists lmain lret,
                 TMacros.code_at_I cde Cf (Pointer.inc pcW)
                   (IConst (IInt 1) R_ONE
                    :: [:: IMov R_SP R_AUX1;
                           IConst (IInt (Z.of_nat (4 + stack_need P_expr)))
                             R_SP;
                           IAlloc R_SP R_SP]
                       ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1
                       ++ push R_AUX1 ++ push R_RA
                       ++ [:: IConst (IPtr (flag_buf_ptr (scr Cf))) R_AUX1;
                              ILoad R_AUX1 R_AUX2]
                       ++ push R_AUX2
                       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                              ILabel lmain; IConst (IInt 1) R_AUX2;
                              IStore R_AUX1 R_AUX2]
                       ++ IJal plf
                          :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                             ++ store_arg (scr Cf) R_AUX1 R_AUX2
                             ++ pop R_SP
                             ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                    IReturn]))
           \/ (Cf = Component.main /\ P = Procedure.main /\ exists tl,
                 TMacros.code_at_I cde Cf (Pointer.inc pcW) (IHalt :: tl))),
          Pointer.component pcE = Cf,
          compile_expr Cf (lbp Cf) (scr Cf) plmf P_expr sA = Some (cbody, sB)
        & TMacros.code_at_I cde Cf pcE
            ([:: ILabel plf; IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                 IAlloc R_SP R_SP]
             ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
             ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].

(** The two bridges into [MS_halted]: an invariant sitting on a FINAL source
    state is matched by a target run onto main's `IHalt`. `diagram_halt` does
    the running; these just repackage it, and the expression-side one first
    spends the leaf's `IConst`. *)
Lemma halted_of_val a scrs C mem v arg ret Sl tmem tregs pct pc fb prot
      temps plm rest cap :
  val_inv a scrs C [::] mem Kstop v arg ret InternalJump Sl tmem tregs pct pc
          fb prot temps plm rest cap ->
  exists ts', plus TS.step cde (tmem, tregs, pc, pct) E0 ts'
              /\ match_states (S.CS.State C [::] mem Kstop (E_val v) arg) ts'.
Proof.
  move=> HI. case: (TDiagram.diagram_halt HI)
    => [tmem' [tregs' [pcH [Ph Hmj [tg [c Hex]]]]]].
  exists (tmem', tregs', pcH, pct). split; first exact: Ph.
  have Ec : Pointer.component pcH = c
    by case: Hex => [C_code [E _]]; exact: E.
  by apply: (@MS_halted a C mem (E_val v) arg tmem' tregs' pct pcH
               Transitional.TrHalt tg) => //; rewrite Ec.
Qed.

Lemma halted_of_expr a scrs C mem v arg ret Sl tmem tregs pct pc fb prot
      temps plm c0 rest s1 s2 cap :
  expr_inv a scrs C [::] mem Kstop (E_val v) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c0 rest s1 s2 cap ->
  exists ts', plus TS.step cde (tmem, tregs, pc, pct) E0 ts'
              /\ match_states (S.CS.State C [::] mem Kstop (E_val v) arg) ts'.
Proof.
  move=> HI. case: (TLeaf.leaf_val_run HI) => [i [Ev S0 Hval]].
  case: (halted_of_val Hval) => [ts' [Ph Hm]].
  exists ts'. split; last exact: Hm.
  eapply plus_left with (t1 := E0) (t2 := E0);
    [exact: S0 | exact: (plus_star Ph) | by []].
Qed.

(* ================================================================== *)
(* Consuming a value: the ten-way dispatch on the continuation         *)
(* ================================================================== *)

Lemma val_consume a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb prot
      temps plm rest cap t s1' :
  entry_int -> entry_ext ->
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  S.CS.kstep G (S.CS.State C stk mem k (E_val v) arg) t s1' ->
  val_inv a scrs C stk mem k v arg ret InternalJump Sl tmem tregs pct pc fb
          prot temps plm rest cap ->
  (* the RESULT is not a halted state — the only states this routing layer
     does not cover, and the ones `MS_halted` is for. Discharged at the top
     level by main's halt pad. *)
  (forall v0, S.CS.s_expr s1' = E_val v0 -> S.CS.s_cont s1' = Kstop ->
     S.CS.s_stack s1' <> [::]) ->
  (exists ts', plus TS.step cde (tmem, tregs, pc, pct) t ts'
               /\ match_states s1' ts')
  \/ [/\ measure s1' < measure (S.CS.State C stk mem k (E_val v) arg),
         t = E0
       & match_states s1' (tmem, tregs, pc, pct)].
Proof.
  move=> Hei Hee Hdomm Hstep HI Hnf.
  inversion Hstep; subst.
  - (* KS_Binop2 : Kbinop1 -> Kbinop2 *)
    case: (TDiagram.diagram_binop2 HI)
      => [pcF [tmem' [tregs' [cd [rest' [sA [sB [Pl Hinv]]]]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_BinopEval : Kbinop2 -> the value *)
    case: (TDiagram.diagram_binop_eval HI)
      => [tmem' [tregs' [pcF [rest' [temps' [Pl Hinv]]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
  - (* KS_Seq2 : Kseq -> the second expression *)
    case: (TDiagram.diagram_seq2 HI)
      => [pc' [c2 [rest' [sA [sB [Sd Hor Hinv]]]]]].
    case: Hor => [Epc|Pl].
    + right. split.
      * rewrite /measure /=. lia.
      * by [].
      * rewrite -Epc. by apply: MS_expr Hinv _; exact: Hnf.
    + left. exists (tmem, tregs, pc', pct). split; first exact: Pl.
      by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_If2 : Kif -> the branch the source took.
       [case: ifP] rather than a hand-written [i != 0]: the [Z] eqType
       instance that makes `Source/CS.v`'s notation elaborate is not in scope
       here, but the term already in the goal carries it. *)
    move: Hnf; case: ifP => Hib Hnf.
    + case: (TDiagram.diagram_if2 (e := e2) HI
               (or_introl (conj (ltac:(by move: Hib => /eqP) : i <> 0%Z)
                                (erefl e2))))
        => [pcF [cd [rest' [sA [sB [Pl Hinv]]]]]].
      left. exists (tmem, tregs, pcF, pct). split; first exact: Pl.
      by apply: MS_expr Hinv _; exact: Hnf.
    + case: (TDiagram.diagram_if2 (e := e3) HI
               (or_intror (conj (ltac:(by move: Hib => /negbFE /eqP)
                                 : i = 0%Z) (erefl e3))))
        => [pcF [cd [rest' [sA [sB [Pl Hinv]]]]]].
      left. exists (tmem, tregs, pcF, pct). split; first exact: Pl.
      by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_AllocEval. [Memory.alloc] always hands back offset 0 in the
       component it was asked for; the source rule keeps its [ptr] abstract,
       so the shape has to be read back off the definition. *)
    have Ha : Common.Memory.Memory.alloc mem C (Z.to_nat size)
            = Some (mem', ptr) by eassumption.
    have [bs Eptr] : exists bs, ptr = (C, bs, 0%Z).
    { move: Ha. rewrite /Common.Memory.Memory.alloc.
      case: (mem C) => [memC|] //.
      case: (Common.Memory.ComponentMemory.alloc memC (Z.to_nat size))
        => [memC' b]. by move=> [_ <-]; exists b. }
    subst ptr.
    case: (TDiagram.diagram_alloc_eval HI ltac:(eassumption) Ha)
      => [a' [tmem' [tregs' [pcF [rest' [Pl Hinv]]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
  - (* KS_DerefEval *)
    case: (TDiagram.diagram_deref_eval HI ltac:(eassumption))
      => [tmem' [tregs' [pcF [rest' [Pl Hinv]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
  - (* KS_Assign2 : Kassign1 -> the address expression *)
    case: (TDiagram.diagram_assign2 HI)
      => [pcF [tmem' [tregs' [cd [rest' [sA [sB [Pl Hinv]]]]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_AssignEval *)
    case: (TDiagram.diagram_assign_eval HI ltac:(eassumption))
      => [tmem' [tregs' [pcF [rest' [temps' [Pl Hinv]]]]]].
    left. exists (tmem', tregs', pcF, pct). split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
  - (* KS_InternalCall — the callee's body, on a fresh frame *)
    case: (TDiagram.diagram_call_int HI
             (fun tl Htl =>
                Hei _ _ _ _ tl ltac:(eassumption) (TMatch.vi_plm HI) Htl))
      => [tmem5 [tregs5 [pcF [c1 [rest1 [sA [sB [fbN [retN [Sl1
         [Pl Hinv]]]]]]]]]]].
    left. exists (tmem5, tregs5, pcF, pct). split; first exact: Pl.
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_ExternalCall — the callee's WRAPPER, then its body *)
    have HneC : C <> C' by eassumption.
    case: (Hee _ _ _ _ HneC ltac:(eassumption) ltac:(eassumption))
      => [HdomF Hres].
    case: (TDiagram.diagram_call_ext HI HneC HdomF Hres)
      => [scrs1 [tmem5 [tregs5 [pcF [c1 [rest1 [sA [sB [fbN [prot1
         [plmf [retN [Sl1 [Pl Hinv]]]]]]]]]]]]]].
    left. exists (tmem5, tregs5, pcF, inc_pc_tag pct).
    split; first exact: Pl.
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* KS_InternalReturn *)
    case: (TDiagram.diagram_return_int HI)
      => [tmem1 [tregs1 [pcF [rest' [temps' [fb' [prot' [cap' [ret'
         [Sl' [Pl Hinv]]]]]]]]]]].
    left. exists (tmem1, tregs1, pcF, pct). split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
  - (* KS_ExternalReturn *)
    have Huniq : TDrain.labels_uniq cde C
      by move=> l0 C_code Hg; exact: (TMatch.vi_uniq HI l0 Hg).
    have HneR : C <> C' by eassumption.
    case: (TDiagram.diagram_return_ext HI HneR Huniq Hdomm)
      => [scrs1 [tmem1 [tregs1 [pcF [rest1 [temps1 [fb1 [prot1 [cap1
         [plm1 [ret1 [Sl1 [Pl Hinv]]]]]]]]]]]]].
    left. exists (tmem1, tregs1, pcF, dec_pc_tag pct).
    split; first exact: Pl.
    apply: MS_val Hinv _. exact: (Hnf _ erefl).
Qed.

(* ================================================================== *)
(* Evaluating an expression: the eleven-way dispatch                   *)
(* ================================================================== *)

(** The mirror of [val_consume], on the expression side. Three shapes:

    - the LEAVES ([E_val] / [E_arg] / [E_local]) take one target step and hand
      over — [E_val] to [val_consume], the other two straight to [MS_val];
    - the COMPOUNDS descend, and the target does nothing at all: those are the
      stutter branches, paid for by [measure];
    - [E_exit] has no source step, so the case is vacuous. *)
Lemma step_diagram_expr a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap t s1' :
  entry_int -> entry_ext ->
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  S.CS.kstep G (S.CS.State C stk mem k e arg) t s1' ->
  expr_inv a scrs C stk mem k e arg ret InternalJump Sl tmem tregs pct pc fb
           prot temps plm c rest s1 s2 cap ->
  (forall v0, S.CS.s_expr s1' = E_val v0 -> S.CS.s_cont s1' = Kstop ->
     S.CS.s_stack s1' <> [::]) ->
  (exists ts', plus TS.step cde (tmem, tregs, pc, pct) t ts'
               /\ match_states s1' ts')
  \/ [/\ measure s1' < measure (S.CS.State C stk mem k e arg), t = E0
       & match_states s1' (tmem, tregs, pc, pct)].
Proof.
  move=> Hei Hee Hdomm Hstep HI Hnf.
  case: e HI Hstep
    => [v|| |op e1 e2|e1 e2|e1 e2 e3|e1|e1|e1 e2|C' P' e1|] HI Hstep.
  - (* E_val — one [IConst], then consume the value *)
    case: (TLeaf.leaf_val_run HI) => [i [Ev S0 Hval]].
    case: (val_consume Hei Hee Hdomm Hstep Hval Hnf)
      => [[ts' [P2 Hm2]]|[Hme Ht Hm2]].
    + left. exists ts'. split; last exact: Hm2.
      eapply plus_left with (t1 := E0) (t2 := t);
        [exact: S0 | exact: (plus_star P2) | by []].
    + left. eexists. split; last exact: Hm2.
      rewrite Ht. exact: plus_one S0.
  - (* E_arg *)
    case: (TLeaf.leaf_arg_run HI) => [S0 Hval].
    inversion Hstep; subst.
    left. eexists. split; first exact: plus_one S0.
    apply: MS_val Hval _. exact: (Hnf _ erefl).
  - (* E_local *)
    case: (TLeaf.leaf_local_run HI) => [S0 Hval].
    inversion Hstep; subst.
    left. eexists. split; first exact: plus_one S0.
    apply: MS_val Hval _. exact: (Hnf _ erefl).
  - (* E_binop — descend into [e1] *)
    inversion Hstep; subst.
    case: (TDiagram.descend_binop HI) => [c1 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_seq *)
    inversion Hstep; subst.
    case: (TDiagram.descend_seq HI) => [c1 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_if *)
    inversion Hstep; subst.
    case: (TDiagram.descend_if HI) => [c1 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_alloc *)
    inversion Hstep; subst.
    case: (TDiagram.descend_alloc HI) => [c1 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_deref *)
    inversion Hstep; subst.
    case: (TDiagram.descend_deref HI) => [c1 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_assign — the VALUE is evaluated first *)
    inversion Hstep; subst.
    case: (TDiagram.descend_assign HI) => [c2 [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_call *)
    inversion Hstep; subst.
    case: (TDiagram.descend_call HI) => [ce [rest' [sA [sB Hinv]]]].
    right. split; [by rewrite /measure /=; lia | by [] | ].
    by apply: MS_expr Hinv _; exact: Hnf.
  - (* E_exit — the source is stuck *)
    by inversion Hstep.
Qed.

(* ================================================================== *)
(* The step diagram                                                    *)
(* ================================================================== *)

(** Source steps map to target `plus` steps, except for the administrative
    descends, which stutter against a decreasing `measure` — the shape
    `forward_simulation_star` wants.

    `MS_halted` needs no case: its source state is a value under `Kstop` with
    an empty stack, and no source rule fires there. *)
Lemma step_diagram s1 t s1' :
  entry_int -> entry_ext ->
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  S.CS.kstep G s1 t s1' ->
  forall ts, match_states s1 ts ->
  (forall v0, S.CS.s_expr s1' = E_val v0 -> S.CS.s_cont s1' = Kstop ->
     S.CS.s_stack s1' <> [::]) ->
  (exists ts', plus TS.step cde ts t ts' /\ match_states s1' ts')
  \/ [/\ measure s1' < measure s1, t = E0 & match_states s1' ts].
Proof.
  move=> Hei Hee Hdomm Hstep ts Hmatch.
  move: Hstep. case: s1 ts / Hmatch.
  - (* MS_expr *)
    move=> a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb prot temps plm
           c0 rest0 sA0 sB0 cap Hinv _ Hstep Hnf.
    exact: (step_diagram_expr Hei Hee Hdomm Hstep Hinv Hnf).
  - (* MS_val *)
    move=> a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb prot temps plm
           rest0 cap Hinv _ Hstep Hnf.
    exact: (val_consume Hei Hee Hdomm Hstep Hinv Hnf).
  - (* MS_halted — the source is stuck *)
    move=> a C mem e arg tmem tregs pct pc i tni _ _ _ Hif Hstep _.
    by move: Hstep; case: e Hif => [v||||||||||] //= _ Hstep; inversion Hstep.
Qed.

(* ================================================================== *)
(* Landing on a final state                                            *)
(* ================================================================== *)

(** The dispatch for the one case `step_diagram` cannot cover: the source step
    lands on a FINAL state, so the target must not stop at the matching
    invariant but run on to main's `IHalt`. Most rules are vacuous here — a
    result whose continuation is `Kbinop2`, or whose stack has just gained a
    frame, is not final — and the rest hand their invariant to one of the two
    bridges. *)
Lemma halt_of_val_step a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb
      prot temps plm rest cap t s1' :
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  S.CS.kstep G (S.CS.State C stk mem k (E_val v) arg) t s1' ->
  val_inv a scrs C stk mem k v arg ret InternalJump Sl tmem tregs pct pc fb
          prot temps plm rest cap ->
  (exists v0, S.CS.s_expr s1' = E_val v0 /\ S.CS.s_cont s1' = Kstop
              /\ S.CS.s_stack s1' = [::]) ->
  exists ts', plus TS.step cde (tmem, tregs, pc, pct) t ts'
              /\ match_states s1' ts'.
Proof.
  move=> Hdomm Hstep HI Hfin.
  inversion Hstep; subst.
  - (* KS_Binop2 *) by case: Hfin => [vf [_ [E _]]].
  - (* KS_BinopEval *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    case: (TDiagram.diagram_binop_eval HI)
      => [tmem' [tregs' [pcF [rest' [temps' [Pl Hinv]]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
    exact: Ph.
  - (* KS_Seq2 *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    case: (TDiagram.diagram_seq2 HI)
      => [pc' [c2 [rest' [sA [sB [Sd _ Hinv]]]]]].
    case: (halted_of_expr Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply star_plus_trans with (t1 := E0) (t2 := E0);
      [exact: Sd | exact: Ph | by []].
  - (* KS_If2 *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    move: HI Ev; case: ifP => Hib HI Ev.
    + case: (TDiagram.diagram_if2 (e := e2) HI
               (or_introl (conj (ltac:(by move: Hib => /eqP) : i <> 0%Z)
                                (erefl e2))))
        => [pcF [cd [rest' [sA [sB [Pl Hinv]]]]]].
      move: Hinv; rewrite Ev => Hinv.
      case: (halted_of_expr Hinv) => [ts' [Ph Hm]].
      exists ts'. split; last exact: Hm.
      eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
      exact: Ph.
    + case: (TDiagram.diagram_if2 (e := e3) HI
               (or_intror (conj (ltac:(by move: Hib => /negbFE /eqP)
                                 : i = 0%Z) (erefl e3))))
        => [pcF [cd [rest' [sA [sB [Pl Hinv]]]]]].
      move: Hinv; rewrite Ev => Hinv.
      case: (halted_of_expr Hinv) => [ts' [Ph Hm]].
      exists ts'. split; last exact: Hm.
      eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
      exact: Ph.
  - (* KS_AllocEval *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    have Ha : Common.Memory.Memory.alloc mem C (Z.to_nat size)
            = Some (mem', ptr) by eassumption.
    have [bs Eptr] : exists bs, ptr = (C, bs, 0%Z).
    { move: Ha. rewrite /Common.Memory.Memory.alloc.
      case: (mem C) => [memC|] //.
      case: (Common.Memory.ComponentMemory.alloc memC (Z.to_nat size))
        => [memC' b]. by move=> [_ <-]; exists b. }
    subst ptr.
    case: (TDiagram.diagram_alloc_eval HI ltac:(eassumption) Ha)
      => [a' [tmem' [tregs' [pcF [rest' [Pl Hinv]]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
    exact: Ph.
  - (* KS_DerefEval *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    case: (TDiagram.diagram_deref_eval HI ltac:(eassumption))
      => [tmem' [tregs' [pcF [rest' [Pl Hinv]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
    exact: Ph.
  - (* KS_Assign2 *) by case: Hfin => [vf [_ [E _]]].
  - (* KS_AssignEval *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    case: (TDiagram.diagram_assign_eval HI ltac:(eassumption))
      => [tmem' [tregs' [pcF [rest' [temps' [Pl Hinv]]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
    exact: Ph.
  - (* KS_InternalCall — the stack GAINS a frame *)
    by case: Hfin => [vf [_ [_ E]]].
  - (* KS_ExternalCall *) by case: Hfin => [vf [_ [_ E]]].
  - (* KS_InternalReturn *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    case: (TDiagram.diagram_return_int HI)
      => [tmem1 [tregs1 [pcF [rest' [temps' [fb' [prot' [cap' [ret'
         [Sl' [Pl Hinv]]]]]]]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pl | | by []].
    exact: Ph.
  - (* KS_ExternalReturn *)
    case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
    have Huniq : TDrain.labels_uniq cde C
      by move=> l0 C_code Hg; exact: (TMatch.vi_uniq HI l0 Hg).
    have HneR : C <> C' by eassumption.
    case: (TDiagram.diagram_return_ext HI HneR Huniq Hdomm)
      => [scrs1 [tmem1 [tregs1 [pcF [rest1 [temps1 [fb1 [prot1 [cap1
         [plm1 [ret1 [Sl1 [Pl Hinv]]]]]]]]]]]]].
    case: (halted_of_val Hinv) => [ts' [Ph Hm]].
    exists ts'. split; last exact: Hm.
    eapply plus_trans with (t2 := E0);
      [exact: Pl | exact: Ph | by rewrite E0_right].
Qed.

(* ================================================================== *)
(* Stage 5 — the semantics record, and the forward simulation          *)
(* ================================================================== *)

Variable tp : Intermediate.program.

(** The T machine as a CompCert `semantics`. Initial states are STAR-CLOSED —
    the base state up to silent setup steps — which is the standard way to let
    the target run its entry sequence before the relation has to hold. *)
Definition t_initial_base (S : TS.state) : Prop :=
  exists pc,
    Transitional.find_plabel_in_code cde Component.main Procedure.main
      = Some pc
    /\ S = (Transitional.Memory.prepare_procedures_initial_memory tp,
            Transitional.Register.init, pc, Level 0).

Definition t_initial (S : TS.state) : Prop :=
  exists S0, t_initial_base S0 /\ star TS.step cde S0 E0 S.

Definition t_final (S : TS.state) : Prop :=
  exists tg c,
    Transitional.executing cde (let: (_, _, pc, _) := S in pc)
      Transitional.TrHalt tg c.

Definition t_sem : semantics :=
  @Semantics_gen TS.state Transitional.code TS.step t_initial t_final cde.

(** The two facts Stage 5 still owes, named so the packaging can be proved
    against them: the INITIAL bridge (the target's setup run reaches a state
    matching the source's initial one) and the HALT case (a source step that
    lands on a final state is matched by a target run onto main's `IHalt`).
    Both are about the compiled program specifically, which is why they are
    not part of Stage 4's abstract development. *)
Definition start_ok : Prop :=
  forall s1, S.CS.initial_state p s1 ->
    exists s2, t_initial s2 /\ match_states s1 s2.

Definition halt_ok : Prop :=
  forall s1 t s1', S.CS.kstep G s1 t s1' ->
    forall ts, match_states s1 ts ->
    (exists v0, S.CS.s_expr s1' = E_val v0 /\ S.CS.s_cont s1' = Kstop
                /\ S.CS.s_stack s1' = [::]) ->
    exists ts', plus TS.step cde ts t ts' /\ match_states s1' ts'.

Theorem halt_ok_proof :
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  halt_ok.
Proof.
  move=> Hdomm s1 t s1' Hstep ts Hm. move: Hstep. case: s1 ts / Hm.
  - (* MS_expr *)
    move=> a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb prot temps plm
           c0 rest0 sA0 sB0 cap Hinv Hnf0 Hstep Hfin.
    move: Hnf0. case: e Hinv Hstep
      => [v|| |op e1 e2|e1 e2|e1 e2 e3|e1|e1|e1 e2|C' P' e1|] Hinv Hstep _.
    + (* E_val — spend the leaf, then dispatch *)
      case: (TLeaf.leaf_val_run Hinv) => [i [Ev S0 Hval]].
      case: (halt_of_val_step Hdomm Hstep Hval Hfin) => [ts' [Ph Hm']].
      exists ts'. split; last exact: Hm'.
      eapply plus_left with (t1 := E0) (t2 := t);
        [exact: S0 | exact: (plus_star Ph) | by []].
    + (* E_arg *)
      case: (TLeaf.leaf_arg_run Hinv) => [S0 Hval].
      inversion Hstep; subst.
      case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
      case: (halted_of_val Hval) => [ts' [Ph Hm']].
      exists ts'. split; last exact: Hm'.
      eapply plus_left with (t1 := E0) (t2 := E0);
        [exact: S0 | exact: (plus_star Ph) | by []].
    + (* E_local *)
      case: (TLeaf.leaf_local_run Hinv) => [S0 Hval].
      inversion Hstep; subst.
      case: Hfin => [vf [Ev [Ek Es]]]. move: Ev Ek Es => /= Ev Ek Es. subst.
      case: (halted_of_val Hval) => [ts' [Ph Hm']].
      exists ts'. split; last exact: Hm'.
      eapply plus_left with (t1 := E0) (t2 := E0);
        [exact: S0 | exact: (plus_star Ph) | by []].
    (* every descend leaves a non-[Kstop] continuation *)
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep; subst; case: Hfin => [vf [_ [E _]]].
    + by inversion Hstep.
  - (* MS_val *)
    move=> a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb prot temps plm
           rest0 cap Hinv Hnf0 Hstep Hfin.
    exact: (halt_of_val_step Hdomm Hstep Hinv Hfin).
  - (* MS_halted — the source is stuck *)
    move=> a C mem e arg tmem tregs pct pc i tni _ _ _ Hif Hstep _.
    by move: Hstep; case: e Hif => [v||||||||||] //= _ Hstep; inversion Hstep.
Qed.


(** A source state either IS about to be final or provably is not — no
    classical reasoning needed, the shape is decidable by inspection. *)
Lemma final_or_not (s : S.CS.state) :
  (exists v0, S.CS.s_expr s = E_val v0 /\ S.CS.s_cont s = Kstop
              /\ S.CS.s_stack s = [::])
  \/ (forall v0, S.CS.s_expr s = E_val v0 -> S.CS.s_cont s = Kstop ->
        S.CS.s_stack s <> [::]).
Proof.
  case: s => [C0 stk0 mem0 k0 e0 arg0] /=.
  case: e0 => [v0||||||||||]; try by right.
  case: k0; try by right.
  case: stk0 => [|f stk1]; last by right.
  by left; exists v0.
Qed.

Theorem t_forward_simulation :
  entry_int -> entry_ext ->
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  start_ok ->
  forward_simulation (S.CS.sem p) t_sem.
Proof.
  move=> Hei Hee Hdomm Hstart.
  have Hhalt := halt_ok_proof Hdomm.
  apply: (@forward_simulation_star (S.CS.sem p) t_sem match_states _ _ measure).
  - (* initial states *)
    exact: Hstart.
  - (* final states *)
    move=> s1 s2 Hm. case: s1 s2 / Hm.
    + (* MS_expr *)
      move=> a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb prot temps
             plm c0 rest0 sA0 sB0 cap Hinv Hnf0 /= Hfin.
      case: Hfin => [Ee|[v0 [Ee [Ek Es]]]]; last by case: (Hnf0 v0 Ee Ek).
      move: (TMatch.ei_comp Hinv) (TMatch.ei_code Hinv); rewrite Ee /=
        /Comp.ret => -[<- _] Hcode.
      by do 2!eexists; exact: (TMacros.code_at_I_head Hcode).
    + (* MS_val *)
      move=> a scrs C stk mem k v arg ret Sl tmem tregs pct pc fb prot temps
             plm rest0 cap Hinv Hnf0 /= Hfin.
      by case: Hfin => [//|[v0 [_ [Ek Es]]]]; case: (Hnf0 Ek).
    + (* MS_halted *)
      move=> a C mem e arg tmem tregs pct pc i tni Hmem Hex Ei _ _.
      by do 2!eexists; rewrite -Ei; exact: Hex.
  - (* the diagram *)
    move=> s1 t s1' Hstep s2 Hm.
    case: (final_or_not s1') => [Hfin|Hnfin].
    + left. exact: (Hhalt _ _ _ Hstep _ Hm Hfin).
    + case: (step_diagram Hei Hee Hdomm Hstep Hm Hnfin)
        => [[ts' [Pl Hm']]|[Hme Ht Hm']].
      * left. by exists ts'.
      * right. split; last split; [ | exact: Ht | exact: Hm'].
        by move: Hme; lia.
Qed.

End WithProgram.

End TSim.

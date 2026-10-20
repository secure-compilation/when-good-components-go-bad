Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Source.Language.
Require Import Source.Definability.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import Common.Traces.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import MicroPolicies.Recomposition.TraceInit.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.
Import Symbolic.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

Lemma rub_single_events : forall (NCv : nat) pI cI (W : program),
  single_events (rub_sem NCv pI cI W).
Proof.
  move=> NCv pI cI W s t s' Hstep.
  have H := rub_step_mp Hstep. clear Hstep. move: H.
  rewrite /prog_step_mp. case: t => [|e [|??]] //= _; by lia.
Qed.

Lemma rub_prefix_star : forall (NCv : nat) pI cI (W : program) m,
  does_prefix (rub_sem NCv pI cI W) m ->
  not_wrong_finpref m ->
  exists cs cs',
    Smallstep.initial_state (rub_sem NCv pI cI W) cs /\
    Star (rub_sem NCv pI cI W) cs (finpref_trace m) cs'.
Proof.
  move=> NCv pI cI W m [b [Hbeh Hpre]] Hnw.
  case: b / Hbeh Hpre.
  - move=> cs beh Hcs Hbeh Hpre.
    case: m Hpre Hnw => [t0|t0|t0] /= Hpre Hnw.
    + case: beh / Hbeh Hpre => //= t cs' Hstar Hfinal -> {t0}.
      by exists cs, cs'; split.
    + by [].
    + destruct Hpre as [beh' ?]; subst beh.
      have [cs' [Hstar Hbehaves]] :=
        state_behaves_app_inv (@rub_single_events NCv pI cI W) t0 beh' Hbeh.
      by exists cs, cs'; split.
  -
    move=> Hnoinit _.
    by have := Hnoinit _
      (erefl (Merged.initial_state (code W) (prog_buffers W) (prog_interface W))).
Qed.

Lemma compilation_buffers :
  forall p pc, compile_program p = Some pc ->
    Intermediate.prog_buffers pc = gen_buffers (Source.prog_buffers p).
Proof.
  intros p pc Hcompile.
  unfold compile_program, Compiler.run in Hcompile.
  simpl in Hcompile. unfold Comp.bind in Hcompile.
  destruct (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    as [[labels cenv1]|] eqn:Hlabs;
    try discriminate.
  destruct (compile_components (gen_buffers (Source.prog_buffers p)) labels
                               (elementsm (Source.prog_procedures p)) cenv1)
    as [[code cenv2]|] eqn:Hcompiled_comps;
    try discriminate.
  simpl in Hcompile.
  inversion Hcompile.
  reflexivity.
Qed.

Lemma size_lengthE (T : Type) (l : seq T) : length l = size l.
Proof. by elim: l => //= x l ->. Qed.

Definition block0_sizes
    (bufs : NMap {fmap Values.Block.id -> nat + seq Values.value}) : NMap nat :=
  mapm (fun bm => odflt 1 (omap bsize (getm bm (0 : Values.Block.id)))) bufs.

Definition bt_bufsz (a b : Intermediate.program) : NMap nat :=
  unionm (block0_sizes (Intermediate.prog_buffers a))
         (block0_sizes (Intermediate.prog_buffers b)).

Definition bt_back (a b : Intermediate.program) (t : Events.trace)
    : Source.program :=
  Definability.program_of_trace
    (unionm (Intermediate.prog_interface a) (Intermediate.prog_interface b))
    (bt_bufsz a b) t.

Definition bt_P'c (a b : Intermediate.program) (t : Events.trace)
    : Source.program :=
  Source.program_unlink (domm (Intermediate.prog_interface a)) (bt_back a b t).

Definition bt_Csc (a b : Intermediate.program) (t : Events.trace)
    : Source.program :=
  Source.program_unlink (domm (Intermediate.prog_interface b)) (bt_back a b t).

Definition lin_ok_at (L0 P0 C0 : nat) (x : Intermediate.program) : Prop :=
  [/\ (forall cid Cprocs,
         Intermediate.prog_procedures x cid = Some Cprocs ->
         exists Pid, Pid \in domm Cprocs),
      (forall C', Intermediate.prog_interface x C' ->
         has_required_local_buffers (compiler L0 P0 C0 (Intermediate.prog_buffers x)
                 (Intermediate.prog_interface x) x) C'),
      (forall cid Cprocs Pid Pcode l0,
         Intermediate.prog_procedures x cid = Some Cprocs ->
         Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L0),
      (forall cid Cprocs Pid,
         Intermediate.prog_procedures x cid = Some Cprocs ->
         Pid \in domm Cprocs -> Pid < P0)
    & (forall cid,
         cid \in domm (Intermediate.prog_interface x) -> cid < C0)].

Record bt_source_pack (a b : Intermediate.program) (m0 : finpref_behavior)
    (P' Cs : Source.program) (ip' ic' : Intermediate.program) : Prop := {
  btsp_wfP    : Source.well_formed_program P';
  btsp_wfCs   : Source.well_formed_program Cs;
  btsp_ifP    : Source.prog_interface P' = Intermediate.prog_interface a;
  btsp_ifCs   : Source.prog_interface Cs = Intermediate.prog_interface b;
  btsp_closed : Source.closed_program (Source.program_link P' Cs);
  btsp_mmP    : matching_mains P' a;
  btsp_mmCs   : matching_mains Cs b;
  btsp_run    : does_prefix (S.CS.sem (Source.program_link P' Cs)) m0;
  btsp_compP  : compile_program P' = Some ip';
  btsp_compCs : compile_program Cs = Some ic';
  btsp_wfip   : Intermediate.well_formed_program ip';
  btsp_wfic   : Intermediate.well_formed_program ic';
  btsp_ifip   : Intermediate.prog_interface ip' = Intermediate.prog_interface a;
  btsp_ific   : Intermediate.prog_interface ic' = Intermediate.prog_interface b;
  btsp_bufP   : forall C, C \in domm (Intermediate.prog_interface a) ->
                  Source.prog_buffers P' C
                  = Some (inr (nseq (Definability.buf_size (bt_bufsz a b) C)
                                    (Int 0)));
  btsp_bufCs  : forall C, C \in domm (Intermediate.prog_interface b) ->
                  Source.prog_buffers Cs C
                  = Some (inr (nseq (Definability.buf_size (bt_bufsz a b) C)
                                    (Int 0)));
  btsp_eqP    : P' = bt_P'c a b (finpref_trace m0);
  btsp_eqCs   : Cs = bt_Csc a b (finpref_trace m0)
}.

Section BTSourceHalfShapes.

  Variables (L0 P0 C0 : nat) (a b : Intermediate.program).
  Hypothesis Hwa : Intermediate.well_formed_program a.
  Hypothesis Hwb : Intermediate.well_formed_program b.
  Hypothesis Hlink : linkable (Intermediate.prog_interface a)
                              (Intermediate.prog_interface b).
  Hypothesis Hclosed : Intermediate.closed_program (Intermediate.program_link a b).

  Let PBW := unionm (Intermediate.prog_buffers a) (Intermediate.prog_buffers b).
  Let PIW := unionm (Intermediate.prog_interface a)
                    (Intermediate.prog_interface b).
  Let W := program_link (compiler L0 P0 C0 PBW PIW a)
                        (compiler L0 P0 C0 PBW PIW b).

  Theorem bt_source_half_shapes : forall (NCv : nat) (m0 : finpref_behavior),
    does_prefix (rub_sem NCv (Intermediate.prog_interface a)
                            (Intermediate.prog_interface b) W) m0 ->
    not_wrong_finpref m0 ->
    exists P' Cs ip' ic', bt_source_pack a b m0 P' Cs ip' ic'.
  Proof.
    move=> NCv m0 Hpre Hnw.
    have [cs [cs' [Hcs Hstar]]] := rub_prefix_star Hpre Hnw.
    have Hwft : well_formed_trace
        (unionm (Intermediate.prog_interface a) (Intermediate.prog_interface b))
        (finpref_trace m0).
    { apply: (lin_link_rub_trace_wf _ Hstar). exact: Hcs. }
    have [P' [Cs [Hif1 [Hif2 [Hmm1 [Hmm2 [HwfP [HwfC [Hscl [Hsrun [HbufP [HbufC [HeqP HeqC]]]]]]]]]]]]] :=
      @definability_with_linking_trace_bufs a b m0 (bt_bufsz a b)
        Hwa Hwb Hlink Hclosed Hwft Hnw.
    have [ip' Hip'] := well_formed_compilable _ HwfP.
    have [ic' Hic'] := well_formed_compilable _ HwfC.
    exists P', Cs, ip', ic'.
    constructor.
    - exact: HwfP.
    - exact: HwfC.
    - exact: Hif1.
    - exact: Hif2.
    - exact: Hscl.
    - exact: Hmm1.
    - exact: Hmm2.
    - exact: Hsrun.
    - exact: Hip'.
    - exact: Hic'.
    - exact: (compilation_preserves_well_formedness HwfP Hip').
    - exact: (compilation_preserves_well_formedness HwfC Hic').
    - by rewrite (compilation_preserves_interface _ _ Hip') Hif1.
    - by rewrite (compilation_preserves_interface _ _ Hic') Hif2.
    - exact: HbufP.
    - exact: HbufC.
    - exact: HeqP.
    - exact: HeqC.
  Qed.

End BTSourceHalfShapes.

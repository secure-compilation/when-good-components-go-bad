(* RecompositionWrapper: recomposition for LINEARIZED programs.

   [IntermediateRecompositionContext] packages the INTERMEDIATE-level premises for a
   quadruple (ip, ic, ip', ic') of Intermediate programs (shared canonical label bounds
   L/P/C, well-formedness, mergeable/equal interfaces, closedness, size bounds).  The
   [RecLinearized] functor pushes them through the verified generator facts of
   LinearizeMerged.v to instantiate [RecompositionContext] + [LinearizerFacts] with the
   four linearized sides, and re-exports the recomposition blame theorems:

     recomposition_blame_linearized  : prefix(p⋈c) ∧ prefix(p'⋈c') ⇒ prefix(p⋈c')
     recomposition_blame_linearized' : the blame-directed refinement

   whose assumption closure is exactly the context's axioms + classical logic
   (see the Print Assumptions gate at the bottom of the functor). *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Maps.
Require Import Common.Linking.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RecompositionTop.
Require Import Coq.micromega.Lia.
Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Type IntermediateRecompositionContext.
  Parameters ip ic ip' ic' : Intermediate.program.

  (* Shared strict bounds of the canonical label scheme (any common upper bounds work,
     e.g. maxima+1 over the quadruple). *)
  Parameters L P C : nat.

  (* The canonical JOINT buffer map both sides compile against (plan-t2me.md
     §3.7): the union over the pair.  The primed variants share it — their
     buffers are equal ([Hbufp]/[Hbufc] below). *)
  Definition PBW := unionm (Intermediate.prog_buffers ip)
                           (Intermediate.prog_buffers ic).

  (* likewise the canonical JOINT interface (plan-t2me.md §3.8): entry-tag
     allowed-caller lists are computed against it, so cross-side calls are
     sanctioned.  Equal across the primed variants by [Hifacep]/[Hifacec]. *)
  Definition PIW := unionm (Intermediate.prog_interface ip)
                           (Intermediate.prog_interface ic).

  Axiom Hwfp  : Intermediate.well_formed_program ip.
  Axiom Hwfc  : Intermediate.well_formed_program ic.
  Axiom Hwfp' : Intermediate.well_formed_program ip'.
  Axiom Hwfc' : Intermediate.well_formed_program ic'.

  Axiom Hmergeable_ifaces :
    mergeable_interfaces (Intermediate.prog_interface ip) (Intermediate.prog_interface ic).

  Axiom Hifacep : Intermediate.prog_interface ip = Intermediate.prog_interface ip'.
  Axiom Hifacec : Intermediate.prog_interface ic = Intermediate.prog_interface ic'.

  (* The linked program has a main component. *)
  Axiom Hmain : Component.main \in domm (unionm (Intermediate.prog_interface ip)
                                                (Intermediate.prog_interface ic)).

  (* The shared segments carry the same static buffers. *)
  Axiom Hbufp : Intermediate.prog_buffers ip = Intermediate.prog_buffers ip'.
  Axiom Hbufc : Intermediate.prog_buffers ic = Intermediate.prog_buffers ic'.

  (* Every declared component implements at least one procedure. *)
  Axiom Hprocs_nonempty_p : forall cid Cprocs,
    Intermediate.prog_procedures ip cid = Some Cprocs -> exists Pid, Pid \in domm Cprocs.
  Axiom Hprocs_nonempty_c : forall cid Cprocs,
    Intermediate.prog_procedures ic cid = Some Cprocs -> exists Pid, Pid \in domm Cprocs.
  Axiom Hprocs_nonempty_p' : forall cid Cprocs,
    Intermediate.prog_procedures ip' cid = Some Cprocs -> exists Pid, Pid \in domm Cprocs.
  Axiom Hprocs_nonempty_c' : forall cid Cprocs,
    Intermediate.prog_procedures ic' cid = Some Cprocs -> exists Pid, Pid \in domm Cprocs.

  (* Every declared component has a nonempty static buffer (the Merged wf requirement;
     [has_required_local_buffers] only inspects [prog_buffers], which the linearized side
     passes through unchanged). *)
  Axiom Hbuffers_wf_p : forall C0,
    Intermediate.prog_interface ip C0 -> has_required_local_buffers (compiler L P C PBW PIW ip) C0.
  Axiom Hbuffers_wf_c : forall C0,
    Intermediate.prog_interface ic C0 -> has_required_local_buffers (compiler L P C PBW PIW ic) C0.
  Axiom Hbuffers_wf_p' : forall C0,
    Intermediate.prog_interface ip' C0 -> has_required_local_buffers (compiler L P C PBW PIW ip') C0.
  Axiom Hbuffers_wf_c' : forall C0,
    Intermediate.prog_interface ic' C0 -> has_required_local_buffers (compiler L P C PBW PIW ic') C0.

  (* Label / procedure-id / component-id bounds. *)
  Axiom HboundL_p : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures ip cid = Some Cprocs ->
    Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
  Axiom HboundL_c : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures ic cid = Some Cprocs ->
    Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
  Axiom HboundL_p' : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures ip' cid = Some Cprocs ->
    Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
  Axiom HboundL_c' : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures ic' cid = Some Cprocs ->
    Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.

  Axiom HboundP_p : forall cid Cprocs Pid,
    Intermediate.prog_procedures ip cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
  Axiom HboundP_c : forall cid Cprocs Pid,
    Intermediate.prog_procedures ic cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
  Axiom HboundP_p' : forall cid Cprocs Pid,
    Intermediate.prog_procedures ip' cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
  Axiom HboundP_c' : forall cid Cprocs Pid,
    Intermediate.prog_procedures ic' cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.

  Axiom HboundC_p : forall cid,
    cid \in domm (Intermediate.prog_interface ip) -> cid < C.
  Axiom HboundC_c : forall cid,
    cid \in domm (Intermediate.prog_interface ic) -> cid < C.

  (* Component ids fit the NC = 14 colour-prefix field. *)
  Axiom Hcomp_bound : forall x,
    (x \in domm (Intermediate.prog_interface ip))
    || (x \in domm (Intermediate.prog_interface ic)) -> 1 + x < 2 ^ 14.

  (* Program-size premises (data + code below the allocator label), per linked run. *)
  Axiom Hsize : size (linearize_bufs (unionm (Intermediate.prog_buffers ip)
                                             (Intermediate.prog_buffers ic)))
                + size (compiler_code L P C PBW PIW ip ++ compiler_code L P C PBW PIW ic) < alloc_label.
  Axiom Hsize' : size (linearize_bufs (unionm (Intermediate.prog_buffers ip')
                                              (Intermediate.prog_buffers ic')))
                 + size (compiler_code L P C PBW PIW ip' ++ compiler_code L P C PBW PIW ic') < alloc_label.
  Axiom Hsize'' : size (linearize_bufs (unionm (Intermediate.prog_buffers ip)
                                               (Intermediate.prog_buffers ic')))
                  + size (compiler_code L P C PBW PIW ip ++ compiler_code L P C PBW PIW ic') < alloc_label.
End IntermediateRecompositionContext.

Module RecLinearized (I : IntermediateRecompositionContext).

  (* ---- derived interface facts ---- *)

  Lemma Hdis_pc : fdisjoint (domm (Intermediate.prog_interface I.ip))
                            (domm (Intermediate.prog_interface I.ic)).
  Proof. by case: I.Hmergeable_ifaces => [[_ Hdis] _]. Qed.

  Lemma Hclosed_pc : closed_interface (unionm (Intermediate.prog_interface I.ip)
                                              (Intermediate.prog_interface I.ic)).
  Proof. by case: I.Hmergeable_ifaces => _ Hc. Qed.

  Lemma Hdis_pc' : fdisjoint (domm (Intermediate.prog_interface I.ip))
                             (domm (Intermediate.prog_interface I.ic')).
  Proof. rewrite -I.Hifacec. exact: Hdis_pc. Qed.

  Lemma Hdis_p'c' : fdisjoint (domm (Intermediate.prog_interface I.ip'))
                              (domm (Intermediate.prog_interface I.ic')).
  Proof. rewrite -I.Hifacep -I.Hifacec. exact: Hdis_pc. Qed.

  Lemma Hclosed_pc' : closed_interface (unionm (Intermediate.prog_interface I.ip)
                                               (Intermediate.prog_interface I.ic')).
  Proof. rewrite -I.Hifacec. exact: Hclosed_pc. Qed.

  Lemma Hclosed_p'c' : closed_interface (unionm (Intermediate.prog_interface I.ip')
                                                (Intermediate.prog_interface I.ic')).
  Proof. rewrite -I.Hifacep -I.Hifacec. exact: Hclosed_pc. Qed.

  Lemma Hclosed_cp : closed_interface (unionm (Intermediate.prog_interface I.ic)
                                              (Intermediate.prog_interface I.ip)).
  Proof.
    rewrite unionmC; first exact: Hclosed_pc.
    rewrite fdisjointC. exact: Hdis_pc.
  Qed.

  Lemma Hclosed_c'p : closed_interface (unionm (Intermediate.prog_interface I.ic')
                                               (Intermediate.prog_interface I.ip)).
  Proof.
    rewrite unionmC; first exact: Hclosed_pc'.
    rewrite fdisjointC. exact: Hdis_pc'.
  Qed.

  Lemma Hclosed_c'p' : closed_interface (unionm (Intermediate.prog_interface I.ic')
                                                (Intermediate.prog_interface I.ip')).
  Proof.
    rewrite unionmC; first exact: Hclosed_p'c'.
    rewrite fdisjointC. exact: Hdis_p'c'.
  Qed.

  Lemma HboundC_p' : forall cid,
    cid \in domm (Intermediate.prog_interface I.ip') -> cid < I.C.
  Proof. move=> cid. rewrite -I.Hifacep. exact: I.HboundC_p. Qed.

  Lemma HboundC_c' : forall cid,
    cid \in domm (Intermediate.prog_interface I.ic') -> cid < I.C.
  Proof. move=> cid. rewrite -I.Hifacec. exact: I.HboundC_c. Qed.

  (* ---- the RecompositionContext instance ---- *)

  Module S_lin <: RecompositionContext.
    Definition p  : program := compiler I.L I.P I.C I.PBW I.PIW I.ip.
    Definition c  : program := compiler I.L I.P I.C I.PBW I.PIW I.ic.
    Definition p' : program := compiler I.L I.P I.C I.PBW I.PIW I.ip'.
    Definition c' : program := compiler I.L I.P I.C I.PBW I.PIW I.ic'.

    Definition NC : nat := 14.

    Lemma Hwfp : well_formed_program p.
    Proof.
      apply: compiler_wf.
      - exact: I.Hwfp.
      - exact: I.Hprocs_nonempty_p.
      - exact: I.Hbuffers_wf_p.
    Qed.

    Lemma Hwfc : well_formed_program c.
    Proof.
      apply: compiler_wf.
      - exact: I.Hwfc.
      - exact: I.Hprocs_nonempty_c.
      - exact: I.Hbuffers_wf_c.
    Qed.

    Lemma Hwfp' : well_formed_program p'.
    Proof.
      apply: compiler_wf.
      - exact: I.Hwfp'.
      - exact: I.Hprocs_nonempty_p'.
      - exact: I.Hbuffers_wf_p'.
    Qed.

    Lemma Hwfc' : well_formed_program c'.
    Proof.
      apply: compiler_wf.
      - exact: I.Hwfc'.
      - exact: I.Hprocs_nonempty_c'.
      - exact: I.Hbuffers_wf_c'.
    Qed.

    Lemma Hmergeable_ifaces :
      mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof. exact: I.Hmergeable_ifaces. Qed.

    Lemma Hifacep : prog_interface p = prog_interface p'.
    Proof. exact: I.Hifacep. Qed.

    Lemma Hifacec : prog_interface c = prog_interface c'.
    Proof. exact: I.Hifacec. Qed.

    Lemma Hprog_is_closed : closed_program (program_link p c).
    Proof.
      constructor.
      - exact: Hclosed_pc.
      - move: I.Hmain. by rewrite domm_union in_fsetU.
    Qed.

    Lemma Hprog_is_closed' : closed_program (program_link p' c').
    Proof.
      constructor.
      - exact: Hclosed_p'c'.
      - move: I.Hmain. by rewrite domm_union in_fsetU /= -I.Hifacep -I.Hifacec.
    Qed.

    Lemma colors_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
    Proof. exact: I.Hcomp_bound. Qed.

    Lemma NC_lt_word : NC < word_size mt.
    Proof. by rewrite word_size_mt. Qed.

    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. by rewrite /alloc_label word_size_mt /NC ltn_exp2l. Qed.
  End S_lin.

  (* ---- the LinearizerFacts instance ---- *)

  Module L_lin <: LinearizerFacts S_lin.
    Module D := RecompositionDefinitions S_lin.
    Import D.

    Lemma lin_wf_p : lin_output_wf p.
    Proof. apply: compiler_output_wf. exact: I.Hwfp. Qed.
    Lemma lin_wf_c : lin_output_wf c.
    Proof. apply: compiler_output_wf. exact: I.Hwfc. Qed.
    Lemma lin_wf_p' : lin_output_wf p'.
    Proof. apply: compiler_output_wf. exact: I.Hwfp'. Qed.
    Lemma lin_wf_c' : lin_output_wf c'.
    Proof. apply: compiler_output_wf. exact: I.Hwfc'. Qed.

    Lemma labels_disjoint_prefix : forall l,
      findopt (is_label_def l) (code p) <> None ->
      findopt (is_label_def l) (code c) = None
      /\ findopt (is_label_def l) (code c') = None.
    Proof.
      move=> l H1. split.
      - exact: (lin_labels_disjoint I.Hwfp I.Hwfc I.HboundL_p I.HboundP_p I.HboundC_p
                  I.HboundL_c I.HboundP_c I.HboundC_c Hdis_pc H1).
      - exact: (lin_labels_disjoint I.Hwfp I.Hwfc' I.HboundL_p I.HboundP_p I.HboundC_p
                  I.HboundL_c' I.HboundP_c' HboundC_c' Hdis_pc' H1).
    Qed.

    Lemma labels_disjoint_suffix : forall l,
      findopt (is_label_def l) (code c') <> None ->
      findopt (is_label_def l) (code p) = None
      /\ findopt (is_label_def l) (code p') = None.
    Proof.
      move=> l H1.
      have Hdis_c'p : fdisjoint (domm (Intermediate.prog_interface I.ic'))
                                (domm (Intermediate.prog_interface I.ip)).
      { rewrite fdisjointC. exact: Hdis_pc'. }
      have Hdis_c'p' : fdisjoint (domm (Intermediate.prog_interface I.ic'))
                                 (domm (Intermediate.prog_interface I.ip')).
      { rewrite fdisjointC. exact: Hdis_p'c'. }
      split.
      - exact: (lin_labels_disjoint I.Hwfc' I.Hwfp I.HboundL_c' I.HboundP_c' HboundC_c'
                  I.HboundL_p I.HboundP_p I.HboundC_p Hdis_c'p H1).
      - exact: (lin_labels_disjoint I.Hwfc' I.Hwfp' I.HboundL_c' I.HboundP_c' HboundC_c'
                  I.HboundL_p' I.HboundP_p' HboundC_p' Hdis_c'p' H1).
    Qed.

    Lemma jal_cross_p : forall n l t,
      nth_error (code p) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p) = None ->
      exists mc mc' (ic_ i_ : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code c) = Some mc,
            findopt (is_label_def l) (code c') = Some mc',
            nth_error (code c) mc = Some (ic_, tc)
            /\ nth_error (code c') mc' = Some (i_, tc)
          & is_code tc /\ color tc \in domm (prog_interface c)].
    Proof.
      move=> n l t Hnth Halloc Hnone.
      case: (lin_jal_foreign I.Hwfp I.Hwfc I.HboundL_c I.HboundP_c I.HboundC_c
               Hclosed_pc Hnth Halloc Hnone)
        => mc [C0 [P0 [Hfc Hnthc Hl Hdom [HC0 HP0]]]].
      case: (lin_jal_foreign I.Hwfp I.Hwfc' I.HboundL_c' I.HboundP_c' HboundC_c'
               Hclosed_pc' Hnth Halloc Hnone)
        => mc' [C1 [P1 [Hfc' Hnthc' Hl' Hdom' [HC1 HP1]]]].
      have [EC EP] := mk_entry_inj HP1 HP0 (etrans (esym Hl') Hl).
      subst C1 P1.
      exists mc, mc', (MrLabel l), (MrLabel l), (head_tag_gen I.PIW C0 P0).
      split.
      - exact: Hfc.
      - exact: Hfc'.
      - split.
        + exact: Hnthc.
        + exact: Hnthc'.
      - split.
        + by [].
        + exact: Hdom.
    Qed.

    Lemma jal_cross_c' : forall n l t,
      nth_error (code c') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c') = None ->
      exists mp' mp (ip_ i_ : Merged.instr) (tp : mem_tag),
        [/\ findopt (is_label_def l) (code p') = Some mp',
            findopt (is_label_def l) (code p) = Some mp,
            nth_error (code p') mp' = Some (ip_, tp)
            /\ nth_error (code p) mp = Some (i_, tp)
          & is_code tp /\ color tp \in domm (prog_interface p)].
    Proof.
      move=> n l t Hnth Halloc Hnone.
      case: (lin_jal_foreign I.Hwfc' I.Hwfp I.HboundL_p I.HboundP_p I.HboundC_p
               Hclosed_c'p Hnth Halloc Hnone)
        => mp [C0 [P0 [Hfp Hnthp Hl Hdom [HC0 HP0]]]].
      case: (lin_jal_foreign I.Hwfc' I.Hwfp' I.HboundL_p' I.HboundP_p' HboundC_p'
               Hclosed_c'p' Hnth Halloc Hnone)
        => mp' [C1 [P1 [Hfp' Hnthp' Hl' Hdom' [HC1 HP1]]]].
      have [EC EP] := mk_entry_inj HP1 HP0 (etrans (esym Hl') Hl).
      subst C1 P1.
      exists mp', mp, (MrLabel l), (MrLabel l), (head_tag_gen I.PIW C0 P0).
      split.
      - exact: Hfp'.
      - exact: Hfp.
      - split.
        + exact: Hnthp'.
        + exact: Hnthp.
      - split.
        + by [].
        + exact: Hdom.
    Qed.

    Lemma jal_cross_p'one : forall n l t,
      nth_error (code p') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p') = None ->
      exists m, findopt (is_label_def l) (code c') = Some m.
    Proof.
      move=> n l t Hnth Halloc Hnone.
      case: (lin_jal_foreign I.Hwfp' I.Hwfc' I.HboundL_c' I.HboundP_c' HboundC_c'
               Hclosed_p'c' Hnth Halloc Hnone)
        => m [C0 [P0 [Hf _ _ _ _]]].
      by exists m.
    Qed.

    Lemma jal_cross_cone : forall n l t,
      nth_error (code c) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c) = None ->
      exists m, findopt (is_label_def l) (code p) = Some m.
    Proof.
      move=> n l t Hnth Halloc Hnone.
      case: (lin_jal_foreign I.Hwfc I.Hwfp I.HboundL_p I.HboundP_p I.HboundC_p
               Hclosed_cp Hnth Halloc Hnone)
        => m [C0 [P0 [Hf _ _ _ _]]].
      by exists m.
    Qed.

    Lemma memory_size_lin :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: I.Hsize. Qed.

    Lemma memory_size_lin' :
      size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c')))
        + size (code p' ++ code c') < alloc_label.
    Proof. exact: I.Hsize'. Qed.

    Lemma memory_size_lin'' :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c')))
        + size (code p ++ code c') < alloc_label.
    Proof. exact: I.Hsize''. Qed.

    Lemma bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p').
    Proof. exact: (congr1 bufs_shape I.Hbufp). Qed.

    Lemma bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c').
    Proof. exact: (congr1 bufs_shape I.Hbufc). Qed.
  End L_lin.

  (* ---- the recomposition theorems for linearized programs ---- *)

  Module Top := RecTop S_lin L_lin.

  Definition recomposition_blame_linearized := Top.recomposition_blame.
  Definition recomposition_blame_linearized' := Top.recomposition_blame'.

  (* Assumption-closure gate: everything below must be an [I.*] axiom or a classical
     principle (CompCert's trace framework). *)
  Print Assumptions recomposition_blame_linearized.
  Print Assumptions recomposition_blame_linearized'.

End RecLinearized.

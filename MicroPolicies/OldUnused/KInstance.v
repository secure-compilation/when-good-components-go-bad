Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Maps.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RSCSigs.
Require Import MicroPolicies.Recomposition.BackTranslation.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.

Module Type LinBoundsSig.
  Parameter L : nat.
  Parameter P : nat.
  Parameter C : nat.
End LinBoundsSig.

Module KStatics (B : LinBoundsSig).

  Definition NC : nat := 14.

  Lemma NC_lt_word : NC < word_size mt.
  Proof. by rewrite word_size_mt. Qed.

  Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
  Proof. by rewrite /alloc_label word_size_mt /NC ltn_exp2l. Qed.

  Definition lin (a : Intermediate.program) : program :=
    lin_side B.L B.P B.C a.

  Definition lin_ok (a : Intermediate.program) : Prop :=
    [/\ (forall cid Cprocs,
           Intermediate.prog_procedures a cid = Some Cprocs ->
           exists Pid, Pid \in domm Cprocs),
        (forall C0, Intermediate.prog_interface a C0 ->
           has_required_local_buffers (lin a) C0),
        (forall cid Cprocs Pid Pcode l0,
           Intermediate.prog_procedures a cid = Some Cprocs ->
           Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < B.L),
        (forall cid Cprocs Pid,
           Intermediate.prog_procedures a cid = Some Cprocs ->
           Pid \in domm Cprocs -> Pid < B.P)
      & (forall cid,
           cid \in domm (Intermediate.prog_interface a) -> cid < B.C)].

  Lemma lin_ok_atE : forall x,
    lin_ok_at B.L B.P B.C x <-> lin_ok x.
  Proof. move=> x. split; exact: id. Qed.

  Lemma lin_interface : forall a,
    prog_interface (lin a) = Intermediate.prog_interface a.
  Proof. by []. Qed.

  Lemma lin_buffers : forall a,
    prog_buffers (lin a) = Intermediate.prog_buffers a.
  Proof. by []. Qed.

  Lemma lin_main : forall a,
    prog_main (lin a)
    = (Component.main \in domm (Intermediate.prog_interface a)).
  Proof. by []. Qed.

  Lemma lin_wf : forall a,
    Intermediate.well_formed_program a -> lin_ok a ->
    well_formed_program (lin a).
  Proof.
    move=> a Hwf [Hne Hbuf _ _ _].
    apply: lin_side_wf.
    - exact: Hwf.
    - exact: Hne.
    - exact: Hbuf.
  Qed.

  Lemma lin_out_wf : forall a,
    Intermediate.well_formed_program a -> lin_output_wf (lin a).
  Proof.
    move=> a Hwf. apply: lin_side_output_wf. exact: Hwf.
  Qed.

  Lemma lin_labels_disjoint : forall a b,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    lin_ok a -> lin_ok b ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    forall l, findopt (is_label_def l) (code (lin a)) <> None ->
              findopt (is_label_def l) (code (lin b)) = None.
  Proof.
    move=> a b Hwa Hwb [_ _ HLa HPa HCa] [_ _ HLb HPb HCb] Hdis l H.
    exact: (LinearizeMerged.lin_labels_disjoint Hwa Hwb HLa HPa HCa
              HLb HPb HCb Hdis H).
  Qed.

  Lemma head_tag_iface : forall a b c p,
    Intermediate.prog_interface a = Intermediate.prog_interface b ->
    head_tag a c p = head_tag b c p.
  Proof. move=> a b c p E. by rewrite /head_tag E. Qed.

  Lemma lin_jal_cross : forall a b b',
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    Intermediate.well_formed_program b' ->
    lin_ok a -> lin_ok b -> lin_ok b' ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    closed_interface (unionm (Intermediate.prog_interface a)
                             (Intermediate.prog_interface b)) ->
    Intermediate.prog_interface b = Intermediate.prog_interface b' ->
    forall n l t,
      nth_error (code (lin a)) n = Some (@MrJal mt l, t) ->
      l <> alloc_label ->
      findopt (is_label_def l) (code (lin a)) = None ->
      exists mb mb' (i i' : @Merged.instr mt) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code (lin b)) = Some mb,
            findopt (is_label_def l) (code (lin b')) = Some mb',
            nth_error (code (lin b)) mb = Some (i, tc)
            /\ nth_error (code (lin b')) mb' = Some (i', tc)
          & is_code tc /\ color tc \in domm (Intermediate.prog_interface b)].
  Proof.
    move=> a b b' Hwa Hwb Hwb' [_ _ HLa HPa HCa] [_ _ HLb HPb HCb]
           [_ _ HLb' HPb' HCb'] Hdis Hclosed Eiface n l t Hn Hne Hnf.
    have Hclosed' : closed_interface
                      (unionm (Intermediate.prog_interface a)
                              (Intermediate.prog_interface b')).
    { by rewrite -Eiface. }
    have [mb [C0 [P0 [F1 F2 F3 F4 [F5 F6]]]]] :=
      LinearizeMerged.lin_jal_foreign Hwa Hwb HLb HPb HCb
        Hclosed Hn Hne Hnf.
    have [mb' [C0' [P0' [G1 G2 G3 G4 [G5 G6]]]]] :=
      LinearizeMerged.lin_jal_foreign Hwa Hwb' HLb' HPb' HCb'
        Hclosed' Hn Hne Hnf.
    have [EC EP] : C0 = C0' /\ P0 = P0'.
    { exact: (mk_entry_inj F6 G6 (etrans (esym F3) G3)). }
    subst C0' P0'.
    exists mb, mb', (@MrLabel mt l), (@MrLabel mt l), (head_tag b C0 P0).
    split.
    - exact: F1.
    - exact: G1.
    - split.
      + exact: F2.
      + rewrite (head_tag_iface C0 P0 Eiface). exact: G2.
    - split.
      + by [].
      + rewrite color_head_tag. exact: F4.
  Qed.

End KStatics.

Module Type KDynamicsSig (B : LinBoundsSig).
  Module S := KStatics B.

  Axiom H_bwd : forall a b m,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    S.lin_ok a -> S.lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    (exists sa, Source.well_formed_program sa /\ compile_program sa = Some a) ->
    (exists sb, Source.well_formed_program sb /\ compile_program sb = Some b) ->
    does_prefix (me_sem S.NC (program_link (S.lin a) (S.lin b))) m ->
    exists beh,
      program_behaves (I.CS.sem (Intermediate.program_link a b)) beh
      /\ (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).

  Parameter bt_fits :
    Intermediate.program -> Intermediate.program -> Events.trace -> Prop.

  Axiom H_bt : forall a b (m0 : finpref_behavior),
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    S.lin_ok a -> S.lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (rub_sem S.NC (Intermediate.prog_interface a)
                            (Intermediate.prog_interface b)
                            (program_link (S.lin a) (S.lin b)))
                m0 ->
    not_wrong_finpref m0 ->
    bt_fits a b (finpref_trace m0) ->
    bt_package S.NC S.lin S.lin_ok a b m0.
End KDynamicsSig.

Module KConcrete (B : LinBoundsSig) (D : KDynamicsSig B) <: MPCompilerSig.
  Module S := KStatics B.
  Include S.
  Definition H_bwd := D.H_bwd.
  Definition bt_fits := D.bt_fits.
  Definition H_bt := D.H_bt.
End KConcrete.

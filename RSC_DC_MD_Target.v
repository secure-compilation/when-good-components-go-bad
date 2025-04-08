Require Import CompCert.Behaviors.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import Common.Util.

Require Import Coq.micromega.Lia.

Require Import RSC_DC_MD_Sigs.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module RSC_DC_MD_Gen
       (Target: Target_Sig).

Definition behavior_improves_blame b m p :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m /\
             undef_in t (Target.prog_interface p).

Section RSC_DC_MD_Section.
  Import Target.
  Variable p: program.
  Variable Ct: program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : well_formed_program p.
  Hypothesis well_formed_Ct : well_formed_program Ct.
  Hypothesis linkability : linkable (prog_interface p) (prog_interface Ct).
  Hypothesis closedness : closed_program (program_link p Ct).
  Hypothesis mains : linkable_mains p Ct.
  Hypothesis disjoint_interface : fdisjoint (domm (prog_interface p)) (domm (prog_interface Ct)).
  
  Lemma last_comp_in_interface_p : forall t t' s s' s'0,
      (CS.initial_state (program_link p Ct) s \/ t' <> []) ->
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s'0 ->
      Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'0 ->
      ((* (t = t' /\ CS.final_state (program_link p Ct) s' /\ ~ CS.final_state (program_link p Ct) s'0) \/ *)
         (t = t' /\ Plus (CS.sem2 (program_link p Ct)) s'0 [] s' /\  ~ CS.final_state (program_link p Ct) s'0) \/
         (t' <> t /\ trace_prefix t' t)) ->
      (last_comp t') \in domm (prog_interface p).
  Proof.
    intros t t' s s' s'0 init star2 star_UB nostep disj.
    assert (eq_t': last_comp t'= CS.current_comp s'0).
      { destruct t'.
        - rewrite <- (Target.component_conservation_on_empty_trace star_UB). unfold last_comp. simpl.
          destruct init as [init|?]; try contradiction. rewrite (Target.initial_state_main init). auto.
        - eapply Target.non_empty_trace_last_comp. intro. inversion H. exact star_UB. } 
      rewrite eq_t'. subst. destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability closedness
                                        (init) star_UB); try done.
    - exfalso. clear eq_t' init. revert star_UB nostep H disj. revert s'0 t'.
      induction star2; intros s'0 t' star_s'0 nostep in_Ct disj; destruct star_s'0;
        destruct disj as (*[eq [final nofinal]] |*) [[eq [plus_s' nofinal]] | [ineq pref]]; try contradiction.
      + inversion plus_s'. eapply nostep. econstructor. eauto. unfold allowed_UB. auto.
     (* + eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))); eauto.
        eapply Target.sem_restricted_UB_generalises_sem2. exact H. *)
      + inv plus_s'. eapply nostep. econstructor. eauto. unfold allowed_UB. auto.
      + destruct pref. apply ineq. destruct t; auto; inversion H1.
      + eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. eauto. auto.
      + eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. eauto. auto.
     (* + eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. eauto. auto. *)
      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
          eapply IHstar2; eauto. left. split; [|split; auto].
          {clear -eq. induction t0; auto. inversion eq. traceEq. }
     (* + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
          eapply IHstar2; eauto. left. split.
          {clear -eq. induction t0; inversion eq; auto. } auto. *)
      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
          eapply IHstar2; eauto. right. split.
          {clear -ineq. intro. induction t0; auto. apply ineq. traceEq. }
          destruct pref. exists x. clear -H0. induction t0; inversion H0; auto.
  Qed.

 Lemma star_max_prefix: forall t s s',
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      (Star (CS.sem_restricted_UB (program_link p Ct)
                      (allowed_UB (prog_interface Ct))) s t s') \/
        exists s'' t' t0,
          t = t' ** t0 /\
            (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
              /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s'') ->
             undef_in t' (prog_interface p)) /\
            Star (CS.sem_restricted_UB (program_link p Ct)
                    (allowed_UB (prog_interface Ct))) s t' s'' /\
            not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                                 (allowed_UB (prog_interface Ct)))) s'') /\
            Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'' /\
            Star (CS.sem2 (program_link p Ct)) s'' t0 s'.
  Proof.
    intros t s s' H1. induction H1.
    - left. econstructor.
    - destruct ((Target.sem_restricted_UB_lem
                   (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 t1)
        as [step_no_UB12 | no_step_UB12].
      + destruct (IHstar) as [ stars'| [s'' [t' [t0 [t2_eq [undef [star [nofinal [nostep starend]]]]]]]]]; clear IHstar.
        * left; econstructor; eauto.
        * destruct t0.
          -- inversion starend.
             { subst. left. econstructor; eauto. traceEq. } subst.
             assert (t0 = []) by (induction t0; inversion H4; auto). subst.
             assert (t3 = []) by (induction t3; inversion H4; auto). subst.
             assert (plus: Plus (CS.sem2 (program_link p Ct)) s'' [] s3). econstructor; eauto.
             right. exists s'', (t1 ** t'), []. split; try now traceEq.
             split; [| split; [auto| split; [auto| split]]].
             ++ intros [init star_s'']. eapply (last_comp_in_interface_p init). eapply star_step; eauto.
                eapply (star_step). exact step_no_UB12. exact star. auto. auto. left. split; auto. traceEq.
             ++ econstructor; eauto.
             ++ auto.
             ++ destruct plus. econstructor; eauto.
          -- inversion starend. subst. remember (e :: t0) as t.
             assert (plus: Plus (CS.sem2 (program_link p Ct)) s'' t s3). econstructor; eauto.
             right. exists s'', (t1 ** t'), t. split; try now traceEq.
             split; [| split; [auto| split; [auto| split]]].
             ++ intros [init star_s'']. eapply (last_comp_in_interface_p init). eapply star_step; eauto.
                eapply (star_step). exact step_no_UB12. exact star. auto. auto. right. split; auto.
                { intro. rewrite Heqt in H0. clear  -H0. remember (t1 ** t') as t. rewrite <- Eapp_assoc in H0.
                  rewrite <- Heqt in H0. clear Heqt. induction t; inversion H0; auto. }
                exists t; traceEq.
             ++ econstructor; eauto.
             ++ auto.
             ++ destruct plus. econstructor; eauto. 
      + right. exists s1, [], (t). split; auto. split; [|split; [|split; [|split]]].
        -- intros [init star_s']. unfold undef_in. eapply (last_comp_in_interface_p init). eapply star_step. exact H. exact H1. 
           reflexivity. eauto. intros t' s'' step. clear -H step star_s' no_step_UB12. induction star_s'.
           ++ eapply no_step_UB12. destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 step) H). subst. auto.
           ++ eapply no_step_UB12. destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 step) H). subst. auto.
           ++ destruct t.
              ** left. split. auto.
                 assert (t1 = []) by (induction t1; inversion H0; auto). subst.
                 assert (t2 = []) by (induction t2; inversion H0; auto). subst.
                 split. econstructor; eauto. intro. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) _ H2). eauto.
              ** right. split; try now (intro eq; rewrite <- eq in H0; inversion H0). exists (t1 ** t2). traceEq.
        -- econstructor.
        -- intro. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) _ H2). exact H.
        -- intros t' s' step. eapply no_step_UB12. destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 step) H). subst. auto.
        -- rewrite H0. econstructor; eauto.
  Qed.

  
  Lemma max_prefix_no_UB: forall (m: finpref_behavior),
    does_prefix (CS.sem2 (program_link p Ct)) m ->
    exists m', does_prefix
            (CS.sem_restricted_UB (program_link p Ct)
               (allowed_UB (prog_interface Ct))) m' /\
            (m = m' \/
               (finpref_trace_prefix m' (finpref_trace m) /\
                  undef_in (finpref_trace m') (prog_interface p) /\
               does_prefix
                (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct) ))
                (FGoes_wrong (finpref_trace m')))).
  Proof.
    setoid_rewrite (does_prefix_equiv (Target.det_sem2 (program_link p Ct))).
    setoid_rewrite (does_prefix_equiv (Target.det_sem_restricted (program_link p Ct) (allowed_UB (prog_interface Ct)))).
    intros m dm.
    assert (pr : trace_prefix (finpref_trace m) (finpref_trace m)) by (exists []; now traceEq).
    inv dm; simpl in pr; try destruct (star_max_prefix H0).
    - exists (FTbc t). split; auto. econstructor; eauto.
    - destruct H1 as [s'' [t' [t0 [t_t'_t0 [undef [star [nofinal [nostep starend]]]]]]]]. 
      exists (FTbc t'). split; [|right; split; simpl; [| split]].
      + econstructor; eauto.
      + exists t0. traceEq.
      + eapply undef. split; [left; auto|eauto].
      + econstructor; eauto.
    - rename H3 into star.
      exists (FGoes_wrong t). split; auto. econstructor; eauto.
      { intros t' s'' step. destruct (H1 t' s'' (Target.sem_restricted_UB_generalises_sem2 step)). }
    - destruct H3 as [s'' [t' [t0 [t_t'_t0 [undef [star [nofinal [nostep starend]]]]]]]]. 
      exists (FTbc t'). split; [|right; split; simpl; [| split]].
      + econstructor; eauto.
      + exists t0. traceEq.
      + eapply undef. split; [left; auto|eauto].
      + econstructor; eauto.
    - exists (FTerminates t). split; auto. econstructor; eauto.
    - destruct H2 as [s'' [t' [t0 [t_t'_t0 [undef [star [nofinal [nostep starend]]]]]]]]. 
      exists (FTbc t'). split; [|right; split; simpl; [| split]].
      + econstructor; eauto.
      + exists t0. traceEq.
      + eapply undef. split; [left; auto|eauto].
      + econstructor; eauto.
    - exists (FGoes_wrong E0). split; auto. eapply does_no_initial_FGoes_wrong. auto.
    - exists (FTbc E0). split; auto. eapply does_no_initial_FTbc. auto.
Qed.

  (* Main Theorem *)
  Theorem RSC_DC_MD:
    forall m,
      does_prefix (CS.sem2 (program_link p Ct)) m ->
      not_wrong_finpref m ->
    exists Cs beh,
      prog_interface Cs = prog_interface Ct /\
      well_formed_program Cs /\
      linkable (prog_interface p) (prog_interface Cs) /\
      closed_program (program_link p Cs) /\
      program_behaves (CS.sem1 (program_link p Cs)) beh /\
      (prefix m beh \/ behavior_improves_blame beh m p).
  Proof.
    intros m [t [Hbeh Hprefix0]] Hsafe_pref.

    (* Some auxiliary results. *)

    (* definability *)
    destruct (Target.definability_with_linking
                well_formed_p well_formed_Ct
                linkability closedness Hbeh Hprefix0 Hsafe_pref)
      as [P' [Cs
         [Hsame_iface1 [Hsame_iface2
         [matching_mains1 [matching_mains2
         [well_formed_P' [well_formed_Cs [HP'Cs_closed HP'_Cs_m]]]]]]]]].

    assert (mergeable_interfaces (prog_interface p)
                                 (prog_interface Ct))
      as Hmergeable_ifaces
           by (eapply Target.compose_mergeable_interfaces; eauto).

    pose proof (max_prefix_no_UB
                  (ex_intro _ t (conj Hbeh Hprefix0)))
      as [m' [p_Ct_does_m' H]].

    destruct H as [H | [m'_m [undef_in_m'_p m'_maximal]]]; try subst m'.
    - pose proof Target.recombination_blame_prefix
                 well_formed_p well_formed_Ct well_formed_P' well_formed_Cs Hmergeable_ifaces
                 (eq_sym Hsame_iface1) (eq_sym Hsame_iface2) closedness HP'Cs_closed
                 p_Ct_does_m' HP'_Cs_m.

      destruct H  as [t' [p_Cs_t' m_t']].
      exists Cs, t'.
      repeat (split; [now auto |]).
      rewrite Hsame_iface2; split; [now auto |].
      split.
      + eapply Target.interface_preserves_closedness_r with (p2 := Ct); eauto.
      + split; eauto.

    - assert (P'_Cs_tbc_m':
               does_prefix (CS.sem1 (program_link P' Cs)) (FTbc (finpref_trace m'))).
      { clear -HP'_Cs_m m'_m.
        revert HP'_Cs_m m'_m.
        generalize (CS.sem1 (program_link P' Cs)). clear.
        intros s. unfold does_prefix.
        intros [b [s_b m_b]] m'_m.
        exists b. split; auto.
        clear -m'_m m_b.
        unfold finpref_trace_prefix in m'_m.
        destruct m'; try now auto. simpl in *.
        eapply trace_behavior_prefix_trans'; eauto. unfold trace_finpref_prefix.
        destruct m; eauto. }

      pose proof Target.recombination_blame_prefix_final_UB
                 well_formed_p well_formed_Ct well_formed_P' well_formed_Cs Hmergeable_ifaces
                 (eq_sym Hsame_iface1) (eq_sym Hsame_iface2) closedness HP'Cs_closed
                 m'_maximal P'_Cs_tbc_m' undef_in_m'_p.

      exists Cs, (Goes_wrong (finpref_trace m')).
      repeat (split; [now auto |]).
      rewrite Hsame_iface2; split; [now auto |].
      split; [| split].
      + eapply Target.interface_preserves_closedness_r with (p2 := Ct); eauto.
      + destruct H as [t' [A B]].
        simpl in B. destruct t'; try now auto. congruence.
      + right. unfold behavior_improves_blame.
        eexists; split; eauto. split.
        * destruct m'; simpl in *; try now auto.
          destruct m; simpl in *; try now auto.
        * eauto.
  Qed.

End RSC_DC_MD_Section.
End RSC_DC_MD_Gen.

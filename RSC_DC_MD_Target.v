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
  Hypothesis closedness :
    closed_program (program_link p Ct).
  Hypothesis mains : linkable_mains p Ct.

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
    unfold does_prefix.
    intros m [beh [prg_beh pref]].
    inv prg_beh.
    - assert (ini_res_s: Smallstep.initial_state
                (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct)))
                s) by auto. 
      remember (finpref_trace m) as m_trace.
      destruct (m_trace) as [|top mt].
      -- exists m. split; try (left ; eauto).
         destruct (Target.get_program_behave_sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))).
         exists x; split; auto. destruct m; simpl in Heqm_trace; rewrite <- Heqm_trace. admit. admit. exists x. unfold behavior_app.
         destruct x; try (now rewrite E0_left) ; try (now rewrite E0_left_inf).
      --
        inv H0.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m)  s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    undef_in t' (prog_interface p) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        admit.
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]].
        * destruct G as [? G]. exists m; split.
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          exists b. split; eauto.
          destruct pb_b.          
          ** destruct (sd_initial_determ (det_sem_restricted (program_link p Ct) (allowed_UB (prog_interface Ct))) s s0) ; auto.
             admit. (* annoying but doable *)
          ** destruct (H0 s). simpl. exact H.
          ** now left.
        * eexists; split.
          ** eexists; split.
             ++ econstructor; eauto.
                eapply state_goes_wrong; eauto.
             ++ instantiate (1 := FTbc t'). simpl.
                unfold behavior_prefix. exists (Goes_wrong []); eauto.
                simpl. now rewrite E0_right.
          ** right.
             split; auto. simpl. rewrite Heqm_trace. auto.
             split; auto.
             eexists; split.
             ++ econstructor; eauto.
                eapply state_goes_wrong; eauto.
             ++ simpl. reflexivity.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m) s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    undef_in t' (prog_interface p) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        {
          clear -H1 pref. revert pref. generalize m.  
          induction H1.
          + left. destruct m0 ; destruct pref. destruct x ; inversion H.  destruct t ; inversion H1. exists s. econstructor.
          + destruct ((Target.sem_restricted_UB_lem
                         (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 t1)
              as [step_no_UB12 | step_UB12].
            ++ intros. destruct m0; inv pref. destruct x; inv H2.
               (* we need to know if t1 is prefix of t0, or the opposite *)
               assert (disj : trace_prefix t1 t0 \/ trace_prefix t0 t1). {eapply help. exists t2. rewrite H3. reflexivity. exists t. auto.}
               unfold finpref_trace. destruct (IHstar (FTbc t2)) 
                 as [star_s2_s3 | [s'' [t' [t'_m_prefix [undef_t' [star_s2_s'' [no_final no_step]]]]]]].
               +++ simpl. exists (Diverges []). simpl. now rewrite E0_right.
               +++  admit. (*left. econstructor ; eauto. simpl. *)
               +++ destruct disj as [t1_t0 | t0_t1].
                   ++++ right. admit.
                   ++++ assert (len_t1 : length t1 <= 1) by (eapply (sd_traces (det_sem2 (program_link p Ct))); exact H).
                        (* deals with the case where t0 = [] + absurd cases *)
                        destruct t1; try (destruct t1); destruct t0 ; try (destruct t0);
                        try (inversion t0_t1); try (inversion H0); try (unfold length in len_t1; lia); try (left; exists s1; eapply star_refl).
                        destruct ((Target.sem_restricted_UB_lem
                                     (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 [e]).
                        +++++ left. exists s2. subst ; auto. econstructor. eauto. econstructor. eauto.
                        +++++ right. exists s1. exists []. split ; try split ; try split ; try split ; auto.
                        ++++++ exists [e0]. auto.
                        ++++++ econstructor.
                        ++++++ simpl. intros t'' s' step_s'. apply H2.
                        assert (conj: [e] = t'' /\ s2 = s').
                        {
                          eapply (strong_det_sem2).
                          exact H. eapply Target.sem_restricted_UB_generalises_sem2. exact step_s'.
                        } destruct conj as [eqt eqs]. subst. exact step_s'.
            ++ right. exists s1. exists []. split ; try split ; try split ; try split ; eauto.
               +++ exists (finpref_trace m0). simpl. reflexivity.
               +++ admit. (* might need some hypothesis *)
               +++ econstructor.
               +++ admit. (* ok *)
               +++ intros t' s' step_t'_s'.  admit. (* ok *)
        (*
                 
              right. destruct ((Target.sem_restricted_UB_lem
                         (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 t1)
                 as [step_no_UB12 | step_UB12].
               +++ destruct m0; inversion pref. destruct (IHstar (FTbc t2))
                     as [star_s2_s3 | [s'' [t' [t'_m_prefix [undef_t' [star_s2_s'' [no_final no_step]]]]]]].
                   ++++ simpl. exists (Diverges []). simpl. now rewrite E0_right.
                   ++++ destruct step_UB13. econstructor. admit.
                   ++++
                   admit.
               +++ exists s1. exists []. split ; try split ; try split ; try split.
                 (*exists s2. exists t1. split.
                   ++++ destruct m ; inversion pref. destruct x ; simpl in H2 ; inversion H2.
                        assert (size_t1 : length t1 <= 1). { eapply sd_traces det_sem2. exact H.}
                        simpl in Heqm_trace. simpl.
                        destruct t1.
                        +++++ exists t0. auto.
                        +++++ assert (t1_eq : t1 = []) by (destruct t1; try reflexivity;  unfold length in size_t1; lia).
                        rewrite t1_eq. exists mt. destruct t ; inversion H0. rewrite <- Heqm_trace in H4. inversion H4.
                        rewrite <- H5. rewrite H7. eauto. *)
                   ++++ exists (finpref_trace m). auto. admit.
                    ++++ unfold step in step_UB12. admit. (* ok *)
                   ++++ constructor.
                   ++++ admit. (* ok *)
                   ++++ intros t' s' step_s'. admit. (*ok*) *)
        }
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]]; admit.
      + induction m ; induction t ; try inversion pref.
        (* unfold prefix, behavior_prefix in pref.  *)
        (* destruct H1 as [s s' t T' starT t_ineq H_forever_reactive].*)
        eexists; eauto.
        eexists; eauto.
        eexists; eauto.
        econstructor. eauto.
        econstructor; eauto.
        unfold CS.sem_restricted_UB, SmallstepUB.L_restricted_UB.
        inv H1.
        remember s2 as s'.
        remember (FTbc t) as m.
        assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m)  s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    undef_in t' (prog_interface p) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        admit.
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]]; admit.
        * admit.
        * admit.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m) s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    undef_in t' (prog_interface p) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        admit.
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]]. 
        * destruct G as [? G]. exists m; split.
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          exists b. split; eauto.
          ** admit. (* same as above: annoying but true *)
          ** now left.
        * exists (FTbc t') ; split.
          eexists; split; eauto.
          econstructor; eauto.
          eapply state_goes_wrong. eapply STAR. eauto. eauto.
          simpl. exists (Goes_wrong []). simpl. now rewrite E0_right.
          right.
          split ; eauto. rewrite Heqm_trace ; eauto.
          split ; eauto.
          eexists ; split ; eauto.
          econstructor; eauto.
          eapply state_goes_wrong. eapply STAR. eauto. eauto.
          simpl. eauto.
    - eexists; split.
      + eexists; split; eauto.
        constructor; auto.
      + auto.
  Admitted.

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

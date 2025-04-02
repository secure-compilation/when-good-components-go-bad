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
  Hypothesis disjoint_interface : fdisjoint (domm (prog_interface p)) (domm (prog_interface Ct)).

  Lemma star_max_prefix: forall m t s s',
      (trace_prefix m t) ->
      (Star (CS.sem2 (program_link p Ct)) s t s') ->
      (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                      (allowed_UB (prog_interface Ct))) s (m) s'') \/
        exists s'' t',
          trace_prefix t' (m) /\
            ((exists s2, (initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                       /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
             undef_in t' (prog_interface p)) /\
            Star (CS.sem_restricted_UB (program_link p Ct)
                    (allowed_UB (prog_interface Ct))) s t' s'' /\
            not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                                 (allowed_UB (prog_interface Ct)))) s'') /\
            (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'').
    intros m t s s' pref H1. revert pref. generalize m.  
    induction H1.
    + left. destruct m0 ; destruct pref; inversion H. destruct x ; inversion H. exists s. econstructor.
    + destruct ((Target.sem_restricted_UB_lem
                   (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 t1)
        as [step_no_UB12 | no_step_UB12].
      ++ intros. destruct m0; inv pref. left; exists s1; econstructor.
         remember (e :: m0) as t0.
         (* we need to know if t1 is a prefix of t0, or the opposite *)
         assert (disj : trace_prefix t1 t0 \/ trace_prefix t0 t1).
         {eapply help. exists t2. rewrite H2. reflexivity. exists (x). auto.}
         destruct disj as [t1_t0 | t0_t1].
         +++ destruct t1_t0 as [t3 t3_eq].
             assert (t3_t2: trace_prefix t3 t2).
             {
               destruct t1.
               + exists (x). simpl in *. subst. auto.
               + destruct t0; inversion t3_eq. exists x. subst. inversion H2.
                 rewrite Eapp_assoc in H3. auto. clear -H3. induction t1; auto. inversion H3. apply IHt1 ; auto.
             }
             destruct (IHstar (t3)) 
               as [star_s2_s3 | [s'' [t' [t'_m_prefix [undef_t' [star_s2_s'' [no_final no_step]]]]]]]; try (exists []; now rewrite E0_right)
             ; auto.
             ++++ destruct star_s2_s3 as [s' star_s2_s'].
                  left. exists s'. rewrite t3_eq. econstructor. exact step_no_UB12. exact star_s2_s'. auto.
             ++++ right. exists s''. exists (t1 ** t'). split; try split; try split; try split; auto.
                  +++++ destruct t'_m_prefix. exists x0. rewrite Eapp_assoc. rewrite <- H0. auto.
                  +++++ intro Hex. destruct Hex as [s4 [disj star_s1_s4]]. destruct disj as [init_s1|?]; admit. (*undef*)
                  +++++ econstructor. exact step_no_UB12. exact star_s2_s''. auto.
                  (*
                  rewrite H3.
               remember (t1 ** t') as t''.
               destruct t''.
               +++++ destruct t1; destruct t'; inversion Heqt''. simpl in *.
               right. exists s''. exists []. split ; try split ; try split ; try split ; auto. exists []; auto.
               intro Hex. destruct Hex as [s4 [disj star_s1_s4]]. destruct disj as [init_s1|?]; try contradiction. admit.
               econstructor. exact step_no_UB12. exact star_s2_s''. auto.
               +++++ assert (non_empty: t1 ** t' <> []). (rewrite <- Heqt''; intro; inversion H0).
               right. exists s''. exists [] ; try split ; try split ; try split ; auto; try (exists []; auto).
                  ++++++
                    intro ex. destruct ex as [s' [disj star_s1_s']]. destruct disj as [init|?]; try contradiction. admit.
                  +++++++
                    unfold undef_in, last_comp. simpl. simpl in init.
                  destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability
                              closedness init star_s1_s') as [in_ct|?] ;
                    try (rewrite <- (Target.non_empty_trace_last_comp non_empty star_s1_s') in H0; auto).
                  destruct star_s1_s'; try contradiction. admit.
                  +++++++ admit. *)
                   (*
                  simpl in no_step. destruct (no_step (t1 ** t')). simpl.
                  eapply SmallstepUB.step_UB_allowed; try (simpl in H; exact H). unfold allowed_UB.
                  rewrite (Target.component_conservation_on_empty_trace star_s1_s'). auto.


                  
                    intro ex. destruct ex as [st2 [init_s1 star_st12]]. unfold undef_in in *.
                   subst.
                   assert (t'_t2 : trace_prefix t' t2).
                   {
                     assert (eq: t2 = t3 ** t) by (clear -H3; induction t1; auto; inversion H3 ; auto).
                     simpl in t'_m_prefix. destruct t'_m_prefix as [t3' t3'_eq].
                     exists (t3' ** t). rewrite eq. rewrite <- Eapp_assoc. rewrite <- t3'_eq.  auto.
                   }
                   assert (s''_in_p: CS.current_comp s'' \in (domm (prog_interface p))).
                   (* {
                     simpl in no_step.
                     assert (not_in_ct: not (CS.current_comp s'' \in domm (prog_interface Ct))).
                     {
                       intro in_Ct.
                       assert (extract_star: forall s s' t t',
                                  (trace_prefix t t') ->
                                  (Star (CS.sem2 (program_link p Ct))) s t' s' ->
                                  exists s'', (Star (CS.sem2 (program_link p Ct))) s t s''). admit.
                       
                       destruct (extract_star s2 s3 t' t2 t'_t2 H1) as [s_aux star_aux].
                       destruct (star_aux).
                       + destruct star_s2_s''.
                         ++ eapply no_step. eapply SmallstepUB.step_UB_allowed. admit. admit.
                         ++
                           admit.
                     }
                     assert (star_s1_s'': Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct)))
                                            s1 (t1 ** t') s'') by (econstructor; eauto).
                     destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability closedness non_empty
                                 star_s1_s''); auto.
                   } *) admit.
                   assert (s''_comp_eq: last_comp (t1 ** t') = CS.current_comp s'').
                   {
                     clear -step_no_UB12 star_s2_s'' non_empty.
                     remember (t1 ** t') as t.
                     destruct t; try contradiction. 
                     eapply Target.non_empty_trace_last_comp; eauto.
                     econstructor. exact step_no_UB12. exact star_s2_s''. auto.
                   }
                   rewrite s''_comp_eq. auto. 
                  ++++++ econstructor. exact step_no_UB12. exact star_s2_s''. reflexivity. *)
             
         +++ assert (len_t1 : length t1 <= 1) by (eapply (sd_traces (Target.det_sem2 (program_link p Ct))); exact H).
             (* deals with the case where t0 = [] + absurd cases *)
             destruct t1; try (destruct t1); destruct t0 ; try (destruct t0);
               try (inversion t0_t1); try (inversion H0); try (unfold length in len_t1; lia); try (left; exists s1; eapply star_refl).
             destruct ((Target.sem_restricted_UB_lem
                          (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 [e]).
             ++++ left. exists s2. subst ; auto. econstructor. eauto. econstructor. inv Heqt0. eauto.
             ++++ right. exists s1. exists []. split ; try split ; try split ; try split ; auto.
                  +++++ exists [e0]. subst. auto.
                  +++++ intro ex. destruct ex as [s' [disj star_s1_s']]. destruct disj as [init|?]; try contradiction.
                  inv Heqt0. admit. (* undef *)
                  +++++ econstructor.
                  +++++ intro s1_final. simpl in *. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))).
                  exact s1_final. exact H.
                  +++++ simpl. unfold nostep. intros. intro step_s'.
                  assert (conj: [e0] = t /\ s2 = s').
                  {
                    eapply (Target.strong_det_sem2).
                    exact H. eapply Target.sem_restricted_UB_generalises_sem2. exact step_s'.
                  } destruct conj as [eqt eqs]. subst. apply H3. inv Heqt0. exact step_s'.
      ++ right. exists s1. exists []. split ; try split ; try split ; try split ; eauto.
         +++ exists (m0). simpl. reflexivity.
         +++ intro ex. destruct ex as [s' [disj star_s1_s']]. destruct disj as [init|?]; try contradiction.
             unfold undef_in, last_comp. simpl. simpl in init.
             destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability
                         closedness init star_s1_s') as [in_ct|?] ;
               try (rewrite <- (Target.initial_state_main init);
                    rewrite (Target.component_conservation_on_empty_trace star_s1_s'); auto).
             destruct no_step_UB12. simpl.
             eapply SmallstepUB.step_UB_allowed; try (simpl in H; exact H). unfold allowed_UB.
             rewrite (Target.component_conservation_on_empty_trace star_s1_s'). auto.
         +++ econstructor.
         +++ intro. simpl in H2. eapply (sd_final_nostep (Target.det_sem2 _)). simpl. exact H2. exact H.
         +++ intros t' s' step_t'_s'. apply no_step_UB12.
             assert (Step (CS.sem2 (program_link p Ct)) s1 t' s').
             eapply Target.sem_restricted_UB_generalises_sem2. exact step_t'_s'.
             destruct (Target.strong_det_sem2 H H2). subst. auto.
  Admitted.
  
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
                (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s) by auto. 
        inv H0.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m)  s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    ((exists s2, (initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                               undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        {
          destruct m; inversion pref; simpl in pref.
          ++ assert (pref' : trace_prefix t0 t) by (exists []; subst; now rewrite E0_right). subst. eapply (star_max_prefix pref' H1).
          ++ destruct x; inversion H0. assert (pref' : trace_prefix t0 t) by (exists (t1); subst; auto).
             subst. eapply (star_max_prefix pref' H1).
        }
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]].
        * destruct G as [? G]. exists m; split.
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          exists b. split; eauto.
          destruct pb_b.          
          ** destruct (sd_initial_determ (Target.det_sem_restricted (program_link p Ct) (allowed_UB (prog_interface Ct))) s s0) ; auto.
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
             split; auto. simpl. split; try (apply UNDEF; eauto). exists (Goes_wrong t'). split ; auto.
             econstructor. eauto. econstructor; eauto.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m) s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    ((exists s2, (initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                     undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        {
          destruct m; inversion pref; simpl in pref.
          destruct x; inversion H0. assert (pref' : trace_prefix t0 t) by (exists (t1); subst; auto).
             subst. simpl. eapply (star_max_prefix pref' H1).
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
                    ((exists s2, (initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                     undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        { destruct x; inversion H0.
          assert (pref': trace_prefix (finpref_trace m) t)  by (exists []; subst; now rewrite E0_right).
          eapply (star_max_prefix pref' H2).
        }
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]]; admit.
        * admit.
        * admit.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m) s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    ((exists s2, (initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                     undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                                         (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).        
        {
          destruct m; inversion pref; simpl in pref.
          ++ assert (pref' : trace_prefix t0 t) by (exists []; subst; now rewrite E0_right). subst. eapply (star_max_prefix pref' H1).
          ++ destruct x; inversion H0. assert (pref' : trace_prefix t0 t) by (exists (t1); subst; auto).
             subst. eapply (star_max_prefix pref' H1).
        }
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
          split; auto. simpl.
          split; try (apply UNDEF; eauto).
          exists (Goes_wrong t'). split; auto.
          econstructor. eauto. econstructor; eauto.
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

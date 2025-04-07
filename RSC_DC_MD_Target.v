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

  Lemma star_convert : forall s t s',
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t s' ->
      Star (CS.sem2 (program_link p Ct)) s t s'.
  Proof.
    intros. induction H; econstructor. eapply Target.sem_restricted_UB_generalises_sem2. eauto. eauto. eauto.
  Qed.
  
  Lemma last_comp_in_interface_p : forall t t' s s' s'0,
      (CS.initial_state (program_link p Ct) s \/ t' <> []) ->
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s'0 ->
      Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'0 ->
      ((t = t' /\ CS.final_state (program_link p Ct) s' /\ ~ CS.final_state (program_link p Ct) s'0) \/
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
        destruct disj as [[eq [final nofinal]] | [ineq pref]]; try contradiction.
      + eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))); eauto.
        eapply Target.sem_restricted_UB_generalises_sem2. exact H.
      + destruct pref. apply ineq. destruct t; auto; inversion H1.
      + eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. eauto. auto.
      + eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. eauto. auto.
      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
          eapply IHstar2; eauto. left. split; [|split; auto].
          {clear -eq. induction t0; auto. inversion eq. traceEq. }
      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
          eapply IHstar2; eauto. right. split.
          {clear -ineq. intro. induction t0; auto. apply ineq. traceEq. }
          destruct pref. exists x. clear -H0. induction t0; inversion H0; auto.
  Qed.

  
  Lemma star_max_prefix: forall m t s s',
      trace_prefix m t ->
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                      (allowed_UB (prog_interface Ct))) s m s'') \/
        exists s'' t',
          trace_prefix t' m /\
            (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
              /\ exists s2, Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
             undef_in t' (prog_interface p)) /\
            Star (CS.sem_restricted_UB (program_link p Ct)
                    (allowed_UB (prog_interface Ct))) s t' s'' /\
            not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                                 (allowed_UB (prog_interface Ct)))) s'') /\
            Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s''.
  Proof.
    intros m t s s' pref H1. revert pref. revert m.
    induction H1.
    - left. destruct m; destruct pref; inversion H. exists s. econstructor.
    - destruct ((Target.sem_restricted_UB_lem
                   (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 t1)
        as [step_no_UB12 | no_step_UB12].
      + intros. destruct m; inv pref. left; exists s1; econstructor.
        remember (e :: m) as t0.
        (* we need to know if t1 is a prefix of t0, or the opposite *)
        assert (disj : trace_prefix t1 t0 \/ trace_prefix t0 t1).
        { eapply help. exists t2. rewrite H2. reflexivity. exists x. auto. }
        destruct disj as [t1_t0 | t0_t1].
        * destruct t1_t0 as [t3 t3_eq].
          assert (t3_t2: trace_prefix t3 t2).
          { destruct t1.
            - exists (x). simpl in *. subst. auto.
            - destruct t0; inversion t3_eq. exists x. subst. inversion H2.
              rewrite Eapp_assoc in H3. auto. clear -H3. induction t1; auto. inversion H3. apply IHt1 ; auto.  }
          destruct (IHstar (t3))
            as [star_s2_s3 |
                 [s'' [t' [t'_m_prefix [undef_t' [star_s2_s'' [no_final no_step]]]]]]];
            try (exists []; now rewrite E0_right); auto.
          -- destruct star_s2_s3 as [s' star_s2_s'].
             left. exists s'. rewrite t3_eq. econstructor. exact step_no_UB12. exact star_s2_s'. auto.
          -- assert (disj: t' = t2 \/ t' <> t2).
             { clear -t3_t2 t'_m_prefix. destruct t3_t2. destruct t'_m_prefix.
               destruct x.
               - destruct x0; try (left; traceEq; done).
                 right. intro. subst. induction t'; inversion H1; auto.
               - right. intro. subst. induction (t'); induction x0; inversion H1; auto. }
             destruct disj as [eq|ineq].
             ++ left. exists s''. subst. econstructor. exact step_no_UB12. exact star_s2_s''.
                rewrite t3_eq. destruct t3_t2; destruct t'_m_prefix.
                assert (eq: t3 = t2).
                { rewrite H3 in H0. rewrite Eapp_assoc in H0.
                  remember (x1 ** x0) as t_ex.
                  destruct t_ex.
                  + destruct x1; inversion Heqt_ex. rewrite H3. traceEq.
                  + clear -H0. exfalso. induction t2; inversion H0; auto. }
                rewrite eq. auto.
             ++ right. exists s''. exists (t1 ** t'). split; [| split; [| split]]; auto.
                ** destruct t'_m_prefix. exists x0. rewrite Eapp_assoc. rewrite <- H0. auto.
                ** intro Hex. destruct Hex as [disj [s4 star_s1_s4]].
                   assert (star_s1_s'': Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s1 (t1 ** t') s'').
                   { econstructor. exact step_no_UB12. eauto. auto. }
                   unfold undef_in. remember (t1 ** t') as t. destruct t.
                   --- inversion disj as [init_s1|not_nil]; try contradiction.
                       assert (pref: trace_prefix t' t2).
                       { clear - t3_t2 t'_m_prefix. destruct t3_t2. destruct t'_m_prefix.
                         subst. exists (x0 ** x). traceEq. }
                       destruct t1; inversion Heqt.
                       eapply (last_comp_in_interface_p (or_introl init_s1)). eapply star_step. exact H. exact H1. reflexivity.
                       exact star_s1_s''. auto.
                       right. split. intro eq. apply ineq. simpl in *. rewrite <- H0. rewrite eq. done. exists t2. auto.
                   --- assert (not_nil': t1 ** t' <> []). { intro. rewrite H0 in Heqt. inv Heqt. }
                       destruct (esym Heqt). 
                       eapply last_comp_in_interface_p. eauto. eapply star_step. eauto. eauto. reflexivity.
                       exact star_s1_s''. eauto. right. split. intro eq. apply ineq. clear -eq. induction t1; inversion eq; auto.
                       { clear - t3_t2 t'_m_prefix. destruct t3_t2. destruct t'_m_prefix.
                         subst. exists (x0 ** x). traceEq. }
                ** econstructor. exact step_no_UB12. exact star_s2_s''. auto.
        *  assert (len_t1 : length t1 <= 1) by (eapply (sd_traces (Target.det_sem2 (program_link p Ct))); exact H).
           (* deals with the case where t0 = [] + absurd cases *)
           destruct t1; try (destruct t1); destruct t0 ; try (destruct t0);
             try (inversion t0_t1); try (inversion H0); try (unfold length in len_t1; lia); try (left; exists s1; eapply star_refl).
           destruct ((Target.sem_restricted_UB_lem
                        (globalenv (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))))) s1 s2 [e]).
           -- left. exists s2. subst ; auto. econstructor. eauto. econstructor. inv Heqt0. eauto.
           -- right. exists s1. exists []. split ; try split ; try split ; try split ; auto.
              ++ exists [e0]. subst. auto.
              ++ intro ex. destruct ex as [disj [s' star_s1_s']].
                 destruct disj as [init|?]; try contradiction.
                 inv Heqt0. eauto.
              ++ econstructor.
              ++ intro s1_final. simpl in *. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))).
                 exact s1_final. exact H.
              ++ simpl. unfold nostep. intros. intro step_s'.
                 assert (conj: [e0] = t /\ s2 = s').
                 {
                   eapply (Target.strong_det_sem2).
                   exact H. eapply Target.sem_restricted_UB_generalises_sem2. exact step_s'.
                 } destruct conj as [eqt eqs]. subst. apply H3. inv Heqt0. exact step_s'.
      + right. exists s1. exists []. split ; try split ; try split ; try split ; eauto.
        * exists m. simpl. reflexivity.
        * intro ex. destruct ex as [disj [s' star_s1_s']].
          inversion disj as [init|?]; try contradiction.
          unfold undef_in, last_comp. simpl. simpl in init.
          destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability
                      closedness disj star_s1_s') as [in_ct|?] ;
            try (rewrite <- (Target.initial_state_main init);
                 rewrite (Target.component_conservation_on_empty_trace star_s1_s'); auto).
          destruct no_step_UB12. simpl.
          eapply SmallstepUB.step_UB_allowed; try (simpl in H; exact H). unfold allowed_UB.
          rewrite (Target.component_conservation_on_empty_trace star_s1_s'). auto.
        * econstructor.
        * intro. simpl in H2. eapply (sd_final_nostep (Target.det_sem2 _)). simpl. exact H2. exact H.
        * intros t' s' step_t'_s'. apply no_step_UB12.
          assert (Step (CS.sem2 (program_link p Ct)) s1 t' s').
          eapply Target.sem_restricted_UB_generalises_sem2. exact step_t'_s'.
          destruct (Target.strong_det_sem2 H H2). subst. auto.
  Qed.


  Lemma parallel_star_prefix: forall s0 t t' s s',
      (Star (CS.sem2 (program_link p Ct)) s0 t s) ->
      (Star (CS.sem2 (program_link p Ct)) s0 t' s') ->
      (CS.final_state (program_link p Ct) s') ->
      trace_prefix t t'.
    intros s0 t t' s s' star_t star_t' final_s'.
    generalize s' t' star_t' final_s'. clear s' star_t' final_s' t'.
    induction star_t; intros s' t' star_t' final_s'.
    - exists t'. auto.
    - subst. induction star_t'.
      + exfalso. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) s final_s'). exact H.
      + destruct (Target.strong_det_sem2 H H0). subst.
        destruct (IHstar_t s4 t3 star_t' final_s').
        exists x. subst. traceEq.
  Qed.

  
  Lemma parallel_star_prefix_bis : forall s0 t t' s s',
      (Star (CS.sem2 (program_link p Ct)) s0 t s) ->
      (Star (CS.sem2 (program_link p Ct)) s0 t' s') ->
      (Nostep (CS.sem2 (program_link p Ct)) s') ->
      trace_prefix t t'.
    intros s0 t t' s s' star_t star_t' nostep.
    generalize s' t' star_t' nostep. clear s' star_t' nostep t'.
    induction star_t; intros s' t' star_t' nostep.
    - exists t'. auto.
    - subst. induction star_t'.
      + exfalso. eapply nostep. exact H.
      + destruct (Target.strong_det_sem2 H H0). subst.
        destruct (IHstar_t s4 t3 star_t' nostep).
        exists x. subst. traceEq.
  Qed.

  
  Lemma parallel_star_prefix_comp : forall s0 t t' s s',
      (Star (CS.sem2 (program_link p Ct)) s0 t s) ->
      (Star (CS.sem2 (program_link p Ct)) s0 t' s') ->
      trace_prefix t' t \/ trace_prefix t t'.
    intros s0 t t' s s' star_t star_t'.
    generalize s' t' star_t'. clear s' star_t' t'.
    induction star_t; intros s' t' star_t'.
    - right. exists t'. auto.
    - subst. destruct star_t'.
      + left. exists (t1 ** t2). traceEq.
      + destruct (Target.strong_det_sem2 H H0). subst.
        destruct (IHstar_t s4 t3 star_t'); destruct H1.
        * left. exists x. traceEq.
        * right. exists x. traceEq.
  Qed.
  
  Lemma parallel_star_prefix_restricted : forall s0 t t' s s',
      (Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s0 t s) ->
      (Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s0 t' s') ->
      (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s') ->
      trace_prefix t t'.
    intros s0 t t' s s' star_t star_t' nostep.
    generalize s' t' star_t' nostep. clear s' star_t' nostep t'.
    induction star_t; intros s' t' star_t' nostep.
    - exists t'. auto.
    - subst. induction star_t'.
      + exfalso. eapply nostep. exact H.
      + destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 H)
                    (Target.sem_restricted_UB_generalises_sem2 H0)). subst.
        destruct (IHstar_t s4 t3 star_t' nostep).
        exists x. subst. traceEq.
  Qed.
  
  
  Lemma forever_silent_contradiction : forall t t' s s' s'',
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      Nostep (CS.sem2 (program_link p Ct)) s' ->
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s'' ->
      Forever_silent (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'' -> False .
  Proof.
    intros t t' s s' s'' star nostep. revert s'' t'.
    induction star; intros s'' t' star' forever.
    - destruct star'.
      + destruct forever. eapply nostep. eapply Target.sem_restricted_UB_generalises_sem2. eauto.
      + eapply nostep. eapply Target.sem_restricted_UB_generalises_sem2. eauto.
    - destruct star'.
      + destruct forever. destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
        eapply IHstar; auto. econstructor. auto.
      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
        eapply IHstar; auto. eauto. auto.
  Qed.

  
  Lemma forever_silent_contradiction_bis : forall t t' s s' s'',
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      Nostep (CS.sem2 (program_link p Ct)) s'' ->
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s'' ->
      Forever_silent ((CS.sem2 (program_link p Ct))) s' -> False .
  Proof.
    intros t t' s s' s'' star nostep star'. revert star. revert s' t.
    induction star'; intros s' t0 star forever.
    - destruct star.
      + destruct forever. eapply nostep. eauto.
      + eapply nostep. eauto.
    - destruct star.
      + destruct forever.
        destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 H) H1). subst.
        eapply IHstar'; auto. econstructor. auto.
      + destruct (Target.strong_det_sem2 H1 (Target.sem_restricted_UB_generalises_sem2 H)). subst.
        eapply IHstar'; auto. eauto. auto.
  Qed.
 
  
  Lemma forever_reactive_contradiction : forall t T s s',
      Star (CS.sem2 (program_link p Ct)) s t s' ->
      Nostep (CS.sem2 (program_link p Ct)) s' ->
      Forever_reactive (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s T -> False .
  Proof.
    intros t T s s' star nostep. revert T.
    induction star; intros T forever.
    - destruct forever. destruct H; try contradiction. eapply nostep. eapply Target.sem_restricted_UB_generalises_sem2. eauto.
    - destruct forever. destruct H1; try (subst; contradiction).
      destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
      destruct t0.
      + destruct t3; try contradiction. eapply IHstar; auto. econstructor. exact H3. auto. eauto.
      + destruct forever. eapply IHstar; auto. econstructor. eapply star_trans. exact H3. exact H0. reflexivity.
        intro eq. clear -eq H4. induction t3; inversion eq; auto.  eauto.
  Qed.

  Lemma forever_reactive_contradiction_bis : forall t T s s',
      Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t s' ->
      Nostep (CS.sem2 (program_link p Ct)) s' ->
      Forever_reactive (CS.sem2 (program_link p Ct)) s T -> False .
  Proof.
    intros t T s s' star nostep. revert T.
    induction star; intros T forever.
    - destruct forever. destruct H; try contradiction. eapply nostep. eauto.
    - destruct forever. destruct H1; try (subst; contradiction).
      destruct (Target.strong_det_sem2 H1 (Target.sem_restricted_UB_generalises_sem2 H)). subst.
      destruct t1.
      + destruct t3; try contradiction. eapply IHstar; auto. econstructor. exact H3. auto. eauto.
      + destruct forever. eapply IHstar; auto. econstructor. eapply star_trans. exact H3. exact H0. reflexivity.
        intro eq. clear -eq H4. induction t3; inversion eq; auto.  eauto.
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
                    (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ exists s2, Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                               undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        {
          destruct m; inversion pref; simpl in pref.
          ++ assert (pref' : trace_prefix t0 t) by (exists []; subst; now rewrite E0_right). subst.
             eapply (star_max_prefix pref' H1).
          ++ destruct x; inversion H0. assert (pref' : trace_prefix t0 t) by (exists (t1); subst; auto).
             subst. eapply (star_max_prefix pref' H1).
        }
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]].
         * destruct G as [? G].
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          destruct b as [t0 | t0 | t0 | t0].
          -- exists m; split.
             ++ exists (Terminates t0). split; eauto.
                assert (t0 = t).
                { (*clear -H H1 H2 pb_b.*)
                  remember (Terminates t0) as beh.
                  destruct pb_b; try (exfalso; apply (H0 s H)).
                  simpl in *. destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
                  destruct H3; inversion Heqbeh. subst. simpl in *.
                  assert (Star (CS.sem2 (program_link p Ct)) s t0 s'0). { clear -H3; induction H3; econstructor; eauto.
                  eapply Target.sem_restricted_UB_generalises_sem2. simpl. eauto. }
                  destruct (parallel_star_prefix H1 H5 H4).
                  destruct (parallel_star_prefix H5 H1 H2).
                  subst. destruct x0; try rewrite E0_right; auto. exfalso. rewrite Eapp_assoc in H7. clear -H7.
                  induction t; inversion H7; auto. }
                subst. auto.
             ++ now left.
          -- exfalso.
             remember (Diverges t0) as beh. destruct pb_b; try destruct (H0 s H).
             destruct H3; inv Heqbeh. destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
             clear - H1 H2 H3 H4.
             eapply forever_silent_contradiction; eauto. eapply sd_final_nostep. exact (Target.det_sem2 (program_link p Ct)). auto.
          -- exfalso.
             remember (Reacts t0) as beh. destruct pb_b; try destruct (H0 s H).
             destruct H3; inv Heqbeh. destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
             (*clear - H1 H2 H3.*)
             eapply forever_reactive_contradiction; eauto. eapply sd_final_nostep. exact (Target.det_sem2 (program_link p Ct)). auto.
          -- destruct (@help t0 (finpref_trace m) t).
             { remember (Goes_wrong t0) as beh. destruct pb_b; try (destruct (H0 s H); done).
               destruct H3; inversion Heqbeh. subst.
               destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
               assert (Star (CS.sem2 (program_link p Ct)) s t0 s'0). clear -H3. induction H3; econstructor; eauto;
                 try (eapply Target.sem_restricted_UB_generalises_sem2; eauto; done).
               eapply parallel_star_prefix. exact H6. exact H1. exact H2. } 
             { destruct m; inversion pref; try (exists []; traceEq; done).
               destruct x0; inversion H0. exists t2. auto. }
             ++ exists (FTbc t0); split.
                ** exists (Goes_wrong t0). split; eauto.
                   simpl. exists (Goes_wrong nil).
                   simpl; now rewrite E0_right.
                ** assert (disj: (finpref_trace m = t0) \/ (finpref_trace m <> t0)).
                   {  clear -H0. destruct H0.
                      destruct x.
                      - left. rewrite H. traceEq.
                      - right. intro eq. rewrite eq in H. clear -H. induction t0; inversion H; auto. }
                   destruct m; destruct disj as [eq | ineq]; inversion pref; try (simpl in *; left; rewrite eq; done);
                     try (subst; right; split; [| split]); simpl; auto; try (eexists (Goes_wrong _); simpl; eauto); simpl in *.
                   --- remember (Goes_wrong t) as beh. destruct pb_b; try destruct (H3 s H).
                       destruct H4; inv Heqbeh. destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H3).
                       unfold undef_in.
                       eapply last_comp_in_interface_p. left. exact ini_res_s. exact H1. exact H4. auto. left.
                       split; [auto|split;auto].
                   --- remember (Goes_wrong t0) as beh. destruct pb_b; try destruct (H3 s H).
                       destruct H4; inv Heqbeh. destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H3).
                       unfold undef_in. assert (eq: last_comp t0= CS.current_comp s'0). 
                       { destruct t0.
                         - rewrite <- (Target.component_conservation_on_empty_trace H4). unfold last_comp. simpl.
                           rewrite (Target.initial_state_main H). auto.
                         - eapply Target.non_empty_trace_last_comp. intro; inversion H7. exact H4. }
                        rewrite eq. 
                       destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability closedness
                                   (or_introl ini_res_s) H4); try done.
                       exfalso. (* destruct H0 as [t' ?]. destruct t'; try (rewrite E0_right in H0; contradiction). subst.*)
                       clear G eq x H0 pref H ini_res_s H3 ineq. revert H4 H5 H6 H7. revert s'0 t0.
                       induction H1; intros s'0 t0 star_s'0 nostep nofinal in_Ct; destruct star_s'0.
                       +++ eapply nofinal. exact H2.
                       +++ eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) s1 H2).
                           eapply Target.sem_restricted_UB_generalises_sem2. exact H.
                       +++ eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. exact H. auto.
                       +++ subst. eapply IHstar; eauto.
                           destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H3)). subst.
                           exact star_s'0.
                   --- remember (Goes_wrong t0) as beh. destruct pb_b; try destruct (H3 s H).
                       destruct H5; inv Heqbeh.
                       destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H4).
                       unfold undef_in. assert (eq: last_comp t0= CS.current_comp s'0). 
                       { destruct t0.
                         - rewrite <- (Target.component_conservation_on_empty_trace H5). unfold last_comp. simpl.
                           rewrite (Target.initial_state_main H). auto.
                         - eapply Target.non_empty_trace_last_comp. intro; inversion H8. exact H5. }
                       rewrite eq. 
                       destruct (Target.state_component_on_linking well_formed_p well_formed_Ct linkability closedness
                                   (or_introl ini_res_s) H5); try done.
                       exfalso. (* destruct H0 as [t' ?]. destruct t'; try (rewrite E0_right in H0; contradiction). subst.*)
                       clear - H1 H2 H5 H6 H7 H8. revert H5 H6 H7 H8. revert s'0 t0.
                       induction H1; intros s'0 t0 star_s'0 nostep nofinal in_Ct; destruct star_s'0.
                       +++ eapply nofinal. exact H2.
                       +++ eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) s1 H2).
                           eapply Target.sem_restricted_UB_generalises_sem2. exact H.
                       +++ eapply nostep. simpl. eapply SmallstepUB.step_UB_allowed. exact H. auto.
                       +++ subst. eapply IHstar; eauto.
                           destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H3)). subst.
                           exact star_s'0.
                       +++ destruct (H4 s H).
             ++ destruct m as [m | m | m]; try inv pref.
                { simpl in *.
                  assert (t = t0).
                  { clear -H H0 H1 H2 pb_b.
                    destruct H0. destruct x; traceEq. exfalso.
                    remember (Goes_wrong (t ** e :: x)) as beh.
                    destruct pb_b; try (apply (H0 s); auto).
                    simpl in *. destruct ((sd_initial_determ (Target.det_sem2 (program_link p Ct))) s s0 H H0).
                    destruct H3; inversion Heqbeh. subst. clear -H1 H2 H3.
                    induction H1.
                    - remember (E0 ** e :: x) as t. simpl in Heqt. induction H3; inversion Heqt.
                      eapply ((sd_final_nostep (Target.det_sem_restricted (program_link p Ct) (allowed_UB (prog_interface Ct)))) s1 H2).
                      exact H.
                    - subst. remember ((t1 ** t2) ** e :: x) as t.
                      destruct H3.
                      + induction (t1 ** t2); simpl in *; subst; inversion Heqt.
                      + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H0)). subst.
                        assert (eq : (t2 ** e :: x) = t3) by (clear -H4; induction t0; inversion H4; auto).
                        clear -H1 H2 H3 eq IHstar. subst. apply IHstar; auto. }
                  subst t0.
                  exists (FTbc t); split.
                  ** exists (Goes_wrong t); split; eauto.
                     simpl. exists (Goes_wrong nil); simpl; eauto. traceEq.
                  ** right. split; [| split].
                     --- simpl. exists []. traceEq.
                     --- simpl. remember (Goes_wrong t) as beh.
                         destruct pb_b; try destruct (H3 s ini_res_s).
                         destruct H4; inv Heqbeh.
                         destruct ((sd_initial_determ (Target.det_sem2 (program_link p Ct))) s s0 H H3).
                         unfold undef_in.
                         eapply last_comp_in_interface_p. left. eauto. eauto. exact H4. eauto.
                         left. split; [auto|split; auto]. 
                     --- eexists; split; eauto. simpl. reflexivity. }
                { exists (FTbc m); split.
                  ** exists (Goes_wrong t0). split; eauto.
                     simpl in *. destruct H0. exists (Goes_wrong x1); eauto. subst; eauto.
                  ** now left. }
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
                    (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ exists s2, Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
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
        destruct G as [G | [s'' [t' [t'_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]].
        * destruct G as [s'' G].
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          destruct pb_b; try destruct (H0 s H).
          destruct ((sd_initial_determ (Target.det_sem2 (program_link p Ct))) s s0 H H0).
          destruct H3.
          -- exfalso. eapply forever_silent_contradiction_bis.
             exact H1. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))).
             exact H4. exact H3. auto.
          -- exists m. destruct m; inversion pref. split; [| left; done].
             assert (t = t0).
             { clear -H1 H2 H3 H4. revert H2 H3 H4. revert s'0 t0.
               induction H1; intros s0 t0 forever_s' star forever_s0.
               - clear - star forever_s'. induction star; auto.
                 destruct forever_s'.
                 destruct (Target.strong_det_sem2 H1 (Target.sem_restricted_UB_generalises_sem2 H)).
                 subst. simpl. eapply IHstar. auto.
               - induction star.
                 + destruct forever_s0. 
                   destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H2)).
                   subst. simpl. eapply (IHstar); auto. econstructor. auto.
                 + destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H2)).
                   subst. assert (t2 = t3). eapply IHstar; auto. exact star. auto. subst. done. }
             subst. exists (Diverges t0). split. econstructor; eauto. econstructor; eauto.
             simpl. exists x. done.
          -- exfalso. clear -H1 H2 H3.
             
             assert (exists t', exists T', trace_prefix t t' /\ T = t' *** T').
             { 
               assert (F: forall n, exists t' s' T', (n < length t') /\ (T = t' *** T')
                                        /\ (Star (CS.sem2 (program_link p Ct)) s t' s')).
               { clear -H3. intro n. revert H3. revert s T. induction n; intros s T forever.
                 - destruct forever. exists t, s2, T. split; [|split;[|auto]].
                   destruct t; try contradiction. simpl. apply Nat.lt_0_succ. auto.
                   eapply (star_convert H).
                 - destruct forever. destruct (IHn s2 T forever) as [t' [s' [T' [len [pref star]]]]].
                   exists (t ** t'), s', T'. split; [|split].
                   + rewrite (app_length t t'). assert (1 <= length t).
                     { destruct t; try contradiction. simpl. lia. } lia.
                   + subst. traceEq.
                   + eapply star_trans. exact (star_convert H). exact star. done. }
               destruct (F (length t)) as [t' [s'' [T' [ineq [eq star]]]]].
               assert (exists T'', T = t *** T'').
               { clear -H1 H3. revert H3. revert T.
                 induction H1; intros T forever. exists T. auto.
                 admit.
                 
                 } admit. (*
               destruct (behavior_prefix_comp (ex_intro _ T' eq) (H)) as [tpref|tpref];
                 try (destruct tpref; subst; rewrite (app_length t' x0) in ineq; lia; done). *)
             }
             destruct H as [t'' [T' [[t' eqt'] eq]]]. subst.
             remember (t' *** T') as T. rewrite Eappinf_assoc in H3. rewrite <- (HeqT) in H3.
             assert (Forever_reactive (CS.sem2 (program_link p Ct)) s' T).
             { clear -H3 H1. revert H1 H3. revert t s' s T. cofix Hind.
               intros t s' s T star forever.  admit.
               (* destruct forever. 
               destruct (parallel_star_prefix_comp star (star_convert H)).
               + admit.
               + *)
             } clear HeqT. clear -H H2.
             destruct H. clear H1.
             induction H; try contradiction. destruct H2.
             destruct (Target.strong_det_sem2 H2 H). subst. simpl in *. auto.
          -- destruct m; inversion pref.
             assert (tmp: trace_prefix t1 t0).
             { eapply parallel_star_prefix_restricted. eauto. eauto. eauto. }
             exists (FTbc t1). split.
             ++ exists (Goes_wrong t0). split. econstructor; eauto. econstructor; eauto.
                simpl. destruct tmp. exists (Goes_wrong x0). simpl. subst. done. 
             ++ left; done.
        * destruct m; inversion pref. simpl in *.
          destruct t'_m.
          destruct x0.
          -- assert (t' = t0) by traceEq. subst.
             exists (FTbc t'). split.
             ++ exists (Goes_wrong t'). split. econstructor; eauto. econstructor; eauto.
                simpl. exists (Goes_wrong []). simpl. traceEq.
             ++ left; traceEq.
          -- 
            exists (FTbc t'). split.
            ++ exists (Goes_wrong t'). split. econstructor; eauto. econstructor; eauto.
                simpl. exists (Goes_wrong []). simpl. traceEq.
            ++ right. simpl. split; [exists (e :: x0); traceEq | split].
               unfold undef_in. eapply last_comp_in_interface_p. left; eauto.
               exact H1. exact STAR. auto.
               right. clear -pref H3. destruct pref. inv H.
               destruct x; inv H1. split.
               { intro. induction t'; inversion H; auto. }
               { exists (e :: x0 ** t0). traceEq. }
               exists (Goes_wrong t'). split; auto. econstructor; eauto. econstructor; eauto.
      + destruct m; inversion pref. simpl in pref.
        assert (F: forall n, exists t' s', (n < length t') /\ (behavior_prefix t' (Reacts T))
                                 /\ (Star (CS.sem2 (program_link p Ct)) s t' s')).
        { clear -H1. intro n. revert H1. revert s T. induction n; intros s T forever.
          - destruct forever. exists t, s2. split; [|split;[exists (Reacts T); done|auto]].
            destruct t; try contradiction. simpl. apply Nat.lt_0_succ.
          - destruct forever.
            destruct (IHn s2 T forever) as [t' [s' [len [pref star]]]].
            exists (t ** t'), s'. split; [|split].
            + rewrite (app_length t t'). assert (1 <= length t).
              { destruct t; try contradiction. simpl. lia. } lia.
            + destruct pref. exists x. destruct x; inversion H1. simpl. traceEq.
            + eapply star_trans. exact H. exact star. done. }
        destruct (F (length t)) as [t' [s' [ineq [Tpref star]]]].
        destruct (behavior_prefix_comp Tpref (ex_intro _ x H0)) as [tpref|tpref];
          try (destruct tpref; subst; rewrite (app_length t' x0) in ineq; lia; done).
        assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                                   (allowed_UB (prog_interface Ct))) s t  s'') \/
                exists s'' t',
                  trace_prefix t' t /\
                    (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ exists s2, Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
                     undef_in t' (prog_interface p)) /\
                    Star (CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct))) s t' s'' /\
                    not (final_state ((CS.sem_restricted_UB (program_link p Ct)
                            (allowed_UB (prog_interface Ct)))) s'') /\
                    (Nostep (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s'')).
        { apply (star_max_prefix tpref star). }
        destruct G as [[s'' star_s''] | [s'' [t'' [t''_m [UNDEF [STAR [NOT_FINAL NOSTEP]]]]]]].
        * destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          destruct pb_b; try destruct (H2 s H).
          destruct ((sd_initial_determ (Target.det_sem2 (program_link p Ct))) s s0 H H2).
          destruct H3.
          -- exfalso.
             eapply forever_reactive_contradiction_bis. exact H3.
             eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct))); auto.
             eauto.
          -- exfalso. admit. (* reactive and silent in parallel *)
          -- exists (FTbc t). split; auto.
             exists (Reacts T0). split. econstructor; eauto. econstructor; eauto.
             simpl.
             assert (Forever_reactive (CS.sem2 (program_link p Ct)) s T0).
             { clear - H3. revert H3. revert s T0. 
               cofix Hind. intros s T forever.
               destruct forever.
               assert (Star (CS.sem2 (program_link p Ct)) s1 t s2).
               { clear -H. induction H; econstructor.
                 eapply Target.sem_restricted_UB_generalises_sem2. exact H. eauto. eauto. }
               econstructor. exact H1. auto. eapply Hind. auto. }
             assert (T = T0).
             { clear -H1 H4. revert H1 H4. revert s T T0.
               (* cofix Hind. *) admit.
             }
             admit. (* forever_reactive in sem2 and semUB *)
          -- assert (tmp: trace_prefix t t0).
             { eapply parallel_star_prefix_restricted. eauto. eauto. eauto. }
             exists (FTbc (t)). split.
             ++ exists (Goes_wrong t0). split. econstructor; eauto. econstructor; eauto.
                simpl. destruct tmp. exists (Goes_wrong x0). simpl. subst. done. 
             ++ left; done.
        * exists (FTbc t''). split; [|right; split; [| split]].
          -- exists (Goes_wrong t''). split; try done. econstructor; eauto. econstructor; eauto.
             simpl. exists (Goes_wrong []). simpl. traceEq.
          -- simpl. done.
          -- simpl. eapply UNDEF. split. left; auto. exists s''; eauto.
          --  exists (Goes_wrong t''). split; try done. econstructor; eauto. econstructor; eauto.
      + assert (G: (exists s'', Star (CS.sem_restricted_UB (program_link p Ct)
                        (allowed_UB (prog_interface Ct))) s (finpref_trace m) s'') \/
                exists s'' t',
                  trace_prefix t' (finpref_trace m) /\
                    (((initial_state (CS.sem2 (program_link p Ct)) s \/ t' <> [])
                               /\ exists s2, Star (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct))) s t' s2) ->
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
        * destruct G as [? G].
          destruct (Target.get_program_behave_sem_restricted_UB  (program_link p Ct) (allowed_UB (prog_interface Ct))) as [b pb_b].
          destruct b as [t0 | t0 | t0 | t0].
          -- exfalso. clear -pb_b H H1 H2 H3.
             remember (Terminates t0) as beh. destruct pb_b; inversion Heqbeh.
             destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
             destruct H4; inversion Heqbeh. subst.
             clear - H1 H2 H3 H4 H6. revert H4 H6. revert s'0 t0.
             induction H1 ; intros s'0 t0 star final_s'.
             ++ induction star; try auto. eapply H2. eapply Target.sem_restricted_UB_generalises_sem2. eauto.
             ++ destruct star. eapply (sd_final_nostep (Target.det_sem2 (program_link p Ct)) s final_s'); eauto.
                destruct (Target.strong_det_sem2 H (Target.sem_restricted_UB_generalises_sem2 H4)). subst.
                eapply IHstar; eauto.
          -- exfalso. 
             remember (Diverges t0) as beh. destruct pb_b; inversion Heqbeh.
             destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
             destruct H4; inversion Heqbeh. subst.
             eapply forever_silent_contradiction; eauto.
          -- exfalso.
             remember (Reacts t0) as beh. destruct pb_b; inversion Heqbeh.
             destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
             destruct H4; inversion Heqbeh. subst.
             eapply forever_reactive_contradiction; eauto.
          -- destruct (@help t0 (finpref_trace m) t).
             { remember (Goes_wrong t0) as beh. destruct pb_b; try (destruct (H0 s H); done).
               destruct H4; inversion Heqbeh. subst.
               destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
               assert (Star (CS.sem2 (program_link p Ct)) s t0 s'0). clear -H4. induction H4; econstructor; eauto;
                 try (eapply Target.sem_restricted_UB_generalises_sem2; eauto; done).
               eapply parallel_star_prefix_bis. exact H7. exact H1. exact H2. } 
             { destruct m; inversion pref; try (exists []; traceEq; done).
               destruct x0; inversion H0. exists t2. auto. }
             ++ assert (eq : t0 = finpref_trace m).
                { remember (Goes_wrong t0) as beh. destruct pb_b; try (destruct (H4 s H)).
                  destruct H5; inversion Heqbeh. subst. destruct H0. destruct x0; try (rewrite H0; traceEq; done).
                  exfalso. rewrite H0 in G.
                  destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H4).
                  clear -G H2 H3 H5 H6 H7. revert H5 H6 H7. revert s'0. remember (e :: x0) as t.
                  assert (ineq: t <> []) by (intro; subst; inv H). 
                  clear Heqt. remember (t0 ** t) as t'. revert Heqt'. revert t0. 
                  induction G; intros t'' Heqt' s'0 star nostep nofinal.
                  - apply ineq. induction t''; try (done).
                  - destruct star. eapply nostep; eauto.
                    destruct (Target.strong_det_sem2 (Target.sem_restricted_UB_generalises_sem2 H)
                                (Target.sem_restricted_UB_generalises_sem2 H1)). subst.
                    eapply (IHG t4); eauto. clear-Heqt'. induction t3; try done; try (inversion Heqt'; auto). }
                subst. remember (finpref_trace m) as t0.
                destruct m; inversion pref; simpl in Heqt0; subst.
                ** exists (FGoes_wrong t). split; try (eexists; split; eauto); auto.
                ** exists (FTbc t1). split; try (eexists; split; eauto); auto. simpl. exists (Goes_wrong []). simpl. traceEq. 
             ++ destruct m; inversion pref; simpl in H0; subst.
                ** destruct H0. destruct x0.
                   --- exists (FGoes_wrong t). split; try (eexists; split; eauto); auto. traceEq.
                   --- exfalso. subst. remember (Goes_wrong (t ** e :: x0)) as beh. destruct pb_b; try destruct (H0 s H).
                       destruct H4; inversion Heqbeh.
                       destruct (sd_initial_determ (Target.det_sem2 (program_link p Ct)) s s0 H H0).
                       clear - H1 H2 H4 H8. revert H4 H8. revert s'0 t0 e x0.
                       induction H1; intros s'0 t0 e x0 star eq.
                       +++ destruct star; inv eq. eapply H2; eauto. eapply Target.sem_restricted_UB_generalises_sem2; eauto.
                       +++ destruct star; try (clear -eq; induction t; done).
                           destruct (Target.strong_det_sem2 H
                                       (Target.sem_restricted_UB_generalises_sem2 H3)). subst.
                           assert (eq': t3 = t2 ** e :: x0) by (clear -eq; induction t0; simpl in eq; try (exact eq); inv eq; auto).
                           eapply IHstar; eauto.
                ** simpl in *. exists (FTbc (t1)). split; try (left; done).
                   eexists. split; eauto. simpl. destruct H0. exists (Goes_wrong x1). simpl. now rewrite H0.
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

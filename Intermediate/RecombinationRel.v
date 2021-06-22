Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.RenamingOption.
Require Import Common.Reachability.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.CSInvariants.
Require Import Intermediate.RecombinationRelCommon.
Require Import Intermediate.RecombinationRelOptionSim.
Require Import Intermediate.RecombinationRelLockstepSim.
(*Require Import Intermediate.RecombinationRelStrengthening.*)

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

From mathcomp Require Import ssreflect ssrnat ssrint ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(* Helpers, epsilon and lockstep versions of three-way simulation. *)
Section ThreewayMultisem1.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.
  Let n' := fun cid =>
              if cid \in domm (prog_interface p)
              then n   cid
              else n'' cid.
  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  

  (* Compose two stars into a merged star. The "program" side drives both stars
     and performs all steps without interruption, the "context" side remains
     unaltered in both stars. *)
  (* NOTE: By itself, the reformulation of this lemma does not say anything
     interesting, because the existential can be discharged trivially by
     reflexivity, but that is not what we want. In fact, even the proof is
     tellingly boring. *)
  Theorem threeway_multisem_star_E0_program s1 s1' s1'' t1 t1' t1'' s2 s2'':
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstar12 Hstar12''.
    inversion Hmerge1.
    - pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'.

      (* inversion H (* as ...*). *)
      find_and_invert_mergeable_states_well_formed.

      rewrite (* Hifacec *) Hifc_cc' in Hcomp1'.
      remember E0 as t eqn:Ht.
      revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''.
      apply star_iff_starR in Hstar12.
      induction Hstar12 as [s | s1 t1E0 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Ht Hmerge1 Hcomp1 Hcomp1'' Hstar12''.
      + exists s1'. split.
        * now apply star_refl.
        * eapply merge_states_silent_star; eassumption.
      + apply Eapp_E0_inv in Ht. destruct Ht; subst.
        specialize (IHstar H H0 H2 H3
                           Hpref_t (*Hgood_mem*) Hstack_s_s' Hpccomp_s'_s
                           Logic.eq_refl Hmerge1 Hcomp1 Hcomp1'' Hstar12'')
          as [s2' [Hstar12' Hmerge2]].
        pose proof CS.epsilon_star_non_inform_preserves_program_component _ _ _ _
             Hcomp1 ((proj2 (star_iff_starR _ _ _ _ _)) Hstar12) as Hcomp2.
        pose proof threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23
          as [s3' [Hstep23' Hmerge3]].
        exists s3'. split.
        * apply star_trans with (t1 := E0) (s2 := s2') (t2 := E0);
            [assumption | | reflexivity].
          now apply star_one.
        * assumption.
    - (* derive a contradiction to Hcomp1 *)
      destruct s1' as [[[? ?] ?] s1'pc].
      destruct s1 as [[[? ?] ?] s1pc].
      destruct s1'' as [[[? ?] ?] s1''pc].
      
      unfold CS.is_program_component,
      CS.is_context_component, turn_of, CS.state_turn in *.
      find_and_invert_mergeable_states_well_formed.
      simpl in *. subst.
      match goal with
      | H1: context[Pointer.component s1''pc \in _] |- _ =>
        rewrite Hpccomp_s'_s in H1;
          by rewrite H1 in Hcomp1
      end.
  Qed.

End ThreewayMultisem1.

(* Helpers and symmetric version of three-way simulation. *)
Section ThreewayMultisem2.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.
  
  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  (* RB: TODO: Rename, relocate. *)
  (* RB: NOTE: [DynShare] In this series of results, identical traces will need
     to be replaced by related traces. We can expect similar complications as in
     previous sections, especially in the need to produce explicit successor
     states that continue to satisfy the mergeability relation. *)
  Lemma threeway_multisem_mergeable
        s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s1, t) (CS.state_mem s1'', t'') p ->
  exists s2' t',
    mergeable_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  (* Qed. *)
  Admitted. (* RB: TODO: Add stepping of [s1']. Redundant? *)

  (* RB: TODO: Implicit parameters, compact if possible. *)
  (* RB: NOTE: Again, without mergeability, this lemma is trivial and
     uninteresting. *)
  Lemma threeway_multisem_star_E0 s1 s1' s1'' t1 t1' t1'' s2 s2'':
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    (* Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2''). *)
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros H H0 H1.
  (*   inversion H as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hprg_component.
    - eapply threeway_multisem_star_E0_program; eassumption.
    - admit.
  (*   - rewrite (merge_states_sym H); try assumption. *)
  (*     rewrite (merge_states_sym (threeway_multisem_mergeable H H0 H1)); try assumption. *)
  (*     assert (Hlinkable : linkable ip ic) by now destruct Hmergeable_ifaces. *)
  (*     unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. *)
  (*     pose proof (program_linkC Hwfp Hwfc' Hlinkable) as Hprg_linkC'. *)
  (*     unfold sem', prog'. *)
  (*     rewrite Hprg_linkC'. *)
  (*     pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''. *)
  (*     unfold sem'', prog'' in H1. *)
  (*     rewrite (Hprg_linkC'' Hlinkable) in H1. *)
  (*     pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC. *)
  (*     unfold sem, prog in H0. *)
  (*     rewrite (Hprg_linkC Hlinkable) in H0. *)
  (*     pose proof (threeway_multisem_star_E0_program) as Hmultisem. *)
  (*     specialize (Hmultisem c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in Hmultisem. *)
  (*     specialize (Hmultisem s1'' s1 s2'' s2). *)
  (*     assert (His_prg_component'' : CS.is_program_component s1'' (prog_interface p)). *)
  (*     { eapply mergeable_states_context_to_program. *)
  (*       apply H. *)
  (*       unfold CS.is_program_component in Hprg_component. apply negbFE in Hprg_component. *)
  (*       assumption. *)
  (*     } *)
  (*     assert (Hmerg_sym : mergeable_states c' p' c p s1'' s1). *)
  (*     { inversion H. *)
  (*       econstructor; *)
  (*         try rewrite <- (Hprg_linkC Hlinkable); try rewrite <- (Hprg_linkC'' Hlinkable); eauto. *)
  (*       apply mergeable_interfaces_sym; congruence. *)
  (*     } *)
  (*     specialize (Hmultisem His_prg_component'' Hmerg_sym H1 H0). *)
  (*     assumption. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Add mergeability. *)

  (* A restricted version of the lockstep simulation on event-producing steps.
     RB: NOTE: Here is where we depart from the multi-semantics and need to
     furnish our own version. We may save effort if, as is the case here, we only
     need to concern ourselves with visible steps. *)
  (* RB: NOTE: Events need to be properly for full generality. Otherwise, this
     is just a symmetry lemma. *)
  Lemma threeway_multisem_event_lockstep s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    mergeable_internal_states p c p' c' n n''  s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    traces_shift_each_other n n'' (rcons t1 e) (rcons t1'' e'') ->
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mergeable_border_states p c p' c' n n'' s2 s2' s2'' (rcons t1 e) 
                            (rcons t1' e') (rcons t1'' e'').
  Proof.
    intros Hmerge1 Hstep12 Hstep12'' Hrel2.
  (*   inversion Hmerge1 as [? ? ? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed _ Hini H1 Hstar H2]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - inversion Hmerge1.
      eapply threeway_multisem_event_lockstep_program; try eassumption.
  (*   - inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof @threeway_multisem_event_lockstep_program c' p' c p as H. *)
  (*     rewrite <- Hifacec, <- Hifacep in H. *)
  (*     specialize (H s1'' s1 e s2'' s2). *)
  (*     assert (Hmerge11 := Hmerge1). *)
  (*     erewrite mergeable_states_sym in Hmerge11; try eassumption. *)
  (*     erewrite mergeable_states_sym; try eassumption. *)
  (*     unfold ip, ic; erewrite merge_states_sym; try eassumption. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s2 s2''). *)
  (*     { inversion Hmerge1. *)
  (*       econstructor; try eassumption. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. } *)
  (*     rewrite (merge_states_sym Hmerge2); try assumption. *)
  (*     unfold sem', prog'; rewrite program_linkC; try congruence. *)
  (*     apply H; try assumption. *)
  (*     + unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn. *)
  (*       pose proof mergeable_states_pc_same_component Hmerge1 as Hpc. *)
  (*       destruct s1 as [[[[? ?] ?] pc1] ?]; destruct s1'' as [[[[? ?] ?] pc1''] ?]. *)
  (*       simpl in Hpc. *)
  (*       rewrite -Hpc. *)
  (*       unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcase. *)
  (*       destruct (CS.star_pc_domm_non_inform _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hdomm | Hdomm]. *)
  (*       apply domm_partition_notin_r with (ctx2 := ic) in Hdomm. *)
  (*       move: Hcase => /idP Hcase. rewrite Hdomm in Hcase. congruence. assumption. *)
  (*       now apply domm_partition_notin with (ctx1 := ip) in Hdomm. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       apply linkable_sym; congruence. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       now apply linkable_sym. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Symmetry lemma. Fix according to program side. *)
  (* JT: TODO: clean this proof. *)

  Theorem threeway_multisem_star_program
          s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    (* mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2',  t' ). *)
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' t'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 ta s2 tb s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' t'' s2'' Hcomp1 Hmerge1 Hstar12'' Hrel3.
    - assert (t'' = E0) by admit; subst t''. (* By the relation. *)
      exists E0, s1'. split.
      + now apply star_refl.
      + eapply merge_states_silent_star; try eassumption.
        (* AEK: 
           The lemma applied above looks suspicious because it seems
           we are now getting the same goal (as before the apply) again.
         *)
        admit.
        (* eapply context_epsilon_star_merge_states. eassumption. *)
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      assert (exists ta'' tb'', t'' = ta'' ** tb'')
        as [ta'' [tb'' ?]] by admit; subst t''. (* By pairwise events.
                                                   More info? *)
      assert (Hstar13''_ := Hstar13''). (* Which variants are needed? *)
      apply (star_app_inv (@CS.singleton_traces_non_inform _)) in Hstar13''_
        as [s2'' [Hstar12'' Hstar23'']].
      assert (Hrel1 : mem_rel2 n n'' (CS.state_mem s2, ta) (CS.state_mem s2'', ta'') p)
        by admit. (* Need to recompose memory relation based on executions. *)

      (*******************************************************************************)
      (*
      specialize (IHstar12' _ _ _ Hcomp1 Hmerge1 Hstar12'' Hrel1)
        as [ta' [s2' [Hstar12' Hmerge2]]].
      destruct tb as [| e2 [| e2' tb]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star.
           eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl]. *)
        assert (tb'' = E0) by admit; subst tb''.
        destruct (threeway_multisem_star_E0
                    Hmerge2 (star_one _ _ _ _ _ Hstep23) Hstar23'')
          as [s3' [Hstar23' Hmerge3]].
        exists ta', s3'. split.
        * eapply star_trans; try eassumption. by rewrite E0_right.
        * by rewrite !E0_right.
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        assert (exists e2'', tb'' = [e2'']) as [e2'' ?]
            by admit; subst tb''. (* By one-to-one event correspondence. More? *)
        change [e2''] with (E0 ** e2'' :: E0) in Hstar23''.
        apply (star_middle1_inv (@CS.singleton_traces_non_inform _)) in Hstar23''
          as [s2''1 [s2''2 [Hstar2'' [Hstep23'' Hstar3'']]]].
        (* Prefix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s2
          as Hstar2.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar2 as Hstar2_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge2 Hstar2_non_inform Hstar2''
          as [s2'1 [Hstar2' Hmerge21]].
        (* Propagate mergeability, step.
           NOTE: This is done early now, just above. *)
        (* assert (Hrel2 : mem_rel2 p α γ (CS.state_mem s2, E0) (CS.state_mem s2'', E0)) *)
          (* by admit. (* Should be easy. *) *)
        (* pose proof threeway_multisem_mergeable Hmerge2 Hstar2_non_inform Hstar2'' Hrel2 *)
          (* as [s2'2 Hmerge21']. *)
        assert (Hrel2 :
                  mem_rel2 n n'' (CS.state_mem s3, [e2]) (CS.state_mem s2''2, [e2'']) p)
          by admit. (* This one should also be obtainable from premises. *)
        pose proof threeway_multisem_event_lockstep Hmerge21 Hstep23 Hstep23'' Hrel2
          as [e' [s2'2 [Hstep23' Hmerge22]]].
        (* Propagate mergeability, suffix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s3
          as Hstar3.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar3 as Hstar3_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge22 Hstar3_non_inform Hstar3''
          as [s3' [Hstar3' Hmerge3]].
        (* Compose. *)
        exists (ta' ++ [e']), s3'. split. (*[| assumption].*)
        * eapply star_trans; first eassumption.
        exact (star_trans
                 (star_right _ _ Hstar2' Hstep23' (eq_refl _))
                 Hstar3' (eq_refl _)).
        rewrite -> E0_right, <- Eapp_assoc, -> E0_right.
        reflexivity.
        * by rewrite <- !Eapp_assoc.
      + (* Contradiction: a step generates at most one event. *)
        pose proof @CS.singleton_traces_non_inform _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  (* Qed. *)
       *)
      (******************************************************************************)
  Admitted. (* RB: TODO: Check admits. *)
End ThreewayMultisem2.

(* Three-way simulation and its inversion. *)
Section ThreewayMultisem3.
  Variables p c p' c' : program.  
  Variables n n'' : Component.id -> nat.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Theorem threeway_multisem_star s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star (CS.sem_non_inform (program_link p  c')) (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
    (* /\ mergeable_states ip ic s2 s2'' *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    intros Hmerge1 Hstar12 Hstar12'' Hrel2.
  (*   inversion Hmerge1 as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcomp1.
    - eapply threeway_multisem_star_program; eassumption.
  Admitted. (* TODO: Proof of symmetry. Harmonize statements as needed. *)
  (*   - apply negb_false_iff in Hcomp1. *)
  (*     apply (mergeable_states_context_to_program Hmerge1) *)
  (*       in Hcomp1. *)
  (*     assert (Hmerge2: mergeable_states p c p' c' s2 s2'') *)
  (*       by (eapply threeway_multisem_mergeable; eassumption). *)
  (*     rewrite program_linkC in Hstar12; try assumption; *)
  (*       last now destruct Hmergeable_ifaces. *)
  (*     rewrite program_linkC in Hstar12''; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec -Hifacep. *)
  (*     rewrite program_linkC; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec. *)
  (*     unfold ip, ic. *)
  (*     setoid_rewrite merge_states_sym at 1 2; try eassumption. *)
  (*     pose proof threeway_multisem_star_program as H. *)
  (*     specialize (H c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in H. *)
  (*     specialize (H s1'' s1 t s2'' s2). *)
  (*     apply H; try assumption. *)
  (*     apply mergeable_states_sym in Hmerge1; try assumption; *)
  (*       try rewrite -Hifacec; try rewrite -Hifacep; try apply mergeable_interfaces_sym; *)
  (*         now auto. *)
  (* Qed. *)
  (* JT: TODO: improve this proof *)

  (* RB: NOTE: With the added premises, this becomes simply the three-way
     simulation lemma, and one of them ([threeway_multisem_mergeable]) becomes
     redundant.
     TODO: Possibly remove that lemma, and/or merge this with the main three-way
     result. *)
  Corollary star_simulation s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n''  (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
  exists t' s2',
    Star sem'  s1' t' s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    now apply threeway_multisem_star.
  Qed.

  (* [DynShare]
     The following tactic applies program_store_from_partialized_memory
     and program_alloc_from_partialized_memory, which will both fail.
   *)
  (* Ltac t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec:= *)
  (*   match goal with *)
  (*   (* Memory operations. *) *)
  (*   | Hstore : Memory.store _ _ _ = _ |- _ => *)
  (*     apply program_store_from_partialized_memory in Hstore as [mem1_ Hstore]; *)
  (*       try eassumption *)
  (*   | Halloc : Memory.alloc _ _ _ = _ |- _ => *)
  (*     apply program_alloc_from_partialized_memory in Halloc as [mem1_ [ptr_ Halloc]]; *)
  (*       try assumption *)
  (*   (* Calls. *) *)
  (*   | Hget : EntryPoint.get _ _ _ = _ |- _ => *)
  (*     apply (genv_entrypoints_interface_some) with (p' := prog) in Hget as [b' Hget]; *)
  (*     last (simpl; congruence); *)
  (*     try assumption *)
  (*   (* Returns. *) *)
  (*   | Hcons : ?PC' :: ?GPS' = ?GPS (* merge_states_stack *) |- _ => *)
  (*     destruct GPS as [| frame1' gps1'] eqn:Hgps; [discriminate |]; *)
  (*     destruct gps1 as [| frame1 gps1]; [now destruct gps1'' |]; *)
  (*     destruct gps1'' as [| frame1'' gps1'']; [easy |]; *)
  (*     inversion Hcons; subst PC' GPS'; *)
  (*     assert (Heq : Pointer.component frame1 = Pointer.component frame1') *)
  (*       by (unfold merge_states_stack in Hgps; *)
  (*           inversion Hgps as [[Hframe Hdummy]]; *)
  (*           unfold merge_frames; *)
  (*           destruct (Pointer.component frame1 \in domm ip) eqn:Hcase; rewrite Hcase; *)
  (*           [ reflexivity *)
  (*           | eapply mergeable_states_cons_domm; last exact Hmerge; eassumption]); *)
  (*     rewrite <- Heq *)
  (*   | _ => idtac *)
  (*   end; *)
  (*   [eexists; *)
  (*   CS.step_of_executing]; *)
  (*     try eassumption; try congruence; try reflexivity; *)
  (*     try (simpl; rewrite Hifacec; eassumption); *)
  (*     match goal with *)
  (*     (* Memory operations. *) *)
  (*     | Hload : Memory.load _ _ = _ |- Memory.load _ _ = _ => *)
  (*       unfold merge_states_mem in Hload; *)
  (*       erewrite <- program_load_to_partialized_memory_strong in Hload; *)
  (*       try exact Hmerge; eassumption *)
  (*     (* Jumps. *) *)
  (*     | Hlabel : find_label_in_component _ _ _ = _ |- find_label_in_component _ _ _ = _ => *)
  (*       rewrite find_label_in_component_program_link_left; *)
  (*       rewrite find_label_in_component_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     | Hlabel : find_label_in_procedure _ _ _ = _ |- find_label_in_procedure _ _ _ = _ => *)
  (*       rewrite find_label_in_procedure_program_link_left; *)
  (*       rewrite find_label_in_procedure_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     (* Calls. *) *)
  (*     | Himp : imported_procedure _ _ _ _ |- imported_procedure _ _ _ _ => *)
  (*       rewrite imported_procedure_unionm_left; [| assumption]; *)
  (*       rewrite Hifacec in Hnotin; now rewrite imported_procedure_unionm_left in Himp *)
  (*     | _ => idtac *)
  (*     end; *)
  (*   [apply execution_invariant_to_linking with (c1 := c')]; *)
  (*   try congruence; *)
  (*   try eassumption. *)
  (*     (* try eassumption; [congruence]. *) *)


  (* AEK: Looks too strong. *)
  Theorem threeway_multisem_step_inv_program s1 s1' s1'' t1 t1' t1'' t' s2' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    (* Step sem' (merge_states ip ic s1 s1'') t s2' -> *)
    Step sem' s1' t' s2' ->
  exists t s2,
    Step sem  s1  t  s2 /\
    mem_rel2 n n'' (CS.state_mem s1', t') (CS.state_mem s1, t) p.
  Admitted. (* RB: TODO: Tweak relations, prove later IF NEEDED. *)
  (* Proof. *)
  (*   intros Hpc Hmerge Hstep. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct s1 as [[[[gps1 mem1] regs1] pc1] addrs1]. *)
  (*   destruct s1'' as [[[[gps1'' mem1''] regs1''] pc1''] addrs1'']. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm'. *)
  (*   pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin; unfold ic in Hnotin; *)
  (*   assert (Hmains : linkable_mains p c') *)
  (*     by (apply linkable_implies_linkable_mains; congruence). *)
  (*   rewrite (mergeable_states_merge_program _ Hmerge) in Hstep; *)
  (*     try assumption. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc Hlinkable as Hwfprog. *)
  (*   pose proof linking_well_formedness Hwfp' Hwfc' Hlinkable' as Hwfprog'. *)
  (*   assert (Hlinkable'' := Hlinkable); rewrite Hifacec in Hlinkable''. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc' Hlinkable'' as Hwfprog''. *)

  (*   (* [DynShare] *)
  (*      Fails because of the program_store_from_partialized_memory and *)
  (*      program_alloc_from_partialized_memory *)
  (*    *) *)
  (*   (* *)
  (*   inversion Hstep; subst; *)
  (*     t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec. *)
  (* Qed. *)
  (*    *) *)
End ThreewayMultisem3.

(* Theorems on initial states for main simulation. *)
Section ThreewayMultisem4.
  Variables p c p' c' : program.

  (* In this section, we should instantiate n and n'', not parameterize over them. *)
  Variables n n'' : Component.id -> nat.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog''_is_closed : closed_program (program_link p' c').
    

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.


  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_trace_extensional (left_addr_good_for_shifting n) tt.
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_trace_extensional (left_addr_good_for_shifting n'') tt''.


  Lemma merged_program_is_closed: closed_program prog'.
  Proof.
    unfold mergeable_interfaces in *.
    destruct Hmergeable_ifaces.
    eapply interface_preserves_closedness_r; eauto.
    - by eapply linkable_implies_linkable_mains.
    - by eapply interface_implies_matching_mains.
  Qed.

  (* Lemma initial_states_mergeability s s'' : *)
  (*   initial_state sem   s   -> *)
  (*   initial_state sem'' s'' -> *)
  (*   mergeable_states p c p' c' s s''. *)
  (* Proof. *)
  (*   simpl. unfold CS.initial_state. *)
  (*   intros Hini Hini''. *)
  (*   apply mergeable_states_intro with (s0 := s) (s0'' := s'') (t := E0); subst; *)
  (*     try assumption; *)
  (*     reflexivity || now apply star_refl. *)
  (* Qed. *)

  Lemma match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
  exists s',
    initial_state sem'  s'  /\
    mergeable_border_states p c p' c' n n'' s s' s'' E0 E0 E0.
  Proof.
    intros Hini Hini''. simpl in *.
    exists (CS.initial_machine_state prog'). split.
    - unfold initial_state, CS.initial_machine_state; reflexivity.
    - pose proof merged_program_is_closed as Hprog'_is_closed.
      assert (CS.initial_machine_state (program_link p c') =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitpc'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacec.
      }
      assert (CS.initial_machine_state (program_link p c) =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c,
                  Z.of_nat 0
                )
              )
             ) as Hinitpc.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          by destruct Hmergeable_ifaces as [? _].
      }
      
      assert (CS.initial_machine_state (program_link p' c') =
              (
                [],
                unionm (prepare_procedures_memory p') (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p' + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitp'c'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacep; rewrite <- Hifacec.
      }
      
      rewrite Hinitpc'.
      (* 
         Need to know whether to apply mergeable_border_states_p_executing
         or mergeable_border_states_c'_executing.

         But in any case, we will need mergeable_states_well_formed.
       *)
      assert (mergeable_states_well_formed
                p c p' c' n n'' s
                ([],
                 unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                 Register.init,
                 (Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0)
                )
                s'' E0 E0 E0
             ) as Hmergewf.
      {
        eapply mergeable_states_well_formed_intro;
          simpl; eauto; unfold CS.initial_state, CSInvariants.is_prefix in *; subst.
        + apply star_refl.
        + rewrite Hinitpc'. apply star_refl.
        + apply star_refl.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- simpl.
             (* good_memory prepare_procedures_memory *)
             (* Search _ prepare_initial_memory. *)
             (* Search _ alloc_static_buffers. *)
             admit.
          -- by inversion Hmergeable_ifaces.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- simpl.
             (* good_memory prepare_procedures_memory *)
             admit.
          -- rewrite <- Hifacep, <- Hifacec. by inversion Hmergeable_ifaces.
        + (* good_memory prepare_procedures_memory *)
          admit.
        + constructor.
        + constructor.
        + constructor.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- constructor.
          -- by inversion Hmergeable_ifaces.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- constructor.
          -- rewrite <- Hifacep, <- Hifacec. by inversion Hmergeable_ifaces.
        + by rewrite Hinitpc.
        + by rewrite Hinitp'c'.
        + constructor. constructor.
        + constructor. constructor.
      } 
      destruct (Component.main \in domm (prog_interface p)) eqn:whereismain.
      + (* Component.main is in p. *)
        eapply mergeable_border_states_p_executing; simpl; eauto.
        * (* Goal: program counters equal *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          assert (CS.prog_main_block c = CS.prog_main_block c') as Hprogmainblk.
          {
            admit.
          }
          by rewrite Hprogmainblk.
        * (* Goal: is_program_component. *)
          admit.
        * (* Goal: registers related *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          eapply regs_rel_of_executing_part_intro.
          intros reg.
          unfold Register.get.
          destruct (Register.to_nat reg \in domm Register.init) eqn:regdomm.
          -- assert (Register.init (Register.to_nat reg) = Some Undef)
              as Hreginit_undef.
             {
               by apply Register.reg_in_domm_init_Undef.
             }
             by rewrite Hreginit_undef.
          -- assert (Register.init (Register.to_nat reg) = None) as Hreginit_none.
             {
               rewrite mem_domm in regdomm.
               by destruct (Register.init (Register.to_nat reg)) eqn:e.
             }
             by rewrite Hreginit_none.
        * (* Goal: mem_of_part_executing_rel_original_and_recombined *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.

          (* Observe that mem_of_part_executing_rel_original_and_recombined 
             only cares about addresses from the left part of the "unionm"'s.
             And observe that the left part is the same in both "uninonm"'s.
           *)
          admit.
          
          (*Search _ prepare_procedures_memory.*)

          (* This assertion is not needed. *)
          (*assert (prepare_procedures_memory c = prepare_procedures_memory c') as Hmemcc'.
          {
            (* Apparently, this assertion is false. *)
            (* The reason it is false is that the memory resulting from 
               prepare_procedures_memory is code memory, and the code of
               c is different from the code of c'.
             *)
            unfold prepare_procedures_memory.
            rewrite !prepare_procedures_initial_memory_equiv.
            unfold prepare_procedures.
            Search _ prog_procedures.
            
            Search _ prepare_procedures_initial_memory.
            Search _ prepare_initial_memory.
          }*)
          
         
        * (* Goal: mem_of_part_not_executing_rel_original_and_recombined_at_border*)
          unfold CS.initial_state in *. subst. rewrite Hinitp'c'. simpl.
          unfold mem_of_part_not_executing_rel_original_and_recombined_at_border.

          (* Observe that this is very similar to the previous subgoal.
             The only difference is that it's the right part of the "unionm"
             that we want to relate.
           *)
          
          admit.
      + (* Component.main is in c'. Should be analogous to the parallel goal. *)
          
  Admitted. (* RB: TODO: Establish trivial relations, should not be hard. *)

  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof initial_states_mergeability Hini Hini'' as Hmerge. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   simpl in *. unfold CS.initial_state in *. subst. *)
  (*   split; last assumption. *)
  (*   (* Expose structure of initial states. *) *)
  (*   rewrite !CS.initial_machine_state_after_linking; try congruence; *)
  (*     last (apply interface_preserves_closedness_r with (p2 := c); try assumption; *)
  (*           now apply interface_implies_matching_mains). *)
  (*   unfold merge_states, merge_memories, merge_registers, merge_pcs; simpl. *)
  (*   (* Memory simplifictions. *) *)
  (*   rewrite (prepare_procedures_memory_left Hlinkable). *)
  (*   unfold ip. erewrite Hifacep at 1. rewrite Hifacep Hifacec in Hlinkable. *)
  (*   rewrite (prepare_procedures_memory_right Hlinkable). *)
  (*   (* Case analysis on main and related simplifications. *) *)
  (*   destruct (Component.main \in domm ip) eqn:Hcase; *)
  (*     rewrite Hcase. *)
  (*   - pose proof domm_partition_notin_r _ _ Hmergeable_ifaces _ Hcase as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfc Hnotin). *)
  (*     rewrite Hifacec in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfc' Hnotin). *)
  (*   - (* Symmetric case. *) *)
  (*     assert (Hcase' : Component.main \in domm ic). *)
  (*     { pose proof domm_partition_program_link_in_neither Hwfp Hwfc Hprog_is_closed as H. *)
  (*       rewrite Hcase in H. *)
  (*       destruct (Component.main \in domm ic) eqn:Hcase''. *)
  (*       - reflexivity. *)
  (*       - rewrite Hcase'' in H. *)
  (*         exfalso; now apply H. *)
  (*     } *)
  (*     pose proof domm_partition_notin _ _ Hmergeable_ifaces _ Hcase' as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfp Hnotin). *)
  (*     rewrite Hifacep in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfp' Hnotin). *)
  (* Qed. *)
End ThreewayMultisem4.

(* Remaining theorems for main simulation.  *)
Section ThreewayMultisem5.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  (* RB: NOTE: Consider execution invariance and similar lemmas on the right as
     well, as symmetry arguments reoccur all the time.
     TODO: Observe the proof of match_nostep is almost identical, and refactor
     accordingly. *)
  Theorem match_final_states s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    final_state sem   s   ->
    final_state sem'' s'' ->
    (* final_state sem'  (merge_states ip ic s s''). *)
    final_state sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   destruct s as [[[[gps mem] regs] pc] addrs]. *)
  (*   destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal''. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c1 := c); try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     rewrite program_linkC; try congruence. *)
  (*     apply linkable_sym in Hlinkable. *)
  (*     apply linkable_mains_sym in Hmain_linkability. *)
  (*     apply linkable_mains_sym in Hmain_linkability'. *)
  (*     apply execution_invariant_to_linking with (c1 := p'); try congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now apply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)

  Theorem match_nofinal s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    (* ~ final_state sem'  (merge_states ip ic s s''). *)
    ~ final_state sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   destruct s as [[[[gps mem] regs] pc] addrs]. *)
  (*   destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal'' Hfinal'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _ ]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c2 := c) in Hfinal'; try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal'; try congruence. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     apply execution_invariant_to_linking with (c2 := p') in Hfinal'; try easy. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now eapply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)

  Lemma match_nostep s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    Nostep sem   s   ->
    Nostep sem'' s'' ->
    (* Nostep sem'  (merge_states ip ic s s''). *)
    Nostep sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   rename s into s1. rename s'' into s1''. *)
  (*   intros Hmerge Hstep Hstep'' t s2' Hstep'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable' _]; rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
  (*   - pose proof threeway_multisem_step_inv_program Hcase Hmerge Hstep' *)
  (*       as [s2 Hcontra]. *)
  (*     specialize (Hstep t s2). contradiction. *)
  (*   - (* Symmetric case. *) *)
  (*     apply negb_false_iff in Hcase. *)
  (*     pose proof mergeable_states_context_to_program Hmerge Hcase as Hcase'. *)
  (*     pose proof proj1 (mergeable_states_sym _ _ _ _ _ _) Hmerge as Hmerge'. *)
  (*     pose proof @threeway_multisem_step_inv_program c' p' c p as H. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H s1'' s1 t s2' Hcase' Hmerge'). *)
  (*     rewrite program_linkC in H; try assumption; [| apply linkable_sym; congruence]. *)
  (*     rewrite Hifacec Hifacep in H. *)
  (*     erewrite merge_states_sym with (p := c') (c := p') (p' := c) (c' := p) in H; *)
  (*       try eassumption; try now symmetry. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H Hstep'). *)
  (*     destruct H as [s2'' Hcontra]. *)
  (*     specialize (Hstep'' t s2''). *)
  (*     unfold sem'', prog'' in Hstep''; rewrite program_linkC in Hstep''; try assumption. *)
  (*     contradiction. *)
  (* Qed. *)
End ThreewayMultisem5.

(* Main simulation theorem. *)
Section Recombination.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_memory (left_addr_good_for_shifting n) (CS.state_mem ss).
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_memory (left_addr_good_for_shifting n'') (CS.state_mem ss'').


  (* RB: NOTE: Possible improvements:
      - Try to refactor case analysis in proof.
      - Try to derive well-formedness, etc., from semantics.
     This result is currently doing the legwork of going from a simulation on
     stars to one on program behaviors without direct mediation from the CompCert
     framework. *)
  (* Theorem recombination_prefix m : *)
  (*   does_prefix sem   m -> *)
  (*   does_prefix sem'' m -> *)
  (*   does_prefix sem'  m. *)
  (* Proof. *)
  (*   unfold does_prefix. *)
  (*   intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']]. *)
  (*   assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh''). *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]]. *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']]. *)
  (*   destruct m as [tm | tm | tm]. *)
  (*   - destruct b   as [t   | ? | ? | ?]; try contradiction. *)
  (*     destruct b'' as [t'' | ? | ? | ?]; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst. *)
  (*     inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst. *)
  (*     exists (Terminates tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_terminates with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     now apply match_final_states with (p' := p'). *)
  (*   - destruct b   as [? | ? | ? | t  ]; try contradiction. *)
  (*     destruct b'' as [? | ? | ? | t'']; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst. *)
  (*     inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst. *)
  (*     exists (Goes_wrong tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_goes_wrong with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     + eapply match_nostep; eassumption. *)
  (*     + eapply match_nofinal; eassumption. *)
  (*   - (* Here we talk about the stars associated to the behaviors, without *)
  (*        worrying now about connecting them to the existing initial states. *) *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix) *)
  (*       as [s1_ [s2 [Hini1_ Hstar12]]]. *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'') *)
  (*       as [s1''_ [s2'' [Hini1''_ Hstar12'']]]. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1_ Hini1''_ as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     eapply program_behaves_finpref_exists; *)
  (*       last now apply Hstar12'. *)
  (*     assumption. *)
  (* Qed. *)

  (* RB: NOTE: [DynShare] This definition may be used to expose a simpler
     relation, which would still fit the theorem statement, though one of the
     explicit connections would be lost. *)
  (* Definition prefix_rel m m' := *)
  (*   exists n n', behavior_rel_behavior_all_cids n n' m m'. *)
  Theorem recombination_prefix_rel m m'' :
    does_prefix sem   m ->
    does_prefix sem'' m'' ->
    behavior_rel_behavior n  n'' m  m'' ->
  exists m' n',
    does_prefix sem'  m' /\
    behavior_rel_behavior n' n   m' m.
  Proof.
    (* unfold does_prefix. *)
    intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']] Hrel.
    (* Invert prefix executions to expose their initial states (and full program
       behaviors. *)
    assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh'').
    apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]].
    apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']].
    (* Suppose we can establish the relation between the initial states of the
       two runs and the initial state of the recombined program. *)
    pose (s1' := CS.initial_machine_state (program_link p c')).

    
    (* AEK: TODO: Get the "t"s from the behaviors. *)
    (*assert (Hmerge1 : mergeable_states p c p' c' n n'' s1 s1' s1'' (* t1 t1' t1''*))
      by admit.*)


    (* In the standard proof, because the two executions produce the same
       prefix, we know that the two runs either terminate, go wrong or are
       unfinished. The third case is probably the most interesting here. *)
    destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix)
      as [s1_ [s2 [Hini1_ Hstar12]]].
    destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'')
      as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
    pose proof match_initial_states (*n n''*) Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
         Hprog_is_closed Hprog_is_closed' Hprog_is_good Hprog''_is_good Hini1_ Hini1''_
      as [s1'_ [Hini1' Hmerge1_]].
    (* By determinacy of initial program states: *)
    assert (Heq1 : s1 = s1_) by admit.
    assert (Heq1' : s1' = s1'_) by admit.
    assert (Heq1'' : s1'' = s1''_) by admit.
    subst s1_ s1'_ s1''_.
    clear Hini1_ Hini1''_ Hmerge1_.


    (* Now we should be able to apply a modified star simulation. *)

    (* AEK: TODO: Uncomment after having defined Hmerge1. See the TODO above. *)
    (************
    pose proof star_simulation Hmerge1 Hstar12 Hstar12''
      as [t' [s2' [Hstar12' Hmerge2]]].
    {
      (* For this, however, we need to be able to establish the memory
         relation between the two, in principle starting from [Hmerge1] and
         [Hrel]. *)
      (* NOTE: The memory relation is designed to hold at the boundaries!
         vs. higher-level memory relation *)
      admit.
    }
`   *************)



    (* AEK: TODO: Uncomment after having defined t'. See the TODO above. *)
    (*************
    (* Actually, we need to ensure that the executed trace corresponds to a
       finite prefix behavior (and that the obtained relation extends to
       it.) *)
    assert (exists m', t' = finpref_trace m') as [m' Heq] by admit; subst.


    (* Now we can instantiate the quantifiers (assume the mapping [n'] can be
       obtained easily). *)
    exists m'. eexists. split.
    - (* In principle, the same lemma that was used for the third case of the
         original proof should work here. *)
      pose proof program_behaves_finpref_exists Hini1' Hstar12'
             as [beh' [Hbeh' Hprefix']].
      exists beh'. admit.
    - (* We would then be left to establish the trace relation. *)
      admit.
     *********)



  Admitted.

End Recombination.

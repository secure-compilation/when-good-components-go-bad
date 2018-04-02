Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Blame.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Section Decomposition.
  Variable p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis closedness_after_linking:
    closed_program (program_link p c).

  Lemma match_initial_states:
    forall ics,
      CS.initial_state (program_link p c) ics ->
    exists ips,
      PS.initial_state p (prog_interface c) ips /\
      PS.partial_state (prog_interface c) ics ips.
  Proof.
    intros ics Hics_init.
    CS.unfold_states.
    (* case analysis on who has control, then build the partial state *)
    destruct (C \in domm (prog_interface c)) eqn:Htarget;
      exists (PS.partialize (prog_interface c) (C, s, mem, k, e));
      simpl; rewrite Htarget.
    (* context has control *)
    - split.
      + eapply PS.initial_state_intro with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * eapply PS.ContextControl; eauto.
        * apply Hics_init.
      + eapply PS.ContextControl; eauto.
    (* program has control *)
    - split.
      + eapply PS.initial_state_intro with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.
        * apply Hics_init.
      + eapply PS.ProgramControl; auto.
        * PS.simplify_turn.
          unfold negb. rewrite Htarget. auto.
  Qed.

  Lemma match_final_states:
    forall ics ips,
      PS.partial_state (prog_interface c) ics ips ->
      CS.final_state ics ->
      PS.final_state p (prog_interface c) ips.
  Proof.
    intros ics ips Hpartial Hics_final.
    CS.unfold_states.
    (* case analysis on who has control *)
    destruct (C \in domm (prog_interface c)) eqn:Htarget.
    (* context has control *)
    - inversion Hpartial; inversion H; subst.
      + PS.simplify_turn.
        rewrite Htarget in H5. discriminate.
      + apply PS.final_state_context.
        PS.simplify_turn. auto.
    (* program has control *)
    - inversion Hpartial; inversion H; subst.
      + eapply PS.final_state_program with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * PS.simplify_turn. rewrite Htarget. auto.
        * eauto.
        * assumption.
      + PS.simplify_turn.
        rewrite Htarget in H5. discriminate.
  Qed.

  Lemma match_initial_states_by_partialize : forall scs0,
    CS.initial_state (program_link p c) scs0 ->
    PS.initial_state p (prog_interface c) (PS.partialize (prog_interface c) scs0).
  Proof.
    intros scs0 Hini.
    eapply PS.initial_state_intro;
      try reflexivity;
      try assumption.
    unfold CS.initial_state in Hini.
    unfold CS.initial_machine_state in *.
    rewrite <- PS.partialize_correct.
    destruct (prog_main (program_link p c)) as [main |] eqn:Hmain;
      subst;
      easy.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.kstep (prepare_global_env (program_link p c)) ics t ics' ->
    forall ips,
      PS.partial_state (prog_interface c) ics ips ->
    exists ips',
      PS.kstep p (prog_interface c) (prepare_global_env p) ips t ips' /\
      PS.partial_state (prog_interface c) ics' ips'.
  Proof.
    intros ics t ics' Hstep ips Hpartial.

    (* case analysis on who has control and the executed step *)
    inversion linkability; subst.
    inversion Hpartial; subst;
    inversion Hstep; subst.

    (** program has control **)

    (* epsilon steps *)

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    (* call *)
    - PS.simplify_turn.
      (* case analisys on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (* internal return (program to program) *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    (* external return *)
    - PS.simplify_turn.
      (* case analisys on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (** context has control **)

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             erewrite <- context_allocation_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- context_allocation_in_partialized_memory; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             erewrite <- context_store_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- context_store_in_partialized_memory; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* internal call *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* external call *)
    - PS.simplify_turn.
      (* case analysis on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (* internal return *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* external return *)
    - PS.simplify_turn.
      (* case analysis on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.
  Qed.

  Theorem decomposition:
    forward_simulation (CS.sem (program_link p c))
                       (PS.sem p (prog_interface c)).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_safe_behavior:
    forall beh,
      program_behaves (CS.sem (program_link p c)) beh ->
      not_wrong beh ->
      program_behaves (PS.sem p (prog_interface c)) beh.
  Proof.
    intros beh.
    eapply forward_simulation_same_safe_behavior; eauto.
    apply decomposition.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.

  Inductive well_defined_components (iface: Program.interface): event -> Prop :=
  | wf_comps_call: forall C1 P arg C2,
      C1 \in domm iface ->
      C2 \in domm iface ->
      well_defined_components iface (ECall C1 P arg C2)
  | wf_comps_ret: forall C1 arg C2,
      C1 \in domm iface ->
      C2 \in domm iface ->
      well_defined_components iface (ERet C1 arg C2).

  Lemma ub_behavior_has_well_defined_components:
    forall t,
      program_behaves (CS.sem (program_link p c)) (Goes_wrong t) ->
    forall e,
      In e t ->
      well_defined_components (prog_interface (program_link p c)) e.
  Proof.
  Admitted.

  Lemma ub_blaming:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) \/
      undef_in Component.main t (prog_interface c).
  Proof.
    (* sketch:
       consider the trace t
       - if it's empty, look at the main component of
         program_link p c. It is either a component of p
         or a component of c because of linking.
       - if it's non-empty, look at the last event.
         an event is either a call or a return.
         consider the component that is in control after
         such event: by well-formedness (maybe the same used
         in definability?) of the trace, it must be a component
         present in the interface of program_link p c.
         Therefore, it must be either a component of p or a
         component of c.
     *)
    intros t Hbeh.
    destruct (last_event t) as [last_event |] eqn:Hlast_event.
    - assert (In last_event t) as Hin_trace. {
        apply last_event_is_in_trace; auto.
      }
      pose proof ub_behavior_has_well_defined_components Hbeh Hin_trace as Hwf.
      unfold undef_in. rewrite Hlast_event.
      inversion Hwf; subst; simpl.
      + unfold program_link in *. simpl in *.
        rewrite domm_union in H0.
        rewrite in_fsetU in H0.
        unfold orb in H0.
        destruct (C2 \in domm (prog_interface p)) eqn:HC_in_p.
        * left. assumption.
        * rewrite HC_in_p in H0. right. assumption.
      + unfold program_link in *. simpl in *.
        rewrite domm_union in H0.
        rewrite in_fsetU in H0.
        unfold orb in H0.
        destruct (C2 \in domm (prog_interface p)) eqn:HC_in_p.
        * left. assumption.
        * rewrite HC_in_p in H0. right. assumption.
    - apply no_last_event_implies_empty_trace in Hlast_event.
      rewrite Hlast_event.
      unfold undef_in. simpl.
      apply linked_programs_main_component_origin; auto.
  Qed.

  Lemma program_ub_preservation:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c))
                      (Goes_wrong t).
  Proof.
    (* sketch:
       there are two cases:
       1) there is an initial state, but after zero or more
          steps we reach a stuck state.
          by the blame hypothesis, we know that such state
          has the program p in control.
          hence, we simulate in the partial semantics up to
          that state and then we stop, since the stuckness
          of p is preserved.
       2) there is not an initial state
          in this case, by definition, there cannot be an
          initial state for the partial semantics.
          therefore, we are stuck in the partial semantics
          as well.
     *)
    intros t Hbeh Hblame.
    inversion Hbeh as [ init_s beh Hinit Hstate_beh | ]; subst.
    (* program reaches a stuck state after zero or many steps *)
    - eapply program_runs.
      + apply PS.initial_state_intro
          with (p':=c) (scs:=init_s) (sps:=PS.partialize (prog_interface c) init_s).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * CS.unfold_state init_s. simpl in *.
          destruct (C \in domm (prog_interface c)) eqn:Hctx.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn. assumption.
             *** reflexivity.
             *** reflexivity.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn.
                 unfold negb. rewrite Hctx.
                 reflexivity.
             *** reflexivity.
             *** reflexivity.
        * assumption.
      + inversion Hstate_beh; subst.
        (* simulate star with decomposition *)
        (* We take this step early to get the pieces needed by [econstructor] later. *)
        pose proof forward_simulation_behavior_improves decomposition Hbeh
          as [beh1 [Hbeh1 Himpr1]].
        inversion Himpr1 as [Hbeh2 | [t2 [Heq [beh3 Hbeh3]]]].
        * subst.
          inversion Hbeh1 as [s ? Hini Hsbeh | Hini]; subst.
          -- (* initial_state_determinism *)
             apply match_initial_states_by_partialize in Hinit.
             pose proof PS.initial_state_determinism Hini Hinit; subst.
             inversion Hsbeh. econstructor; eassumption.
          -- econstructor.
             ++ apply star_refl.
             ++ (* show preservation of stuckness *)
                (* By contradiction on initial state from CS and lack thereof in PS. *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
             ++ (* show preservation of non-final state *)
                (* Likewise by contradiction. *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
        * inversion Heq; subst t2; subst; clear Heq.
          inversion Hbeh1 as [s ? Hini Hsbeh | Hini Happ]; subst.
          -- apply match_initial_states_by_partialize in Hinit.
             pose proof PS.initial_state_determinism Hini Hinit; subst.
             (* Discharge by stuckness of p in the blame hypothesis. *)
             admit.
          -- unfold behavior_app in Happ.
             destruct beh3 as [? | ? | ? | t1];
               inversion Happ as [Heq].
             symmetry in Heq.
             apply Eapp_E0_inv in Heq.
             destruct Heq; subst.
             (* As above. *)
             econstructor.
             ++ apply star_refl.
             ++ (* show preservation of stuckness *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
             ++ (* show preservation of non-final state *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
    (* program went wrong because it doesn't have an initial state *)
    - apply program_goes_initially_wrong.
      intros s.
      unfold not. intro contra.
      inversion contra as [p' scs ? Hsame_iface _ wf' linkability' Hpartial Hini]; subst.
      apply H with (s:=scs). simpl.
      unfold CS.initial_state in *. subst.
      unfold CS.initial_machine_state.
      (* same main and main expr *)
      (* empty stack *)
      (* stop continuation *)
      (* same initial memory memory because of same components *)
      (* Stack and continuation are easy. *)
      (* 1. main has to be in p. *)
      unfold undef_in in Hblame; simpl in Hblame.
      inversion wf1 as [_ _ _ _ _ _ Hmain_p].
      specialize (Hmain_p Hblame).
      (* Some more facts about mains. *)
      inversion closedness_after_linking as [_ Hmain_p_c].
      pose proof linkable_disjoint_mains wf1 wf2 linkability as Hmains_p_c.
      pose proof linkable_disjoint_mains wf1 wf' linkability' as Hmains_p_p'.
      unfold linkable_mains in Hmains_p_c. unfold linkable_mains in Hmains_p_p'.
      rewrite Hmain_p in Hmains_p_c. rewrite Hmain_p in Hmains_p_p'.
      simpl in Hmains_p_c. simpl in Hmains_p_p'.
      destruct (prog_main (program_link p c)) as [main_p_c |] eqn:Heqmain_p_c;
        last by inversion Heqmain_p_c.
      destruct (prog_main (program_link p p')) as [main_p_p' |] eqn:Heqmain_p_p';
        last by admit. (* Easy contradiction. *)
      (* Complete the equality of mains. *)
      assert (main_p_p' = main_p_c) as Heqmains.
      {
        unfold prog_main, program_link in Heqmain_p_c.
        simpl in Heqmain_p_c.
        (* Choosing p on both linked programs; other sides identical by contradiction. *)
        apply
          (linkable_programs_find_procedure
             wf1 wf2 linkability Component.main Procedure.main main_p_c)
          in Heqmain_p_c as [Heqmain_p_c | Heqmain_p_c].
        - apply
            (linkable_programs_find_procedure
               wf1 wf' linkability' Component.main Procedure.main main_p_p')
            in Heqmain_p_p' as [Heqmain_p_p' | Heqmain_p_p'].
          + rewrite Heqmain_p_p' in Heqmain_p_c.
            by inversion Heqmain_p_c.
          + unfold prog_main, negb in Hmains_p_p'.
            rewrite Heqmain_p_p' in Hmains_p_p'.
            simpl in Hmains_p_p'.
            by inversion Hmains_p_p'.
        - unfold prog_main, negb in Hmains_p_c.
          rewrite Heqmain_p_c in Hmains_p_c.
          simpl in Hmains_p_c.
          by inversion Hmains_p_c.
      }
      subst.
      (* 2. Equality of memories. *)
      admit.
  Admitted.

  (* If a state s leads to two states s1 and s2 with the same trace t, it must
     be the case that s1 and s2 are connected. We arrive at s1 and s2 after a
     series of coordinated and identical alternations between program and
     context. Both s1 and s2 are either in the program or in the context. From
     the common starting state, observe the following facts about the sequence
     of phases.

      - A program phase starting from the same state is deterministic until
        the end of the execution or a change of control.

      - A context phase from the same state is silent until the end of the
        execution or a change of control.

     Note moreover that the shared trace preserves the state across turn
     boundaries. In the final phase, i.e., that of s1 and s2, we stop at two
     points in the deterministic execution of the program (in which case one
     of the two may always catch up to the other if needed), or at two
     indistinguishable states of the context. *)
  Lemma state_determinism_star_same_trace :
    forall p1 p2 s t s1 s2,
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s t s1 ->
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s t s2 ->
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s1 E0 s2 \/
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s2 E0 s1.
  Admitted.

  (* s and s1 are both either in the program or in the context.

      - If they are in the program, the transitions are deterministic, thus s1
        is always after s and goes on to s2.

      - If they are in the program, the transitions are silent, thus s = s1,
        which goes on to s2. *)
  Lemma state_determinism_star_silent_prefix :
    forall p1 p2 s t s1 s2,
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s E0 s1 ->
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s t s2 ->
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s1 t s2.
  Admitted.

  (* NOTE: the first disjunct is subsumed by the third. *)
  Lemma star_improvement:
    forall p1 p2 s t t' s' s'',
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s t s' ->
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s (t ** t') s'' ->
      (* same steps, hence same final state and trace *)
      (t' = E0 /\ s'' = s') \/
      (* missing steps in the first star (with trace t') *)
      star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s' t' s'' \/
      (* missing internal steps in the second star *)
      (t' = E0 /\
       star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s'' E0 s').
  Proof.
    intros p1 p2 s t t' s' s''.
    intros Hstar1 Hstar2.
    apply star_app_inv in Hstar2 as [s''' [Hstar2 Hstar2']];
      last apply PS.atomic_traces.
    destruct (state_determinism_star_same_trace Hstar1 Hstar2) as [Hstar12 | Hstar21].
    - pose proof star_trans Hstar12 Hstar2' (E0_right t') as Hstar12'.
      rewrite E0_right in Hstar12'.
      right. left. done.
    - pose proof state_determinism_star_silent_prefix Hstar21 Hstar2' as Hstar1'.
      right. left. done.
(*
    apply star_starN in Hstar1.
    apply star_starN in Hstar2.
    destruct Hstar1 as [n1 HstarN1].
    destruct Hstar2 as [n2 HstarN2].
    destruct (Nat.compare n1 n2) eqn:Hcmp.
    - apply Nat.compare_eq in Hcmp. subst.
      destruct (PS.state_determinism_starN_with_same_prefix HstarN1 HstarN2)
        as [[]|[[m []]|[m [? []]]]]; subst.
      + auto.
      + apply starN_star in H. auto.
      + apply starN_star in H0. auto.
    - right. left.
      admit.
    - right. right.
      admit.
*)
  Qed.

  Lemma program_ub_doesnt_improve:
    forall t beh_imp,
      program_behaves (PS.sem p (prog_interface c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c))
                      (behavior_app t beh_imp) ->
      beh_imp = Goes_wrong E0.
  Proof.
    intros t beh_imp Hbeh1 Hblame Hbeh2.
    inversion Hbeh1; subst.
    (* program reaches a stuck state after zero or many steps *)
    - inversion Hbeh2; subst.
      + (* show that we start from the same state *)
        assert (s = s0). {
          apply PS.initial_state_determinism with p (prog_interface c); auto.
        }
        subst.
        (* show that (Goes_wrong t) makes beh_imp empty *)
        inversion H0; subst; inversion H2; subst;
        destruct beh_imp; simpl in *; try discriminate;
          inversion H3; subst.
        * (* contra *)
          destruct (star_improvement H4 H7) as [[]|[|[]]]; subst.
          ** contradiction.
          ** inversion H9; subst.
             *** contradiction.
             *** exfalso. eapply H5. eauto.
          ** inversion H10; subst.
             *** contradiction.
             *** symmetry in H12.
                 apply Eapp_E0_inv in H12. destruct H12; subst.
                 admit.
        * (* contra *)
          destruct (star_improvement H4 H7) as [[]|[|[]]]; subst.
          ** inversion H8; subst.
             exfalso. eapply H5. eauto.
          ** inversion H9; subst.
             *** inversion H8; subst.
                 exfalso. eapply H5. eauto.
             *** exfalso. eapply H5. eauto.
          ** inversion H10; subst.
             *** inversion H8; subst.
                 exfalso. eapply H5. eauto.
             *** symmetry in H12.
                 apply Eapp_E0_inv in H12. destruct H12; subst.
                 admit.
        * (* contra *)
          (* s' cannot step, hence t1 is E0 and s'0 is s'
             but s' is not forever reactive *)
          inversion H7; subst. inversion H9; subst.
          ** contradiction.
          ** exfalso. eapply H5.
             admit.
        * (* s' cannot step, hence t1 is E0 and s'0 is s'
             done *)
          destruct (star_improvement H4 H7) as [[]|[|[]]]; subst.
          ** reflexivity.
          ** inversion H10; subst.
             *** reflexivity.
             *** exfalso. eapply H5. eauto.
          ** inversion H11; subst; reflexivity.
      + assert (t = E0).
        { destruct t.
          - reflexivity.
          - destruct beh_imp; simpl in *;
              discriminate.
        } subst.
        rewrite H1 behavior_app_E0.
        reflexivity.
    (* program went wrong because it doesn't have an initial state *)
    - inversion Hbeh2; subst.
      + exfalso.
        eapply H0. eauto.
      + rewrite H behavior_app_E0.
        reflexivity.
  Admitted.

  Corollary decomposition_with_refinement_and_blame:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      (beh1 = beh2 \/
       exists t, beh1 = Goes_wrong t /\
                 behavior_prefix t beh2 /\
                 undef_in Component.main t (prog_interface c)).
  Proof.
    intros beh1 Hbeh1.
    assert (Hbeh1' := Hbeh1).
    apply decomposition_with_refinement in Hbeh1'.
    destruct Hbeh1' as [beh2 [Hbeh2 [Hsame | Hwrong]]]; subst.
    - eexists. split.
      + eassumption.
      + left. reflexivity.
    - destruct Hwrong as [t [Hbeh1_wrong Hbeh2_pref]]; subst.
      eexists. split.
      + eassumption.
      + (* sketch:
           p[c] does UB(t), therefore either we blame p or
           we blame c.
           - if we blame p, we prove the left disjunct by
             showing that the undefined behavior is preserved
           - if we blame c, we prove the right disjunct by
             using our assumptions
         *)
        destruct (ub_blaming Hbeh1) as [Hblame | Hblame].
        * left.
          apply program_ub_preservation in Hbeh1; auto.
          (* beh2 is an improvement of t, but we know that
             p goes wrong with t (which is a prefix of beh2).
             Moreover, p remains the same after partialization
             (it's determinate).
           *)
          destruct Hbeh2_pref as [Hbeh_imp ?]; subst.
          rewrite (program_ub_doesnt_improve Hbeh1 Hblame Hbeh2).
          simpl. rewrite E0_right. reflexivity.
        * right.
          eexists. split.
          ** reflexivity.
          ** split; assumption.
  Qed.

  Set Implicit Arguments.

  Lemma improving_star_ending_in_stuck_state:
    forall s t s' t' s'',
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s t s' ->
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s (t ** t') s'' ->
      nostep (PS.kstep c (prog_interface p)) (prepare_global_env c) s' ->
      t' = E0 /\
      (s' = s'' \/ star (PS.kstep c (prog_interface p)) (prepare_global_env c) s'' E0 s').
  Proof.
    intros s t s' t' s''.
    intros Hstar1 Hstar2 Hnostep.
    destruct (star_improvement Hstar1 Hstar2) as [|[|]].
    - destruct H. intuition.
    - inversion H; subst.
      + split; auto.
      + exfalso. eapply Hnostep. eauto.
    - destruct H; subst. split; auto.
  Qed.

  Lemma blame_program : forall t b,
    program_behaves (PS.sem c (prog_interface p)) b ->
    program_behaves (PS.sem c (prog_interface p)) (Goes_wrong t) ->
    behavior_prefix t b ->
    undef_in Component.main t (prog_interface p).
  Proof.
    intros t b.
    intros Hbeh_improved Hbeh_wrong Hprefix.
    unfold behavior_prefix in Hprefix.
    destruct Hprefix as []; subst.
    inversion Hbeh_wrong; subst.
    - inversion Hbeh_improved; subst.
      + inversion H0; subst.
        inversion H2; subst;
          pose proof PS.initial_state_determinism H H1; subst;
          destruct x; simpl in *; try discriminate;
          inversion H3; subst.
        * (* termination *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** contradiction.
          ** admit.
        * (* silent divergence *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** inversion H8; subst.
             exfalso. eapply H5. eauto.
          ** admit.
        * (* reactive divergence *)
          admit.
        * (* goes wrong *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** admit.
          ** inversion H10; subst.
             *** admit.
             *** exfalso. eapply H8. eauto.
      + specialize (H2 s). contradiction.
    - inversion Hbeh_improved; subst.
      + specialize (H0 s). contradiction.
      + unfold behavior_app in *. simpl in *.
        destruct x; try discriminate.
        inversion H; subst.
        unfold undef_in. simpl.
        exfalso. eapply H0.
        eapply PS.initial_state_intro
          with (p:=c) (p':=p)
               (scs:=CS.initial_machine_state (Source.program_link c p))
               (sps:=PS.partialize (Source.prog_interface p)
                                   (CS.initial_machine_state (Source.program_link c p)));
          auto.
        * apply linkable_sym; auto.
        * apply PS.partialize_correct; auto.
        * unfold CS.initial_state.
          reflexivity.
  Admitted.
End Decomposition.

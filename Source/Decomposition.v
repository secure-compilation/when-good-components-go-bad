Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Blame.
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

Import Source.

Section Decomposition.
  Variable p c: program.

  Hypothesis linkability:
    linkable_programs p c.

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
        * eapply PS.ContextControl; eauto.
          ** apply Hics_init.
      + eapply PS.ContextControl; eauto.
    (* program has control *)
    - split.
      + eapply PS.initial_state_intro with (p':=c).
        * reflexivity.
        * assumption.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.
          ** apply Hics_init.
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
        * PS.simplify_turn. rewrite Htarget. auto.
        * eauto.
        * assumption.
      + PS.simplify_turn.
        rewrite Htarget in H5. discriminate.
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
             erewrite <- PS.context_allocation_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- PS.context_allocation_in_partialized_memory; eauto.

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
             erewrite <- PS.context_store_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- PS.context_store_in_partialized_memory; eauto.

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

  Lemma ub_blaming:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in (main_comp (program_link p c)) t
               (prog_interface p) \/
      undef_in (main_comp (program_link p c)) t
               (prog_interface c).
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
    - pose proof (who_is_in_control_after last_event) as comp_to_blame.
      (* comp_to_blame is either in p or c due to trace well-formedness *)
      admit.
    - apply no_last_event_implies_empty_trace in Hlast_event.
      rewrite Hlast_event.
      unfold undef_in. simpl.
      apply linked_programs_main_component_origin; auto.
  Admitted.

  Lemma program_ub_preservation:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in (main_comp (program_link p c)) t
               (prog_interface p) ->
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
          intial state for the partial semantics.
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
        * auto.
        * CS.unfold_state init_s. simpl in *.
          destruct (C \in domm (prog_interface c)) eqn:Hctx.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn. auto.
             *** reflexivity.
             *** reflexivity.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn.
                 unfold negb. rewrite Hctx.
                 auto.
             *** reflexivity.
             *** reflexivity.
             *** auto.
      + inversion Hstate_beh; subst.
        econstructor.
        * (* simulate star with decomposition *) admit.
        * (* show preservation of stuckness *) admit.
        * (* show preservation of non-final state *) admit.
    (* program went wrong because it doesn't have an initial state *)
    - apply program_goes_initially_wrong.
      intros s.
      unfold not. intro contra.
      inversion contra; subst.
      unfold CS.initial_state in H3. subst.
      eapply H.
      admit.
  Admitted.

  Lemma ub_improvement:
    forall t beh_imp,
      program_behaves (PS.sem p (prog_interface c))
                      (Goes_wrong t) ->
      undef_in (main_comp (program_link p c)) t
               (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c))
                      (behavior_app t beh_imp) ->
      beh_imp = Goes_wrong E0.
  Proof.
    intros t beh_imp Hbeh1 Hbeh2.
  Admitted.

  Corollary decomposition_with_refinement_and_blame:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      (beh1 = beh2 \/
       exists t, beh1 = Goes_wrong t /\
                 behavior_prefix t beh2 /\
                 undef_in (main_comp (program_link p c)) t
                          (prog_interface c)).
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
          rewrite (ub_improvement Hbeh1 Hblame Hbeh2).
          simpl. rewrite E0_right. reflexivity.
        * right.
          eexists. split.
          ** reflexivity.
          ** split; assumption.
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
End Decomposition.
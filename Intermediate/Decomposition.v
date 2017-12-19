Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Blame.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Intermediate.

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
    destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Htarget;
      exists (PS.partialize (gps, mem, regs, pc) (prog_interface c));
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
      CS.final_state (prepare_global_env (program_link p c)) ics ->
      PS.final_state p (prog_interface c) ips.
  Proof.
    intros ics ips Hpartial Hics_final.
    CS.unfold_states.
    (* case analysis on who has control *)
    destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Htarget.
    (* context has control *)
    - inversion Hpartial; inversion H; subst.
      + PS.simplify_turn.
        rewrite Htarget in H4. discriminate.
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
        rewrite Htarget in H4. discriminate.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.step (prepare_global_env (program_link p c)) ics t ics' ->
    forall ips,
      PS.partial_state (prog_interface c) ics ips ->
    exists ips',
      PS.step p (prog_interface c) (prepare_global_env p) ips t ips' /\
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
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             erewrite <- find_label_in_component_1; eauto.
      + econstructor; auto.
        ** PS.simplify_turn.
           erewrite <- find_label_in_component_1; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             match goal with
             | Hsame_comp: Pointer.component _ = Pointer.component _ |- _ =>
               rewrite Hsame_comp; assumption
             end.
      + econstructor; auto.
        * PS.simplify_turn.
          match goal with
          | Hsame_comp: Pointer.component _ = Pointer.component _ |- _ =>
            rewrite Hsame_comp; assumption
          end.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             erewrite <- find_label_in_procedure_1; eauto.
      + econstructor; auto.
        * PS.simplify_turn.
          erewrite <- find_label_in_procedure_1; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    (* call *)
    (* case analysis on the target *)
    - destruct (C' \in domm (prog_interface c)) eqn:Htarget.
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

    (* return *)
    (* case analysis on the target *)
    - destruct (Pointer.component pc' \in domm (prog_interface c)) eqn:Htarget.
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

    (* epsilon steps *)

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             erewrite <- find_label_in_component_1; eauto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           erewrite <- find_label_in_component_1; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             match goal with
             | Heq_comp: Pointer.component ?PC' = Pointer.component ?PC |- _ =>
               rewrite Heq_comp
             end; auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           match goal with
           | Heq_comp: Pointer.component ?PC' = Pointer.component ?PC |- _ =>
             rewrite Heq_comp
           end; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             erewrite <- find_label_in_procedure_1; eauto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           erewrite <- find_label_in_procedure_1; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); auto.
        * eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    (* call *)
    (* case analysis on the target *)
    - destruct (C' \in domm (prog_interface c)) eqn:Htarget.
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

    (* return *)
    (* case analysis on the target *)
    - destruct (Pointer.component pc' \in domm (prog_interface c)) eqn:Htarget.
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

  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  Hypothesis starting_component:
    prog_main (program_link p c) = Some (mainC, mainP).

  Corollary preservation_of_program_ub:
    forall t,
      program_behaves (CS.sem (program_link p c)) (Goes_wrong t) ->
      undef_in mainC t (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c)) (Goes_wrong t).
  Proof.
    intros t.
    intros Hbeh Hblame.
    inversion Hbeh; subst.
    - eapply program_runs with (PS.partialize s (prog_interface c)).
      + apply PS.initial_state_intro with (p':=c) (ics:=s); auto.
        apply PS.partialized_state_is_partial.
      + inversion H0; subst.
        admit.
    - apply program_goes_initially_wrong.
      intros s contra.
      inversion contra; subst.
      apply (H0 ics).
      admit.
  Admitted.
End Decomposition.

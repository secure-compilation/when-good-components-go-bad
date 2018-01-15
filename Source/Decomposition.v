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
          ** erewrite <- PS.context_allocation_gets_filtered; eauto.
      + eapply PS.ContextControl; eauto.
        * erewrite <- PS.context_allocation_gets_filtered; eauto.

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
          ** erewrite <- PS.context_store_gets_filtered; eauto.
      + eapply PS.ContextControl; eauto.
        * erewrite <- PS.context_store_gets_filtered; eauto.

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
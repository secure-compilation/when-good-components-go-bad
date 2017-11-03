Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.
Require Import S2I.Definitions.

Import Intermediate.

Section Decomposition.
  Variable prog: Intermediate.program.
  Variable ctx: Program.interface.

  (*
  Hypothesis input_program_closedness:
    Intermediate.closed_program prog.

  Hypothesis context_validity:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (Intermediate.prog_interface prog).
  *)

  Let G : Intermediate.GlobalEnv.global_env := Intermediate.GlobalEnv.init_genv prog.

  Lemma match_initial_states:
    forall ics,
      I.CS.initial_state prog ics ->
    exists ips,
      I.PS.initial_state prog ctx ips /\ I.PS.partial_state ctx ics ips.
  Proof.
    intros ics Hics_init.
    (* case analysis on who has control, then build the partial state *)
  Admitted.

  Lemma match_final_states:
    forall ics ips r,
      I.PS.partial_state ctx ics ips ->
      I.CS.final_state G ics r ->
      I.PS.final_state prog ctx ips r.
  Proof.
    intros ics ips r Hpartial Hics_final.
    (* case analysis on who has control *)
  Admitted.

  Ltac simplify_turn :=
    unfold S.PS.is_program_component, S.PS.is_context_component in *;
    unfold I.PS.is_program_component, I.PS.is_context_component in *;
    unfold turn_of, S.PS.state_turn, I.PS.state_turn in *;
    simpl in *;
    auto.

  Lemma lockstep_simulation:
    forall ics t ics',
      I.CS.step G ics t ics' ->
    forall ips,
      I.PS.partial_state ctx ics ips ->
    exists ips',
      I.PS.step ctx G ips t ips' /\ I.PS.partial_state ctx ics' ips'.
  Proof.
    intros ics t ics' Hstep ips Hpartial.

    (* case analysis on who has control *)
    inversion Hpartial; subst;
    inversion Hstep; subst.

    (** program has control **)

    (* epsilon steps *)

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
          ** admit.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
        ** admit.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. erewrite <- find_label_in_component_1; eauto.
      + econstructor; auto.
        ** simplify_turn. erewrite <- find_label_in_component_1; eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. rewrite H9. eauto.
      + econstructor; auto.
        ** simplify_turn. rewrite H9. eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. erewrite <- find_label_in_procedure_1; eauto.
      + econstructor; auto.
        ** simplify_turn. erewrite <- find_label_in_procedure_1; eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
          ** admit.
      + econstructor; auto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
          ** admit.

    (* call *)
    - (* case analysis on the target *)
      admit.

    (* return *)
    - (* case analysis on the target *)
      admit.

    (** context has control **)

    (* epsilon steps *)
    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.
        * admit.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * erewrite find_label_in_component_1; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * rewrite H9; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * erewrite find_label_in_procedure_1; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.
        * admit.

    (* call *)
    - (* case analysis on the target *)
      admit.

    (* return *)
    - (* case analysis on the target *)
      admit.
  Admitted.

  Theorem decomposition:
    forward_simulation (I.CS.sem prog) (I.PS.sem prog ctx).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1, program_behaves (I.CS.sem prog) beh1 ->
    exists beh2, program_behaves (I.PS.sem prog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.
End Decomposition.

Section DecompositionAndLinking.
  Variable p c: Intermediate.program.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  Corollary decomposition_with_linking:    
    forward_simulation (I.CS.sem (Intermediate.program_link p c mainC mainP))
                       (I.PS.sem (Intermediate.program_link p c mainC mainP)
                                 (Intermediate.prog_interface p)).
  Proof.
    apply decomposition.
  Qed.
End DecompositionAndLinking.
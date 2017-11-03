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
    inversion Hpartial; subst.

    (** program has control **)
    - admit.

    (** context has control **)
    - admit.
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
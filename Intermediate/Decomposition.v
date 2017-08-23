Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.

Import Intermediate.

Section Decomposition.
  Variable p: program.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.
  Variable split: list Component.id.

  Let G := init_env p.
  Let G' := init_env (PS.partialize p split).

  Inductive related_states : CS.state -> PS.state -> Prop := .

  Lemma initial_states_match:
    forall s1,
      CS.initial_state G mainC mainP s1 ->
    exists s2,
      PS.initial_state G' mainC mainP s2 /\ related_states s1 s2.
  Proof.
    intros s1 Hs1_init.
    Admitted.

  Lemma final_states_match:
    forall s1 s2 r,
      related_states s1 s2 ->
      CS.final_state G s1 r -> PS.final_state G' s2 r.
  Proof.
  Admitted.

  Lemma step_simulation:
    forall s1 s2,
      related_states s1 s2 ->
    forall t s1',
      CS.step G s1 t s1' ->
    exists s2',
      PS.step G' s2 t s2' /\ related_states s1' s2'.
  Proof.
  Admitted.

  Theorem forward_sim:
    forward_simulation (CS.sem p mainC mainP) (PS.sem (PS.partialize p split) mainC mainP).
  Proof.
  Admitted.
End Decomposition.
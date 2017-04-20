(* from CompCert Behaviors.v *)

Require Import Traces.
Require Import Smallstep.
Set Implicit Arguments.

Inductive program_behavior: Type :=
  | Terminates: trace -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.


Section PROGRAM_BEHAVIORS.
  
  Variable L: semantics.

  (* only removed the return value *)
  Inductive state_behaves (s: state L): program_behavior -> Prop :=
  | state_terminates: forall t s',
      Star L s t s' ->
      final_state L s' ->
      state_behaves s (Terminates t)
  | state_diverges: forall t s',
      Star L s t s' -> Forever_silent L s' ->
      state_behaves s (Diverges t)
  | state_reacts: forall T,
      Forever_reactive L s T ->
      state_behaves s (Reacts T)
  | state_goes_wrong: forall t s',
      Star L s t s' ->
      Nostep L s' ->
      ~final_state L s' ->
      state_behaves s (Goes_wrong t).

  Inductive program_behaves: program_behavior -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves s beh ->
      program_behaves beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves (Goes_wrong E0).

End PROGRAM_BEHAVIORS.

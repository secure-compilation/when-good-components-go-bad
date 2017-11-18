Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the given argument *)

Open Scope positive_scope.

Definition identity : program := {|
  prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := PMapExtra.of_list [(1, 1%nat)];
  prog_procedures := PMapExtra.of_list [
    (1, PMapExtra.of_list [
      (1, E_deref E_local)])];
  prog_main := (1, 1)
|}.

Definition fuel := 1000%nat.
Definition to_run := run identity (Int 42) fuel.

Extraction "/tmp/run_identity.ml" to_run.
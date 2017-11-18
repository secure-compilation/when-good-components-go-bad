Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the given argument incremented by 1 *)

Open Scope positive_scope.

Definition increment : program := {|
  prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := PMapExtra.of_list [(1, 1%nat)];
  prog_procedures := PMapExtra.of_list [
    (1, PMapExtra.of_list [
      (1, E_binop Add (E_deref E_local) (E_val (Int 1)))])];
  prog_main := (1, 1)
|}.

Definition fuel := 1000%nat.
Definition to_run := run increment (Int 42) fuel.

Extraction "/tmp/run_increment.ml" to_run.
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* nested calls between two components *)

Open Scope positive_scope.

Definition nested_calls : program := {|
  prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [(2, 1)];
                              Component.export := [1; 2] |});
                       (2, {| Component.import := [(1, 2)];
                              Component.export := [1] |})];
  prog_buffers := PMapExtra.of_list [(1, inl 1%nat); (2, inl 1%nat)];
  prog_procedures := PMapExtra.of_list [
    (1, PMapExtra.of_list [
      (1, E_binop Add (E_deref E_local) (E_call 2 1 (E_deref E_local)));
      (2, E_deref E_local)]);
    (2, PMapExtra.of_list [
      (1, E_binop Add (E_deref E_local) (E_call 2 2 (E_deref E_local)));
      (2, E_binop Add (E_deref E_local) (E_call 1 2 (E_deref E_local)))])];
  prog_main := (1, 1)
|}.

Definition fuel := 1000%nat.
Definition to_run := run nested_calls (Int 1) fuel.

Extraction "/tmp/run_nested_calls.ml" to_run.
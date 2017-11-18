Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* naive factorial *)

Open Scope positive_scope.

Definition factorial : program := {|
  prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [(2, 1)];
                              Component.export := [1] |});
                       (2, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := PMapExtra.of_list [(1, inl 1%nat); (2, inl 1%nat)];
  prog_procedures := PMapExtra.of_list [
    (1, PMapExtra.of_list [
      (1, E_call 2 1 (E_deref E_local))]);
    (2, PMapExtra.of_list [
      (1, E_if (E_binop Leq (E_deref E_local) (E_val (Int 1)))
               (E_val (Int 1))
               (E_binop Mul
                        (E_deref E_local)
                        (E_call 2 1 (E_binop Minus (E_deref E_local) (E_val (Int 1))))))])];
  prog_main := (1, 1)
|}.

Definition fuel := 1000%nat.
Definition to_run := run factorial (Int 5) fuel.

Extraction "/tmp/run_fact.ml" to_run.
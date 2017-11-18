Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the value present in the second cell of its
   local buffer *)

Open Scope positive_scope.

Definition default_init_buffer: program := {|
  prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := PMapExtra.of_list [(1, inr [Undef; Int 42])];
  prog_procedures := PMapExtra.of_list [
    (1, PMapExtra.of_list [
      (1, E_deref (E_binop Add E_local (E_val (Int 1))))])];
  prog_main := (1, 1)
|}.

Definition fuel := 1000%nat.
Definition to_run := run default_init_buffer (Int 0) fuel.

Extraction "/tmp/run_default_init_buffer.ml" to_run.
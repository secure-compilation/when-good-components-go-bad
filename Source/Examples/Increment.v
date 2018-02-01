Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that calls the increment function *)

Definition increment : program := {|
  prog_interface :=
    mkfmap [(1, {| Component.import := fset [];
                   Component.export := fset [] |})];
  prog_buffers :=
    mkfmap [(1, inl 1)];
  prog_procedures :=
    mkfmap [(1, mkfmap [(1, E_call 1 2 (E_val (Int 42)));
                        (2, E_binop Add (E_deref E_local) (E_val (Int 1)))])];
  prog_main := Some (1, 1)
|}.

Definition fuel := 1000.
Definition to_run := run increment fuel.

Extraction "/tmp/run_source_increment.ml" to_run.
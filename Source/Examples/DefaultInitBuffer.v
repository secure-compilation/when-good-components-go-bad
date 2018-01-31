Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the value present in the second cell of its
   local buffer *)

Definition default_init_buffer: program := {|
  prog_interface :=
    mkfmap [(1, {| Component.import := fset [];
                   Component.export := fset [1] |})];
  prog_buffers :=
    mkfmap [(1, inr [Undef; Int 42])];
  prog_procedures :=
    mkfmap [(1, mkfmap [(1, E_deref (E_binop Add E_local (E_val (Int 1))))])];
  prog_main := Some (1, 1)
|}.

Definition fuel := 1000.
Definition to_run := run default_init_buffer fuel.

Extraction "/tmp/run_source_default_init_buffer.ml" to_run.
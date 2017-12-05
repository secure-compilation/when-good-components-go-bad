Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the given argument *)

Definition identity : program := {|
  prog_interface :=
    mkfmap [(1, {| Component.import := fset [];
                   Component.export := fset [1] |})];
  prog_buffers :=
    mkfmap [(1, inl 1)];
  prog_procedures :=
    mkfmap [(1, mkfmap [(1, E_val (Int 42))])];
  prog_main := Some (1, 1)
|}.

Definition fuel := 1000.
Definition to_run := run identity fuel.

Extraction "/tmp/run_identity.ml" to_run.
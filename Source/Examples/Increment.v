Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that calls the increment function *)

Definition increment : program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [] |})];
  prog_buffers :=
    mkfmap [(Component.main, inl 1)];
  prog_procedures :=
    mkfmap [(Component.main,
             mkfmap [(Procedure.main, E_call Component.main 1 (E_val (Int 42)));
                     (1, E_binop Add (E_deref E_local) (E_val (Int 1)))])]
|}.

Definition fuel := 1000.
Definition to_run := run increment fuel.

Set Warnings "-extraction-reserved-identifier -extraction-opaque-accessed".
Extraction "/tmp/run_source_increment.ml" to_run.
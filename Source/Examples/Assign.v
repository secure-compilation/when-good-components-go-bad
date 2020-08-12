Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* A program that uses assignments *)

Definition assign: program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [] |})];
  prog_buffers :=
    mkfmap [(Component.main, inr [Undef; Int 42])];
  prog_procedures :=
    mkfmap [(Component.main, mkfmap [(Procedure.main,
                                      E_seq (E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 44)))
                                            (E_deref (E_binop Add E_local (E_val (Int 1)))))])]
|}.

Definition fuel := 1000.
Definition to_run := run assign fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_source_assign.ml" to_run.

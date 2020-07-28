Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that does litteraly nothing *)

Definition empty : program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [] |})];
  prog_buffers :=
    mkfmap [(Component.main, inl 1)];
  prog_procedures :=
    mkfmap [(Component.main,
             mkfmap [(Procedure.main, E_exit)])]
|}.

Definition fuel := 1000.
Definition to_run := run empty fuel.

(* Unset Extraction AccessOpaque. *)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_source_empty.ml" to_run.

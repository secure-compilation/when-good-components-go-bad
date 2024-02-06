Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that calls the identity function *)

Definition identity : program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [] |})];
  prog_buffers :=
    mkfmap [(Component.main, inl 1)];
  prog_procedures :=
    mkfmap [(Component.main,
             mkfmap [(Procedure.main, E_call Component.main 1 (E_val (Int 42)));
                     (1, E_arg)])]
|}.

Definition fuel := 1000.
Definition to_run := run identity fuel.

(* Unset Extraction AccessOpaque. *)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_source_identity.ml" to_run.

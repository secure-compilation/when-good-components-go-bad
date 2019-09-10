Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that calls the identity function *)

Definition identity : program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [];
                Component.public_buffer_size := 0|})];
  prog_buffers :=
    mkfmap [(Component.main, (inl 1, inl 0))];
  prog_procedures :=
    mkfmap [(Component.main,
             mkfmap [(Procedure.main, E_call Component.main 1 (E_val (Int 42)));
                     (1, E_deref (E_local Block.priv))])]
|}.

Definition fuel := 1000.
Definition to_run := run identity fuel.

(* Unset Extraction AccessOpaque. *)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_source_identity.ml" to_run.

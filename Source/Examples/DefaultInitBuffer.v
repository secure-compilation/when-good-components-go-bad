Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* a program that returns the value present in the second cell of its
   local buffer *)

Definition default_init_buffer: program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [];
                Component.export := fset [];
                Component.public_buffer_size := 0|})];
  prog_buffers :=
    mkfmap [(Component.main, (inr [Undef; Int 42], inl 0))];
  prog_procedures :=
    mkfmap [(Component.main, mkfmap [(Procedure.main, E_deref (E_binop Add (E_local Block.priv) (E_val (Int 1))))])]
|}.

Definition fuel := 1000.
Definition to_run := run default_init_buffer fuel.

Extraction "/tmp/run_source_default_init_buffer.ml" to_run.
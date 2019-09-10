Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* naive factorial *)

Definition factorial : program := {|
  prog_interface :=
    mkfmap [(Component.main,
             {| Component.import := fset [(2, 1)];
                Component.export := fset [];
                   Component.public_buffer_size := 0|});
            (2, {| Component.import := fset [];
                   Component.export := fset [1];
                   Component.public_buffer_size := 0|})];
  prog_buffers :=
    mkfmap [(Component.main, (inl 1, inl 0)); (2, (inl 1, inl 0))];
  prog_procedures :=
    mkfmap [
      (Component.main, mkfmap [
        (Procedure.main, E_call 2 1 (E_val (Int 6)))]);
      (2, mkfmap [
        (1, E_if (E_binop Leq (E_deref (E_local Block.priv)) (E_val (Int 1)))
                 (E_val (Int 1))
                 (E_binop Mul
                          (E_deref (E_local Block.priv))
                          (E_call 2 1 (E_binop Minus (E_deref (E_local Block.priv)) (E_val (Int 1))))))])]
|}.

Definition fuel := 1000.
Definition to_run := run factorial fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_source_factorial.ml" to_run.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* nested calls between two components *)

Definition nested_calls : program := {|
  prog_interface :=
    mkfmap [(Component.main,
                {| Component.import := fset [(2, 1)];
                   Component.export := fset [2] |});
            (2, {| Component.import := fset [(Component.main, 2)];
                   Component.export := fset [1] |})];
  prog_buffers :=
    mkfmap [(Component.main, inl 1); (2, inl 1)];
  prog_procedures :=
    mkfmap [
      (Component.main, mkfmap [
        (Procedure.main, E_binop Add (E_val (Int 1)) (E_call 2 1 (E_val (Int 1))));
        (2, E_deref E_local)]);
      (2, mkfmap [
        (1, E_binop Add (E_deref E_local) (E_call 2 2 (E_deref E_local)));
        (2, E_binop Add (E_deref E_local) (E_call Component.main 2 (E_deref E_local)))])]
|}.

Definition fuel := 1000.
Definition to_run := run nested_calls fuel.

Set Warnings "-extraction-reserved-identifier -extraction-opaque-accessed".
Extraction "/tmp/run_source_nested_calls.ml" to_run.
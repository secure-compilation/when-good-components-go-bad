Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Helper.

Import Source.

(* nested calls between two components *)

Definition nested_calls : program := {|
  prog_interface :=
    mkfmap [(1, {| Component.import := fset [(2, 1)];
                   Component.export := fset [1; 2] |});
            (2, {| Component.import := fset [(1, 2)];
                   Component.export := fset [1] |})];
  prog_buffers :=
    mkfmap [(1, inl 1); (2, inl 1)];
  prog_procedures :=
    mkfmap [
      (1, mkfmap [
        (1, E_binop Add (E_val (Int 1)) (E_call 2 1 (E_val (Int 1))));
        (2, E_deref E_local)]);
      (2, mkfmap [
        (1, E_binop Add (E_deref E_local) (E_call 2 2 (E_deref E_local)));
        (2, E_binop Add (E_deref E_local) (E_call 1 2 (E_deref E_local)))])];
  prog_main := Some (1, 1)
|}.

Definition fuel := 1000.
Definition to_run := run nested_calls fuel.

Extraction "/tmp/run_source_nested_calls.ml" to_run.
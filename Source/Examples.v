Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Source.CS.
Require Import Lib.Tactics.
Require Import CompCert.Smallstep.
Require Import CompCert.Events.

Import Source.

(* naive factorial *)

Definition factorial : program := {|
  prog_interface :=
    NMapExtra.of_list [(1, {| Component.import := [(2, 0)];
                              Component.export := [1] |});
                       (2, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := NMapExtra.of_list [(1, 1); (2, 1)];
  prog_procedures := NMapExtra.of_list [
    (1, NMapExtra.of_list [(0, E_call 2 0 (E_val (Int 3)))]);
    (2, NMapExtra.of_list [(0,
      E_if (E_binop Leq (E_deref E_local) (E_val (Int 1)))
        (E_val (Int 1))
        (E_binop Mul
                 (E_deref E_local)
                 (E_call 2 0 (E_binop Minus (E_deref E_local) (E_val (Int 1))))))])]
|}.
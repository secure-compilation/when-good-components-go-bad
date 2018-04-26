
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.

Require Extraction.
Require extraction.ExtrOcamlString.

Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.Printer.
Require Import I2MP.Encode.
Require Import I2MP.Linearize.

Definition test_program : Intermediate.program :=
  let c0 := [fmap (0, [:: ICall 1 0; IReturn])] in
  let c0_i := Component.mkCompInterface
                fset0
                (fset [:: (1, 0)]) in
  let c1 := [fmap (0, [:: IConst (IInt 5) R_COM; IReturn])] in
  let c1_i := Component.mkCompInterface
                (fset [:: 0])
                fset0 in
  Intermediate.mkProg
    [fmap (0, c0_i); (1, c1_i)] (* Interface: nothing imported/exported*)
    [fmap (0, c0); (1, c1)] (* code *)
    (emptym) (* Pre-allocated buffers *)
    (Some 0). (* Main procedure idtac *)

Definition test_program_machine := load (encode (linearize test_program)).

Extraction "/tmp/tl_test.ml" coqstring_of_state test_program_machine stepf.

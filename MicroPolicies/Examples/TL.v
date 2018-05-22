
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

Require Extraction.
Require extraction.ExtrOcamlString.

Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.Printer.
Require Import I2MP.Encode.
Require Import I2MP.Linearize.

Require Import MicroPolicies.Utils.
Import DoNotation.

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


Definition test_alloc : Intermediate.program :=
  let c0 := [fmap (0, [:: IConst (IInt 5) R_ONE ; IAlloc R_COM R_ONE; IReturn])] in
  let c0_i := Component.mkCompInterface fset0 fset0 in
  Intermediate.mkProg
    emptym (* Interface: nothing imported/exported*)
    [fmap (0, c0)] (* code *)
    (emptym) (* Pre-allocated buffers *)
    (Some 0). (* Main procedure idtac *)

Definition test_program_machine := load (encode (linearize test_program)).
Definition test_alloc_machine := load (encode (linearize test_alloc)).

Extraction "/tmp/tl_test.ml" coqstring_of_state test_program_machine test_alloc_machine stepf.

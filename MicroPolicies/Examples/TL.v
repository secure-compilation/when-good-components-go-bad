
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import word.
From extructures Require Import fmap fset.

Require Extraction.
Require extraction.ExtrOcamlString.

Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.Printer.
(*Require Import I2MP.Encode.*)
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

(*
Definition test_program_machine := load (encode (linearize test_program)).
Definition test_alloc_machine := load (encode (linearize test_alloc)).

Extraction "/tmp/tl_test.ml" coqstring_of_state test_program_machine test_alloc_machine stepf.
 *)

Require Import Transitional S2I.Examples.Helper.

Definition fuel := 1000%nat.
Definition to_run_i1 := compile_intermediate_and_run test_program fuel.
Definition to_run_i2 := compile_intermediate_and_run test_alloc fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_intermediate_compiled_test_program.ml" to_run_i1.
Extraction "/tmp/run_intermediate_compiled_test_alloc.ml" to_run_i2.

Definition to_run1 := compile_and_run_from_intermediate test_program fuel.
Definition to_run2 := compile_and_run_from_intermediate test_alloc fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_test_program.ml" to_run1.
Extraction "/tmp/run_mp_compiled_test_alloc.ml" to_run2.

(*
Require Import Merged Int32.

Definition to_run_mr := @Merged.compile_and_run_from_source_merged_ex concrete_int_32_mt identity fuel.
(*
Definition to_run_mr := @I2MP.Examples.Helper.compile_and_run_and_show_from_source_merged concrete_int_32_mt identity fuel.
*)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_merged_compiled_identity.ml" to_run_mr.
*

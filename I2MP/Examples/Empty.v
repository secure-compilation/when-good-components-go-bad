Require Import Common.Definitions.
Require Import Common.Values.
Require Import Transitional.
Require Import Source.Examples.Empty.

Definition fuel := 1000%nat.
Definition to_run_tr := compile_and_run_from_source_ex empty fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_tagged_compiled_empty.ml" to_run_tr.

Require Import Merged Int32 I2MP.Examples.Helper.

Definition to_run_mr := @Merged.compile_and_run_from_source_merged_ex concrete_int_32_mt empty fuel.
(*
Definition to_run_mr := @I2MP.Examples.Helper.compile_and_run_and_show_from_source_merged concrete_int_32_mt empty fuel. *)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_merged_compiled_empty.ml" to_run_mr.

Require Import I2MP.Examples.Helper.

Definition to_run := compile_and_run_mp empty fuel.
Extraction "/tmp/run_mp_compiled_empty.ml" to_run.

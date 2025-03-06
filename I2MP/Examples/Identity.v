Require Import Common.Definitions.
Require Import Common.Values.
Require Import Transitional.
Require Import Source.Examples.Identity.

Definition fuel := 200%nat.
Definition to_run_tr := compile_and_run_from_source_ex identity fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_tagged_compiled_identity.ml" to_run_tr.


Require Import Merged Int32.

Definition to_run_mr := @Merged.compile_and_run_from_source_merged_ex concrete_int_32_mt identity fuel.
(*
Definition to_run_mr := @I2MP.Examples.Helper.compile_and_run_and_show_from_source_merged concrete_int_32_mt identity fuel.
*)
Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_merged_compiled_identity.ml" to_run_mr.

Require Import I2MP.Examples.Helper.

Definition to_run := compile_and_run_mp identity fuel.
Extraction "/tmp/run_mp_compiled_identity.ml" to_run.

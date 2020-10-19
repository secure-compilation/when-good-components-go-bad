Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Examples.Increment.
Require Import Tagging.Examples.Helper.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run_from_source_ex increment fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_increment.ml" to_run.
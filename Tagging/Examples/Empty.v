Require Import Common.Definitions.
Require Import Common.Values.
Require Import Tagging.Examples.Helper.
Require Import Source.Examples.Empty.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run_from_source_ex empty fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_empty.ml" to_run.

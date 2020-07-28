Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Empty.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run empty fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_intermediate_compiled_empty.ml" to_run.

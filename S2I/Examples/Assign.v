Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Assign.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run assign fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_intermediate_compiled_assign.ml" to_run.

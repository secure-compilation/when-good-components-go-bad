Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Increment.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run increment fuel.

Set Warnings "-extraction-reserved-identifier -extraction-opaque-accessed".
Extraction "/tmp/run_intermediate_compiled_increment.ml" to_run.
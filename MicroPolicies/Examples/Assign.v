Require Import Source.Examples.Assign.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 20.
Definition to_run := compile_and_run assign fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_assign.ml" to_run.

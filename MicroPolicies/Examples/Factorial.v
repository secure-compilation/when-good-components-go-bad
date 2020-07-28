Require Import Source.Examples.Factorial.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 1000.
Definition to_run := compile_and_run factorial fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_factorial.ml" to_run.

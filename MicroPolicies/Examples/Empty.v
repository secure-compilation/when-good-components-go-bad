Require Import Source.Examples.Empty.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 50.
Definition to_run := compile_and_run empty fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_empty.ml" to_run.

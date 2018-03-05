Require Import Source.Examples.Increment.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 1000.
Definition to_run := compile_and_run increment fuel.

Extraction "/tmp/run_compiled_increment.ml" to_run.
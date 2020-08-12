Require Import Source.Examples.NestedCalls.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 1000.
Definition to_run := compile_and_run nested_calls fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_nested_calls.ml" to_run.

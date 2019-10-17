Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.NestedCalls.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run nested_calls fuel.

Set Warnings "-extraction-reserved-identifier -extraction-opaque-accessed".
Extraction "/tmp/run_intermediate_compiled_nested_calls.ml" to_run.

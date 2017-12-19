Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Factorial.

Definition fuel := 1000.
Definition to_run := compile_and_run factorial fuel.

Extraction "/tmp/run_compiled_fact.ml" to_run.

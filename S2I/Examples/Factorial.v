Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Factorial.

Definition fuel := 1000.
Definition to_run := compile_and_run factorial fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_intermediate_compiled_factorial.ml" to_run.

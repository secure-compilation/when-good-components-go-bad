Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Source.Examples.Factorial.
Require Import Tagging.Examples.Helper.


Definition fuel := 2000%nat.
Definition to_run := compile_and_run_from_source_ex factorial fuel.
Definition to_show := compile_and_show factorial.
Definition to_debug := debug factorial fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_factorial.ml" to_run.

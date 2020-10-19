Require Import Common.Definitions.
Require Import Common.Values.
Require Import Tagging.Examples.Helper.
Require Import Source.Examples.Identity.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run_from_source_ex identity fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_identity.ml" to_run.
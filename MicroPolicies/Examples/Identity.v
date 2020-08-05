Require Import Source.Examples.Identity.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 100.
Definition to_run := compile_and_run identity fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_identity.ml" to_run.

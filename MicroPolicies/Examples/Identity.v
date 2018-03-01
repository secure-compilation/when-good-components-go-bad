Require Import Source.Examples.Identity.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 20.
Definition to_run := compile_and_run identity fuel.

Extraction "/tmp/run_compiled_identity.ml" to_run.
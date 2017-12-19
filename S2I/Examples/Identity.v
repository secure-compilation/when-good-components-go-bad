Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.Identity.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run identity fuel.

Extraction "/tmp/run_compiled_identity.ml" to_run.

Require Import Source.Examples.Identity.
Require Import I2MP.Examples.Helper.

Definition fuel := 8.
Definition to_run := compile_and_run' identity fuel.
Definition compiled_id := compile identity.

Set Warnings "-extraction-reserved-identifier".

Eval cbv in compiled_id.

Extraction "/tmp/run_compiled_identity.ml" to_run compiled_id.

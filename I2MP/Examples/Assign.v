Require Import Source.Examples.Assign.
Require Import I2MP.Examples.Helper.

Definition fuel := 60.
Definition to_run := compile_and_run assign fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_assign.ml" to_run.

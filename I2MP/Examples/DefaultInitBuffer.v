Require Import Source.Examples.DefaultInitBuffer.
Require Import I2MP.Examples.Helper.

Definition fuel := 100.
Definition to_run := compile_and_run default_init_buffer fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_compiled_default_init_buffer.ml" to_run.

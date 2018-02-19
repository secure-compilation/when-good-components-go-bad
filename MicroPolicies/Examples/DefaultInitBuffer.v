Require Import Source.Examples.DefaultInitBuffer.
Require Import MicroPolicies.Examples.Helper.

Definition fuel := 1000.
Definition to_run := compile_and_run default_init_buffer fuel.

Extraction "/tmp/run_compiled_default_init_buffer.ml" to_run.
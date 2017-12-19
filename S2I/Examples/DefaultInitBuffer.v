Require Import Common.Definitions.
Require Import Common.Values.
Require Import S2I.Examples.Helper.
Require Import Source.Examples.DefaultInitBuffer.

Definition fuel := 1000%nat.
Definition to_run := compile_and_run default_init_buffer fuel.

Extraction "/tmp/run_compiled_default_init_buffer.ml" to_run.

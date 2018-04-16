Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import MicroPolicies.Examples.Helper.
Require Import I2MP.Encode.
Require Import I2MP.Precompile.
From mathcomp Require Import seq.
From CoqUtils Require Import fset fmap.

Definition program : Intermediate.program :=
  let code_main := [:: IConst (IInt 5) R_COM; IReturn] in
  let main := setm emptym 0 (code_main) in
  let code := setm emptym 0 (main) in
  let comp_interface := Component.mkCompInterface (fset0) (fset0) in
  Intermediate.mkProg
    (setm emptym 0 comp_interface) (* Interface: nothing imported/exported*)
    code (* code *)
    (emptym) (* Pre-allocated buffers *)
    (Some 0). (* Main procedure id *)


Definition fuel := 6.
Definition to_run := compile_and_run' program fuel.

Extraction "/tmp/run_compiled_program.ml" to_run.
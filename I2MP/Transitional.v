From mathcomp Require Import ssreflect eqtype seq.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.

(* TL TODO: to keep working, assuming the "mt" parameter, but have to get rid of all this stuff *)



Import Machine.

Definition program := seq (instr * mem_tag).

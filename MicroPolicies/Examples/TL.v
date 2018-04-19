
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.

Require Extraction.
Require extraction.ExtrOcamlString.
Require Import MicroPolicies.Printer.

Require Import MicroPolicies.Examples.Helper.

Definition empty_machine := load emptym.

Extraction "/tmp/tl_test.ml" coqstring_of_regs empty_machine.

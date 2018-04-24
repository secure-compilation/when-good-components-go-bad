
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.

Require Extraction.
Require extraction.ExtrOcamlString.

Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Printer.
Require Import MicroPolicies.Exec.
Require Import I2MP.Encode.
Require Import I2MP.Precompile.

(* needed registers *)
Definition reg0 : {fmap reg Symbolic.mt -> ratom } :=
  let m := emptym in
  let m := setm m (as_word 0) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 1) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 2) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 3) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 4) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 5) (Atom (as_word 0) (Other)) in
   setm m (as_word 6) (Atom (as_word 0) (Other)).


Definition load (m : {fmap mword Symbolic.mt -> matom }) : state :=
  {| Symbolic.mem := m ;
     Symbolic.regs := reg0 ;
     Symbolic.pc := {| vala := word.as_word 0 ; taga := Level 0 |} ;
     Symbolic.internal := tt |}.

Definition test_program : Intermediate.program :=
  let c0 := [fmap (0, [:: ICall 1 0; IReturn])] in
  let c0_i := Component.mkCompInterface
                fset0
                (fset [:: (1, 0)]) in
  let c1 := [fmap (0, [:: IConst (IInt 5) R_COM; IReturn])] in
  let c1_i := Component.mkCompInterface
                (fset [:: 0])
                fset0 in
  Intermediate.mkProg
    [fmap (0, c0_i); (1, c1_i)] (* Interface: nothing imported/exported*)
    [fmap (0, c0); (1, c1)] (* code *)
    (emptym) (* Pre-allocated buffers *)
    (Some 0). (* Main procedure idtac *)

Definition empty_machine := load emptym.

Definition test_program_machine := load (encode (precompile test_program)).

Definition stepf := @stepf sym_lrc lrc_syscalls.

Extraction "/tmp/tl_test.ml" coqstring_of_state encode precompile test_program_machine stepf.


From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.


Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Exec.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import I2MP.Precompile.
Require Import I2MP.Encode.

(* TL TODO: it is not the right place to put state initialization? *)
Definition reg0 : {fmap reg Symbolic.mt -> ratom } := emptym.

Definition load (m : {fmap mword Symbolic.mt -> matom }) : state :=
  {| Symbolic.mem := m ;
     Symbolic.regs := reg0 ;
     Symbolic.pc := {| vala := word.as_word 0 ; taga := Level 0 |} ;
     Symbolic.internal := tt |}.


Definition test : Intermediate.program.
Admitted.

Check let istate := load (encode (precompile test)) in
      stepf istate.

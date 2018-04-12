From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import I2MP.Encode.
Require Import I2MP.Precompile.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Export Extraction.Definitions.

Require Import Source.Examples.Identity.

Fixpoint execN (n: nat) (st: state) : option state :=
  match n with
  | O => Some st
  | S n' =>
    match stepf st with
    | None => None
    | Some st' => execN n' st'
    end
  end.

(* Six needed registers *)
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

Definition print_reg (st : state) (n : nat) :=
  match (Symbolic.regs st) (as_word n) with
  | None => print_error ocaml_int_2
  | Some n => print_ocaml_int (int2int (int_of_word (vala n)))
  end.

Definition compile_and_run (p: Source.program) (fuel: nat) :=
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some inter_p =>
    let st := load (encode (precompile inter_p)) in
    match execN fuel st with
    | None => print_error ocaml_int_1
    | Some st => print_reg st 2
    end
  end.

Definition compile_and_run' (p: Intermediate.program) (fuel:nat) :=
  let st := load (encode (precompile p)) in
    match execN fuel st with
    | None => print_error ocaml_int_1
    | Some st' => print_reg st' 2
    end
.

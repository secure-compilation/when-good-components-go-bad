From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap fset.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import I2MP.Encode.
Require Import I2MP.Linearize.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Instance.
Require Export Extraction.Definitions.

Require Import Source.Examples.Identity.

(* needed registers *)
Definition reg0 : {fmap reg Instance.mt -> ratom } :=
  let m := emptym in
  let m := setm m (as_word 0) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 1) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 2) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 3) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 4) (Atom (as_word 0) (Other)) in
  let m := setm m (as_word 5) (Atom (as_word 0) (Other)) in
   setm m (as_word 6) (Atom (as_word 0) (Other)).


Definition load (m : {fmap mword Instance.mt -> matom }) : state :=
  {| Symbolic.mem := m ;
     Symbolic.regs := reg0 ;
     Symbolic.pc := {| vala := word.as_word 0 ; taga := Level 0 |} ;
     Symbolic.internal := tt |}.

Definition print_reg (st : state) (n : nat) : unit :=
  match (Symbolic.regs st) (as_word n) with
  | None => print_error ocaml_int_2
  | Some n => print_ocaml_int (int2int (int_of_word (vala n)))
  end.

Fixpoint print_regs (st : state) (n : nat) (f : fstate) : fstate :=
  match n with
  | O => unit_to_fstate (print_reg st n)
  | S n => let f' := unit_to_fstate (print_reg st (S n)) in print_regs st n f'
  end.

Fixpoint execN (n: nat) (st: state) : option state :=
  match n with
  | O => Some st
  | S n' =>
    match stepf st with
    | None => None
    | Some (st', _) =>
        let fstate' := print_regs st' 6 fstate0 in
        execN n' st'
    end
  end.


Definition compile_and_run (p: Source.program) (fuel: nat) :=
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some inter_p =>
    let st := load (encode (linearize inter_p)) in
    match execN fuel st with
    | None => print_error ocaml_int_1
    | Some st => print_reg st 2
    end
  end.

Definition compile (p: Source.program) :=
  match compile_program p with
  | None => None
  | Some inter_p =>
      Some (load (encode (linearize inter_p)))
  end.

Definition compile_and_run' (p: Source.program) (fuel:nat) :=
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some inter_p =>
      let st := load (encode (linearize inter_p)) in
      match execN fuel st with
      | None => print_error ocaml_int_1
      | Some st' => fstate_to_unit (print_regs st' 6 fstate0)
      end
  end
.

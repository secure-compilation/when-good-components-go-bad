From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrint seq.
From CoqUtils Require Import fmap word.

Require Import Int32.
Require Import LRC.
Require Import Types.
Require Import Symbolic.
Require Import Exec.

Definition mt := concrete_int_32_mt.

Global Instance ops : machine_ops mt := concrete_int_32_ops.
(* ra := word.as_word 5 *)

Global Instance scr : syscall_regs mt := concrete_int_32_scr.
(* syscall_ret  := as_word 16;
   syscall_arg1 := as_word 17;
   syscall_arg2 := as_word 18;
   syscall_arg3 := as_word 19 *)

Definition alloc_addr : imm mt := shlw 1%w (as_word 14). (* 1 << 14 ; as to be an imm for Jal, so under 2^15 *)

Definition table : @Symbolic.syscall_table mt sym_lrc :=
  [fmap (swcast alloc_addr, {| Symbolic.entry_tag := tt ; Symbolic.sem := alloc_fun |})].

Definition state := (@Symbolic.state mt sym_lrc).
Definition stepf := (@Exec.stepf mt ops sym_lrc table).

Definition ratom := (atom (mword mt) value_tag).
Definition matom := (atom (mword mt) mem_tag).

(* Machine initialisation *)
Definition reg0 : {fmap reg mt -> ratom } :=
  [fmap (as_word 0, Atom (as_word 0) Other)
      ; (as_word 1, Atom (as_word 0) Other)
      ; (as_word 2, Atom (as_word 0) Other)
      ; (as_word 3, Atom (as_word 0) Other)
      ; (as_word 4, Atom (as_word 0) Other)
      ; (as_word 5, Atom (as_word 0) Other)
      ; (as_word 6, Atom (as_word 0) Other)
      ; (as_word 16, Atom (as_word 0) Other)
      ; (as_word 17, Atom (as_word 0) Other)
      ; (as_word 18, Atom (as_word 0) Other)
      ; (as_word 19, Atom (as_word 0) Other)].


Definition load (m : {fmap mword mt -> matom }) : state :=
  {| Symbolic.mem := m ;
     Symbolic.regs := reg0 ;
     Symbolic.pc := {| vala := word.as_word 0 ; taga := Level 0 |} ;
     Symbolic.internal := tt |}.

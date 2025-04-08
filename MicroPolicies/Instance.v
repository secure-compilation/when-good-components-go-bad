From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrint seq.
From CoqUtils Require Import word.
From extructures Require Import fmap.

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
Definition reg0 {sp:Symbolic.params} (Other: (Symbolic.tag_type Symbolic.ttypes Symbolic.R)) : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type Symbolic.ttypes Symbolic.R) } :=
  [fmap (as_word 0, Atom (as_word 0) Other)
      ; (as_word 1, Atom (as_word 0) Other)
      ; (as_word 2, Atom (as_word 0) Other)
      ; (as_word 3, Atom (as_word 0) Other)
      ; (as_word 4, Atom (as_word (Nat.pow 2 15)) Other)
      ; (as_word 5, Atom (as_word 0) Other)
      ; (as_word 6, Atom (as_word 0) Other)
      ; (as_word 7, Atom (as_word 0) Other)
      ; (as_word 16, Atom (as_word 0) Other)
      ; (as_word 17, Atom (as_word 0) Other)
      ; (as_word 18, Atom (as_word 0) Other)
      ; (as_word 19, Atom (as_word 0) Other)].


Definition load {sp} {Other} {start_tag} {start_internal} (start : {fmap mword mt -> _ } * nat) nc : @Symbolic.state mt sp :=
  {| Symbolic.mem := fst start ;
     Symbolic.regs := reg0 Other;
     Symbolic.pc := {| vala := word.as_word (snd start) ; taga := start_tag |} ;
     Symbolic.internal := start_internal ;
     Symbolic.comp_num := nc|}.


Require Import Merged.

Definition step_eval_mp := (@Exec.stepf mt ops sym_lrc Merged.table_lrc).
Definition step_eval_me := (@Exec.stepf mt ops Merged.sym_lrc_merged Merged.table).
Definition step_mp := (@Symbolic.step mt ops sym_lrc Merged.table_lrc).
Definition step_me := (@Symbolic.step mt ops Merged.sym_lrc_merged Merged.table).

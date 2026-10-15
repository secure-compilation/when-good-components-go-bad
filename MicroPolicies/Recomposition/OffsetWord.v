(* Word-level helpers for GENERAL (possibly negative, nonzero) per-component code offsets.

   Support kernel for the alignment-free recomposition: [offset1]/[offset2]
   (Recomposition/Definitions.v) are faithful ssrint differences
   [intZmod.addz (Posz p3) (intZmod.oppz (Posz p1))] of code base positions, and the
   simulation relates addresses via [addw w (as_word off)].  Everything here is proven
   over an ABSTRACT width [k] (never reduce concrete 2^32 words — see WordExtra.v's
   proof discipline; ssreflect [rewrite] of word lemmas at the concrete width hangs on
   keyed matching, so downstream users apply these with explicit arguments or vanilla
   [rewrite]).

   All facts are unconditional mod-2^k ring identities: [as_word] is an additive
   morphism ([as_word_add]), so no non-wrap side conditions are needed. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssrint ssralg.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* The faithful (possibly negative) int difference of two nat positions.  A dedicated
   wrapper so [simpl]/[cbn] can NEVER unfold the underlying [intZmod.addz] match (which
   would break rewriting by shape); convert to ring form with [int_diffE]. *)
Definition int_diff (a b : nat) : int := intZmod.addz (Posz a) (intZmod.oppz (Posz b)).
Arguments int_diff : simpl never.

Lemma int_diffE (a b : nat) : int_diff a b = Posz a - Posz b.
Proof. by []. Qed.

(* Common suffix-position cancellation: [a + f + d] vs [b + f + d] differ by [a - b]. *)
Lemma int_diff_cancel2 (a b f d : nat) : int_diff (a + f + d) (b + f + d) = Posz a - Posz b.
Proof. rewrite int_diffE. by lia. Qed.

Section OffsetWordKernel.

Variable k : nat.

(* Rotate the two summands of a double [addw]: (a+b)+c = (a+c)+b.
   The pc-advance congruence: addw (addw pc δ) off = addw (addw pc off) δ. *)
Lemma addw_rotate (a b c : word k) : addw (addw a b) c = addw (addw a c) b.
Proof. by rewrite -addwA (addwC b c) addwA. Qed.

(* [as_word] turns int addition into word addition. *)
Lemma as_word_addwD (x y : int) :
  addw (as_word x) (as_word y) = as_word (x + y) :> word k.
Proof. by rewrite as_word_add. Qed.

Lemma as_word_int0 : as_word (0 : int) = zerow :> word k.
Proof. by []. Qed.

(* THE base-shift lemma: the same in-component position [x] placed at bases [a] vs [b]
   differs by the (possibly negative) offset [Posz a - Posz b].
   [word_of_nat n = as_word (Posz n)] definitionally, so this applies to
   [word_of_nat (x + a) = addw (word_of_nat (x + b)) (as_word off)] directly. *)
Lemma as_word_shiftAB (a b x : nat) :
  as_word (Posz (x + a))
  = addw (as_word (Posz (x + b))) (as_word (Posz a - Posz b)) :> word k.
Proof.
rewrite as_word_addwD.
by have -> : (Posz (x + b) + (Posz a - Posz b)) = Posz (x + a) by lia.
Qed.

(* Bare-position variant (x = 0): any two nat positions differ by their int difference. *)
Lemma as_word_shiftD (a b : nat) :
  as_word (Posz a) = addw (as_word (Posz b)) (as_word (Posz a - Posz b)) :> word k.
Proof.
rewrite as_word_addwD.
by have -> : (Posz b + (Posz a - Posz b)) = Posz a by lia.
Qed.

End OffsetWordKernel.

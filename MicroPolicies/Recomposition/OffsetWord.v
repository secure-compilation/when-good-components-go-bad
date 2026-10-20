From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssrint ssralg.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Definition int_diff (a b : nat) : int := intZmod.addz (Posz a) (intZmod.oppz (Posz b)).
Arguments int_diff : simpl never.

Lemma int_diffE (a b : nat) : int_diff a b = Posz a - Posz b.
Proof. by []. Qed.

Lemma int_diff_cancel2 (a b f d : nat) : int_diff (a + f + d) (b + f + d) = Posz a - Posz b.
Proof. rewrite int_diffE. by lia. Qed.

Section OffsetWordKernel.

Variable k : nat.

Lemma addw_rotate (a b c : word k) : addw (addw a b) c = addw (addw a c) b.
Proof. by rewrite -addwA (addwC b c) addwA. Qed.

Lemma as_word_addwD (x y : int) :
  addw (as_word x) (as_word y) = as_word (x + y) :> word k.
Proof. by rewrite as_word_add. Qed.

Lemma as_word_int0 : as_word (0 : int) = zerow :> word k.
Proof. by []. Qed.

Lemma as_word_shiftAB (a b x : nat) :
  as_word (Posz (x + a))
  = addw (as_word (Posz (x + b))) (as_word (Posz a - Posz b)) :> word k.
Proof.
rewrite as_word_addwD.
by have -> : (Posz (x + b) + (Posz a - Posz b)) = Posz (x + a) by lia.
Qed.

Lemma as_word_shiftD (a b : nat) :
  as_word (Posz a) = addw (as_word (Posz b)) (as_word (Posz a - Posz b)) :> word k.
Proof.
rewrite as_word_addwD.
by have -> : (Posz b + (Posz a - Posz b)) = Posz a by lia.
Qed.

End OffsetWordKernel.

(* Complements to the standard Coq library, ssreflect, and Coq utils *)

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From CoqUtils Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Section FMap.

Variables (T : ordType) (S S' : Type).
Implicit Types (m : {fmap T -> S}) (x : T).

(* FIXME: Move to CoqUtils *)

Lemma domm_mapi (f : T -> S -> S') m : domm (mapim f m) = domm m.
Proof.
by apply/eq_fset=> x; rewrite !mem_domm mapimE; case: (m x).
Qed.

Lemma domm_map (f : S -> S') m : domm (mapm f m) = domm m.
Proof. exact: domm_mapi. Qed.

Lemma unionmK m1 m2 : filterm (fun k _ => m1 k) (unionm m1 m2) = m1.
Proof.
apply/eq_fmap=> k; rewrite filtermE unionmE.
by case: (m1 k) (m2 k)=> //= - [].
Qed.

End FMap.

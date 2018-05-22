From extructures Require Export ord fmap fset.
From mathcomp Require Export ssrbool. (* TODO, strange *)
From mathcomp Require Import ssreflect ssrfun seq.
Require Import Lib.Extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition NMap T := {fmap nat -> T}.

Definition elementsm {A: Type} : NMap A -> list (nat * A) := @FMap.fmval nat_ordType A _.

(* RB: TODO: These lemmas, with their clean proofs, probably belong in CoqUtils. *)

Lemma mapm_unionm (T T' : Type) (m1 m2 : NMap T) (f : T -> T') :
  mapm f (unionm m1 m2) = unionm (mapm f m1) (mapm f m2).
Proof.
  apply /eq_fmap => n. rewrite !(mapmE, unionmE). by case: (m1 n).
Qed.

Lemma filterm_predT (T : Type) (m : NMap T) :
  filterm (fun (k : nat) (_ : T) => true) m = m.
Proof.
  apply /eq_fmap => n. rewrite filtermE. by case: (m n).
Qed.

Lemma filterm_predF (T : Type) (m : NMap T) :
  filterm (fun (k : nat) (_ : T) => false) m = emptym.
Proof.
  apply /eq_fmap => n. rewrite filtermE. by case: (m n).
Qed.

Lemma eq_in_filterm (T:Type) f1 f2 (m : NMap T) :
  (forall k v, m k = Some v -> f1 k v = f2 k v) ->
  filterm f1 m = filterm f2 m.
Proof.
  move=> e. apply/eq_fmap=> k. rewrite 2!filtermE.
  case H : (m k) => [v|] //=.
  now rewrite e.
Qed.

Lemma fdisjoint_filterm_full (T T' : Type) (m1 : NMap T) (m2 : NMap T') :
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m2) m1 = m1.
Proof.
  move => /fdisjointP H.
  rewrite -[RHS]filterm_predT. apply eq_in_filterm => k v kv.
  apply H. apply /dommP. by exists v.
Qed.

Lemma fdisjoint_filterm_empty (T : Type) (m1 m2 : NMap T) :
  domm m1 = domm m2 ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Proof.
  move => H.
  rewrite -[RHS](filterm_predF m2). apply eq_in_filterm => k v kv.
  apply negbTE. apply /negPn. rewrite H. apply /dommP. by exists v.
Qed.

Lemma fdisjoint_filterm_mapm_empty (T T' : Type) (m : NMap T) (f : T -> T') :
  filterm (fun (k : nat) (_ : T') => k \notin domm m) (mapm f m) = emptym.
Proof.
  rewrite -[RHS](filterm_predF (mapm f m)). apply eq_in_filterm => k v kv.
  rewrite -(domm_map f).
  apply negbTE. apply /negPn. apply /dommP. by exists v.
Qed.

Lemma fdisjoint_filterm_mapm_unionm (T T' : Type) (m1 m2 : NMap T) (f : T -> T') :
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f (unionm m1 m2)) =
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f m1).
Proof.
  move => Hdisjoint. rewrite mapm_unionm filterm_union.
  - by rewrite -(fdisjoint_filterm_full Hdisjoint) fdisjoint_filterm_mapm_empty unionm0.
  - by rewrite! domm_map.
Qed.

From extructures Require Export ord fmap fset.
From mathcomp Require Export ssrbool. (* TODO, strange *)
From mathcomp Require Import ssreflect ssrfun seq.
Require Import Lib.Extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

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

(* RB: TODO: Fix name! There is no disjointness condition here, even though its
   counterpart does have it. *)
Lemma fdisjoint_filterm_empty (T : Type) (m1 m2 : NMap T) :
  domm m1 = domm m2 ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Proof.
  move => H.
  rewrite -[RHS](filterm_predF m2). apply eq_in_filterm => k v kv.
  apply negbTE. apply /negPn. rewrite H. apply /dommP. by exists v.
Qed.

(* RB: NOTE: This generalizes the above result. *)
Lemma fsubset_filterm_domm_emptym (T : Type) (m1 m2 : NMap T) :
  fsubset (domm m2) (domm m1) ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Admitted.

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

(* Filter has no effect on reads outside its domain. *)
Lemma getm_filterm_notin_domm :
  forall (T T' : Type) (m1 : NMap T) (m2 : NMap T') k,
    k \notin domm m1 ->
    (filterm (fun (k : nat) (_ : T') => k \notin domm m1) m2) k = m2 k.
Proof.
  intros T T' m1 m2 k Hnotin.
  rewrite filtermE Hnotin.
  destruct (m2 k) as [v |] eqn:Hcase; now rewrite Hcase.
Qed.

(* Set and filter commute if the key is outside the domain of filter. *)
Lemma setm_filterm_notin_domm :
  forall (T T' : Type) (m1 : NMap T) (m2 : NMap T') k (v : T'),
    k \notin domm m1 ->
    setm (filterm (fun (k : nat_ordType) (_ : T') => k \notin domm m1) m2) k v =
    filterm (fun (k : nat_ordType) (_ : T') => k \notin domm m1) (setm m2 k v).
Proof.
  intros T T' m1 m2 k v Hnotin.
  apply /eq_fmap => n.
  rewrite filtermE !setmE filtermE.
  destruct (eqtype.eq_op n k) eqn:Hcase.
  - pose proof eqtype.eqP Hcase; subst n. now rewrite Hnotin.
  - reflexivity.
Qed.

(* RB: NOTE: filterm_union, a related lemma, does not include the final 'm' in
   its name. *)
Lemma filterm_domm_unionm (T T' : Type) (m : NMap T) (m1 m2 : NMap T') :
  filterm (fun (k : nat) (_ : T) => k \notin domm m1)
          (filterm (fun (k : nat) (_ : T) => k \notin domm m2) m) =
  filterm (fun (k : nat) (_ : T) => k \notin domm (unionm m1 m2)) m.
Admitted.

Lemma domm_filterm_fdisjoint_unionm
      (T T' : Type) (i1 i2 : NMap T) (m : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m = domm (unionm i1 i2) ->
  domm (filterm (fun (k : nat) (_ : T') => k \notin domm i2) m) = domm i1.
Admitted.

Lemma domm_filterm_partial_memory
      (T T' : Type) (i1 i2 : NMap T) (m0 m1 m2 : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m0 = domm m1 ->
  domm m2 = domm (unionm i1 i2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m0 =
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m2 ->
  domm (filterm (fun (k : nat) (_ : T') => k \notin domm i1) m1) = domm i2.
Admitted.

Lemma filterm_partial_memory_fsubset
      (T T' : Type) (i1 i2 : NMap T) (m0 m1 m2 : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m0 = domm m1 ->
  domm m2 = domm (unionm i1 i2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m0 =
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m2 ->
  fsubset (domm m1) (domm m2).
Admitted.

(* RB: NOTE: This is not a map lemma proper. More generally, absorption on
   arbitrary subsets. *)
Lemma fsetU1in (T : ordType) (x : T) (s : {fset T}) :
  x \in s -> (x |: s)%fset = s.
Proof.
  rewrite -eq_fset.
  move => x_in_s x0.
  case: (@in_fsetU1 T x0 x s) => H0. 
  destruct (x0 \in s) eqn: Hx0.
     by rewrite H0 orbT. 
  rewrite H0 orbF.     
  destruct (eqtype.eq_op x0 x) eqn: Hx0_x; auto. 
    rewrite -(eqtype.eqP Hx0_x) in x_in_s.  
    now inversion x_in_s.
Qed.
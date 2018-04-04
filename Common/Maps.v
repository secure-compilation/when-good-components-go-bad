From CoqUtils Require Export ord fmap fset.
From mathcomp Require Export ssrbool.

Definition NMap T := {fmap nat -> T}.

Definition elementsm {A: Type} : NMap A -> list (nat * A) := @FMap.fmval nat_ordType A _.

(* RB: TODO: These lemmas, with their clean proofs, probably belong in CoqUtils. *)
Lemma mapm_unionm : forall (T T' : Type) (m1 m2 : NMap T) (f : T -> T'),
  mapm f (unionm m1 m2) = unionm (mapm f m1) (mapm f m2).
Proof.
Admitted.

Lemma domm_mapm : forall T T' (m : NMap T) (f : T -> T'),
  domm (mapm f m) = domm m.
Admitted.

Lemma mapm_some_in_domm : forall T (m : NMap T) k v,
  m k = Some v -> k \in domm m.
Admitted.

Lemma fdisjoint_filterm_full : forall (T T' : Type) (m1 : NMap T) (m2 : NMap T'),
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m2) m1 = m1.
Proof.
Admitted.

Lemma fdisjoint_filterm_empty : forall (T : Type) (m1 m2 : NMap T),
  domm m1 = domm m2 ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Proof.
Admitted.

Lemma fdisjoint_filterm_mapm_empty : forall (T T' : Type) (m : NMap T) (f : T -> T'),
  filterm (fun (k : nat) (_ : T') => k \notin domm m) (mapm f m) = emptym.
Proof.
Admitted.

Lemma unionm_emptym_r : forall (T : Type) (m : NMap T),
  unionm m emptym = m.
Proof.
Admitted.

Lemma fdisjoint_filterm_mapm_unionm: forall (T T' : Type) (m1 m2 : NMap T) (f : T -> T'),
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f (unionm m1 m2)) =
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f m1).
Proof.
  intros T T' m1 m2 f Hdisjoint.
  rewrite mapm_unionm.
  rewrite filterm_union.
  - rewrite <- (fdisjoint_filterm_full T T m1 m2 Hdisjoint).
    rewrite fdisjoint_filterm_mapm_empty.
    pose proof unionm_emptym_r.
    rewrite unionm_emptym_r.
    reflexivity.
  - rewrite! domm_mapm.
    assumption.
Qed.

Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ltb_0_Z_nat n : (0 <? Z.of_nat n)%Z = (0 <? n).
Proof.
  now destruct n.
Qed.

Lemma lt_Z_nat p n : (Z.pos p < Z.of_nat n)%Z <-> (Pos.to_nat p < n).
Proof.
  split; intros H.
  - apply Z2Nat.inj_lt in H.
    + rewrite Z2Nat.inj_pos in H.
      rewrite Nat2Z.id in H.
      assumption.
    + by apply Zle_0_pos.
    + by apply Zle_0_nat.
  - apply Nat2Z.inj_lt in H.
    rewrite positive_nat_Z in H.
    assumption.
Qed.

Lemma ltb_Z_nat p n : (Z.pos p <? Z.of_nat n)%Z = (Pos.to_nat p <? n).
Proof.
  destruct (Z.pos p <? Z.of_nat n)%Z eqn:H.
  - move: H => /Z.ltb_spec0 => H.
    apply lt_Z_nat in H.
    by move: H => /Nat.ltb_spec0.
  - move: H => /Z.ltb_spec0 => H.
    move: (iffLRn (lt_Z_nat _ _) H) => /Nat.ltb_spec0.
    intros H'. by apply negb_true_iff in H'.
Qed.


Lemma filterm_identity (T: ordType) (S: Type):
  forall (m: {fmap T -> S}),
    filterm (fun _ _ => true) m = m.
Proof.
  intros m.
  apply eq_fmap. intros k.
  rewrite filtermE.
  unfold obind, oapp.
  destruct (m k); auto.
Qed.

Lemma mapm_mkfmapf {S S': Type} {T: ordType} (fim : S -> S') (f : T -> S) d:
  mapm fim (mkfmapf f d) = mkfmapf (fim \o f) d.
Proof.
  rewrite <- eq_fmap.
  intros x. rewrite mapmE. unfold omap, obind, oapp.
  destruct (mkfmapf f d x) as [y|] eqn:e; rewrite mkfmapfE; rewrite mkfmapfE in e.
  - assert (H: x \in d).
    { by destruct (x \in d). }
    rewrite H. rewrite H in e. by inversion e.
  - assert (H: x \in d = false).
    { by destruct (x \in d). }
    rewrite H. rewrite H in e. by inversion e.
Qed.

Module Util.
  Module Z.
    Definition of_bool (b : bool) : Z :=
      if b then 1%Z else 0%Z.
  End Z.
End Util.

Section Domm.

Lemma notin_to_in_false : forall (Cid : Component.id) (iface : Program.interface),
  Cid \notin domm iface -> Cid \in domm iface = false.
Proof.
  intros Cid iface Hnotin.
  destruct (Cid \in domm iface) eqn:Heq;
    easy.
Qed.

End Domm.


Lemma cats2 {A} s (e1 e2 : A) :
  (s ++ [:: e1]) ++ [:: e2] = rcons (rcons s e1) e2.
Proof.
  do 2 rewrite cats1. reflexivity.
Qed.

Lemma cats2_inv {A} s s' (e1 e1' e2 e2' : A) :
  (s ++ [:: e1]) ++ [:: e2] = rcons (rcons s' e1') e2' ->
  s = s' /\ e1 = e1' /\ e2 = e2'.
Proof.
  intro H.
  rewrite cats2 in H.
  apply rcons_inj in H.
  injection H as H ?.
  apply rcons_inj in H.
  injection H as H ?.
  auto.
Qed.


Lemma mem_codomm_setm :
  forall (T S : ordType) (m : {fmap T -> S}) (k1 k2 : T) (v v' : S),
    m k1 = Some v ->
    v' \in codomm (setm m k2 v) ->
    v' \in codomm m.
Proof.
  intros T S m k1 k2 v v' Hmem Hmemcodomm.
  apply/codommP.
  pose (H' := @codommP _ _ (setm m k2 v) v' Hmemcodomm).
  destruct H' as [kOfv' H'mem].
  rewrite setmE in H'mem.
  destruct (kOfv' == k2) eqn:k2kOfv'.
  - eexists k1. rewrite <- H'mem. exact Hmem.
  - eexists kOfv'. exact H'mem.
Qed.

Lemma in_fsubset :
  forall (T : ordType) (s1 s2 : {fset T}),
    (forall v, v \in s1 -> v \in s2) -> fsubset s1 s2.
Proof.
  intros ? ? ? Hinin.
  apply/fsubsetP.
  unfold sub_mem.
  exact Hinin.
Qed.

Lemma fsubset_in :
  forall (T : ordType) (s1 s2 : {fset T}) v,
    fsubset s1 s2 -> v \in s1 -> v \in s2.
Proof.
  intros ? ? ? ? Hsubset Hin.
  pose (@fsubsetP _ s1 s2 Hsubset) as Hsubset'.
  unfold sub_mem in Hsubset'.
  apply Hsubset'.
  assumption.
Qed.

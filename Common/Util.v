Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Remark ltb_0_Z_nat n : (0 <? Z.of_nat n)%Z = (0 <? n).
Proof.
  now destruct n.
Qed.

Remark lt_Z_nat p n : (Z.pos p < Z.of_nat n)%Z <-> (Pos.to_nat p < n).
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

Remark ltb_Z_nat p n : (Z.pos p <? Z.of_nat n)%Z = (Pos.to_nat p <? n).
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

Remark notin_to_in_false : forall (Cid : Component.id) (iface : Program.interface),
  Cid \notin domm iface -> Cid \in domm iface = false.
Proof.
  intros Cid iface Hnotin.
  destruct (Cid \in domm iface) eqn:Heq;
    easy.
Qed.

End Domm.

Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Require Import Common.Definitions.

Module Util.
  Module Nat.
    Fixpoint safe_sub (n1 n2 : nat) : option nat :=
      match n1, n2 with
      | 0    , 0     => Some 0
      | 0    , S _   => None (* underflow *)
      | S _  , 0     => Some n1
      | S n1', S n2' => safe_sub n1' n2'
      end.

    Definition of_bool (b : bool) : nat :=
      if b then 1 else 0.
  End Nat.

  Module Z.
    Definition of_bool (b : bool) : Z :=
      if b then 1 else 0.
  End Z.

  Module Lists.
    Fixpoint update {A : Type} (l : list A) (n : nat) (val : A) {struct l} : list A :=
      match l with
      | [] => []
      | x :: xs => match n with
                   | 0 => val :: xs
                   | S n' => x :: update xs n' val
                   end
      end.

    Fixpoint mem x xs :=
      match xs with
      | [] => false
      | x' :: xs' => if (x =? x')%Z then true else mem x xs'
      end.

    Lemma not_in_iff_mem_false :
      forall x xs,
        ~ (In x xs) <-> mem x xs = false.
    Proof.
      intros. split.
      - intro Hxs. induction xs.
        + auto.
        + simpl.
          apply not_in_cons in Hxs. destruct Hxs.
          unfold not in H.
          destruct (x =? a)%Z eqn:Heq_xa.
          * exfalso. apply Z.eqb_eq in Heq_xa.
            apply H. apply Heq_xa.
          * apply IHxs. apply H0.
      - intro Hxs. induction xs.
        + auto.
        + destruct (x =? a)%Z eqn:Heq_xa.
          * apply not_in_cons.
            split;
              unfold mem in Hxs; rewrite Heq_xa in Hxs;
                discriminate Hxs.
          * apply not_in_cons. split.
            ** intro Heq_xa_true.
               rewrite Heq_xa_true in Heq_xa. simpl in Heq_xa.
               apply Z.eqb_neq in Heq_xa. auto.
            ** apply IHxs.
               unfold mem in Hxs. rewrite Heq_xa in Hxs.
               auto.
    Qed.

    Lemma in_iff_mem_true :
      forall x xs,
        In x xs <-> mem x xs = true.
    Proof.
      intros. split.
      - intro Hxs.
        induction xs.
        + auto.
        + simpl.
          destruct (x =? a)%Z eqn:Heq_xa.
          * reflexivity.
          * apply IHxs. apply in_inv in Hxs. destruct Hxs.
            ** exfalso. rewrite Z.eqb_neq in Heq_xa.
               apply Heq_xa. symmetry. auto.
            ** auto.
      - intro Hxs.
        induction xs.
        + discriminate Hxs.
        + simpl.
          destruct (x =? a)%Z eqn:Heq_xa.
          * left. symmetry. apply Z.eqb_eq in Heq_xa. auto.
          * right. apply IHxs.
            unfold mem in Hxs.
            rewrite Heq_xa in Hxs. auto.
    Qed.
  End Lists.
End Util.
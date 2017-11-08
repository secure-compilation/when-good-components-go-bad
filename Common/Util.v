Require Import Common.Definitions.

Module Util.
  Module Z.
    Definition of_bool (b : bool) : Z :=
      if b then 1 else 0.
  End Z.

  Module Lists.
    Fixpoint update {A : Type} (l : list A) (n : nat) (val : A) {struct l} : list A :=
      match l with
      | [] => []
      | x :: xs => match n with
                  | O => val :: xs
                  | S n' => x :: update xs n' val
                  end
      end.

    Fixpoint mem x xs :=
      match xs with
      | [] => false
      | x' :: xs' => if Pos.eqb x x' then true else mem x xs'
      end.

    Lemma in_iff_mem_true :
      forall x xs,
        In x xs <-> mem x xs = true.
    Proof.
      intros x xs. induction xs as [|x' xs IH]; simpl; try easy.
      rewrite IH, Pos.eqb_sym.
      now destruct (Pos.eqb_spec x' x) as [E|NE]; tauto.
    Qed.

    Lemma not_in_iff_mem_false :
      forall x xs,
        ~ (In x xs) <-> mem x xs = false.
    Proof.
      intros x xs.
      now rewrite in_iff_mem_true, not_true_iff_false.
    Qed.

  End Lists.
End Util.

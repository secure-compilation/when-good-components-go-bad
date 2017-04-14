Require Export List.
Require Export Bool.
Require Export Arith.

Export ListNotations.
Open Scope list_scope.

Definition admit {T: Type} : T. Admitted.

Module Procedure.

Definition id := nat.

End Procedure.

Module Component.

Definition id := nat.

Record interface := mkCompInterface {
  name : id;
  export : nat;
  import : list (id * Procedure.id)
}.

End Component.

Module Program.

Definition interface := list Component.interface.

End Program.

Module Util.

Fixpoint mem x xs :=
  match xs with
  | [] => false
  | x' :: xs' => if x =? x' then true else mem x xs'
  end.

Lemma not_in_implies_mem_false :
  forall x xs,
    ~ (In x xs) -> mem x xs = false.
Proof.
  intros.
  induction xs.
  - reflexivity.
  - simpl.
    apply not_in_cons in H. destruct H.
    unfold not in H.
    destruct (x =? a) eqn:Heq_xa.
    + exfalso. apply beq_nat_true in Heq_xa.
      apply H. apply Heq_xa.
    + apply IHxs. apply H0.
Qed.

Lemma in_implies_mem_true :
  forall x xs,
    In x xs -> mem x xs = true.
Proof.
  intros.
  induction xs.
  - exfalso. apply (in_nil H).
  - simpl.
    destruct (x =? a) eqn:Heq_xa.
    + reflexivity.
    + apply IHxs. apply in_inv in H. destruct H.
      * exfalso. rewrite beq_nat_false_iff in Heq_xa.
        apply Heq_xa. symmetry. apply H.
      * apply H.
Qed.

End Util.
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
      destruct (x =? a) eqn:Heq_xa.
      * exfalso. apply beq_nat_true in Heq_xa.
        apply H. apply Heq_xa.
      * apply IHxs. apply H0.
  - intro Hxs. induction xs.
    + auto.
    + destruct (x =? a) eqn:Heq_xa.
      * apply not_in_cons.
        split;
          unfold mem in Hxs; rewrite Heq_xa in Hxs;
          discriminate Hxs.
      * apply not_in_cons. split.
        ** intro Heq_xa_true.
           rewrite Heq_xa_true in Heq_xa. simpl in Heq_xa.
           apply beq_nat_false in Heq_xa. auto.
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
      destruct (x =? a) eqn:Heq_xa.
      * reflexivity.
      * apply IHxs. apply in_inv in Hxs. destruct Hxs.
        ** exfalso. rewrite beq_nat_false_iff in Heq_xa.
           apply Heq_xa. symmetry. auto.
        ** auto.
  - intro Hxs.
    induction xs.
    + discriminate Hxs.
    + simpl.
      destruct (x =? a) eqn:Heq_xa.
      * left. symmetry. apply beq_nat_true in Heq_xa. auto.
      * right. apply IHxs.
        unfold mem in Hxs.
        rewrite Heq_xa in Hxs. auto.
Qed.

End Util.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.Reachability.
Require Import Common.CompCertExtensions.

Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrnat eqtype path ssrfun seq fingraph fintype.

Set Bullet Behavior "Strict Subproofs".

(* RB: NOTE: [DynShare] Later in the development the name "address" can become
   confusing when offsets come into the picture. We should explain this model
   carefully, and maybe find an alternative name if the confusion persists. *)

Section ShiftingBlockIdsAsPartialBijection.
  (* The following is a definition of a so-called "partial bijection", namely
     the bijection between the set [count_blocks_to_shift_per_comp, inf) and the set N
     of all the natural numbers.
     However, I am defining this bijection
     (between [count_blocks_to_shift_per_comp, inf) and N)
     as a total bijection between
     {care, dontcare} x N and {care, dontcare} x N.
     Totalizing it enables us to reuse useful results about total bijections.
   *)
  (* RB: NOTE: [DynShare] We should give a type declaration for this pair, either
     as a definition or as a variant that clarifies the intent of the
     pseudo-boolean. *)

  (* Variable cid_with_shifting : Component.id. *)
  Variable count_blocks_to_shift_for_cid : nat.

  Definition care := true.
  Definition dontcare := false.

  (** Obtain a new map as follows:
      - Ignore blocks outside the component of interest.
      - "Uninteresting" blocks are incremented by the set threshold.
      - "Interesting" blocks below the threshold are left unchanged (and
        declared uninteresting).
      - "Interesting" blocks at the threshold and above are decremented by the
        threshold. *)

  Definition sigma_from_bigger_dom (x: bool * Block.id) : bool * Block.id :=
    match x with
    | (c, bid) =>
      if c =? care then
        if bid <? count_blocks_to_shift_for_cid
        then (dontcare, bid)
        else (care, bid - count_blocks_to_shift_for_cid)
      else (dontcare, bid + count_blocks_to_shift_for_cid)
    end.

  (** Reverse previous changes. *)

  Definition inv_sigma_from_bigger_dom (x: bool * Block.id) : bool * Block.id :=
    match x with
    | (c, bid) =>
      if c =? care then
        (care, bid + count_blocks_to_shift_for_cid)
      else if bid <? count_blocks_to_shift_for_cid
           then (care, bid)
           else (dontcare, bid - count_blocks_to_shift_for_cid)
    end.

  Lemma cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom :
    cancel sigma_from_bigger_dom inv_sigma_from_bigger_dom.
  Proof.
    unfold cancel. intros [c bid]. simpl.
    - destruct c; simpl.
      + destruct (bid <? count_blocks_to_shift_for_cid) eqn:bid_lt; simpl.
        * rewrite bid_lt. reflexivity.
        * rewrite subnK; try reflexivity.
          assert (le count_blocks_to_shift_for_cid bid) as Hle.
          { rewrite <- Nat.ltb_ge. assumption. }
          apply/leP. assumption.
      + pose proof (leq_addl bid count_blocks_to_shift_for_cid) as H.
        destruct (bid + count_blocks_to_shift_for_cid <? count_blocks_to_shift_for_cid)
                 eqn:bid_plus_lt; simpl.
        * pose proof Nat.ltb_lt (addn bid count_blocks_to_shift_for_cid)
               (count_blocks_to_shift_for_cid) as [Hif _].
          rewrite bid_plus_lt in Hif. pose proof (Hif Logic.eq_refl) as Hlt. clear Hif.
          assert (leq (S (addn bid count_blocks_to_shift_for_cid))
                      count_blocks_to_shift_for_cid) as Hleq.
          { apply/ltP. assumption. }
          pose proof (leqP count_blocks_to_shift_for_cid
                           (addn bid count_blocks_to_shift_for_cid)) as Hcontra.
          rewrite H in Hcontra. rewrite Hleq in Hcontra.
          inversion Hcontra.
        * rewrite addnK. reflexivity.
  Qed.

  Lemma cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom :
    cancel inv_sigma_from_bigger_dom sigma_from_bigger_dom.
  Proof.
    unfold cancel. intros [c bid]. simpl.
    destruct c; simpl.
    - pose proof leq_addl bid count_blocks_to_shift_for_cid.
      assert (bid + count_blocks_to_shift_for_cid <? count_blocks_to_shift_for_cid = false)
        as Hfalse.
      { rewrite Nat.ltb_ge. apply/leP. assumption. }
      rewrite Hfalse addnK. reflexivity.
    - destruct (bid <? count_blocks_to_shift_for_cid) eqn:HNatlt;
        unfold sigma_from_bigger_dom; simpl.
      + rewrite HNatlt. reflexivity.
      + rewrite subnK; try reflexivity.
        apply/leP. rewrite <- Nat.ltb_ge. assumption.
  Qed.

  Lemma sigma_from_bigger_dom_bijective : bijective sigma_from_bigger_dom.
  Proof. apply Bijective with (g := inv_sigma_from_bigger_dom).
         - exact cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom.
         - exact cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom.
  Qed.

  Lemma inv_sigma_from_bigger_dom_bijective : bijective inv_sigma_from_bigger_dom.
  Proof. apply Bijective with (g := sigma_from_bigger_dom).
         - exact cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom.
         - exact cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom.
  Qed.

End ShiftingBlockIdsAsPartialBijection.

Section SigmaShiftingBlockIds.

  (** Shift renaming on a given component with given numbers of additional
      metadata blocks on both sides. *)

  (* Variable cid_with_shifting: Component.id. *)
  Variable metadata_size_lhs: nat.
  Variable metadata_size_rhs: nat.

  (** The LHS has a given number of extra blocks (attention, this number can be
      negative). *)

  Let num_extra_blocks_of_lhs : Z :=
    Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs.

  (** To shift an address map, apply the direct mapping if the LHS requires as
      much or more metadata, otherwise apply the inverse mapping (and vice
      versa). *)

  Definition sigma_shifting : bool * Block.id -> bool * Block.id :=
    if (num_extra_blocks_of_lhs >=? 0)%Z
    then (sigma_from_bigger_dom (Z.to_nat num_extra_blocks_of_lhs))
    else (inv_sigma_from_bigger_dom (Z.to_nat (- num_extra_blocks_of_lhs))).

  Definition inv_sigma_shifting : bool * Block.id -> bool * Block.id :=
    if (num_extra_blocks_of_lhs >=? 0)%Z
    then (inv_sigma_from_bigger_dom (Z.to_nat num_extra_blocks_of_lhs))
    else (sigma_from_bigger_dom (Z.to_nat (- num_extra_blocks_of_lhs))).

  Lemma cancel_sigma_shifting_inv_sigma_shifting:
    cancel sigma_shifting inv_sigma_shifting.
  Proof.
    unfold sigma_shifting, inv_sigma_shifting.
    destruct (num_extra_blocks_of_lhs >=? 0)%Z.
    - apply cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom.
    - apply cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom.
  Qed.

  Lemma cancel_inv_sigma_shifting_sigma_shifting:
    cancel inv_sigma_shifting sigma_shifting.
  Proof.
    unfold sigma_shifting, inv_sigma_shifting.
    destruct (num_extra_blocks_of_lhs >=? 0)%Z.
    - apply cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom.
    - apply cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom.
  Qed.

  Lemma sigma_shifting_bijective : bijective sigma_shifting.
  Proof. apply Bijective with (g := inv_sigma_shifting).
         - exact cancel_sigma_shifting_inv_sigma_shifting.
         - exact cancel_inv_sigma_shifting_sigma_shifting.
  Qed.

  Lemma inv_sigma_shifting_bijective : bijective inv_sigma_shifting.
  Proof. apply Bijective with (g := sigma_shifting).
         - exact cancel_inv_sigma_shifting_sigma_shifting.
         - exact cancel_sigma_shifting_inv_sigma_shifting.
  Qed.

  (** A block id can be shifted iff it is above the size of the metadata 
      in the corresponding side. *)

  Definition left_block_id_good_for_shifting (bid: Block.id) : Prop :=
    bid >= metadata_size_lhs.

  Definition right_block_id_good_for_shifting (bid: Block.id) : Prop :=
    bid >= metadata_size_rhs.
  
  Lemma sigma_left_good_right_good lbid:
    left_block_id_good_for_shifting lbid ->
    exists rbid,
      sigma_shifting (care, lbid) = (care, rbid) /\
      right_block_id_good_for_shifting rbid.
  Proof.
    unfold left_block_id_good_for_shifting,
    sigma_shifting, right_block_id_good_for_shifting.
    intros Hleft_good.
    unfold num_extra_blocks_of_lhs in *.
    destruct (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs >=? 0)%Z eqn:Hge0;
    simpl in *.
    - eexists.
      assert (metadata_size_rhs <= metadata_size_lhs)%coq_nat as lhs_rhs.
      { rewrite Nat2Z.inj_le. apply Zle_0_minus_le. rewrite <- Z.geb_le. exact Hge0. }
      assert (Z.to_nat (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs) =
              (metadata_size_lhs - metadata_size_rhs)%coq_nat) as simplify_minus.
      {
        rewrite <- Nat2Z.inj_sub.
        + rewrite Nat2Z.id. reflexivity.
        + exact lhs_rhs.
      }
      assert (lbid <? Z.to_nat (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs)
              = false) as Hcond.
      {
        rewrite Nat.ltb_ge. apply/leP. rewrite simplify_minus.
        apply leq_trans with (n := metadata_size_lhs).
        + apply leq_subr.
        + exact Hleft_good.
      }
      rewrite !Hcond. rewrite simplify_minus in Hcond.
      assert ((metadata_size_lhs - metadata_size_rhs) <= lbid)%coq_nat as Hall.
      { rewrite <- Nat.ltb_ge. exact Hcond. }
      assert (metadata_size_rhs <= lbid) as rhs_lbid.
      { apply leq_trans with (n := metadata_size_lhs); auto. apply/leP. auto. }
      split.
      + reflexivity.
      + simpl. rewrite !simplify_minus. rewrite !minusE.
        destruct (metadata_size_lhs == lbid) eqn:Heq.
        * assert (metadata_size_lhs = lbid) as Heq'.
          { apply/eqP. rewrite Heq. auto. }
          rewrite Heq'. rewrite <- minnE.
          assert (minn lbid metadata_size_rhs = metadata_size_rhs) as Hrhs.
          { apply/minn_idPr. assumption. }
          rewrite Hrhs. auto.
        * apply ltnW. rewrite ltn_subRL. rewrite subnK.
          -- rewrite leq_eqVlt in Hleft_good.
             pose proof orP Hleft_good as H. destruct H.
             ++ rewrite H in Heq. discriminate.
             ++ assumption.
          -- apply/leP. assumption.
    - eexists.
      split; try reflexivity. simpl.
      assert (Z.of_nat metadata_size_lhs <= Z.of_nat metadata_size_rhs)%Z as lhs_rhs.
      {
        rewrite <- Z.le_sub_0. apply Znot_gt_le. rewrite neg_false.
        split; try (intros; exfalso; auto).
        rewrite Z.geb_leb in Hge0. apply Z.leb_gt in Hge0.
        unfold Z.lt, Z.gt in *. rewrite H in Hge0. discriminate.
      }
      assert (metadata_size_lhs <= metadata_size_rhs) as lhs_rhs'.
      { apply/leP. rewrite Nat2Z.inj_le. exact lhs_rhs. }
      rewrite Z.opp_sub_distr Z.add_opp_l Z2Nat.inj_sub; try apply Nat2Z.is_nonneg.
      rewrite !Nat2Z.id addnC. rewrite <- leq_subLR. rewrite subKn; assumption.
  Qed.

  Lemma inv_sigma_right_good_left_good rbid:
    right_block_id_good_for_shifting rbid ->
    exists lbid,
      inv_sigma_shifting (care, rbid) = (care, lbid) /\
      left_block_id_good_for_shifting lbid.
  Proof.
    unfold right_block_id_good_for_shifting,
    inv_sigma_shifting, left_block_id_good_for_shifting.
    intros Hright_good.
    unfold num_extra_blocks_of_lhs.
    destruct (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs >=? 0)%Z eqn:Hge0;
      simpl in *.
    - eexists.
      assert (metadata_size_rhs <= metadata_size_lhs)%coq_nat as lhs_rhs.
      { rewrite Nat2Z.inj_le. apply Zle_0_minus_le. rewrite <- Z.geb_le. exact Hge0. }
      assert (Z.to_nat (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs) =
              (metadata_size_lhs - metadata_size_rhs)%coq_nat) as simplify_minus.
      {
        rewrite <- Nat2Z.inj_sub.
        + rewrite Nat2Z.id. reflexivity.
        + exact lhs_rhs.
      }
      split; eauto. simpl. rewrite simplify_minus addnC. rewrite <- leq_subLR.
      rewrite subKn; auto. apply/leP. auto.
    - assert (Z.of_nat metadata_size_lhs <= Z.of_nat metadata_size_rhs)%Z as lhs_rhs.
      {
        rewrite <- Z.le_sub_0. apply Znot_gt_le. rewrite neg_false.
        split; try (intros; exfalso; auto).
        rewrite Z.geb_leb in Hge0. apply Z.leb_gt in Hge0.
        unfold Z.lt, Z.gt in *. rewrite H in Hge0. discriminate.
      }
      assert (metadata_size_lhs <= metadata_size_rhs) as lhs_rhs'.
      { apply/leP. rewrite Nat2Z.inj_le. exact lhs_rhs. }
      eexists. simpl.
      assert (Z.to_nat (- (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs)) =
              metadata_size_rhs - metadata_size_lhs) as simplify_minus.
      {
        rewrite Z.opp_sub_distr Z.add_opp_l. rewrite <- Nat2Z.inj_sub.
        + rewrite Nat2Z.id minusE. reflexivity.
        + apply/leP. exact lhs_rhs'.
      }
      rewrite simplify_minus.
      assert (rbid <? metadata_size_rhs - metadata_size_lhs = false) as Hnecessary.
      {
        rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := metadata_size_rhs); auto.
        apply leq_subr.
      }
      rewrite Hnecessary. split; eauto. simpl.
      destruct (rbid == metadata_size_rhs) eqn:Heq.
      + assert (rbid = metadata_size_rhs) as Heq'.
        { apply/eqP. auto. }
        rewrite Heq'. rewrite <- minnE.
        assert (minn metadata_size_rhs metadata_size_lhs = metadata_size_lhs) as Hminn.
        { apply/minn_idPr. auto. }
        rewrite Hminn. auto.
      + apply ltnW. rewrite ltn_subRL. rewrite subnK.
        * rewrite leq_eqVlt in Hright_good.
          pose proof orP Hright_good as H. destruct H.
          -- rewrite eq_sym H in Heq. discriminate.
          -- assumption.
        * assumption.
  Qed.

End SigmaShiftingBlockIds.

Section SigmaShiftingBlockIdsProperties.

  Lemma sigma_from_bigger_dom_0_id x: sigma_from_bigger_dom 0 x = x.
  Proof. destruct x as [c bid]. unfold sigma_from_bigger_dom.
         assert (bid <? 0 = false) as Himposs.
         { rewrite Nat.ltb_ge. apply Nat.le_0_l. }
         rewrite Himposs. rewrite subn0 addn0.
         destruct c; simpl; reflexivity.
  Qed.

  Lemma inv_sigma_from_bigger_dom_0_id x: inv_sigma_from_bigger_dom 0 x = x.
  Proof. destruct x as [c bid]. unfold inv_sigma_from_bigger_dom.
         assert (bid <? 0 = false) as Himposs.
         { rewrite Nat.ltb_ge. apply Nat.le_0_l. }
         rewrite Himposs. rewrite subn0 addn0.
         destruct c; simpl; reflexivity.
  Qed.

  Lemma sigma_shifting_n_n_id:
    forall n x, sigma_shifting n n x = x.
  Proof.
    intros n x. unfold sigma_shifting.
    rewrite <- !Zminus_diag_reverse. simpl. apply sigma_from_bigger_dom_0_id.
  Qed.

  Lemma inv_sigma_shifting_n_n_id:
    forall n x, inv_sigma_shifting n n x = x.
  Proof.
    intros n x. unfold inv_sigma_shifting.
    rewrite <- !Zminus_diag_reverse. simpl. apply inv_sigma_from_bigger_dom_0_id.
  Qed.

  Lemma inv_sigma_shifting_sigma_shifting:
    forall n1 n2 x,
      inv_sigma_shifting n1 n2 x = sigma_shifting n2 n1 x.
  Proof.
    intros n1 n2 [cdc bid].
    unfold inv_sigma_shifting, sigma_shifting.
    destruct (Z.of_nat n1 - Z.of_nat n2 >=? 0)%Z eqn:Hminus;
      destruct (Z.of_nat n2 - Z.of_nat n1 >=? 0)%Z eqn:Hinv_minus.
    - assert (n1 = n2) as n1n2.
      { apply Nat2Z.inj, Z.le_antisymm; apply Zle_0_minus_le; apply Z.geb_le; auto. }
      subst. rewrite Z.sub_diag.
      rewrite sigma_from_bigger_dom_0_id inv_sigma_from_bigger_dom_0_id. auto.
    - rewrite Z.opp_sub_distr Z.add_opp_l. reflexivity.
    - rewrite Z.opp_sub_distr Z.add_opp_l. reflexivity.
    - pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as Hminus'. rewrite Hminus in Hminus'.
      pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n1) 0 as Hinv'. rewrite Hinv_minus in Hinv'.
      assert (Z.of_nat n1 < Z.of_nat n2)%Z as n1n2.
      { apply Z.lt_sub_0. assumption. }
      assert (Z.of_nat n2 < Z.of_nat n1)%Z as n2n1.
      { apply Z.lt_sub_0. assumption. }
      apply Z.lt_le_incl, Zle_not_lt in n1n2.
      pose proof @absurd (Z.lt (Z.of_nat n2) (Z.of_nat n1)) False n2n1 n1n2. exfalso. auto.
  Qed.

  Lemma sigma_shifting_transitive n1 n2 n3 bid:
    left_block_id_good_for_shifting n1 bid ->
    sigma_shifting n2 n3
                   (care, (sigma_shifting n1 n2 (care, bid)).2) =
    sigma_shifting n1 n3 (care, bid).
  Proof.
    intros lgood_bid.
    destruct (sigma_left_good_right_good n1 n2 bid lgood_bid)
      as [bid' [Ha'1 Ha'2]].
    assert (left_block_id_good_for_shifting n2 bid') as lgood_a'.
    { unfold left_block_id_good_for_shifting.
      unfold right_block_id_good_for_shifting in Ha'2. auto. }
    simpl in *.
    rewrite Ha'1. simpl in *.
    unfold sigma_shifting in *.
    destruct (Z.of_nat n2 - Z.of_nat n3 >=? 0)%Z eqn:n2n3;
      destruct (Z.of_nat n1 - Z.of_nat n2 >=? 0)%Z eqn:n1n2;
      destruct (Z.of_nat n1 - Z.of_nat n3 >=? 0)%Z eqn:n1n3.
    - (* n1 >= n2, n2 >= n3, thus n1 >= n3  *)
      move: Ha'1.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption).
      rewrite !Nat2Z.id.
      move=> Ha'1. (*rewrite Ha'1.*)
      unfold sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      assert (bid' <? (n2 - n3)%coq_nat = false) as Hcond.
      { rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := n2); auto. apply leq_subr. }
      rewrite Hcond.
      assert (bid <? (n1 - n3)%coq_nat = false) as Hcond'.
      { rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := n1); auto. apply leq_subr. }
      rewrite Hcond'.
      assert (bid <? (n1 - n2)%coq_nat = false) as Hcond''.
      { rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := n1); auto. apply leq_subr. }
      rewrite Hcond'' in Ha'1.
      inversion Ha'1. subst.
      rewrite <- subnDA.
      rewrite addnBA.
      + rewrite subnK;
          try (apply /leP; rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le); auto.
      + apply /leP. rewrite Nat2Z.inj_le. apply Zle_0_minus_le, Z.geb_le; assumption.
    - assert ((Z.of_nat n1 - Z.of_nat n3 >=? 0)%Z = true) as Hcontra.
      {
        rewrite Z.geb_le. rewrite Z.le_0_sub.
        apply Z.le_trans with (m := Z.of_nat n2);
          rewrite <- Z.le_0_sub; rewrite <- Z.geb_le; assumption.
      }
      rewrite Hcontra in n1n3. discriminate.
    - (* n1 >= n3, n2 >= n3, n1 ~>= n2, i.e., n2 > n1 *)
      assert (n1n2': n1 <= n2).
      { apply/leP.
        rewrite Nat2Z.inj_le; apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as G. rewrite n1n2 in G.
        apply Z.lt_sub_0. assumption.
      }
      assert (n1n3': n3 <= n1).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n3) 0 as G. rewrite n1n3 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      assert (n2n3': n3 <= n2).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le.
        pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n3) 0 as G. rewrite n2n3 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      move: Ha'1.
      rewrite !Z.opp_sub_distr !Z.add_opp_l.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption);
        try (apply/leP; auto).
      rewrite !Nat2Z.id.
      move=> Ha'1. (*rewrite Ha'1.*)
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      inversion Ha'1. subst.
      destruct (bid + (n2 - n1)%coq_nat <? (n2 - n3)%coq_nat) eqn:Hif.
      + (* Here, contradiction *)
        assert ((n2 - n3)%coq_nat <= n2) as Hfact.
        { apply leq_subr. }
        assert (n2 < (n2 - n3)%coq_nat) as Hcontra.
        {
          apply/ltP.
          apply Nat.le_lt_trans with (m := bid + (n2 - n1)%coq_nat).
          * apply/leP. assumption.
          * apply/Nat.ltb_spec0. assumption.
        }
        assert (n2 < n2) as Hfalse.
        { apply/ltP. apply Nat.lt_le_trans with (m := (n2 - n3)%coq_nat);
                       try apply/leP; assumption. }
        pose proof Nat.lt_irrefl n2 as H. pose proof @ltP _ _ Hfalse as H1.
        exfalso. apply H. exact H1.
      + destruct (bid <? (n1 - n3)%coq_nat) eqn:Hif'.
        * (* Here, contradiction*)
          assert ((n1 - n3)%coq_nat <= n1) as Hfact.
          { apply leq_subr. }
          assert (n1 < (n1 - n3)%coq_nat) as Hcontra.
          {
            apply/ltP.
            apply Nat.le_lt_trans with (m := bid).
            -- apply/leP. assumption.
            -- apply/Nat.ltb_spec0. assumption.
          }
          assert (n1 < n1) as Hfalse.
          { apply/ltP. apply Nat.lt_le_trans with (m := (n1 - n3)%coq_nat);
                         try apply/leP; assumption. }
          pose proof Nat.lt_irrefl n1 as H. pose proof @ltP _ _ Hfalse as H1.
          exfalso. apply H. exact H1.
        * rewrite <- subnBA; try (apply leq_sub2l; assumption).
          assert ((n2 - n3)%coq_nat - (n2 - n1) = (n2 - n3) + n1 - n2) as Hdist.
          { rewrite subnBA; auto. }
          rewrite Hdist.
          assert ((n2 - n3 + n1 - n2) = n1 - n3) as Hgoal.
          { rewrite <- subnBA; auto. rewrite <- subnDA. rewrite addnC subnDA.
            rewrite <- minnE.
            assert (minn n2 n1 = n1) as Hmin.
            { apply/minn_idPr. auto. }
            rewrite Hmin. reflexivity.
          }
          rewrite Hgoal. reflexivity.
    - (* n2 >= n3, n1 ~>= n3 ==> n1 < n3, n1 ~>= n2 ==> n1 < n2 *)
      assert (n2n3': n3 <= n2).
      { apply/leP.
        rewrite Nat2Z.inj_le; apply Z.geb_le. rewrite Z.geb_le.
        pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n3) 0 as G. rewrite n2n3 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      assert (n1n3': n1 <= n3).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n3) 0 as G. rewrite n1n3 in G.
        apply Z.lt_sub_0. assumption.
      }
      assert (n1n2': n1 <= n2).
      { apply leq_trans with (n := n3); assumption. }
      move: Ha'1.
      rewrite !Z.opp_sub_distr !Z.add_opp_l.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption);
        try (apply/leP; auto).
      rewrite !Nat2Z.id.
      move=> Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      inversion Ha'1. subst.
      assert (Hnecessary: bid + (n2 - n1) <? (n2 - n3) = false).
      { rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := n1 + (n2 - n1)).
        + rewrite <- maxnE.
          assert (Hmax: maxn n1 n2 = n2).
          { apply/maxn_idPr. assumption. }
          rewrite Hmax. apply leq_subr.
        + rewrite leq_add2r. assumption.
      }
      rewrite Hnecessary.
      assert (Hgoal: bid + (n2 - n1) - (n2 - n3) = bid + (n3 - n1)).
      {
        rewrite subnBA; auto. rewrite <- (addnA bid (n2 - n1)).
        rewrite <- addnBA.
        + assert (G: n2 - n1 + n3 - n2 = n3 - n1).
          { rewrite <- subnBA; auto. rewrite <- subnDA. rewrite addnC subnDA.
            rewrite <- minnE.
            assert (minn n2 n3 = n3) as Hmin.
            { apply/minn_idPr. auto. }
            rewrite Hmin. reflexivity.
          }
          rewrite G. reflexivity.
        + rewrite <- leq_subLR. rewrite <- minnE.
          assert (Hmin: minn n2 n1 = n1).
          { apply/minn_idPr. auto. }
          rewrite Hmin. auto.
      }
      rewrite Hgoal. reflexivity.
    - (* n1 >= n2, n1 >= n3, n2 ~>= n3 ==> n3 >= n2 *)
      assert (n1n2': n2 <= n1).
      { apply/leP.
        rewrite Nat2Z.inj_le; apply Z.geb_le. rewrite Z.geb_le.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as G. rewrite n1n2 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      assert (n1n3': n3 <= n1).
      { apply/leP.
        rewrite Nat2Z.inj_le; apply Z.geb_le. rewrite Z.geb_le.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n3) 0 as G. rewrite n1n3 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      assert (n2n3': n2 <= n3).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n3) 0 as G. rewrite n2n3 in G.
        apply Z.lt_sub_0. assumption.
      }
      move: Ha'1.
      rewrite !Z.opp_sub_distr !Z.add_opp_l.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption);
        try (apply/leP; auto).
      rewrite !Nat2Z.id.
      move=> Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      destruct (bid <? (n1 - n2)%coq_nat) eqn:Hif; inversion Ha'1. subst.
      assert (Hnecessary: bid <? (n1 - n3) = false).
      { rewrite Nat.ltb_ge. apply/leP. apply leq_trans with n1; auto. apply leq_subr. }
      rewrite Hnecessary.
      assert (Hbid: n2 <= bid + n2 - n1).
      { rewrite <- subnBA; auto. }
      assert (Hgoal: bid - (n1 - n2) + (n3 - n2) = bid - (n1 - n3)).
      {
        rewrite !subnBA; auto. rewrite addnBA; auto.
        rewrite <- (@subnBA bid n1); auto.
        rewrite <- addnBA; auto. rewrite subnBA; auto.
        rewrite addnBA; auto. rewrite addnC. rewrite <- addnBA; auto.
        rewrite <- (@subnBA bid n1); auto.
        rewrite <- subnDA. rewrite subnK; auto. rewrite addnC.
        rewrite (addnC bid). rewrite <- addnBA; auto. rewrite addnC. reflexivity.
      }
      rewrite Hgoal. reflexivity.
    - (* n2 <= n1, n2 !>= n3 ==> n2 <= n3, n1 !>= n3 ==> n1 <= n3 *)
      assert (n1n2': n2 <= n1).
      { apply/leP.
        rewrite Nat2Z.inj_le; apply Z.geb_le. rewrite Z.geb_le. 
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as G. rewrite n1n2 in G.
        apply Zle_0_minus_le, Z.ge_le. assumption.
      }
      assert (n1n3': n1 <= n3).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n3) 0 as G. rewrite n1n3 in G.
        apply Z.lt_sub_0. assumption.
      }
      assert (n2n3': n2 <= n3).
      { apply leq_trans with n1; auto. }
      move: Ha'1.
      rewrite !Z.opp_sub_distr !Z.add_opp_l.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption);
        try (apply/leP; auto).
      rewrite !Nat2Z.id.
      move=> Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      destruct (bid <? (n1 - n2)%coq_nat) eqn:Hif; inversion Ha'1. subst.
      assert (Hbid: n2 <= bid + n2 - n1).
      { rewrite <- subnBA; auto. }
      assert (Hgoal: bid - (n1 - n2) + (n3 - n2) = bid + (n3 - n1)).
      { rewrite addnBA; auto. rewrite addnC. rewrite <- addnBA; rewrite subnBA; auto.
        rewrite <- subnDA. rewrite addnBA; try (rewrite leq_add2r; auto).
        rewrite (addnC n1). rewrite subnDA. rewrite <- addnBA; try apply leq_addl.
        rewrite <- (@subnBA bid n2); auto. rewrite subnn subn0 addnC addnBA; auto.
      }
      rewrite Hgoal. reflexivity.
    - (* n1 !>= n2 ==> n1 < n2, n2 !>= n3 ==> n2 < n3, n1 >= n3 *)
      assert ((Z.of_nat n1 - Z.of_nat n3 >=? 0)%Z = false) as Hcontra.
      {
        rewrite Z.geb_leb Z.leb_gt Z.lt_sub_0.
        apply Z.lt_trans with (Z.of_nat n2); rewrite <- Z.lt_sub_0.
        + pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as H. rewrite n1n2 in H. auto.
        + pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n3) 0 as H. rewrite n2n3 in H. auto.
      }
      rewrite Hcontra in n1n3. discriminate.
    - (* n1 !>= n2 ==> n1 < n2, n2 !>= n3 ==> n2 < n3, n1 !>= n3 ==> n1 < n3 *)
      assert (n1n2': n1 <= n2).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n1 - Z.of_nat n2) 0 as G. rewrite n1n2 in G.
        apply Z.lt_sub_0. assumption.
      }
      assert (n2n3': n2 <= n3).
      { apply/leP.
        rewrite Nat2Z.inj_le. apply Z.geb_le. rewrite Z.geb_le. apply Z.lt_le_incl.
        pose proof Zge_cases (Z.of_nat n2 - Z.of_nat n3) 0 as G. rewrite n2n3 in G.
        apply Z.lt_sub_0. assumption.
      }
      assert (n1n3': n1 <= n3).
      { apply leq_trans with n2; auto. }
      move: Ha'1.
      rewrite !Z.opp_sub_distr !Z.add_opp_l.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption);
        try (apply/leP; auto).
      rewrite !Nat2Z.id.
      move=> Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      unfold left_block_id_good_for_shifting, right_block_id_good_for_shifting in *.
      inversion Ha'1. subst.
      assert (Hgoal: bid + (n2 - n1) + (n3 - n2) = bid + (n3 - n1)).
      { rewrite <- addnA. apply/eqP. rewrite eqn_add2l. apply/eqP. rewrite addnBA; auto.
        rewrite addnC. rewrite <- subnBA; try apply leq_subr. rewrite <- minnE.
        assert (Hmin: minn n2 n1 = n1).
        { apply/minn_idPr. auto. }
        rewrite Hmin. auto.
      }
      rewrite Hgoal. reflexivity.
  Qed.

  Lemma left_block_id_good_for_shifting_0_true bid:
    left_block_id_good_for_shifting 0 bid.
  Proof. unfold left_block_id_good_for_shifting. auto.
  Qed.


End SigmaShiftingBlockIdsProperties.


Definition addr_t : Type := (Component.id * Block.id).
(* It seems only Block.id will need to be renamed.
     However, to compute a renaming, we have to know which "component memory" we are
     considering. To know the component memory, we need the Component.id.
*)

Definition mem_of_event (e: event) : Memory.t :=
  match e with
  | ECall _ _ _ mem _ => mem
  | ERet _ _ mem _ => mem
  end.

Definition arg_of_event (e: event) : value :=
  match e with
  | ECall _ _ v _ _ => v
  | ERet _ v _ _ => v
  end.

(* RB: NOTE: [DynShare] Using a set instead of an option type for easier
   integration with reachability predicates later. *)
Definition addr_of_value (v: value) : {fset addr_t} :=
  match v with
  | Ptr (perm, cid, bid, _) =>
    if perm =? Permission.data then fset1 (cid, bid) else fset0
  | _ => fset0
  end.

(** Given a trace, an address is reachable iff it is shared through the argument
    of the last event in the trace, or transitively through some previously
    shared address. Reachability operates on the memory contained in the last
    event of the trace, which must subsume that in previous events.

    This reachability property is monotonic: once shared, an address is
    considered public forever.
 *)

(*
   An attempt to simplify the phrasing of the property might divide it into
   three cases:
    1. Reachable from initial memory (given a fixed component, say)
    2. Reachable from memory in current event in the trace
    3. Reachable from some future event in the trace

  This considers the POV of *shared* address sets, not *private* addresses.
  Using shared addresses, it is possible to add incrementally to the set,
  however with private addresses the set cannot be built recursively "on the
  left".

  Moreover, when thinking about private or "not shared" addresses, we cannot
  constrain these considerations to the current domain of the memory, as
  addresses beyond that range, i.e., not yet allocated, are also unshared.

  No need to refer to components explicitly. The current trace relation does
  not consider the POV of any particular component.

   - Which addresses remain private to each component?
   - Address states: already shared/still private
   - Once an address has been shared, it does not matter with whom (why?
     because we want per-component compositionality)
   - Why is it simpler? At the very least it avoids parameterizing the trace
     relation by an execution trace, i.e., only on a trace of addresses
 *)

Inductive addr_shared_so_far : addr_t -> trace event -> Prop :=
| reachable_from_args_is_shared:
    forall addr t e,
      Reachable (mem_of_event e) (addr_of_value (arg_of_event e)) addr ->
      addr_shared_so_far addr (rcons t e)
| reachable_from_previously_shared:
    forall addr addr' t e,
      addr_shared_so_far addr' t ->
      Reachable (mem_of_event e) (fset1 addr') addr ->
      addr_shared_so_far addr (rcons t e).

Lemma addr_shared_so_far_load_addr_shared_so_far addr t e offset cid_load bid_load o:
  addr_shared_so_far addr (rcons t e) ->
  Memory.load (mem_of_event e) (Permission.data, addr.1, addr.2, offset) =
  Some (Ptr (Permission.data, cid_load, bid_load, o)) ->
  addr_shared_so_far (cid_load, bid_load) (rcons t e).
Proof.
  intros Hshrsfr Hload.
  unfold Memory.load in Hload. simpl in Hload.
  destruct ((mem_of_event e) addr.1) eqn:Hmem; try discriminate.
  assert (HIn: (cid_load, bid_load) \in (ComponentMemory.load_block s addr.2)).
    by (rewrite In_in ComponentMemory.load_block_load; eexists; eauto).
  inversion Hshrsfr as [x y z Hreach l Heq | x addr' y z Hshrsfr' Hreach l Heq]. subst.
  - assert (tmp: rcons y z == rcons t e). by (apply/eqP). rewrite eqseq_rcons in tmp.
    destruct (andP tmp) as [tmp1 tmp2].
    assert (y = t). by (apply/eqP). assert (z = e). by (apply/eqP).
    subst. clear Heq tmp tmp1 tmp2.
    eapply reachable_from_args_is_shared; eauto.
    eapply Reachable_step; eauto. rewrite <- surjective_pairing. auto.
  - assert (tmp: rcons y z == rcons t e). by (apply/eqP). rewrite eqseq_rcons in tmp.
    destruct (andP tmp) as [tmp1 tmp2].
    assert (y = t). by (apply/eqP). assert (z = e). by (apply/eqP).
    subst. clear Heq tmp tmp1 tmp2.
    eapply reachable_from_previously_shared; eauto.
    eapply Reachable_transitive; eauto.
    eapply Reachable_step; eauto. rewrite <- surjective_pairing. eapply Reachable_refl.
    by rewrite in_fset1.
Qed.

Section PredicateOnReachableAddresses.

  (** Given a set of designated addresses, a memory is well-formed iff all
      successful pointer loads from designated addresses in that memory refer to
      addresses in the designated set. *)

  Variable good_addr: addr_t -> Prop.

  Definition good_memory (m: Memory.t) : Prop :=
    forall cid bid offset p cid_l bid_l o,
      good_addr (cid, bid) ->
      Memory.load m (Permission.data, cid, bid, offset) = Some (Ptr (p, cid_l, bid_l, o)) ->
      good_addr (cid_l, bid_l).

  Variable mem: Memory.t.

  Hypothesis good_memory_mem: good_memory mem.

  Lemma reachable_addresses_are_good a_set a':
    Reachable mem a_set a' ->
    (forall a, a \in a_set -> good_addr a) ->
    good_addr a'.
  Proof.
    intros Hreach. induction Hreach as [x Hx|cid bid b compMem Hreach' H1 H2 H3].
    - intros Hallgood. apply Hallgood in Hx. assumption.
    - intros Hallgood. apply H1 in Hallgood. destruct b as [a'cid a'bid].
      pose proof ComponentMemory.load_block_load compMem bid a'cid a'bid as [Hif Hiff].
      pose proof (In_in (a'cid, a'bid) (ComponentMemory.load_block compMem bid)) as
          [HinIn _].
      unfold is_true in H3. rewrite H3 in HinIn.
      assert (In (a'cid, a'bid) (ComponentMemory.load_block compMem bid)) as HIn.
      { apply HinIn. trivial. }
      destruct (Hif HIn) as [ptro [i Hload]].
      apply good_memory_mem with (cid := cid) (bid := bid) (offset := i) (p := Permission.data)
                                (o := ptro); auto.
      unfold Memory.load. simpl. rewrite H2. assumption.
  Qed.

End PredicateOnReachableAddresses.

Section PredicateOnSharedSoFar.

  (** A trace is well-formed iff for all events their memories are well-formed
      and their arguments refer to addresses in the designated set. *)

  Variable good_addr: addr_t -> Prop.

  Inductive good_trace : trace event -> Prop :=
  | nil_good_trace : good_trace nil
  | rcons_good_trace :
      forall tpref e,
        good_trace tpref ->
        good_memory good_addr (mem_of_event e) ->
        (forall a, a \in addr_of_value (arg_of_event e) -> good_addr a) ->
        good_trace (rcons tpref e).

  Variable t: trace event.

  Hypothesis good_trace_t: good_trace t.

  Lemma addr_shared_so_far_good_addr a:
    addr_shared_so_far a t -> good_addr a.
  Proof.
    intros Hshsfr. induction Hshsfr as [a t e H|a a' t e Ha'shrsfr IH H].
    - inversion good_trace_t as [H1|tpref e' Htpref Hgoodmem Hin Heq].
      + pose proof size_rcons t e as Hcontra. rewrite <- H1 in Hcontra. discriminate.
      + assert (rcons tpref e' == rcons t e) as Hrcons_eq.
        { apply/eqP. assumption. }
        pose proof eqseq_rcons tpref t e' e as Hinv. rewrite Hrcons_eq in Hinv.
        destruct (andb_true_eq _ _ Hinv) as [Htpref_t He'e].
        assert (tpref = t).
        { apply/eqP. rewrite <- Htpref_t. trivial. }
        assert (e' = e).
        { apply/eqP. rewrite <- He'e. trivial. }
        subst.
        eapply reachable_addresses_are_good.
        * exact Hgoodmem.
        * exact H.
        * exact Hin.
    - inversion good_trace_t as [H1|tpref e' Htpref Hgoodmem Hin Heq].
      + pose proof size_rcons t e as Hcontra. rewrite <- H1 in Hcontra. discriminate.
      + assert (rcons tpref e' == rcons t e) as Hrcons_eq.
        { apply/eqP. assumption. }
        pose proof eqseq_rcons tpref t e' e as Hinv. rewrite Hrcons_eq in Hinv.
        destruct (andb_true_eq _ _ Hinv) as [Htpref_t He'e].
        assert (tpref = t).
        { apply/eqP. rewrite <- Htpref_t. trivial. }
        assert (e' = e).
        { apply/eqP. rewrite <- He'e. trivial. }
        subst.
        eapply reachable_addresses_are_good.
        * exact Hgoodmem.
        * exact H.
        * intros a0 Ha0. rewrite in_fset1 in Ha0. pose proof eqP Ha0. subst. apply IH.
          exact Htpref.
  Qed.

End PredicateOnSharedSoFar.


Section RenamingAddr.

  (** Address renamings are simply applications of given address maps. *)

  Variable sigma: addr_t -> addr_t (*{fmap addr_t -> addr_t}*).
  Variable inverse_sigma: addr_t -> addr_t.

  Definition rename_addr (addr: addr_t) : addr_t := sigma addr.
  (*  match sigma addr with
  | Some addr' => addr'
  | None => addr
  end.
   *)

  Definition inverse_rename_addr (addr: addr_t) := inverse_sigma addr.

  (** Value renamings apply address renamings to rich pointer values, leaving
      all other values unchanged. *)

  Definition rename_value_template (rnm_addr : addr_t -> addr_t) (v: value) : value :=
    match v with
    | Ptr (perm, cid, bid, off) =>
      if (perm =? Permission.data) then (*rename only addresses that are loadable*)
        let (cid', bid') := rnm_addr (cid, bid) in
        Ptr (perm, cid', bid', off)
      else
        v
    | _ => v
    end.

  Definition rename_value : value -> value :=
    rename_value_template rename_addr.

  Definition inverse_rename_value : value -> value :=
    rename_value_template inverse_rename_addr.

  (** Various liftings of value renamings. *)

  Definition rename_list_values : list value -> list value :=
    map rename_value.

  Definition inverse_rename_list_values : list value -> list value :=
    map inverse_rename_value.

  Definition option_rename_value option_v :=
    omap rename_value option_v.

  Definition option_inverse_rename_value option_v :=
    omap inverse_rename_value option_v.

  (** Given the current state of the memory at two given events, these
      properties are satisfied for a given memory block iff all loads on renamed
      addresses in the second memory equal the lifted renaming of the loads on
      the original addresses in the first memory. *)

  Definition memory_renames_memory_at_addr addr m m' : Prop :=
    forall offset,
      Memory.load m'
                  (
                    Permission.data,
                    (rename_addr addr).1,
                    (rename_addr addr).2,
                    offset
                  )
      =
      option_rename_value
        (
          Memory.load m
                      (Permission.data,
                       addr.1,
                       addr.2,
                       offset)
        ).

  Definition memory_inverse_renames_memory_at_addr addr' m m' : Prop :=
    forall offset,
      option_inverse_rename_value
        (
          Memory.load m'
                      (Permission.data,
                       addr'.1,
                       addr'.2,
                       offset
                      )
        )
      =
      Memory.load m
                  (Permission.data,
                   (inverse_rename_addr addr').1,
                   (inverse_rename_addr addr').2,
                   offset
                  ).

  Definition event_renames_event_at_addr addr e e' : Prop :=
    memory_renames_memory_at_addr addr (mem_of_event e) (mem_of_event e').

  Definition event_inverse_renames_event_at_addr addr' e e' : Prop :=
    memory_inverse_renames_memory_at_addr addr' (mem_of_event e) (mem_of_event e').
      
  (** A pair of events is compatible when both instances correspond to the same
      type of event and their involved components and procedures coincide. *)
  Definition match_events (e1 e2 : event) : Prop :=
    match e1, e2 with
    | ECall C1 P1 _ _ C1', ECall C2 P2 _ _ C2' =>
      C1 = C2 /\ P1 = P2 /\ C1' = C2'
    | ERet C1 _ _ C1', ERet C2 _ _ C2' =>
      C1 = C2 /\ C1' = C2'
    | _, _ => False
    end.

  (** Two traces are mutual renamings iff all pointwise event pairs satisfy the
      event renaming property on shared addresses. The "forward" address map is
      applied to the first trace and the inverse map is applied to the second
      trace, and these maps preserve shared addresses on the traces. *)

  (* RB: NOTE: [DynShare] Would it be useful to have a trace renaming relation
     and use that to build a mutual relation? *)

  Inductive traces_rename_each_other :
    trace event -> trace event -> Prop :=
  | nil_renames_nil: traces_rename_each_other nil nil
  | rcons_renames_rcons:
      forall tprefix e tprefix' e',
        traces_rename_each_other tprefix tprefix' ->
        (
          forall addr, addr_shared_so_far addr (rcons tprefix e) ->
                       (
                         event_renames_event_at_addr addr e e'
                         /\
                         addr_shared_so_far (rename_addr addr) (rcons tprefix' e')
                       )
        )
        ->
        (
          forall addr', addr_shared_so_far addr' (rcons tprefix' e') ->
                        (
                          event_inverse_renames_event_at_addr addr' e e'
                          /\
                          addr_shared_so_far (inverse_rename_addr addr')
                                             (rcons tprefix e)
                        )
        )
        ->
        match_events e e' ->
        arg_of_event e' = rename_value (arg_of_event e) ->
        arg_of_event e  = inverse_rename_value (arg_of_event e') ->
        traces_rename_each_other (rcons tprefix e) (rcons tprefix' e').

  Lemma traces_rename_each_other_nil_rcons t x:
    traces_rename_each_other [::] (rcons t x) -> False.
  Proof. intros H. inversion H as [y Hy|tp e ? ? ? ? ? ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- Hy. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp e) = 0) as Hcontra.
           { rewrite Ha. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_rcons_nil t x:
    traces_rename_each_other (rcons t x) [::] -> False.
  Proof. intros H. inversion H as [y Hy|tp e tp' e' ? ? ? ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- y. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp' e') = 0) as Hcontra.
           { rewrite Hb. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_same_size t1 t2:
    traces_rename_each_other t1 t2 -> size t1 = size t2.
  Proof.
    intros H. induction H as [ |tp e tp' e' ? ? ? Ha]; auto.
      by rewrite !size_rcons IHtraces_rename_each_other.
  Qed.

  (* The following lemma "__traces_rename_each_other_append" is probably false.
     The reason it is false is that we cannot be sure that the shared addresses
     at the start of t1b are a continuation of the shared addresses at the end
     of t1a (neither can we do so for t2b and t2a).
   *)
  Lemma __traces_rename_each_other_append sz:
    forall t1a t1b t2a t2b,
    length (t1a ** t1b) <= sz ->
    traces_rename_each_other t1a t2a ->
    traces_rename_each_other t1b t2b ->
    traces_rename_each_other (t1a ** t1b) (t2a ** t2b).
  Abort.

End RenamingAddr.

Section TheShiftRenamingAddr.

  (** Shift renaming on a given component with given numbers of additional
      metadata blocks. *)

  Variable metadata_size_lhs_per_cid: Component.id -> nat.
  Variable metadata_size_rhs_per_cid: Component.id -> nat.

  (** Functions to return the new address after shifting the block identifier. *)

  Definition sigma_shifting_addr (a: addr_t) : addr_t :=
    let (cid, bid) := a in
    let metadata_size_lhs := metadata_size_lhs_per_cid cid in
    let metadata_size_rhs := metadata_size_rhs_per_cid cid in
    match sigma_shifting metadata_size_lhs metadata_size_rhs (care, bid) with
    | (_, bid') => (cid, bid')
    end.

  Definition inv_sigma_shifting_addr (a: addr_t) : addr_t :=
    let (cid, bid) := a in
    let metadata_size_lhs := metadata_size_lhs_per_cid cid in
    let metadata_size_rhs := metadata_size_rhs_per_cid cid in
    match inv_sigma_shifting metadata_size_lhs metadata_size_rhs (care, bid) with
    | (_, bid') => (cid, bid')
    end.


  Definition left_addr_good_for_shifting (left_addr: addr_t) : Prop :=
    match left_addr with
    | (cid, bid) =>
      let metadata_size_lhs := metadata_size_lhs_per_cid cid in
      left_block_id_good_for_shifting metadata_size_lhs bid
    end.

  Definition right_addr_good_for_shifting (right_addr: addr_t) : Prop :=
    match right_addr with
    | (cid, bid) =>
      let metadata_size_rhs := metadata_size_rhs_per_cid cid in
      right_block_id_good_for_shifting metadata_size_rhs bid
    end.
  
  (** Data pointer values can be shifted in previously specified conditions;
      code pointers and non-pointer values can always be shifted. *)

  Definition left_value_good_for_shifting (v: value) : Prop :=
    match v with
    | Ptr (perm, cid, bid, _) =>
      if perm =? Permission.data then
        left_addr_good_for_shifting (cid, bid)
      else True
    | _ => True
    end.

  Definition right_value_good_for_shifting (v: value) : Prop :=
    match v with
    | Ptr (perm, cid, bid, _) =>
      if perm =? Permission.data then
        right_addr_good_for_shifting (cid, bid)
      else True
    | _ => True
    end.

  Definition option_left_value_good_for_shifting (ov: option value) : Prop :=
    match ov with
    | Some v => left_value_good_for_shifting v
    | None => True
    end.

  Definition option_right_value_good_for_shifting (ov: option value) : Prop :=
    match ov with
    | Some v => right_value_good_for_shifting v
    | None => True
    end.

  (** A pair of traces are mutual shiftings of one another if they are
      renamings, as defined above. *)

  Inductive traces_shift_each_other : trace event -> trace event -> Prop :=
  | shifting_is_special_case_of_renaming:
      forall t t',
        traces_rename_each_other sigma_shifting_addr inv_sigma_shifting_addr t t' ->
        traces_shift_each_other t t'.

  (* For use in the state invariant *)

  Definition shift_value (v: value) : value :=
    rename_value (rename_addr sigma_shifting_addr) v.

  Definition inverse_shift_value (v': value) : value :=
    inverse_rename_value (inverse_rename_addr inv_sigma_shifting_addr) v'.
  
  Definition memory_shifts_memory_at_addr (addr: addr_t) m m' : Prop :=
    memory_renames_memory_at_addr (rename_addr sigma_shifting_addr) addr m m'.

  Definition memory_inverse_shifts_memory_at_addr (addr': addr_t) m m' : Prop :=
    memory_inverse_renames_memory_at_addr
      (inverse_rename_addr inv_sigma_shifting_addr) addr' m m'.

End TheShiftRenamingAddr.

Section ExampleShifts.

  Definition uniform_shift (n: nat) : (Component.id -> nat) :=
    fun (c: Component.id) => n.

  Definition all_zeros_shift : (Component.id -> nat) := uniform_shift 0.

  Definition fmap_extension_shift (m: {fmap Component.id -> nat}) : (Component.id -> nat) :=
    fun (c: Component.id) =>
      match m c with
      | Some n => n
      | None => 0
      end.

  Lemma fmap_extension_shift_Some cid (m: {fmap Component.id -> nat}) n:
    m cid = Some n -> (fmap_extension_shift m) cid = n.
  Proof. by move=> H; unfold fmap_extension_shift; rewrite H. Qed.

End ExampleShifts.


Section PropertiesOfTheShiftRenaming.

  Lemma sigma_shifting_addr_cid_same_injective n1 n2 cid bid1 bid2:
    left_block_id_good_for_shifting (n1 cid) bid1 ->
    left_block_id_good_for_shifting (n1 cid) bid2 ->
    rename_addr (sigma_shifting_addr n1 n2) (cid, bid1) =
    rename_addr (sigma_shifting_addr n1 n2) (cid, bid2)
    ->
    bid1 = bid2.
  Proof.
    intros H1good H2good Hrenameeq.
    unfold rename_addr, sigma_shifting_addr in *.
    assert ((care, bid1) = (care, bid2)) as H.
    {
      pose proof sigma_shifting_bijective (n1 cid) (n2 cid) as Hbij.
      inversion Hbij as [g Hcanc Hcanc'].
      unfold cancel in *.

      pose proof (Hcanc (care, bid1)) as Hg1.
      pose proof (Hcanc (care, bid2)) as Hg2.

      pose proof sigma_left_good_right_good (n1 cid) (n2 cid) bid1 H1good as
          [bid1' [H1 _]].
      pose proof sigma_left_good_right_good (n1 cid) (n2 cid) bid2 H2good as
          [bid2' [H2 _]].
      
      rewrite H1 H2 in Hrenameeq.
      rewrite H1 in Hg1. rewrite H2 in Hg2.
      
      inversion Hrenameeq. subst.
      by rewrite Hg1 in Hg2. 
    }
    
      by inversion H.
  Qed.
  
  Lemma inv_sigma_shifting_addr_cid_same_injective n1 n2 cid bid1 bid2:
    right_block_id_good_for_shifting (n2 cid) bid1 ->
    right_block_id_good_for_shifting (n2 cid) bid2 ->
    inverse_rename_addr (inv_sigma_shifting_addr n1 n2) (cid, bid1) =
    inverse_rename_addr (inv_sigma_shifting_addr n1 n2) (cid, bid2)
    ->
    bid1 = bid2.
  Proof.
    intros H1good H2good Hrenameeq.
    unfold inverse_rename_addr, inv_sigma_shifting_addr in *.
    assert ((care, bid1) = (care, bid2)) as H.
    {
      pose proof inv_sigma_shifting_bijective (n1 cid) (n2 cid) as Hbij.
      inversion Hbij as [g Hcanc Hcanc'].
      unfold cancel in *.

      pose proof (Hcanc (care, bid1)) as Hg1.
      pose proof (Hcanc (care, bid2)) as Hg2.

      pose proof inv_sigma_right_good_left_good (n1 cid) (n2 cid) bid1 H1good as
          [bid1' [H1 _]].
      pose proof inv_sigma_right_good_left_good (n1 cid) (n2 cid) bid2 H2good as
          [bid2' [H2 _]].
      
      rewrite H1 H2 in Hrenameeq.
      rewrite H1 in Hg1. rewrite H2 in Hg2.
      
      inversion Hrenameeq. subst.
      by rewrite Hg1 in Hg2. 
    }
    
      by inversion H.
  Qed.

  Lemma rename_addr_sigma_shifting_addr_cid_constant n1 n2 addr:
    (rename_addr (sigma_shifting_addr n1 n2) addr).1 = addr.1.
  Proof.
    unfold rename_addr, sigma_shifting_addr.
    destruct addr as [cid bid].
    by destruct (sigma_shifting (n1 cid) (n2 cid) (care, bid)).
  Qed.

  Lemma inverse_rename_addr_inverse_sigma_shifting_addr_cid_constant n1 n2 addr':
    (inverse_rename_addr (inv_sigma_shifting_addr n1 n2) addr').1 = addr'.1.
  Proof.
    unfold inverse_rename_addr, inv_sigma_shifting_addr.
    destruct addr' as [cid bid].
    by destruct (inv_sigma_shifting (n1 cid) (n2 cid) (care, bid)).
  Qed.
    
  Lemma left_addr_good_for_shifting_all_zeros_shift_true addr:
    left_addr_good_for_shifting all_zeros_shift addr.
  Proof.
    destruct addr.
    by unfold left_addr_good_for_shifting, all_zeros_shift, uniform_shift.
  Qed.
  
  Lemma good_memory_left_all_zeros_shift_true mem:
    good_memory (left_addr_good_for_shifting all_zeros_shift) mem.
  Proof. unfold good_memory. intros.
         apply left_addr_good_for_shifting_all_zeros_shift_true.
  Qed.

  Lemma trace_good_left_all_zeros_shift_true t:
    good_trace (left_addr_good_for_shifting all_zeros_shift) t.
  Proof.
    induction t using last_ind.
    - apply nil_good_trace.
    - apply rcons_good_trace; auto.
      + apply good_memory_left_all_zeros_shift_true.
      + intros. apply left_addr_good_for_shifting_all_zeros_shift_true.
  Qed.

  Lemma right_addr_good_for_shifting_all_zeros_shift_true addr:
    right_addr_good_for_shifting all_zeros_shift addr.
  Proof.
    destruct addr.
    by unfold right_addr_good_for_shifting, all_zeros_shift, uniform_shift.
  Qed.
  
  Lemma good_memory_right_all_zeros_shift_true mem:
    good_memory (right_addr_good_for_shifting all_zeros_shift) mem.
  Proof. unfold good_memory. intros.
         apply right_addr_good_for_shifting_all_zeros_shift_true.
  Qed.

  Lemma trace_good_right_all_zeros_shift_true t:
    good_trace (right_addr_good_for_shifting all_zeros_shift) t.
  Proof.
    induction t using last_ind.
    - apply nil_good_trace.
    - apply rcons_good_trace; auto.
      + apply good_memory_right_all_zeros_shift_true.
      + intros. apply right_addr_good_for_shifting_all_zeros_shift_true.
  Qed.

  Lemma rename_addr_reflexive n a:
    rename_addr (sigma_shifting_addr n n) a = a.
  Proof. unfold rename_addr, sigma_shifting_addr.
         destruct a. by rewrite sigma_shifting_n_n_id.
  Qed.

  Lemma inverse_rename_addr_reflexive n a:
    inverse_rename_addr (inv_sigma_shifting_addr n n) a = a.
  Proof. unfold inverse_rename_addr, inv_sigma_shifting_addr.
         destruct a. by rewrite inv_sigma_shifting_n_n_id.
  Qed.

  Lemma rename_value_reflexive n v:
    rename_value (sigma_shifting_addr n n) v = v.
  Proof. unfold rename_value, rename_value_template.
         destruct v as [ | [[[perm cid] bid] o] | ]; auto.
         destruct (perm =? Permission.data); auto.
         rewrite rename_addr_reflexive. auto.
  Qed.

  Lemma inverse_rename_value_reflexive n v:
    inverse_rename_value (inv_sigma_shifting_addr n n) v = v.
  Proof. unfold inverse_rename_value, rename_value_template.
         destruct v as [ | [[[perm cid] bid] o] | ]; auto.
         destruct (perm =? Permission.data); auto.
         rewrite inverse_rename_addr_reflexive. auto.
  Qed.

  Lemma option_rename_value_reflexive n ov:
    option_rename_value (sigma_shifting_addr n n) ov = ov.
  Proof. unfold option_rename_value, omap, obind, oapp. destruct ov as [ | ]; auto.
         by rewrite rename_value_reflexive.
  Qed.

  Lemma option_inverse_rename_value_reflexive n ov:
    option_inverse_rename_value (inv_sigma_shifting_addr n n) ov = ov.
  Proof. unfold option_inverse_rename_value, omap, obind, oapp. destruct ov as [ | ]; auto.
         by rewrite inverse_rename_value_reflexive.
  Qed.

  Lemma rename_addr_inverse_rename_addr n1 n2 a:
    rename_addr (sigma_shifting_addr n1 n2) a =
    inverse_rename_addr (inv_sigma_shifting_addr n2 n1) a.
  Proof. unfold rename_addr, inverse_rename_addr, sigma_shifting_addr, inv_sigma_shifting_addr.
         destruct a. by rewrite inv_sigma_shifting_sigma_shifting.
  Qed.

  Lemma rename_value_inverse_rename_value n2 n1 v:
    inverse_rename_value (inv_sigma_shifting_addr n2 n1) v =
    rename_value (sigma_shifting_addr n1 n2) v.
  Proof.
    destruct v as [ | [[[perm cid] bid] o] | ]; auto. simpl.
    rewrite rename_addr_inverse_rename_addr. reflexivity.
  Qed.

  Lemma option_rename_value_option_inverse_rename_value n2 n1 v:
    option_inverse_rename_value (inv_sigma_shifting_addr n2 n1) v =
    option_rename_value (sigma_shifting_addr n1 n2) v.
  Proof.
    destruct v as [[ | [[[perm cid] bid] o] | ] | ]; auto. simpl.
    rewrite rename_addr_inverse_rename_addr. reflexivity.
  Qed.

  Lemma event_rename_inverse_event_rename n1 n2 addr' e e':
    event_inverse_renames_event_at_addr
      (inv_sigma_shifting_addr n1 n2) addr' e e' <->
    event_renames_event_at_addr (sigma_shifting_addr n2 n1) addr' e' e.
  Proof.
    unfold event_inverse_renames_event_at_addr, event_renames_event_at_addr.
    split; intros H offset; pose proof (H offset) as H'. clear H.
    - rewrite <- option_rename_value_option_inverse_rename_value,
      H', rename_addr_inverse_rename_addr. reflexivity.
    - rewrite option_rename_value_option_inverse_rename_value.
      rewrite <- H', rename_addr_inverse_rename_addr. reflexivity.
  Qed.

  Lemma rename_addr_transitive n1 n2 n3 addr:
    left_addr_good_for_shifting n1 addr ->
    rename_addr (sigma_shifting_addr n2 n3)
                (rename_addr (sigma_shifting_addr n1 n2) addr) =
    rename_addr (sigma_shifting_addr n1 n3) addr.
  Proof. intros H. unfold rename_addr, sigma_shifting_addr.
         destruct addr as [cid bid] eqn:eqaddr.
         destruct (sigma_shifting (n1 cid) (n2 cid) (care, bid)) as [c12 bid'] eqn:e12.
         unfold left_addr_good_for_shifting in H.
         assert (c12 = care) as Hc12.
         {
           pose proof sigma_left_good_right_good _ (n2 cid) _ H as [rbid [Hcare _]].
           rewrite Hcare in e12. by inversion e12.
         }
         subst.
         rewrite <- (sigma_shifting_transitive (n1 cid) (n2 cid) (n3 cid)); auto.
         by rewrite e12.
  Qed.
             
  Lemma rename_value_transitive n1 n2 n3 v:
    left_value_good_for_shifting n1 v ->
    rename_value (sigma_shifting_addr n2 n3)
                 (rename_value (sigma_shifting_addr n1 n2) v) =
    rename_value (sigma_shifting_addr n1 n3) v.
  Proof.
    unfold left_value_good_for_shifting.
    intros Hgood. destruct v as [ | [[[perm cid] bid] o] | ]; auto. simpl.
    destruct (rename_addr (sigma_shifting_addr n1 n2) (cid, bid)) eqn:Hn1n2.
    simpl. destruct (perm =? Permission.data) eqn:Hperm; simpl; try rewrite Hperm; auto.
    rewrite <- Hn1n2. rewrite rename_addr_transitive; auto.
  Qed.
  
  Lemma option_rename_value_transitive n1 n2 n3 v:
    option_left_value_good_for_shifting n1 v ->
    option_rename_value (sigma_shifting_addr n2 n3)
                        (option_rename_value (sigma_shifting_addr n1 n2) v) =
    option_rename_value (sigma_shifting_addr n1 n3) v.
  Proof.
    unfold option_left_value_good_for_shifting, option_rename_value.
    intros Hgood. destruct v as [v' | ]; auto. simpl.
    rewrite rename_value_transitive; auto.
  Qed.

  Lemma event_rename_reflexive n addr e:
    event_renames_event_at_addr (sigma_shifting_addr n n) addr e e.
  Proof. unfold event_renames_event_at_addr, memory_renames_memory_at_addr.
         rewrite !rename_addr_reflexive. intros.
         rewrite option_rename_value_reflexive. auto.
  Qed.

  Lemma event_inverse_rename_reflexive n addr e:
    event_inverse_renames_event_at_addr (inv_sigma_shifting_addr n n) addr e e.
  Proof. unfold event_inverse_renames_event_at_addr, memory_inverse_renames_memory_at_addr.
         rewrite !inverse_rename_addr_reflexive. intros.
         rewrite option_inverse_rename_value_reflexive. auto.
  Qed.

  Lemma event_rename_transitive n1 n2 n3 addr e1 e2 e3:
    left_addr_good_for_shifting n1 addr ->
    (forall offset,
        option_left_value_good_for_shifting
          n1
          (Memory.load
             (mem_of_event e1)
             (Permission.data, addr.1, addr.2, offset)
          )
    )
    ->
    event_renames_event_at_addr (sigma_shifting_addr n1 n2) addr e1 e2 ->
    event_renames_event_at_addr (sigma_shifting_addr n2 n3)
                                (rename_addr (sigma_shifting_addr n1 n2) addr)
                                e2 e3 ->
    event_renames_event_at_addr (sigma_shifting_addr n1 n3) addr e1 e3.
  Proof.
    intros Haddr_good Hloads_good.
    unfold event_renames_event_at_addr. intros Hn1n2 Hn2n3 offset.
    pose proof Hn2n3 offset as Hn2n3'.
    erewrite rename_addr_transitive, (Hn1n2 offset) in Hn2n3'; auto. erewrite Hn2n3'.
    apply option_rename_value_transitive; auto.
  Qed.

  Lemma match_events_reflexive e:
    match_events e e.
  Proof.
    now destruct e.
  Qed.

  Lemma match_events_sym e1 e2:
    match_events e1 e2 ->
    match_events e2 e1.
  Proof.
    destruct e1; destruct e2;
      intros Hmatch; inversion Hmatch;
      easy.
  Qed.

  Lemma match_events_trans e1 e2 e3:
    match_events e1 e2 ->
    match_events e2 e3 ->
    match_events e1 e3.
  Proof.
    intros Hmatch1 Hmatch2.
    destruct e1; destruct e2; destruct e3;
      inversion Hmatch1; inversion Hmatch2;
      intuition; subst; done.
  Qed.

  Lemma traces_shift_each_other_reflexive n t:
    traces_shift_each_other n n t t.
  Proof.
    apply shifting_is_special_case_of_renaming.
    induction t using last_ind.
    - apply nil_renames_nil.
    - apply rcons_renames_rcons.
      + assumption.
      + intros addr Hshrsfr. split.
        * apply event_rename_reflexive.
        * by rewrite rename_addr_reflexive.
      + intros addr Hshrsfr. split.
        * apply event_inverse_rename_reflexive.
        * by rewrite inverse_rename_addr_reflexive.
      + now apply match_events_reflexive.
      + symmetry. by apply rename_value_reflexive.
      + symmetry. by apply inverse_rename_value_reflexive.
  Qed.

  Lemma traces_shift_each_other_symmetric t1 t2 n1 n2:
    traces_shift_each_other n1 n2 t1 t2 ->
    traces_shift_each_other n2 n1 t2 t1.
  Proof.
    intros Ht1t2. apply shifting_is_special_case_of_renaming.
    inversion Ht1t2. subst. induction H as [|tprefix e tprefix' e' Hprefix_rename IH He He'].
    - apply nil_renames_nil.
    - apply rcons_renames_rcons.
      + apply IH. apply shifting_is_special_case_of_renaming. exact Hprefix_rename.
      + intros [cid bid] Hshrsfr. destruct (He' (cid, bid) Hshrsfr) as [G1 G2]. split.
        * rewrite <- event_rename_inverse_event_rename. exact G1.
        * rewrite rename_addr_inverse_rename_addr. exact G2.
      + intros [cid bid] Hshrsfr. destruct (He (cid, bid) Hshrsfr) as [G1 G2]. split.
        * rewrite event_rename_inverse_event_rename. exact G1.
        * rewrite <- rename_addr_inverse_rename_addr. exact G2.
      + now apply match_events_sym.
      + by rewrite <- rename_value_inverse_rename_value.
      + by rewrite rename_value_inverse_rename_value.
  Qed.

  Lemma rcons_trace_event_eq_inversion (tp1 tp2: trace event) (e1 e2: event):
    rcons tp1 e1 = rcons tp2 e2 -> tp1 = tp2 /\ e1 = e2.
  Proof.
    intros rconseq. assert (rcons tp1 e1 == rcons tp2 e2) as rconseq'. apply/eqP. assumption.
    rewrite eqseq_rcons in rconseq'. destruct (andP rconseq') as [G1 G2].
    split; apply/eqP; assumption.
  Qed.

  Lemma __traces_shift_each_other_transitive n1 n2 n3 sz:
    forall t1 t2 t3,
      size t1 = sz ->
      good_trace (left_addr_good_for_shifting n1) t1 ->
      good_trace (left_addr_good_for_shifting n3) t3 ->
      traces_shift_each_other n1 n2 t1 t2 ->
      traces_shift_each_other n2 n3 t2 t3 ->
      traces_shift_each_other n1 n3 t1 t3.
  Proof.
    induction sz as [ | sz IHsz]; intros t1 t2 t3 t1sz t1good t3good H12 H23.
    - assert (t2sz: size t2 = 0).
      { inversion H12. erewrite <- traces_rename_each_other_same_size; eauto. }
      assert (t3sz: size t3 = 0).
      { inversion H23. erewrite <- traces_rename_each_other_same_size; eauto. }
      assert (t1nil: t1 = [::]). by (apply size0nil).
      assert (t2nil: t2 = [::]). by (apply size0nil).
      assert (t3nil: t3 = [::]). by (apply size0nil).
      subst. apply shifting_is_special_case_of_renaming, nil_renames_nil.
    - inversion H12 as [? ? H12']. inversion H23 as [? ? H23']. subst. clear H12 H23.
      assert (size t2 = sz.+1) as Hsizet2.
      {
        symmetry. rewrite <- t1sz.
        apply (traces_rename_each_other_same_size _ _ t1 t2 H12').
      }
      assert (size t3 = sz.+1) as Hsizet3.
      {
        symmetry. rewrite <- Hsizet2.
        apply (traces_rename_each_other_same_size _ _ t2 t3 H23').
      }
      induction t1 as [ | t1 e1 IHt1] using last_ind; try discriminate.
      induction t2 as [ | t2 e2 IHt2] using last_ind; try discriminate.
      induction t3 as [ | t3 e3 IHt3] using last_ind; try discriminate.

      assert (t1_tlsz: size t1 = sz). by (rewrite size_rcons in t1sz; inversion t1sz).
      pose proof (IHsz t1 t2 t3 t1_tlsz) as IHsz'.

      inversion H12' as [ | ? ? ? ? H12a H12b H12c Hevsa H12d H12e Heq1 Heq2];
        try by (rewrite <- H in t1sz; inversion t1sz).
      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq1) as [tmp1 tmp2]. subst. clear Heq1.
      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq2) as [tmp1 tmp2]. subst. clear Heq2.

      inversion H23' as [ | ? ? ? ? H23a H23b H23c Hevsb H23d H23e Heq1 Heq2];
        try by (rewrite <- H in Hsizet2; inversion Hsizet2).
      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq1) as [tmp1 tmp2]. subst. clear Heq1.
      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq2) as [tmp1 tmp2]. subst. clear Heq2.

      pose proof (shifting_is_special_case_of_renaming _ _ _ _ H12a) as H12a_shift.
      pose proof (shifting_is_special_case_of_renaming _ _ _ _ H23a) as H23a_shift.

      inversion t1good as [H | ? ? t1gooda t1goodb t1goodc Heq];
        try by (rewrite <- H in t1sz; inversion t1sz).

      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq) as [tmp1 tmp2]. subst. clear Heq.

      inversion t3good as [H | ? ? t3gooda t3goodb t3goodc Heq];
        try by (rewrite <- H in Hsizet3; inversion Hsizet3).

      destruct (rcons_trace_event_eq_inversion _ _ _ _ Heq) as [tmp1 tmp2]. subst. clear Heq.

      pose proof (IHsz' t1gooda t3gooda H12a_shift H23a_shift) as H13a_shift.
      apply shifting_is_special_case_of_renaming, rcons_renames_rcons.
      + inversion H13a_shift; auto.
      + intros addr Haddr.
        assert (addr_n1_good: left_addr_good_for_shifting n1 addr).
        { eapply addr_shared_so_far_good_addr with (t := rcons t1 e1); eauto. }
        pose proof H12b addr Haddr as [He1e2 Hshrsfr2].
        pose proof H23b (rename_addr (sigma_shifting_addr n1 n2) addr) Hshrsfr2
          as [He2e3 Hshrsfr3].
        split.
        * eapply event_rename_transitive; eauto.
          unfold option_left_value_good_for_shifting, left_value_good_for_shifting.
          intros offset.
          destruct (Memory.load (mem_of_event e1) (Permission.data, addr.1, addr.2, offset))
            as [ [ | [[[perm cid] bid] off] | ] | ] eqn:Hload; eauto.
          destruct (perm =? Permission.data) eqn:Hperm; auto.
          assert (perm = Permission.data) by (apply Nat.eqb_eq; auto). subst.
          assert (addr_shared_so_far (cid, bid) (rcons t1 e1)).
          { eapply addr_shared_so_far_load_addr_shared_so_far; eauto. }
          eapply addr_shared_so_far_good_addr with (t := rcons t1 e1); eauto.
        * erewrite <- rename_addr_transitive; eauto.
      + intros addr' Haddr'.
        assert (addr_n3_good: left_addr_good_for_shifting n3 addr').
        { eapply addr_shared_so_far_good_addr with (t := rcons t3 e3); eauto. }
        pose proof H23c addr' Haddr' as [He2e3 Hshrsfr2].
        pose proof H12c
             (inverse_rename_addr (inv_sigma_shifting_addr n2 n3) addr') Hshrsfr2
          as [He1e2 Hshrsfr1].
        split.
        * erewrite event_rename_inverse_event_rename.
          erewrite event_rename_inverse_event_rename in He2e3, He1e2.
          erewrite <- rename_addr_inverse_rename_addr in He1e2.
          erewrite <- !rename_addr_inverse_rename_addr in Hshrsfr1.
          eapply event_rename_transitive; eauto.
          unfold option_left_value_good_for_shifting, left_value_good_for_shifting.
          intros offset.
          destruct (Memory.load (mem_of_event e3) (Permission.data, addr'.1, addr'.2, offset))
            as [ [ | [[[perm cid] bid] off] | ] | ] eqn:Hload; eauto.
          destruct (perm =? Permission.data) eqn:Hperm; auto.
          assert (perm = Permission.data) by (apply Nat.eqb_eq; auto). subst.
          assert (addr_shared_so_far (cid, bid) (rcons t3 e3)).
          { eapply addr_shared_so_far_load_addr_shared_so_far; eauto. }
          eapply addr_shared_so_far_good_addr with (t := rcons t3 e3); eauto.
        * erewrite <- rename_addr_inverse_rename_addr.
          erewrite <- !rename_addr_inverse_rename_addr in Hshrsfr1.
          erewrite <- rename_addr_transitive; eauto.
      + eapply match_events_trans; eassumption.
      + rewrite H23d H12d. apply rename_value_transitive.
        unfold left_value_good_for_shifting.
        destruct (arg_of_event e1) as [| [[[perm cid] bid] ?] |]; auto.
        destruct (perm =? Permission.data) eqn:eperm; auto.
        apply t1goodc. simpl. rewrite eperm. by apply/fset1P.
      + rewrite H12e H23e.
        rewrite !rename_value_inverse_rename_value.
        apply rename_value_transitive.
        unfold left_value_good_for_shifting.
        destruct (arg_of_event e3) as [| [[[perm cid] bid] ?] |]; auto.
        destruct (perm =? Permission.data) eqn:eperm; auto.
        apply t3goodc. simpl. rewrite eperm. by apply/fset1P.
  Qed.

  Lemma traces_shift_each_other_transitive n1 n2 n3 t1 t2 t3:
      good_trace (left_addr_good_for_shifting n1) t1 ->
      good_trace (left_addr_good_for_shifting n3) t3 ->
      traces_shift_each_other n1 n2 t1 t2 ->
      traces_shift_each_other n2 n3 t2 t3 ->
      traces_shift_each_other n1 n3 t1 t3.
  Proof.
    eapply __traces_shift_each_other_transitive. eauto.
  Qed.

  Lemma traces_shift_each_other_nil_rcons n1 n2 t x:
    traces_shift_each_other n1 n2 [::] (rcons t x) -> False.
  Proof. intros H. inversion H. eapply traces_rename_each_other_nil_rcons. eauto. Qed.

  Lemma traces_shift_each_other_rcons_nil n1 n2 t x:
    traces_shift_each_other n1 n2 (rcons t x) [::] -> False.
  Proof. intros H. inversion H. eapply traces_rename_each_other_rcons_nil. eauto. Qed.

  Lemma traces_shift_each_other_same_size n1 n2 t1 t2:
    traces_shift_each_other n1 n2 t1 t2 -> size t1 = size t2.
  Proof. intros H. inversion H. eapply traces_rename_each_other_same_size. eauto. Qed.

End PropertiesOfTheShiftRenaming.



Section StructuralPropertiesOfValueRenaming.

  Lemma rename_value_template_Int f i:
    rename_value_template f (Int i) = Int i. by auto.
  Qed.

  Lemma rename_value_template_Undef f:
    rename_value_template f Undef = Undef. by auto.
  Qed.

  Lemma rename_value_template_Ptr f perm cid bid off:
    rename_value_template f (Ptr (perm, cid, bid, off)) =
    if perm =? Permission.data then
      Ptr (perm, (f (cid, bid)).1, (f (cid, bid)).2, off)
    else
      Ptr (perm, cid, bid, off).
  Proof.
    unfold rename_value_template. by destruct (f (cid, bid)).
  Qed.

  Lemma shift_value_Ptr_perm_off n1 n2 perm cid bid off:
    exists cid' bid',
      shift_value n1 n2 (Ptr (perm, cid, bid, off)) = Ptr (perm, cid', bid', off).
  Proof.
    unfold shift_value, rename_value. rewrite rename_value_template_Ptr.
    destruct (perm =? Permission.data) eqn:eperm; eauto.
  Qed.
  
End StructuralPropertiesOfValueRenaming.


Section AdequacyOfTheShiftRenaming.

  Lemma load_memory_shifts_memory_value_shifts_value n1 n2 ptr ptr' m m':
    memory_shifts_memory_at_addr
      n1
      n2
      (Pointer.component ptr, Pointer.block ptr)
      m
      m' ->
    Ptr ptr' = shift_value n1 n2 (Ptr ptr) ->
    omap (shift_value n1 n2) (Memory.load m ptr)
    =
    Memory.load m' ptr'.
  Proof.
    intros Hmemshift Hvshift.
    unfold
      memory_shifts_memory_at_addr,
    memory_renames_memory_at_addr, option_rename_value in Hmemshift.
    simpl in Hmemshift.
    unfold shift_value in *.
    destruct ptr as [[[perm cid] bid] off]. simpl in Hvshift.
    destruct (perm =? Permission.data) eqn:permdata.
    - destruct ptr' as [[[perm' cid'] bid'] off']. simpl in *.
      destruct (
          rename_addr
            (rename_addr
               (sigma_shifting_addr
                  n1
                  n2
               )
            )
            (cid, bid)
        ) as [cid_ren bid_ren] eqn:renameeq.
      inversion Hvshift. subst.
      pose proof Hmemshift off as G.
      simpl in G.
      assert (perm = Permission.data) as permeq.
      {
         by apply/Nat.eqb_spec.
      }
      by rewrite permeq.
    - destruct ptr' as [[[perm' cid'] bid'] off']. simpl in *. inversion Hvshift. subst.
      unfold Memory.load. simpl. by rewrite permdata.
  Qed.

  Lemma load_memory_inverse_shifts_memory_value_inverse_shifts_value
        n1 n2 ptr ptr' m' m:
    memory_inverse_shifts_memory_at_addr
      n1
      n2
      (Pointer.component ptr, Pointer.block ptr)
      m
      m' ->
    Ptr ptr' = inverse_shift_value n1 n2 (Ptr ptr) ->
    omap (inverse_shift_value n1 n2) (Memory.load m' ptr)
    =
    Memory.load m ptr'.
  Proof.
    intros Hmemshift Hvshift.
    unfold
      memory_inverse_shifts_memory_at_addr,
    memory_inverse_renames_memory_at_addr, option_inverse_rename_value in Hmemshift.
    simpl in Hmemshift.
    unfold inverse_shift_value in *.
    destruct ptr as [[[perm cid] bid] off]. simpl in Hvshift.
    destruct (perm =? Permission.data) eqn:permdata.
    - destruct ptr' as [[[perm' cid'] bid'] off']. simpl in *.
      destruct (
          inverse_rename_addr
            (inverse_rename_addr
               (inv_sigma_shifting_addr
                  n1
                  n2
               )
            )
            (cid, bid)
        ) as [cid_ren bid_ren] eqn:renameeq.
      inversion Hvshift. subst.
      pose proof Hmemshift off as G.
      simpl in G.
      assert (perm = Permission.data) as permeq.
      {
         by apply/Nat.eqb_spec.
      }
      by rewrite permeq.
    - destruct ptr' as [[[perm' cid'] bid'] off']. simpl in *. inversion Hvshift. subst.
      unfold Memory.load. simpl. by rewrite permdata.
  Qed.

  Variable n1 n2: Component.id -> nat.
  Let renfun := sigma_shifting_addr n1 n2.
  Let inv_renfun := inv_sigma_shifting_addr n1 n2.

  Lemma store_memory_shifts_memory_value_shifts_value
        cid_i bid_i cid_i' bid_i' ptr_st ptr_st' v v' m m' m_st m_st':
    left_addr_good_for_shifting n1 (cid_i, bid_i) ->
    left_value_good_for_shifting n1 (Ptr ptr_st) ->
    memory_renames_memory_at_addr
      renfun
      (cid_i, bid_i)
      m
      m'
    ->
    (cid_i', bid_i') = rename_addr renfun (cid_i, bid_i) ->
    Ptr ptr_st' = rename_value renfun (Ptr ptr_st) ->
    v' = rename_value renfun v ->
    Memory.store m ptr_st v = Some m_st ->
    Memory.store m' ptr_st' v' = Some m_st' ->
    memory_renames_memory_at_addr
      renfun
      (cid_i, bid_i)
      m_st
      m_st'.
  Proof.
    unfold memory_renames_memory_at_addr, option_rename_value.
    (* intros Hmemshift Hptr_i Hptr_st Hv Hstoresome Hstoresome'. *)
    destruct ptr_st as [[[permst cidst] bidst] offst].
    destruct ptr_st' as [[[permst' cidst'] bidst'] offst'].

    intros Higoodaddr Hptr_stgood
           Hmm' Hcid_i'bid_i' Hptr_st' Hv' HstoreSome HstoreSome'.
    simpl in *.
    destruct (permst =? Permission.data) eqn:eqpermst.
    - assert (permst = Permission.data). { by apply/Nat.eqb_spec. }
      subst. clear eqpermst.
      intros offset.
      pose proof Memory.load_after_store
             m (Permission.data, cidst, bidst, offst) v
             m_st (Permission.data, cid_i, bid_i, offset)
             HstoreSome as H.

      assert (permst' = Permission.data).
      {
        destruct (rename_addr renfun (cidst, bidst)). by inversion Hptr_st'.
      }
      subst.

      assert (offst' = offst).
      {
        destruct (rename_addr renfun (cidst, bidst)). by inversion Hptr_st'.
      }
      subst.

      assert (cidst' = (rename_addr renfun (cidst, bidst)).1) as Hcidst'.
      {
        destruct (rename_addr renfun (cidst, bidst)). by inversion Hptr_st'.
      }

      assert (bidst' = (rename_addr renfun (cidst, bidst)).2) as Hbidst'.
      {
        destruct (rename_addr renfun (cidst, bidst)). by inversion Hptr_st'.
      }

      clear Hptr_st'.

      destruct ((Permission.data, cid_i, bid_i, offset) ==
                (Permission.data, cidst, bidst, offst)) eqn:i_st.
      + assert ((Permission.data, cid_i, bid_i, offset) =
                (Permission.data, cidst, bidst, offst)) as H_.
        {
          by apply/eqP.
        }
        inversion H_. subst. clear H_ i_st.
        rewrite H. simpl.

        pose proof Memory.load_after_store
             m' (Permission.data,
                 (rename_addr renfun (cidst, bidst)).1,
                 (rename_addr renfun (cidst, bidst)).2, offst)
             (rename_value renfun v)
             m_st' (Permission.data,
                    (rename_addr renfun (cidst, bidst)).1,
                    (rename_addr renfun (cidst, bidst)).2, offst)
             HstoreSome' as H'.
          by rewrite eqxx in H'.
      + rewrite H. rewrite <- Hmm'.
          pose proof Memory.load_after_store
             m' (Permission.data, cidst', bidst', offst)
             (rename_value renfun v)
             m_st'
             (Permission.data, (rename_addr renfun (cid_i, bid_i)).1,
              (rename_addr renfun (cid_i, bid_i)).2, offset)
             HstoreSome' as H'.

          destruct ((Permission.data, (rename_addr renfun (cid_i, bid_i)).1,
                     (rename_addr renfun (cid_i, bid_i)).2, offset) ==
                    (Permission.data, cidst', bidst', offst)) eqn:eq_renames; auto.
          (* case true remains. derive a contradiction to i_st using 
             injectivity of sigma_shifting_addr *)
          assert ((Permission.data, (rename_addr renfun (cid_i, bid_i)).1,
                     (rename_addr renfun (cid_i, bid_i)).2, offset) =
                  (Permission.data, cidst', bidst', offst)) as eq_renames_.
            by apply/eqP.
            inversion eq_renames_. subst. clear eq_renames_.
            
            assert ((rename_addr renfun (cid_i, bid_i)).1 = cid_i) as Hcid_i.
              by rewrite rename_addr_sigma_shifting_addr_cid_constant.
            assert ((rename_addr renfun (cidst, bidst)).1 = cidst) as Hcidst.
            {  by rewrite rename_addr_sigma_shifting_addr_cid_constant. }
            assert (cid_i = cidst).
            {
              rewrite <- Hcid_i. by rewrite <- Hcidst.
            }
            subst.
            pose proof sigma_shifting_addr_cid_same_injective
                 n1 n2 cidst _ _ Higoodaddr Hptr_stgood as Hinj.
            unfold renfun in *.
            assert (bid_i = bidst).
            {
              apply Hinj.
              destruct (rename_addr (sigma_shifting_addr n1 n2) (cidst, bid_i)).
              destruct (rename_addr (sigma_shifting_addr n1 n2) (cidst, bidst)).
              simpl in *. by subst.
            }
            subst. by rewrite eqxx in i_st.
    - unfold Memory.store in *. rewrite eqpermst in HstoreSome. discriminate.
  Qed.
    
      
End AdequacyOfTheShiftRenaming.

Section BehaviorsRelated.

  (** Trace relation (between finite trace prefixes),
     parameterized by the size of the metadata of each trace. Two traces are
     related iff they shift each other and correspond to either a pair of
     unfinished program executions or to a pair of successfully terminated
     program executions. *)

  Inductive behavior_rel_behavior
            (size_meta_t1: Component.id -> nat) (size_meta_t2: Component.id -> nat)
  : @finpref_behavior Events.event -> @finpref_behavior Events.event -> Prop :=
  | Terminates_rel_Terminates:
      forall t1 t2,
        traces_shift_each_other size_meta_t1 size_meta_t2 t1 t2 ->
        behavior_rel_behavior size_meta_t1 size_meta_t2 (FTerminates t1) (FTerminates t2)
  | Tbc_rel_Tbc:
      forall t1 t2,
        traces_shift_each_other size_meta_t1 size_meta_t2 t1 t2 ->
        behavior_rel_behavior size_meta_t1 size_meta_t2 (FTbc t1) (FTbc t2).

  Lemma behavior_rel_behavior_reflexive b n:
    not_wrong_finpref b ->
    behavior_rel_behavior n n b b.
  Proof. intros not_wrong. unfold not_wrong_finpref in *. destruct b; auto.
         - apply Terminates_rel_Terminates. apply traces_shift_each_other_reflexive.
         - exfalso. auto.
         - apply Tbc_rel_Tbc. apply traces_shift_each_other_reflexive.
  Qed.

  Lemma behavior_rel_behavior_symmetric b1 b2 n1 n2:
    behavior_rel_behavior n1 n2 b1 b2 -> behavior_rel_behavior n2 n1 b2 b1.
  Proof. intros H. inversion H.
         - apply Terminates_rel_Terminates. apply traces_shift_each_other_symmetric. auto.
         - apply Tbc_rel_Tbc. apply traces_shift_each_other_symmetric. auto.
  Qed.

  (** well-formedness of finite program behaviors (on the left) lifts
      well-formedness of traces to successfully terminating and unfinished
      program behaviors. *)

  Inductive good_behavior_left
            (size_meta_t: Component.id -> nat) :
    @finpref_behavior Events.event -> Prop :=
  | good_trace_Terminates:
      forall t,
        good_trace (left_addr_good_for_shifting size_meta_t) t ->
        good_behavior_left size_meta_t (FTerminates t)
  | good_trace_Tbc:
      forall t,
        good_trace (left_addr_good_for_shifting size_meta_t) t ->
        good_behavior_left size_meta_t (FTbc t).

  Lemma behavior_rel_behavior_transitive b1 b2 b3 n1 n2 n3:
    good_behavior_left n1 b1 ->
    good_behavior_left n3 b3 ->
    behavior_rel_behavior n1 n2 b1 b2 ->
    behavior_rel_behavior n2 n3 b2 b3 ->
    behavior_rel_behavior n1 n3 b1 b3.
  Proof.
    intros Hg1 Hg3 H12 H23.
    inversion Hg1; subst; inversion Hg3; subst; inversion H12; subst; inversion H23; subst.
    - eapply Terminates_rel_Terminates.
      eapply traces_shift_each_other_transitive with n2 t2; eauto.
    - eapply Tbc_rel_Tbc.
      eapply traces_shift_each_other_transitive with n2 t2; eauto.
  Qed.

End BehaviorsRelated.

(* [DynShare]
   The following definition is NOT needed when we define a trace relation that
   (implicitly) specifies the shared part of the memory.

   It would be needed though if instead we define a trace semantics
   that (explicitly) emits only the shared memory rather than the whole memory.
*)
Definition shared_part_of_memory
           (mshr: Memory.t)
           (m: Memory.t)
           (t: trace event)
  : Prop :=
  forall addr offset, (addr_shared_so_far addr t ->
                       Memory.load mshr (Permission.data, addr.1, addr.2, offset)
                       =
                       Memory.load m (Permission.data, addr.1, addr.2, offset)
                      )
                      /\
                      (~ addr_shared_so_far addr t) ->
                      Memory.load mshr (Permission.data, addr.1, addr.2, offset) = None.


  (*Hypothesis cancel_inverse_sigma_sigma: cancel inverse_sigma sigma.
  Hypothesis cancel_sigma_inverse_sigma: cancel sigma inverse_sigma.
  Hypothesis sigma_injective: injective sigma.*)

  (*Definition inverse_sigma (addr: addr_t) : addr_t :=
  let dom_sigma := domm sigma in
  if has (fun y => sigma y == Some addr) dom_sigma
  then nth (0,0) dom_sigma (find (fun y => sigma y == Some addr) dom_sigma)
  else addr.
   *)


  (*Lemma inverse_rename_addr_left_inverse addr: inverse_rename_addr (rename_addr addr) = addr.
  Proof.
    unfold inverse_rename_addr, rename_addr. pose proof (cancel_sigma_inverse_sigma addr). auto.
  Qed.*)


  (*****************************
    [DEPRECATED]: sigma was fmap.

Lemma inverse_rename_addr_left_inverse addr:
  addr \in domm sigma -> (*Is this precondition ok?*)
  inverse_rename_addr (rename_addr addr) = addr.
  (* This lemma
     without the precondition "addr \in domm sigma"
     is not really provable because the rename_addr function can actually cause
     two addresses addr1 and addr2 to clash at some addr' when still sigma itself is injective.

    This lemma only holds for "addr \in domm sigma".

    However, under the "addr \in domm sigma" precondition,
    it is not very clear whether the lemma will be usable.
    It will be comfortably usable when we have a "complete" sigma, i.e., when
    we only call rename_addr on some addr \in sigma.
   *)
Proof.
  intros Haddr.
  unfold inverse_rename_addr, inverse_sigma. simpl.
  unfold rename_addr.
  destruct (sigma addr) as [addr'|] eqn:e_sigma_addr.
  - destruct (has (fun y => sigma y == Some addr') (domm sigma)) eqn:e_has; rewrite e_has.
    + pose proof (nth_find (0,0) e_has) as Hnth. simpl in Hnth.
      apply/inj_eqAxiom.
      * exact sigma_injective.
      * rewrite e_sigma_addr. exact Hnth.
    + pose proof (mem_domm sigma addr) as Hin_domm.
      pose proof (@hasP _ (fun y => sigma y == Some addr') (domm sigma)) as H.
      rewrite e_has in H.
      apply elimF in H; auto.
      assert (exists2 x, x \in domm sigma & sigma x == Some addr') as contra.
      {
        eexists addr.
        * rewrite mem_domm e_sigma_addr. auto.
        * rewrite e_sigma_addr. auto.
      }
      apply H in contra. exfalso. assumption.
  - rewrite mem_domm in Haddr. rewrite e_sigma_addr in Haddr. easy.
Qed.

   ****************************************)


  (*Lemma inverse_rename_addr_right_inverse addr:
    rename_addr (inverse_rename_addr addr) = addr.
  Proof.
    unfold inverse_rename_addr, rename_addr. pose proof (cancel_inverse_sigma_sigma addr). auto.
  Qed.*)



  (**************************************
    [DEPRECATED]: sigma was finmap

Lemma inverse_rename_addr_right_inverse addr_pre addr:
  sigma addr_pre = Some addr ->
  rename_addr (inverse_rename_addr addr) = addr.
Proof.
  intros Haddr.
  unfold inverse_rename_addr, inverse_sigma. simpl. unfold rename_addr.
  destruct (has (fun y : nat * nat => sigma y == Some addr) (domm sigma)) eqn:e_has.
  - pose proof (nth_find (0,0) e_has) as H. simpl in H.
    pose proof (@eqP _ _ _ H) as H'. rewrite H'. reflexivity.
  - pose proof (@hasP _ (fun y => sigma y == Some addr) (domm sigma)) as H.
    rewrite e_has in H. apply elimF in H; auto.
    assert (exists2 x, x \in domm sigma & sigma x == Some addr) as contra.
    {
      eexists addr_pre.
      + rewrite mem_domm Haddr. auto.
      + rewrite Haddr. auto.
    }
    apply H in contra. exfalso. assumption.
Qed.

   *********************************)


  (******************************************
     [DEPRECATED]: Memory renaming has now been defined as part of event renaming.

  Definition rename_memory_content_at_addr (m: Memory.t) (addr: Component.id * Block.id)
    : Memory.t :=
    match omap rename_list_values (Memory.load_all m addr) with
    | Some vs => match Memory.store_all m addr vs with
                 | Some m' => m'
                 | None => m
                 end
    | None => m
    end.

  Fixpoint rename_memory_content_at_addrs (m: Memory.t) (addrs: list (Component.id * Block.id))
    : Memory.t :=
    match addrs with
    | nil => m
    | cb :: cbs => rename_memory_content_at_addrs (rename_memory_content_at_addr m cb) cbs
    end.

  Definition rename_memory_addrs (m: Memory.t) (addrs: list (Component.id * Block.id))
    : Memory.t :=
    Memory.transfer_memory_blocks m addrs m (map rename_addr addrs).

  Definition rename_memory_subgraph (m: Memory.t) (addrs: list (Component.id * Block.id))
    : Memory.t :=
    rename_memory_content_at_addrs (rename_memory_addrs m addrs) (map rename_addr addrs).

  (* [DynShare]: TODO:
   Is the following lemma needed?
   This lemma may be a bit too tedious to prove.

   Alternatively, I will experiment with representing the trace renaming
   as a Prop. Such a Trace_Renames_Trace Prop
   will use the definitions of the following Prop's:
   * Mem_Renames_Mem
   * Addr_shared_so_far, which itself will use the definition of
   * Reachable
   *)
  Lemma reachable_nodes_nat_rename m start:
    fset (
        reachable_nodes_nat
          (rename_memory_subgraph m (reachable_nodes_nat m start))
          (rename_addr start)
      )
    =
    fset (map rename_addr (reachable_nodes_nat m start)).
  Admitted.

   *********************************************)

(***********************************


Section ShiftingAsPartialBijectionAllCids.

  Variable count_blocks_to_shift_for_cid : Component.id -> nat.

  Definition sigma_from_bigger_dom_all_cids (x: bool * addr_t) : bool * addr_t :=
    sigma_from_bigger_dom x.2.1 (count_blocks_to_shift_for_cid x.2.1) x.

  Definition inv_sigma_from_bigger_dom_all_cids (x: bool * addr_t) : bool * addr_t :=
    inv_sigma_from_bigger_dom x.2.1 (count_blocks_to_shift_for_cid x.2.1) x.

  Lemma cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom_all_cids :
    cancel sigma_from_bigger_dom_all_cids inv_sigma_from_bigger_dom_all_cids.
  Proof.
    unfold sigma_from_bigger_dom_all_cids, inv_sigma_from_bigger_dom_all_cids.
    intros x. rewrite sigma_from_bigger_dom_cid_constant.
    eapply cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom.
  Qed.

  Lemma cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom_all_cids :
    cancel inv_sigma_from_bigger_dom_all_cids sigma_from_bigger_dom_all_cids.
  Proof.
    unfold sigma_from_bigger_dom_all_cids, inv_sigma_from_bigger_dom_all_cids.
    intros x. rewrite inv_sigma_from_bigger_dom_cid_constant.
    eapply cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom.
  Qed.

  Lemma sigma_from_bigger_dom_bijective_all_cids : bijective sigma_from_bigger_dom_all_cids.
  Proof. apply Bijective with (g := inv_sigma_from_bigger_dom_all_cids).
         - exact cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom_all_cids.
         - exact cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom_all_cids.
  Qed.

  Lemma inv_sigma_from_bigger_dom_bijective_all_cids :
    bijective inv_sigma_from_bigger_dom_all_cids.
  Proof. apply Bijective with (g := sigma_from_bigger_dom_all_cids).
         - exact cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom_all_cids.
         - exact cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom_all_cids.
  Qed.

  Lemma sigma_from_bigger_dom_cid_constant_all_cids x:
    (sigma_from_bigger_dom_all_cids x).2.1 = x.2.1.
  Proof.
    unfold sigma_from_bigger_dom_all_cids.
    by rewrite sigma_from_bigger_dom_cid_constant.
  Qed.

  Lemma inv_sigma_from_bigger_dom_cid_constant_all_cids x:
    (inv_sigma_from_bigger_dom_all_cids x).2.1 = x.2.1.
  Proof.
    unfold inv_sigma_from_bigger_dom_all_cids.
    by rewrite inv_sigma_from_bigger_dom_cid_constant.
  Qed.

End ShiftingAsPartialBijectionAllCids.



*************************************)

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
Require Import Coq.Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Ltac find_nil_rcons :=
  let Hcontra := fresh "Hcontra" in
  match goal with
  | H: [::] = rcons ?t ?e |- _ =>
    pose proof size_rcons t e as Hcontra;
      by rewrite <- H in Hcontra
  | H: rcons ?t ?e = [::] |- _ =>
    pose proof size_rcons t e as Hcontra;
      by rewrite H in Hcontra
  end.

Ltac find_rcons_rcons :=
  match goal with
  | H: rcons ?t1 ?e1 = rcons ?t2 ?e2 |- _ =>
    apply rcons_inj in H; inversion H; subst; clear H
  end.

Lemma le_false_lt n1 n2:
  n2 <= n1 = false -> n1 < n2.
Proof.
  intros n1n2.
  apply/ltP.
  apply Nat.ltb_lt.
  destruct (n1 <? n2) eqn:contra; auto.
  rewrite -> Nat.ltb_ge in contra.
  assert (n2 <= n1) as H. by apply/leP.
  by rewrite H in n1n2.
Qed.

Lemma subn_eq_subn_cancel n1 n2 s:
  n1 >= s ->
  n2 >= s ->
  n1 - s = n2 - s ->
  n1 = n2.
Proof.
  induction s; intuition.
  - by rewrite !subn0 in H1.
  - apply IHs; auto.
    rewrite !subnS in H1.
    unfold Init.Nat.pred in H1.
    assert (0 < n1 - s). by rewrite subn_gt0.
    assert (0 < n2 - s). by rewrite subn_gt0.
    destruct (n1 - s); try by auto.
      by destruct (n2 - s); auto.
Qed.

Lemma subn_n_m_n_0:
  forall n m, n - m = n -> m = 0 \/ n = 0.
Proof.
  intros n m Hnm.
  destruct n; intuition.
  unfold subn, subn_rec in Hnm. simpl in Hnm.
  destruct m; auto.
  pose proof Nat.le_sub_l n m as Hcontra.
  rewrite Hnm in Hcontra.
    by intuition.
Qed.

(**********************************************************
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

  Definition sigma_from_bigger_dom_option (bid: Block.id) : option Block.id :=
    if bid <? count_blocks_to_shift_for_cid
    then None
    else Some (bid - count_blocks_to_shift_for_cid).


  Definition sigma_from_smaller_dom (bid: Block.id) : Block.id :=
    bid + count_blocks_to_shift_for_cid.

  
  Lemma ocancel_sigma_from_bigger_dom_option_sigma_from_smaller_dom:
    ocancel sigma_from_bigger_dom_option
            sigma_from_smaller_dom.
  Proof.
    unfold ocancel, sigma_from_bigger_dom_option, sigma_from_smaller_dom,
    oapp.
    intros bid.
    destruct (bid <? count_blocks_to_shift_for_cid) eqn:ebid; auto.
    rewrite subnK; auto.
    assert (count_blocks_to_shift_for_cid <= bid)%coq_nat. by rewrite <- Nat.ltb_ge.
    by apply/leP.
  Qed.

  Lemma pcancel_sigma_from_smaller_dom_sigma_from_bigger_dom_option:
    pcancel sigma_from_smaller_dom
            sigma_from_bigger_dom_option.
  Proof.
    unfold pcancel, sigma_from_bigger_dom_option, sigma_from_smaller_dom.
    intros bid.
    destruct (bid + count_blocks_to_shift_for_cid <? count_blocks_to_shift_for_cid)
             eqn:ebid.
    - specialize (leq_addl bid count_blocks_to_shift_for_cid) as Hcontra.
      specialize (@leP _ _ Hcontra) as Hcontra'.
      rewrite <- Nat.ltb_ge in Hcontra'.
      by rewrite Hcontra' in ebid.
    - rewrite <- addnBA; auto.
      by rewrite subnn addn0.
  Qed.      

  
End ShiftingBlockIdsAsPartialBijection.
*****************************************************************)

Section SigmaShiftingBlockIds.

  (** Shift renaming on a given component with given numbers of additional
      metadata blocks on both sides. *)

  (* Variable cid_with_shifting: Component.id. *)
  Variable metadata_size_lhs: nat.
  Variable metadata_size_rhs: nat.

  (****************************************
  Definition sigma_shifting_lefttoright_option : Block.id -> option Block.id :=
    if (metadata_size_lhs >= metadata_size_rhs)%nat
    then sigma_from_bigger_dom_option (metadata_size_lhs - metadata_size_rhs)
    else fun bid =>
           omap
             (sigma_from_smaller_dom (metadata_size_rhs - metadata_size_lhs))
             (Some bid).

  Definition sigma_shifting_righttoleft_option : Block.id -> option Block.id :=
    if (metadata_size_lhs >= metadata_size_rhs)%nat
    then fun bid =>
           omap
             (sigma_from_smaller_dom (metadata_size_lhs - metadata_size_rhs))
             (Some bid)
    else sigma_from_bigger_dom_option (metadata_size_rhs - metadata_size_lhs).
   ***********************************************)

  Definition sigma_shifting_lefttoright_option (b: Block.id) : option Block.id :=
    if b >= metadata_size_lhs
    then Some (b - metadata_size_lhs + metadata_size_rhs)
    else None.

  Definition sigma_shifting_righttoleft_option (b: Block.id) : option Block.id :=
    if b >= metadata_size_rhs
    then Some (b - metadata_size_rhs + metadata_size_lhs)
    else None.
  
  
  Lemma sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some
        bidl bidr:
    sigma_shifting_lefttoright_option bidl = Some bidr ->
    sigma_shifting_righttoleft_option bidr = Some bidl.
  Proof.
    unfold sigma_shifting_righttoleft_option, sigma_shifting_lefttoright_option.
    destruct (metadata_size_lhs <= bidl) eqn:elhs; try discriminate.
    intros Hbidr. inversion Hbidr. subst. clear Hbidr.
    destruct (metadata_size_rhs <= bidl - metadata_size_lhs + metadata_size_rhs)
             eqn:e.
    - by rewrite addnK subnK.
    - rewrite addnBAC in e; auto.
      rewrite addnC in e.
      rewrite <- addnBA in e; auto.
      by rewrite <- leq_subLR, subnn in e.
  Qed.

  (*****************************************
  destruct (metadata_size_rhs <= metadata_size_lhs) eqn:e; intros Hlr.
    - specialize (ocancel_sigma_from_bigger_dom_option_sigma_from_smaller_dom
                    (metadata_size_lhs - metadata_size_rhs)
                 ) as Hcan.
      unfold ocancel, oapp in Hcan.
      specialize (Hcan bidl). rewrite Hlr in Hcan.
      unfold omap, obind, oapp. by rewrite Hcan.
    - specialize (pcancel_sigma_from_smaller_dom_sigma_from_bigger_dom_option
                    (metadata_size_rhs - metadata_size_lhs)
                 ) as Hcan.
      unfold omap, obind, oapp in Hlr. inversion Hlr. subst.
      unfold pcancel in Hcan. by apply Hcan.
  Qed.
   **********************************************)

  Lemma sigma_shifting_righttoleft_option_Some_sigma_shifting_lefttoright_option_Some
        bidl bidr:
    sigma_shifting_righttoleft_option bidr = Some bidl ->
    sigma_shifting_lefttoright_option bidl = Some bidr.
  Proof.
    unfold sigma_shifting_righttoleft_option, sigma_shifting_lefttoright_option.
    destruct (metadata_size_rhs <= bidr) eqn:elhs; try discriminate.
    intros Hbidr. inversion Hbidr. subst. clear Hbidr.
    destruct (metadata_size_lhs <= bidr - metadata_size_rhs + metadata_size_lhs)
             eqn:e.
    - by rewrite addnK subnK.
    - rewrite addnBAC in e; auto.
      rewrite addnC in e.
      rewrite <- addnBA in e; auto.
      by rewrite <- leq_subLR, subnn in e.
  Qed.

  (**************************************************
  Proof.
    unfold sigma_shifting_righttoleft_option, sigma_shifting_lefttoright_option.
    destruct (metadata_size_rhs <= metadata_size_lhs) eqn:e; intros Hlr.
    - specialize (pcancel_sigma_from_smaller_dom_sigma_from_bigger_dom_option
                    (metadata_size_lhs - metadata_size_rhs)
                 ) as Hcan.
      unfold omap, obind, oapp in Hlr. inversion Hlr. subst.
      unfold pcancel in Hcan. by apply Hcan.
    - specialize (ocancel_sigma_from_bigger_dom_option_sigma_from_smaller_dom
                    (metadata_size_rhs - metadata_size_lhs)
                 ) as Hcan.
      unfold ocancel, oapp in Hcan.
      specialize (Hcan bidr). rewrite Hlr in Hcan.
      unfold omap, obind, oapp. by rewrite Hcan.
  Qed.
   ********************************************************)

  Definition left_block_id_good_for_shifting (bid: Block.id) : Prop :=
    bid >= metadata_size_lhs.

  Definition right_block_id_good_for_shifting (bid: Block.id) : Prop :=
    bid >= metadata_size_rhs.
  
  Lemma sigma_lefttoright_Some_spec lbid:
    left_block_id_good_for_shifting lbid
    <->
    (exists rbid, sigma_shifting_lefttoright_option lbid = Some rbid).
  Proof.
    unfold left_block_id_good_for_shifting, sigma_shifting_lefttoright_option.
    destruct (metadata_size_lhs <= lbid) eqn:elhs; intuition.
    - by eexists.
    - by destruct H.
  Qed.

  Lemma sigma_righttoleft_Some_spec lbid:
    right_block_id_good_for_shifting lbid
    <->
    (exists rbid, sigma_shifting_righttoleft_option lbid = Some rbid).
  Proof.
    unfold right_block_id_good_for_shifting, sigma_shifting_righttoleft_option.
    destruct (metadata_size_rhs <= lbid) eqn:elhs; intuition.
    - by eexists.
    - by destruct H.
  Qed.

  Lemma sigma_lefttoright_Some_good lbid rbid:
    sigma_shifting_lefttoright_option lbid = Some rbid ->
    right_block_id_good_for_shifting rbid.
  Proof.
    intros Hsome.
    apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in Hsome.
    rewrite sigma_righttoleft_Some_spec.
      by eexists; eauto.
  Qed.

  
  Lemma sigma_righttoleft_Some_good lbid rbid:
    sigma_shifting_righttoleft_option rbid = Some lbid ->
    left_block_id_good_for_shifting lbid.
  Proof.
    intros Hsome.
    apply sigma_shifting_righttoleft_option_Some_sigma_shifting_lefttoright_option_Some in Hsome.
    rewrite sigma_lefttoright_Some_spec.
      by eexists; eauto.
  Qed.

  
  
  (****************************************************
  Lemma sigma_lefttoright_Some_spec lbid:
    lbid >= (metadata_size_lhs - metadata_size_rhs)
    (* This condition is strictly weaker than the goodness condition. *)
    <->
    (exists rbid, sigma_shifting_lefttoright_option lbid = Some rbid).
  Proof.
    unfold sigma_shifting_lefttoright_option, sigma_from_bigger_dom_option,
    sigma_from_smaller_dom.
    split.
    - intros Hlbid.
      destruct (metadata_size_rhs <= metadata_size_lhs) eqn:eextra.
      + assert (lbid <? metadata_size_lhs - metadata_size_rhs = false) as H.
        by apply Nat.ltb_ge; apply/leP.
        rewrite H. by eexists.
      + eexists. unfold omap, obind, oapp. intuition.
    - intros [rbid esigma].
      destruct (metadata_size_rhs <= metadata_size_lhs) eqn:eextra.
      + destruct (lbid <? metadata_size_lhs - metadata_size_rhs) eqn:G;
          try discriminate.
        by apply/leP; apply Nat.ltb_ge.
      + assert (metadata_size_lhs <= metadata_size_rhs) as G.
        {
          apply ltnW. rewrite leqNgt in eextra. unfold negb in *.
          by destruct (metadata_size_lhs < metadata_size_rhs).
        }
        rewrite <- subn_eq0 in G.
        assert (metadata_size_lhs - metadata_size_rhs = 0) as rewr. by apply/eqP.
        by rewrite rewr.
  Qed.

  Lemma sigma_lefttoright_good_Some lbid:
    left_block_id_good_for_shifting lbid ->
    exists rbid, sigma_shifting_lefttoright_option lbid = Some rbid /\
                 right_block_id_good_for_shifting rbid.
  Proof.
    unfold left_block_id_good_for_shifting in *. intros.
    assert (metadata_size_lhs - metadata_size_rhs <= lbid) as G1.
    {
        by apply leq_trans with (n := metadata_size_lhs); auto; apply leq_subr.
    }
    specialize (sigma_lefttoright_Some_spec lbid) as [G _].
    specialize (G G1) as [rbid Hrbid].
    eexists; split; eauto.
    unfold sigma_shifting_lefttoright_option, sigma_from_bigger_dom_option,
    sigma_from_smaller_dom, right_block_id_good_for_shifting in *.
    destruct (metadata_size_rhs <= metadata_size_lhs) eqn:rhslhs.
    - destruct (lbid <? metadata_size_lhs - metadata_size_rhs); try discriminate.
      inversion Hrbid.
      rewrite subnBA; auto.
      rewrite <- addnBAC; auto.
      rewrite <- add0n at 1.
      by rewrite leq_add2r.
    - inversion Hrbid.
      rewrite addnBCA; auto.
      + by apply leq_addr.
      + specialize (le_false_lt _ _ rhslhs).
        by apply ltnW.
  Qed.
    
  Lemma sigma_righttoleft_Some_spec rbid:
    rbid >= (metadata_size_rhs - metadata_size_lhs) <->
    (exists lbid, sigma_shifting_righttoleft_option rbid = Some lbid).
  Proof.
    unfold sigma_shifting_righttoleft_option, sigma_from_bigger_dom_option,
    sigma_from_smaller_dom.    
    split.
    - intros Hrbid.
      destruct (metadata_size_rhs <= metadata_size_lhs) eqn:eextra.
      + by eexists.
      + assert (rbid <? metadata_size_rhs - metadata_size_lhs = false) as H.
        by apply Nat.ltb_ge; apply/leP.
        rewrite H. by eexists.
    - intros [lbid esigma].
      destruct (metadata_size_rhs <= metadata_size_lhs) eqn:eextra.
      + rewrite <- subn_eq0 in eextra.
        assert (metadata_size_rhs - metadata_size_lhs = 0) as rewr. by apply/eqP.
        by rewrite rewr.
      + destruct (rbid <? metadata_size_rhs - metadata_size_lhs) eqn:erbid;
          try discriminate.
        by apply/leP; apply Nat.ltb_ge.
  Qed.

  Lemma sigma_righttoleft_good_Some rbid:
    right_block_id_good_for_shifting rbid ->
    exists lbid, sigma_shifting_righttoleft_option rbid = Some lbid /\
                 left_block_id_good_for_shifting lbid.
  Proof.
    unfold right_block_id_good_for_shifting in *. intros.
    assert (metadata_size_rhs - metadata_size_lhs <= rbid) as G1.
    {
        by apply leq_trans with (n := metadata_size_rhs); auto; apply leq_subr.
    }
    specialize (sigma_righttoleft_Some_spec rbid) as [G _].
    specialize (G G1) as [lbid Hlbid].
    eexists; split; eauto.
    unfold sigma_shifting_righttoleft_option, sigma_from_bigger_dom_option,
    sigma_from_smaller_dom, left_block_id_good_for_shifting in *.
    destruct (metadata_size_rhs <= metadata_size_lhs) eqn:rhslhs.
    - inversion Hlbid.
      rewrite addnBCA; auto.
      + by apply leq_addr.
      
    - destruct (rbid <? metadata_size_rhs - metadata_size_lhs); try discriminate.
      inversion Hlbid.
      rewrite subnBA; auto.
      + rewrite <- addnBAC; auto.
        rewrite <- add0n at 1.
          by rewrite leq_add2r.
      + specialize (le_false_lt _ _ rhslhs).
          by apply ltnW.
  Qed.
  ******************************************************************)

  
  Lemma sigma_shifting_lefttoright_option_Some_inj bid1 bid2 bid_shift:
    sigma_shifting_lefttoright_option bid1 = Some bid_shift ->
    sigma_shifting_lefttoright_option bid2 = Some bid_shift ->
    bid1 = bid2.
  Proof.
    intros Hsigma1 Hsigma2.
    unfold sigma_shifting_lefttoright_option in *.
    destruct (metadata_size_lhs <= bid1) eqn:ebid1; try discriminate.
    destruct (metadata_size_lhs <= bid2) eqn:ebid2; try discriminate.
    inversion Hsigma1. subst. inversion Hsigma2 as [G].
    
    assert (bid2 - metadata_size_lhs = bid1 - metadata_size_lhs) as G'.
      by
        apply/eqP;
        rewrite <- eqn_add2r with (p := metadata_size_rhs);
        rewrite G eqxx.
    by eapply subn_eq_subn_cancel; eauto.  
  Qed.
  
End SigmaShiftingBlockIds.


Section SigmaShiftingBlockIdsOptionProperties.
  
  (***************************************************
  Lemma sigma_from_bigger_dom_option_0_id x: sigma_from_bigger_dom_option 0 x = Some x.
  Proof. unfold sigma_from_bigger_dom_option. destruct x; by intuition. Qed.
  
  Lemma sigma_from_smaller_dom_0_id x:
    sigma_from_smaller_dom 0 x = x.
  Proof. unfold sigma_from_smaller_dom. by rewrite addn0. Qed.
  ********************************************************)

  Lemma sigma_shifting_lefttoright_option_n_n_id:
    forall n x y, sigma_shifting_lefttoright_option n n x = Some y ->
             y = x.
  Proof. intros n x y H. unfold sigma_shifting_lefttoright_option in *.
         destruct (n <= x) eqn:e; try discriminate.
         inversion H. subst. by rewrite subnK; auto.
  Qed.

  Lemma sigma_shifting_righttoleft_option_n_n_id:
    forall n x y, sigma_shifting_righttoleft_option n n x = Some y ->
             y = x.
  Proof. intros n x y H. unfold sigma_shifting_righttoleft_option in *.
         destruct (n <= x) eqn:e; try discriminate.
         inversion H. subst. by rewrite subnK; auto.
  Qed.

  Lemma sigma_shifting_lefttoright_option_id_n_n:
    forall n1 n2 x, sigma_shifting_lefttoright_option n1 n2 x = Some x -> n1 = n2.
  Proof.
    intros n1 n2 bid H.
    unfold sigma_shifting_lefttoright_option in *.
    destruct (n1 <= bid) eqn:e; try discriminate.
    inversion H as [G].
    destruct (n1 <= n2) eqn:en1n2.
  Abort.

  (*****       !!!!!    DO NOT DELETE   !!!!!    ********)
  (***** We may take inspiration from this proof ********)
  (*****
    unfold sigma_shifting_lefttoright_option, sigma_from_bigger_dom_option,
    sigma_from_smaller_dom.
    intros Hbid.
    destruct (n2 <= n1) eqn:en1n2.
    - destruct (bid <? n1 - n2) eqn:ebid; try discriminate.
      inversion Hbid as [H].
      specialize (subn_n_m_n_0 _ _ H) as [H1|H2].
      + assert (n1 <= n2) as H_antisym. by rewrite <- subn_eq0; apply/eqP.
        apply Nat.le_antisymm; apply/leP; auto.
      + subst.
        rewrite -> Nat.ltb_ge in ebid.
        assert (n1 - n2 <= 0) as ebid'. by apply/leP.
        rewrite leqn0 in ebid'. assert (n1 - n2 = 0). by apply/eqP.
        assert (n1 <= n2) as H_antisym. by rewrite <- subn_eq0; apply/eqP.
        apply Nat.le_antisymm; apply/leP; auto.
    - simpl in Hbid. inversion Hbid.
      destruct (n2 - n1) eqn:n2n1.
      + assert (n2 <= n1) as Hcontra. by rewrite <- subn_eq0; apply/eqP.
        by rewrite Hcontra in en1n2.
      + rewrite addnS in H0.
        assert ((bid + n).+1 > (bid + n)) as Hcontra. by intuition.
        assert (bid > bid + n) as Hcontra'. by rewrite <- H0 at 2.
        specialize (leq_addr n bid) as Hcontra''.
        specialize (leq_gtF Hcontra'') as rewr. by rewrite rewr in Hcontra'.
  Qed.
   ******)

  Lemma sigma_shifting_righttoleft_lefttoright:
    forall n1 n2 x,
      sigma_shifting_righttoleft_option n1 n2 x =
      sigma_shifting_lefttoright_option n2 n1 x.
  Proof.
    intros n1 n2 bid.
      by unfold sigma_shifting_righttoleft_option,
         sigma_shifting_lefttoright_option.
  Qed.

  Corollary sigma_shifting_righttoleft_lefttoright_partially_applied:
    forall n1 n2,
      sigma_shifting_righttoleft_option n1 n2 = sigma_shifting_lefttoright_option n2 n1.
  Proof. intros.
         apply functional_extensionality, sigma_shifting_righttoleft_lefttoright.
  Qed.

  Lemma sigma_shifting_lefttoright_transitive n1 n2 n3 bid1 bid2 bid3:
    sigma_shifting_lefttoright_option n1 n2 bid1 = Some bid2 ->
    sigma_shifting_lefttoright_option n2 n3 bid2 = Some bid3 ->
    sigma_shifting_lefttoright_option n1 n3 bid1 = Some bid3.
  Proof.
    intros Hsigma12 Hsigma23.
    unfold sigma_shifting_lefttoright_option in *.
    destruct (n1 <= bid1) eqn:e1; try discriminate.
    destruct (n2 <= bid2) eqn:e2; try discriminate.
    inversion Hsigma12. subst. clear Hsigma12.
    inversion Hsigma23. subst. clear Hsigma23.
    assert (bid1 - n1 + n2 - n2 + n3 = n3 + (bid1 - n1 + n2 - n2)) as Hrewr.
      by rewrite addnC.
    rewrite -> addnC, Hrewr, <- addnBA, subnn, addn0; auto.
  Qed.
    
    (*******************************************************
    destruct (n3 <= n2) eqn:n2n3;
      destruct (n2 <= n1) eqn:n1n2;
      destruct (n3 <= n1) eqn:n1n3.
    - (* n1 >= n2, n2 >= n3, thus n1 >= n3  *)
      destruct (bid1 <? n1 - n2) eqn:ebid1cond;
        try discriminate.
      destruct (bid2 <? n2 - n3) eqn:ebid2cond;
        try discriminate.
      inversion Hsigma12. subst. inversion Hsigma23. subst. clear Hsigma12 Hsigma23.

      assert (bid1 <? (n1 - n3) = false) as G. by rewrite Nat.ltb_ge; apply/leP.
      rewrite G. 
      
      rewrite <- subnDA, addnBA; try by apply/leP.
      + by rewrite subnK; try by apply/leP.
      + assumption.


    - assert (n3 <= n1) as H.
        by apply/leP; apply le_trans with (m := n2); eauto; apply/leP.
      by rewrite H in n1n3. 
    - (* n1 >= n3, n2 >= n3, n1 ~>= n2, i.e., n2 > n1 *)
      destruct (bid2 <? n2 - n3) eqn:Hbid2_n2_n3'; try discriminate.
      inversion Hsigma23. subst. clear Hsigma23. simpl in *.
      inversion Hsigma12. subst. clear Hsigma12.
      assert (n1 < n2) as G. by apply le_false_lt.
      assert (n1 <= n2) as n1n2'. by intuition.
      assert (bid1 <? n1 - n3 = false) as Hfalse.
      {
        rewrite Nat.ltb_ge. by apply/leP.
      }
      rewrite Hfalse.
      rewrite !subnBA; auto.
      rewrite addnAC.
      rewrite addnBA; auto.
      rewrite <- subnAC, <- subnDA.
      assert (n2 + n1 = n1 + n2) as rewr. by rewrite addnC.
      by rewrite rewr subnDr.
    - (* n2 >= n3, n1 ~>= n3 ==> n1 < n3, n1 ~>= n2 ==> n1 < n2 *)
      simpl in *. inversion Hsigma12. subst. clear Hsigma12.
      destruct (bid1 + (n2 - n1) <? n2 - n3) eqn:e; try discriminate.
      inversion Hsigma23. subst. clear Hsigma23.
      assert (n1 < n2) as n1n2'. by apply le_false_lt.
      assert (n1 < n3) as n1n3'. by apply le_false_lt.
      rewrite !subnBA; auto.
      rewrite addnAC.
      rewrite !addnBA; auto.
      rewrite <- subnAC, <- subnDA.
      assert (n2 + n1 = n1 + n2) as rewr. by rewrite addnC.
      by rewrite rewr subnDr.
    - (* n1 >= n2, n1 >= n3, n2 ~>= n3 ==> n3 >= n2 *)
      assert (n2 < n3). by apply le_false_lt.
      simpl in *. inversion Hsigma23. subst. clear Hsigma23.
      destruct (bid1 <? n1 - n2) eqn:e; try discriminate. 
      inversion Hsigma12. subst. clear Hsigma12.
      assert (bid1 <? n1 - n3 = false) as Hfalse.
      {
        rewrite Nat.ltb_ge. by apply/leP.
      }
      rewrite Hfalse.
      rewrite !subnBA; auto.
      rewrite !addnBA; auto.
      rewrite addnBAC.
      + rewrite <- addnA.
        assert (n3 + n2 = n2 + n3) as rewr. by rewrite addnC.
        rewrite <- rewr. rewrite addnA.
        rewrite <- subnAC, <- subnDA.
        assert (n2 + n1 = n1 + n2) as rewr'. by rewrite addnC.
        by rewrite rewr' subnDr.
      + erewrite <- leq_add2r in Hbid1_n1_n2.
        erewrite subnK in Hbid1_n1_n2; intuition.
    - (* n2 <= n1, n2 !>= n3 ==> n2 <= n3, n1 !>= n3 ==> n1 <= n3 *)
      assert (n2 < n3) as n2n3'. by apply le_false_lt.
      assert (n1 < n3) as n1n3'. by apply le_false_lt.
      simpl in *. inversion Hsigma23. subst. clear Hsigma23.
      destruct (bid1 <? n1 - n2) eqn:e; try discriminate.
      inversion Hsigma12. subst. clear Hsigma12.
      rewrite !subnBA; auto.
      rewrite !addnBA; auto.
      rewrite addnBAC.
      + rewrite <- addnA.
        assert (n3 + n2 = n2 + n3) as rewr. by rewrite addnC.
        rewrite <- rewr. rewrite addnA.
        rewrite <- subnAC, <- subnDA.
        assert (n2 + n1 = n1 + n2) as rewr'. by rewrite addnC.
        by rewrite rewr' subnDr.
      + erewrite <- leq_add2r in Hbid1_n1_n2.
        erewrite subnK in Hbid1_n1_n2; intuition.
    - (* n1 !>= n2 ==> n1 < n2, n2 !>= n3 ==> n2 < n3, n1 >= n3 *)
      assert (n1 < n2) as n1n2'. by apply le_false_lt.
      assert (n2 < n3) as n2n3'. by apply le_false_lt.
      assert (n1 < n3)%coq_nat as contra.
      { apply lt_trans with (m := n2); by apply/ltP. }
      assert (n3 <= n1)%coq_nat as n1n3_. by apply/leP.
      specialize (leb_correct _ _ n1n3_) as n1n3__.
      specialize (leb_correct_conv _ _ contra) as contra_.
      by rewrite contra_ in n1n3__.
    - assert (n1 < n2) as n1n2'. by apply le_false_lt.
      assert (n2 < n3) as n2n3'. by apply le_false_lt.
      assert (n1 < n3) as n1n3'. by apply le_false_lt.
      simpl in *. inversion Hsigma12. subst. clear Hsigma12.
      inversion Hsigma23. subst. clear Hsigma23.
      rewrite <- addnA.
      assert (n2 - n1 + (n3 - n2) = (n3 - n2) + (n2 - n1)) as rewr. by rewrite addnC.
      rewrite rewr addnA.
      rewrite !addnBA; auto.
      rewrite subnK; auto.
      apply leq_trans with (n := n3); intuition.
      + by apply leq_addl.
  Qed.
     *****************************************************************)

  Lemma sigma_shifting_lefttoright_Some_inv_Some n1 n2 bid1 bid2:
    sigma_shifting_lefttoright_option n1 n2 bid1 = Some bid2 ->
    sigma_shifting_lefttoright_option n2 n1 bid2 = Some bid1.
  Proof.
    unfold sigma_shifting_lefttoright_option.
    destruct (n1 <= bid1) eqn:ebid1; try discriminate.
    intros H. inversion H. subst. clear H.

    destruct (n2 <= bid1 - n1 + n2) eqn:contra.
    - by rewrite addnK subnK.
    - rewrite <- add0n in contra at 1.
        by rewrite leq_add2r in contra.
  Qed.

  Lemma sigma_shifting_lefttoright_option_None_None n1 n2 n3 bid:
    sigma_shifting_lefttoright_option n1 n2 bid = None ->
    sigma_shifting_lefttoright_option n1 n3 bid = None.
  Proof.
    intros HNone.
    destruct (sigma_shifting_lefttoright_option n1 n3 bid) as [bid'|] eqn:esigma; auto.
    assert (Hgood: left_block_id_good_for_shifting n1 bid).
    {
      by eapply sigma_lefttoright_Some_spec; eexists; eauto.
    }
    eapply sigma_lefttoright_Some_spec in Hgood. 
    destruct Hgood as [? contra].
    by erewrite HNone in contra.
  Qed. 
      
End SigmaShiftingBlockIdsOptionProperties.

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
    if Permission.eqb perm Permission.data then fset1 (cid, bid) else fset0
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
    forall cid bid offset cid_l bid_l o,
      good_addr (cid, bid) ->
      Memory.load m (Permission.data, cid, bid, offset) =
      Some (Ptr (Permission.data, cid_l, bid_l, o)) ->
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
      apply good_memory_mem with (cid := cid) (bid := bid) (offset := i)
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


Section GoodTraceExtensional.

  Variable good_addr: addr_t -> Prop.

  Inductive good_trace_extensional : trace event -> Prop :=
  | all_shared_is_good:
      forall t,
        (forall a, addr_shared_so_far a t -> good_addr a) ->
        good_trace_extensional t.
  
End GoodTraceExtensional.

Section RenamingAddrOption.

  (** Address renamings are simply applications of given address maps. *)

  Variable sigma: addr_t -> option addr_t (*{fmap addr_t -> addr_t}*).

  (*Variable inverse_sigma: addr_t -> addr_t.*)
  Variable left_addr_good: addr_t -> Prop.
  Variable right_addr_good: addr_t -> Prop.

  Definition rename_addr_option (addr: addr_t) : option addr_t := sigma addr.
  (*  match sigma addr with
  | Some addr' => addr'
  | None => addr
  end.
   *)

  (*Definition inverse_rename_addr (addr: addr_t) := inverse_sigma addr.*)

  (** Value renamings apply address renamings to rich pointer values, leaving
      all other values unchanged. *)

  Definition rename_value_template_option
             (rnm_addr : addr_t -> option addr_t) (v: value) : option value :=
    match v with
    | Ptr (perm, cid, bid, off) =>
      if (Permission.eqb perm Permission.data) then (*rename only addresses that are loadable*)
        let oa := rnm_addr (cid, bid) in
        match oa with
        | Some (cid', bid') => Some (Ptr (perm, cid', bid', off))
        | None => None
        end
      else
        Some v
    | _ => Some v
    end.

  Definition rename_value_option : value -> option value :=
    rename_value_template_option rename_addr_option.

  Lemma rename_value_option_arg_Int i:
    rename_value_option (Int i) = Some (Int i).
      by simpl.
  Qed.

  Lemma rename_value_option_res_Int v i:
    rename_value_option v = Some (Int i) -> v = Int i.
  Proof.
    destruct v as [| [[[perm c] b] o] |]; try discriminate; simpl.
    - by intros H; inversion H.
    - by destruct (Permission.eqb perm Permission.data); try discriminate;
        destruct (rename_addr_option (c, b)) as [[c' b']|]; discriminate.
  Qed.
  
  Lemma rename_value_option_arg_Undef:
    rename_value_option Undef = Some Undef.
      by simpl.
  Qed.

  Lemma rename_value_option_res_Undef v:
    rename_value_option v = Some Undef -> v = Undef.
  Proof.
    destruct v as [| [[[perm c] b] o] |]; try discriminate; simpl.
    - by destruct (Permission.eqb perm Permission.data); try discriminate;
        destruct (rename_addr_option (c, b)) as [[c' b']|]; discriminate.
    - by intros H; inversion H.  
  Qed.
  
  Lemma rename_value_option_arg_Ptr p:
    exists p', rename_value_option (Ptr p) = Some (Ptr p') /\
               Pointer.permission p = Pointer.permission p' /\
               Pointer.component p = Pointer.component p' /\
               Pointer.offset p = Pointer.offset p'.
  Admitted.

  Lemma rename_value_option_res_Ptr v p':
    rename_value_option v = Some (Ptr p') ->
    exists p,
      v = Ptr p /\
      Pointer.permission p = Pointer.permission p' /\
      Pointer.component p = Pointer.component p' /\
      Pointer.offset p = Pointer.offset p'.
  Admitted.
  

  
  
  (*Definition inverse_rename_value : value -> value :=
    rename_value_template inverse_rename_addr.*)

  (** Various liftings of value renamings. *)

  Definition rename_list_values_option : list value -> list (option value) :=
    map rename_value_option.

  (*Definition inverse_rename_list_values : list value -> list value :=
    map inverse_rename_value.*)

  (*Definition option_rename_value_option option_v : option value :=
    obind rename_value_option option_v.*)

  (*Definition option_inverse_rename_value option_v :=
    omap inverse_rename_value option_v.*)

  (** Given the current state of the memory at two given events, these
      properties are satisfied for a given memory block iff all loads on renamed
      addresses in the second memory equal the lifted renaming of the loads on
      the original addresses in the first memory. *)

End RenamingAddrOption.


Section TheShiftRenamingAddrOption.

  (** Shift renaming on a given component with given numbers of additional
      metadata blocks. *)

  Variable metadata_size_lhs_per_cid: Component.id -> nat.
  Variable metadata_size_rhs_per_cid: Component.id -> nat.

  (** Functions to return the new address after shifting the block identifier. *)

  Definition sigma_shifting_lefttoright_addr_bid (a: addr_t) : option Block.id :=
    let (cid, bid) := a in
    let metadata_size_lhs := metadata_size_lhs_per_cid cid in
    let metadata_size_rhs := metadata_size_rhs_per_cid cid in
    sigma_shifting_lefttoright_option metadata_size_lhs metadata_size_rhs bid.


  Definition sigma_shifting_righttoleft_addr_bid (a: addr_t) : option Block.id :=
    let (cid, bid) := a in
    let metadata_size_lhs := metadata_size_lhs_per_cid cid in
    let metadata_size_rhs := metadata_size_rhs_per_cid cid in
    sigma_shifting_righttoleft_option metadata_size_lhs metadata_size_rhs bid.

  Definition sigma_shifting_wrap_bid_in_addr
             (sigma: addr_t -> option Block.id) (a: addr_t) : option addr_t :=
    match sigma a with
    | Some bid => Some (a.1, bid)
    | None => None
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
      if Permission.eqb perm Permission.data then
        left_addr_good_for_shifting (cid, bid)
      else True
    | _ => True
    end.

  Definition right_value_good_for_shifting (v: value) : Prop :=
    match v with
    | Ptr (perm, cid, bid, _) =>
      if Permission.eqb perm Permission.data then
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

End TheShiftRenamingAddrOption.

Section MemoryAndTraceRenaming.

  Variable n n': Component.id -> nat.

  Let rename_addr_option :=
    sigma_shifting_wrap_bid_in_addr
      (sigma_shifting_lefttoright_addr_bid n n').
  Let inverse_rename_addr_option :=
    sigma_shifting_wrap_bid_in_addr
      (sigma_shifting_lefttoright_addr_bid n' n).
  Let left_addr_good := left_addr_good_for_shifting n.
  Let right_addr_good := right_addr_good_for_shifting n'.
  
  Definition memory_renames_memory_at_shared_addr addr m m' : Prop :=
    exists addr',
      rename_addr_option addr = Some addr'
      /\
      (
        forall offset v,
          Memory.load m (Permission.data, addr.1, addr.2, offset) = Some v ->
          (
            exists v',
              Memory.load m' (Permission.data, addr'.1, addr'.2, offset) = Some v'
              /\
              rename_value_option rename_addr_option v = Some v'
          )
      )
      /\
      (
        forall offset v',
          Memory.load m' (Permission.data, addr'.1, addr'.2, offset) = Some v' ->
          (
            exists v,
              Memory.load m (Permission.data, addr.1, addr.2, offset) = Some v
              /\
              rename_value_option rename_addr_option v = Some v'
          )
      ).

  (**********************************************
  Definition memory_renames_memory_at_private_addr addr m1 m2 : Prop :=
    (
      forall offset v,
        Memory.load m1 (Permission.data, addr.1, addr.2, offset) = Some v ->
        (
          Memory.load m2 (Permission.data, addr.1, addr.2, offset) =
          match rename_value_option rename_addr_option v with
          | Some v' => Some v'
          | None => Some v
          end
        )
    )
    /\
    (
      forall offset v',
        Memory.load m2 (Permission.data, addr.1, addr.2, offset) = Some v' ->
        (
          exists v,
            Memory.load m1 (Permission.data, addr.1, addr.2, offset) = Some v
            /\
            ((rename_value_option rename_addr_option v = None /\ v = v')
             \/ rename_value_option rename_addr_option v = Some v')
        )
    ).
    *****************************************************)

    Definition memory_renames_memory_at_private_addr addr m1 m2 : Prop :=
    (
      forall offset v,
        Memory.load m1 (Permission.data, addr.1, addr.2, offset) = Some v ->
        (
          match rename_value_option rename_addr_option v with
          | Some v' =>
            Memory.load m2 (Permission.data, addr.1, addr.2, offset) =
            Some v'
          | None =>
            Memory.load m2 (Permission.data, addr.1, addr.2, offset) =
            Some v
            /\
            rename_value_option inverse_rename_addr_option v = None
          end
        )
    )
    /\
    (
      forall offset v',
        Memory.load m2 (Permission.data, addr.1, addr.2, offset) = Some v' ->
        (
          exists v,
            Memory.load m1 (Permission.data, addr.1, addr.2, offset) = Some v
            /\
            (
              (rename_value_option rename_addr_option v = None /\
               rename_value_option inverse_rename_addr_option v' = None /\
               v = v'
              )
              \/
              rename_value_option rename_addr_option v = Some v'
            )
        )
    ).


  Definition event_renames_event_at_shared_addr addr e e' : Prop :=
    memory_renames_memory_at_shared_addr addr (mem_of_event e) (mem_of_event e').

 (* Definition event_inverse_renames_event_at_addr addr' e e' : Prop :=
    memory_inverse_renames_memory_at_addr addr' (mem_of_event e) (mem_of_event e').*)
      
  
  (** Two traces are mutual renamings iff all pointwise event pairs satisfy the
      event renaming property on shared addresses. The "forward" address map is
      applied to the first trace and the inverse map is applied to the second
      trace, and these maps preserve shared addresses on the traces. *)

  (* RB: NOTE: [DynShare] Would it be useful to have a trace renaming relation
     and use that to build a mutual relation? *)

  (***********************************************************************
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
****************************************************************************)

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
  
  Inductive traces_rename_each_other_option :
    trace event -> trace event -> Prop :=
  | nil_renames_nil_option: traces_rename_each_other_option nil nil
  | rcons_renames_rcons_option:
      forall tprefix e tprefix' e' v',
        traces_rename_each_other_option tprefix tprefix' ->
        (
          forall addr, addr_shared_so_far addr (rcons tprefix e) ->
                       (
                         event_renames_event_at_shared_addr addr e e'
                         /\
                         exists addr',
                           rename_addr_option addr = Some addr'
                           /\
                           addr_shared_so_far addr' (rcons tprefix' e')
                       )
        )
        ->
        (
          forall addr', addr_shared_so_far addr' (rcons tprefix' e') ->
                        (
                          exists addr,
                            rename_addr_option addr = Some addr'
                            /\
                            event_renames_event_at_shared_addr addr e e'
                            /\
                            addr_shared_so_far addr (rcons tprefix e)
                        )
        )
        ->
        match_events e e' ->
        rename_value_option rename_addr_option (arg_of_event e) = Some v' ->
        arg_of_event e' = v' ->
        (*arg_of_event e  = inverse_rename_value (arg_of_event e') ->*)
        good_trace_extensional left_addr_good (rcons tprefix e) ->
        good_trace_extensional (right_addr_good) (rcons tprefix' e') ->
        traces_rename_each_other_option (rcons tprefix e) (rcons tprefix' e').


  Lemma traces_rename_each_other_option_nil_rcons t x:
    traces_rename_each_other_option [::] (rcons t x) -> False.
  Proof. intros H. inversion H as [y Hy|tp e ? ? ? ? ? ? ? ? ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- Hy. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp e) = 0) as Hcontra.
           { rewrite Ha. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_option_rcons_nil t x:
    traces_rename_each_other_option (rcons t x) [::] -> False.
  Proof. intros H. inversion H as [y Hy|tp e tp' e' ? ? ? ? ? ? ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- y. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp' e') = 0) as Hcontra.
           { rewrite Hb. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_option_same_size t1 t2:
    traces_rename_each_other_option t1 t2 -> size t1 = size t2.
  Proof.
    intros H. induction H as [ |tp e tp' e' ? ? ? ? Ha]; auto.
      by rewrite !size_rcons IHtraces_rename_each_other_option.
  Qed.


End MemoryAndTraceRenaming.


Section TheShiftRenamingAddrOption.

  (** Shift renaming on a given component with given numbers of additional
      metadata blocks. *)

  Variable metadata_size_lhs_per_cid: Component.id -> nat.
  Variable metadata_size_rhs_per_cid: Component.id -> nat.

  
  (** A pair of traces are mutual shiftings of one another if they are
      renamings, as defined above. *)

  Inductive traces_shift_each_other_option : trace event -> trace event -> Prop :=
  | shifting_is_special_case_of_renaming_option:
      forall t t',
        traces_rename_each_other_option
          (*(sigma_shifting_wrap_bid_in_addr sigma_shifting_lefttoright_addr_bid)
          (left_addr_good_for_shifting)
          (right_addr_good_for_shifting)*)
          metadata_size_lhs_per_cid
          metadata_size_rhs_per_cid
          t
          t' ->
        (*
        (* symmetric by definition *)
        traces_rename_each_other
          inv_sigma_shifting_addr
          sigma_shifting_addr
          right_addr_good_for_shifting
          left_addr_good_for_shifting
          t'
          t ->*)
        traces_shift_each_other_option t t'.

  (* For use in the state invariant *)

  Definition shift_value_option (v: value) : option value :=
    rename_value_option (rename_addr_option
                           (sigma_shifting_wrap_bid_in_addr
                              (sigma_shifting_lefttoright_addr_bid
                                 metadata_size_lhs_per_cid
                                 metadata_size_rhs_per_cid
                              )
                           )
                        ) v.
  
  (*Definition inverse_shift_value (v': value) : value :=
    inverse_rename_value (inverse_rename_addr inv_sigma_shifting_addr) v'.*)
  
  Definition memory_shifts_memory_at_shared_addr (addr: addr_t) m m' : Prop :=
    memory_renames_memory_at_shared_addr
      metadata_size_lhs_per_cid
      metadata_size_rhs_per_cid
      addr
      m
      m'.

  Definition memory_shifts_memory_at_private_addr (addr: addr_t) m m' : Prop :=
    memory_renames_memory_at_private_addr
      metadata_size_lhs_per_cid
      metadata_size_rhs_per_cid
      addr
      m
      m'.

  (*Definition memory_inverse_shifts_memory_at_addr (addr': addr_t) m m' : Prop :=
    memory_inverse_renames_memory_at_addr
      (inverse_rename_addr inv_sigma_shifting_addr) addr' m m'.*)

End TheShiftRenamingAddrOption.


Section PropertiesOfTheShiftRenamingAddrOption.

  Lemma shift_value_option_symmetry n1 n2 v v':
    shift_value_option n1 n2 v = Some v' -> shift_value_option n2 n1 v' = Some v.
  Proof.
    unfold shift_value_option, rename_value_option, rename_value_template_option,
    rename_addr_option, sigma_shifting_wrap_bid_in_addr.
    intros H.
    destruct v' as [| [[[perm' cid'] bid'] off'] |];
      destruct v as [| [[[perm cid] bid] off] |]; inversion H; subst; auto.
    - destruct (Permission.eqb perm Permission.data);
        destruct (sigma_shifting_lefttoright_addr_bid n1 n2 (cid, bid)); discriminate.
    - destruct (Permission.eqb perm Permission.data) eqn:eperm;
        destruct (sigma_shifting_lefttoright_addr_bid n1 n2 (cid, bid))
        as [bid_shift|] eqn:ebid_shift.
      + inversion H. subst. rewrite eperm.
        assert (sigma_shifting_lefttoright_addr_bid n2 n1 (cid', bid') = Some bid) as G.
        {
          unfold sigma_shifting_lefttoright_addr_bid in *.
          apply sigma_shifting_righttoleft_option_Some_sigma_shifting_lefttoright_option_Some.
          by rewrite sigma_shifting_righttoleft_lefttoright.
        }
        by rewrite G.
      + discriminate.
      + inversion H. subst. by rewrite eperm.
      + inversion H. subst. by rewrite eperm.
    - destruct (Permission.eqb perm Permission.data);
        destruct (sigma_shifting_lefttoright_addr_bid n1 n2 (cid, bid)); discriminate.
  Qed.


  Lemma event_renames_event_at_shared_addr_symmetric n n' c b b' e e':
    sigma_shifting_lefttoright_option (n c) (n' c) b = Some b' ->
    event_renames_event_at_shared_addr n n' (c, b) e e' ->
    event_renames_event_at_shared_addr n' n (c, b') e' e.
  Proof.
    unfold event_renames_event_at_shared_addr,
    memory_renames_memory_at_shared_addr,
    rename_value_option, rename_value_template_option,
    sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid,
    rename_addr_option.
    intros Hsigma [[c' b'_] [esigma [mem_mem' mem'_mem]]].
    rewrite Hsigma in esigma. symmetry in esigma. inversion esigma. clear esigma. subst.
    apply sigma_shifting_lefttoright_Some_inv_Some in Hsigma.
    rewrite Hsigma.
    eexists; split; first reflexivity; split.
    - intros ? v' Hload; simpl in *.
      specialize (mem'_mem _ _ Hload) as [v [Hloadv vv']].
      eexists; split; eauto.
      destruct v as [| [[[pv cv] bv] ov] |]; try by inversion vv'; subst.
      destruct (Permission.eqb pv Permission.data) eqn:epv;
        last by inversion vv'; rewrite epv; subst.
      destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv) eqn:ebv;
        try discriminate.
      inversion vv'; subst. rewrite epv.
      apply sigma_shifting_lefttoright_Some_inv_Some in ebv. by rewrite ebv.
    - intros ? v Hload; simpl in *.
      specialize (mem_mem' _ _ Hload) as [v' [Hloadv' vv']].
      eexists; split; eauto.
      destruct v as [| [[[pv cv] bv] ov] |]; try by inversion vv'; subst.
      destruct (Permission.eqb pv Permission.data) eqn:epv;
        last by inversion vv'; rewrite epv; subst.
      destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv) eqn:ebv;
        try discriminate.
      inversion vv'; subst. rewrite epv.
      apply sigma_shifting_lefttoright_Some_inv_Some in ebv. by rewrite ebv.
  Qed.
      
  Lemma traces_rename_each_other_same_size n1 n2 t1 t2:
    traces_rename_each_other_option n1 n2 t1 t2 -> size t1 = size t2.
  Proof.
    intros H. induction H as [ |tp e tp' e' ? ? ? Ha]; auto.
      by rewrite !size_rcons IHtraces_rename_each_other_option.
  Qed.
  
  Lemma traces_rename_each_other_option_transitive n n' n'' sz:
    forall t t' t'',
      size t = sz ->
      traces_rename_each_other_option n  n'  t  t'  ->
      traces_rename_each_other_option n' n'' t' t'' ->
      traces_rename_each_other_option n  n'' t  t''.
  Proof.
    induction sz as [ | sz IHsz]; intros ? ? ? tsz Htt' Ht't''.
    - assert (t2sz: size t' = 0).
      { erewrite <- traces_rename_each_other_same_size; eauto. }
      assert (t3sz: size t'' = 0).
      { erewrite <- traces_rename_each_other_same_size; eauto. }
      assert (t1nil: t = [::]). by (apply size0nil).
      assert (t2nil: t' = [::]). by (apply size0nil).
      assert (t3nil: t'' = [::]). by (apply size0nil).
      subst. constructor.
    - assert (size t' = sz.+1) as Hsizet'.
      { symmetry; rewrite <- tsz; by eapply traces_rename_each_other_same_size; eauto. }
      assert (size t'' = sz.+1) as Hsizet''.
      { symmetry; rewrite <- Hsizet';
          by eapply traces_rename_each_other_same_size; eauto. }
      induction t   as [ | t   e   _] using last_ind; try discriminate.
      induction t'  as [ | t'  e'  _] using last_ind; try discriminate.
      induction t'' as [ | t'' e'' _] using last_ind; try discriminate.

      inversion Htt' as [|? ? ? ? ?
                            Htt'_ Hshrtt' Hshrt't Hmatchtt' Hargee' ? Hgoodt Hgoodt'];
        try find_nil_rcons; repeat find_rcons_rcons.
      inversion Ht't'' as [|? ? ? ? ? Ht't''_ Hshrt't'' Hshrt''t'
                              Hmatcht't'' Harge'e'' ? _ Hgoodt''];
        try find_nil_rcons; repeat find_rcons_rcons.
      constructor 2 with (v' := arg_of_event e''); auto.
      + eapply IHsz; eauto; by rewrite size_rcons in tsz; auto.
      + intros ? Hshr; specialize (Hshrtt' _ Hshr)
          as [Hee' [[c' b'] [Hsigmann' Hshr']]].
        specialize (Hshrt't'' _ Hshr')
          as [He'e'' [[c'' b''] [Hsigman'n'' Hshr'']]].
        destruct addr as [c b].
        unfold event_renames_event_at_shared_addr,
        memory_renames_memory_at_shared_addr,
        rename_value_option, rename_value_template_option,
        sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid,
        rename_addr_option in *.
        destruct (sigma_shifting_lefttoright_option (n c) (n' c) b) eqn:G1;
          try discriminate.
        inversion Hsigmann'; subst; clear Hsigmann'.
        destruct (sigma_shifting_lefttoright_option (n' c') (n'' c') b') eqn:G2;
          try discriminate.
        inversion Hsigman'n''; subst; clear Hsigman'n''.
        
        assert (G: sigma_shifting_lefttoright_option (n c'') (n'' c'') b = Some b'').
        { by eapply sigma_shifting_lefttoright_transitive; eauto. }

        split.
        * exists (c'', b''); split; first by rewrite G. split.
          -- intros ? ? Hload.
             destruct Hee' as [[? ?] [inv [Hee'1 Hee'2]]].
             symmetry in inv; inversion inv; subst; clear inv; simpl in *.
             specialize (Hee'1 _ _ Hload) as [v' [Hloadv' vv']].
             destruct He'e'' as [[? ?] [inv [He'e''1 He'e''2]]].
             symmetry in inv; inversion inv; subst; clear inv; simpl in *.
             specialize (He'e''1 _ _ Hloadv') as [v'' [Hloadv'' v'v'']].
             eexists; split; first eassumption.
             destruct v as [| [[[pv cv] bv] ov] |];
               try by inversion vv' as [rewr]; rewrite <- rewr in v'v''; auto.
             destruct (Permission.eqb pv Permission.data) eqn:epv.
             ++ destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv)
                 as [bv'|] eqn:G1v; try discriminate.
                inversion vv'; subst; clear vv'.
                rewrite epv in v'v''.
                destruct (sigma_shifting_lefttoright_option (n' cv) (n'' cv) bv')
                  as [bv''|] eqn:G2v; try discriminate.
                inversion v'v''; subst; clear v'v''.
                assert (Gv: sigma_shifting_lefttoright_option (n cv) (n'' cv) bv
                        = Some bv'').
                { by eapply sigma_shifting_lefttoright_transitive; eauto. }
                  by rewrite Gv.
             ++ inversion vv'; subst; clear vv'; by rewrite epv in v'v''.
          -- intros ? v'' Hload''.
             destruct He'e'' as [[? ?] [inv [He'e''1 He'e''2]]].
             symmetry in inv; inversion inv; subst; clear inv; simpl in *.
             specialize (He'e''2 _ _ Hload'') as [v' [Hloadv' v'v'']].
             destruct Hee' as [[? ?] [inv [Hee'1 Hee'2]]].
             symmetry in inv; inversion inv; subst; clear inv; simpl in *.
             specialize (Hee'2 _ _ Hloadv') as [v [Hloadv vv']].
             eexists; split; first eassumption.
             destruct v as [| [[[pv cv] bv] ov] |];
               try by inversion vv' as [rewr]; rewrite <- rewr in v'v''; auto.
             destruct (Permission.eqb pv Permission.data) eqn:epv.
             ++ destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv)
                 as [bv'|] eqn:G1v; try discriminate.
                inversion vv'; subst; clear vv'.
                rewrite epv in v'v''.
                destruct (sigma_shifting_lefttoright_option (n' cv) (n'' cv) bv')
                  as [bv''|] eqn:G2v; try discriminate.
                inversion v'v''; subst; clear v'v''.
                assert (Gv: sigma_shifting_lefttoright_option (n cv) (n'' cv) bv
                        = Some bv'').
                { by eapply sigma_shifting_lefttoright_transitive; eauto. }
                  by rewrite Gv.
             ++ inversion vv'; subst; clear vv'; by rewrite epv in v'v''.
             
        * exists (c'', b''); split; last exact Hshr''.
            by rewrite G.
          
      + intros addr'' Hshr''; specialize (Hshrt''t' _ Hshr'')
          as [[c' b'] [Hsigman'n'' [He'e'' Hshr']]].
        specialize (Hshrt't _ Hshr')
          as [[c b] [Hsigmann' [Hee' Hshr]]].
        destruct addr'' as [c'' b''].
        unfold event_renames_event_at_shared_addr,
        memory_renames_memory_at_shared_addr,
        rename_value_option, rename_value_template_option,
        sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid,
        rename_addr_option in *.
        destruct (sigma_shifting_lefttoright_option (n c) (n' c) b) eqn:G1;
          try discriminate.
        inversion Hsigmann'; subst; clear Hsigmann'.
        destruct (sigma_shifting_lefttoright_option (n' c') (n'' c') b') eqn:G2;
          try discriminate.
        inversion Hsigman'n''; subst; clear Hsigman'n''.
        assert (G: sigma_shifting_lefttoright_option (n c'') (n'' c'') b = Some b'').
        { by eapply sigma_shifting_lefttoright_transitive; eauto. }
        exists (c'', b). split; last split; last exact Hshr; rewrite G; auto.
        (** event_renames_event (unfolded) remains *)
        eexists; split; first reflexivity. split.
        * intros ? ? Hload.
          destruct Hee' as [[? ?] [inv [Hee'1 Hee'2]]].
          symmetry in inv; inversion inv; subst; clear inv; simpl in *.
          specialize (Hee'1 _ _ Hload) as [v' [Hloadv' vv']].
          destruct He'e'' as [[? ?] [inv [He'e''1 He'e''2]]].
          symmetry in inv; inversion inv; subst; clear inv; simpl in *.
          specialize (He'e''1 _ _ Hloadv') as [v'' [Hloadv'' v'v'']].
          eexists; split; first eassumption.
          destruct v as [| [[[pv cv] bv] ov] |];
            try by inversion vv' as [rewr]; rewrite <- rewr in v'v''; auto.
          destruct (Permission.eqb pv Permission.data) eqn:epv.
          -- destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv)
              as [bv'|] eqn:G1v; try discriminate.
             inversion vv'; subst; clear vv'.
             rewrite epv in v'v''.
             destruct (sigma_shifting_lefttoright_option (n' cv) (n'' cv) bv')
               as [bv''|] eqn:G2v; try discriminate.
             inversion v'v''; subst; clear v'v''.
             assert (Gv: sigma_shifting_lefttoright_option (n cv) (n'' cv) bv
                        = Some bv'').
             { by eapply sigma_shifting_lefttoright_transitive; eauto. }
               by rewrite Gv.
          -- inversion vv'; subst; clear vv'; by rewrite epv in v'v''.

        * intros ? v'' Hload''.
          destruct He'e'' as [[? ?] [inv [He'e''1 He'e''2]]].
          symmetry in inv; inversion inv; subst; clear inv; simpl in *.
          specialize (He'e''2 _ _ Hload'') as [v' [Hloadv' v'v'']].
          destruct Hee' as [[? ?] [inv [Hee'1 Hee'2]]].
          symmetry in inv; inversion inv; subst; clear inv; simpl in *.
          specialize (Hee'2 _ _ Hloadv') as [v [Hloadv vv']].
          eexists; split; first eassumption.
          destruct v as [| [[[pv cv] bv] ov] |];
            try by inversion vv' as [rewr]; rewrite <- rewr in v'v''; auto.
          destruct (Permission.eqb pv Permission.data) eqn:epv.
          -- destruct (sigma_shifting_lefttoright_option (n cv) (n' cv) bv)
              as [bv'|] eqn:G1v; try discriminate.
             inversion vv'; subst; clear vv'.
             rewrite epv in v'v''.
             destruct (sigma_shifting_lefttoright_option (n' cv) (n'' cv) bv')
               as [bv''|] eqn:G2v; try discriminate.
             inversion v'v''; subst; clear v'v''.
             assert (Gv: sigma_shifting_lefttoright_option (n cv) (n'' cv) bv
                         = Some bv'').
             { by eapply sigma_shifting_lefttoright_transitive; eauto. }
               by rewrite Gv.
          -- inversion vv'; subst; clear vv'; by rewrite epv in v'v''.
             
          
      + unfold match_events in *.
        destruct e; destruct e''; destruct e';
          try discriminate; auto; try (by exfalso);
            repeat match goal with | Hand: _ /\ _ |- _ =>
                                     destruct Hand as [? ?] end.
        * repeat constructor; subst; reflexivity.
        * repeat constructor; subst; reflexivity.

      + unfold rename_value_option, rename_value_template_option,
        sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid in *.
        destruct (arg_of_event e) as [| [[[p c] b] o] |];
          try inversion Hargee' as [Harge']; rewrite <- Harge' in Harge'e''; auto.
        destruct (Permission.eqb p Permission.data) eqn:ep.
        * unfold rename_addr_option in *.
          destruct (sigma_shifting_lefttoright_option (n c) (n' c) b)
            as [b'|] eqn:esigma; try discriminate.
          inversion Harge' as [rewr].
          rewrite <- rewr, ep in Harge'e''.
          destruct (sigma_shifting_lefttoright_option (n' c) (n'' c) b')
            as [b''|] eqn:esigma2; try discriminate.
          inversion Harge'e'' as [rewr2].
          assert (G: sigma_shifting_lefttoright_option (n c) (n'' c) b = Some b'').
          { by eapply sigma_shifting_lefttoright_transitive; eauto. }
          by rewrite G.
        * inversion Harge' as [rewr]; rewrite <- rewr, ep in Harge'e''. by auto.
            
  Qed.        

  Lemma traces_shift_each_other_option_transitive n n' n'' t t' t'':
    traces_shift_each_other_option n  n'  t  t'  ->
    traces_shift_each_other_option n' n'' t' t'' ->
    traces_shift_each_other_option n  n'' t  t''.
  Proof.
    intros H1 H2. inversion H1. inversion H2. subst.
    constructor. eapply traces_rename_each_other_option_transitive; eauto.
  Qed.

  
  Lemma traces_rename_each_other_option_symmetric n n' sz:
    forall t t',
      size t = sz ->
      traces_rename_each_other_option n  n'  t  t'  ->
      traces_rename_each_other_option n' n   t' t.
  Proof.
    induction sz as [ | sz IHsz]; intros ? ? tsz Htt'.
    - assert (t2sz: size t' = 0).
      { erewrite <- traces_rename_each_other_same_size; eauto. }
      assert (t1nil: t = [::]). by (apply size0nil).
      assert (t2nil: t' = [::]). by (apply size0nil).
      subst. constructor.
    - assert (size t' = sz.+1) as Hsizet'.
      { symmetry; rewrite <- tsz; by eapply traces_rename_each_other_same_size; eauto. }
      induction t   as [ | t   e   _] using last_ind; try discriminate.
      induction t'  as [ | t'  e'  _] using last_ind; try discriminate.
      inversion Htt' as [|? ? ? ? ?
                            Htt'_ Hshrtt' Hshrt't Hmatchtt' Hargee' ? Hgoodt Hgoodt'];
        first find_nil_rcons; repeat find_rcons_rcons.
  
      econstructor 2 with (v' := arg_of_event e); auto.
      + eapply IHsz; eauto. by rewrite size_rcons in tsz; auto.
      + intros [c' b'] Hshr'. specialize (Hshrt't _ Hshr') as [[c b] [cbsigma [ee' ?]]].
        unfold sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid,
        rename_addr_option in *.
        destruct (sigma_shifting_lefttoright_option (n c) (n' c) b) eqn:eb;
          try discriminate; inversion cbsigma; subst; clear cbsigma.
        apply sigma_shifting_lefttoright_Some_inv_Some in eb.
        rewrite eb.
        split; last (eexists; split; first reflexivity; assumption).
        eapply event_renames_event_at_shared_addr_symmetric; eauto.
        apply sigma_shifting_lefttoright_Some_inv_Some; auto.
      + intros [c b] Hshr.
        specialize (Hshrtt' _ Hshr) as [ee' [[c' b'] [esigma ?]]].
        unfold sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid,
        rename_addr_option in *.
        destruct (sigma_shifting_lefttoright_option (n c) (n' c) b) eqn:eb;
          try discriminate; inversion esigma; subst; clear esigma.
        eexists (c', b').
        apply sigma_shifting_lefttoright_Some_inv_Some in eb.
        rewrite eb. intuition.
        eapply event_renames_event_at_shared_addr_symmetric; eauto.
        apply sigma_shifting_lefttoright_Some_inv_Some; auto.
      + destruct e; destruct e'; simpl in *; try (by exfalso); intuition.
      + specialize (shift_value_option_symmetry
                      n n' (arg_of_event e) (arg_of_event e')) as G.
        unfold shift_value_option in *.
        by apply G.
  Qed.
      
    
  Lemma traces_shift_each_other_option_symmetric n n' t t':
    traces_shift_each_other_option n  n'  t  t'  ->
    traces_shift_each_other_option n' n   t' t.
  Proof.
    intros Hshift. inversion Hshift as [? ? Hren]; subst.
    inversion Hren as [|? ? ? ? ?
                          Htt'_ Hshrtt' Hshrt't Hmatchtt' Hargee' ? Hgoodt Hgoodt'];
      subst.
    - constructor; constructor.
    - constructor.
      eapply traces_rename_each_other_option_symmetric; eauto.
  Qed.      
                        
    
End PropertiesOfTheShiftRenamingAddrOption.

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
        traces_shift_each_other_option size_meta_t1 size_meta_t2 t1 t2 ->
        behavior_rel_behavior size_meta_t1 size_meta_t2 (FTerminates t1) (FTerminates t2)
  | Tbc_rel_Tbc:
      forall t1 t2,
        traces_shift_each_other_option size_meta_t1 size_meta_t2 t1 t2 ->
        behavior_rel_behavior size_meta_t1 size_meta_t2 (FTbc t1) (FTbc t2).

  (*
  Lemma behavior_rel_behavior_reflexive b n:
    not_wrong_finpref b ->
    behavior_rel_behavior n n b b.
  Proof. intros not_wrong. unfold not_wrong_finpref in *. destruct b; auto.
         - apply Terminates_rel_Terminates.
           apply traces_shift_each_other_option_reflexive.
         - exfalso. auto.
         - apply Tbc_rel_Tbc. apply traces_shift_each_other_reflexive.
  Qed.

  Lemma behavior_rel_behavior_symmetric b1 b2 n1 n2:
    behavior_rel_behavior n1 n2 b1 b2 -> behavior_rel_behavior n2 n1 b2 b1.
  Proof. intros H. inversion H.
         - apply Terminates_rel_Terminates. apply traces_shift_each_other_symmetric. auto.
         - apply Tbc_rel_Tbc. apply traces_shift_each_other_symmetric. auto.
  Qed.

*)

  (** well-formedness of finite program behaviors (on the left) lifts
      well-formedness of traces to successfully terminating and unfinished
      program behaviors. *)

  Inductive good_behavior_left
            (size_meta_t: Component.id -> nat) :
    @finpref_behavior Events.event -> Prop :=
  | good_trace_Terminates:
      forall t,
        good_trace_extensional (left_addr_good_for_shifting size_meta_t) t ->
        good_behavior_left size_meta_t (FTerminates t)
  | good_trace_Tbc:
      forall t,
        good_trace_extensional (left_addr_good_for_shifting size_meta_t) t ->
        good_behavior_left size_meta_t (FTbc t).

  (*
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
*)
End BehaviorsRelated.

Definition shared_locations_have_only_shared_values mem metadata_size :=
  forall (ptr : Pointer.t)
         (addr : Component.id * Block.id) (v : value),
    Memory.Memory.load mem ptr = Some v ->
    addr = (Pointer.component ptr, Pointer.block ptr) ->
    left_addr_good_for_shifting metadata_size addr ->
    left_value_good_for_shifting metadata_size v.

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

Definition addr_t : Type := (Component.id * Block.id).
(* It seems only Block.id will need to be renamed.
     However, to compute a renaming, we have to know which "component memory" we are
     considering. To know the component memory, we need the Component.id.
*)

Section ShiftingAsPartialBijection.
  (* The following is a definition of a so-called "partial bijection", namely
     the bijection between the set [count_blocks_to_shift_per_comp, inf) and the set N
     of all the natural numbers.
     However, I am defining this bijection 
     (between [count_blocks_to_shift_per_comp, inf) and N)
     as a total bijection between
     {care, dontcare} x N and {care, dontcare} x N.
     Totalizing it enables us to reuse useful results about total bijections.
   *)

  Variable count_blocks_to_shift_per_comp : nat.
  
  Definition care := true.
  Definition dontcare := false.

  Definition sigma_from_bigger_dom (x: bool * addr_t) : bool * addr_t :=
    match x with
    | (c, (cid, bid)) =>
      if c =? care then
        if bid <? count_blocks_to_shift_per_comp
        then (dontcare, (cid, bid))
        else (care, (cid, bid - count_blocks_to_shift_per_comp))
      else (dontcare, (cid, bid + count_blocks_to_shift_per_comp))
    end.

  Definition inv_sigma_from_bigger_dom (x: bool * addr_t) : bool * addr_t :=
    match x with
    | (c, (cid, bid)) =>
      if c =? care then
        (care, (cid, bid + count_blocks_to_shift_per_comp))
      else if bid <? count_blocks_to_shift_per_comp
           then (care, (cid, bid))
           else (dontcare, (cid, bid - count_blocks_to_shift_per_comp))
    end.

  Lemma cancel_sigma_from_bigger_dom_inv_sigma_from_bigger_dom :
    cancel sigma_from_bigger_dom inv_sigma_from_bigger_dom.
  Proof.
    unfold cancel. intros [c [cid bid]].
    destruct c; simpl.
    - destruct (bid <? count_blocks_to_shift_per_comp) eqn:bid_lt; simpl.
      + rewrite bid_lt. reflexivity.
      + rewrite subnK; try reflexivity.
        assert (le count_blocks_to_shift_per_comp bid) as Hle.
        { rewrite <- Nat.ltb_ge. assumption. }
        apply/leP. assumption.
    - pose proof (leq_addl bid count_blocks_to_shift_per_comp) as H.
      destruct (bid + count_blocks_to_shift_per_comp <? count_blocks_to_shift_per_comp)
               eqn:bid_plus_lt; simpl.
      + pose proof Nat.ltb_lt (addn bid count_blocks_to_shift_per_comp)
             (count_blocks_to_shift_per_comp) as [Hif _].
        rewrite bid_plus_lt in Hif. pose proof (Hif Logic.eq_refl) as Hlt. clear Hif.
        assert (leq (S (addn bid count_blocks_to_shift_per_comp))
                    count_blocks_to_shift_per_comp) as Hleq.
        { apply/ltP. assumption. }
        pose proof (leqP count_blocks_to_shift_per_comp
                         (addn bid count_blocks_to_shift_per_comp)) as Hcontra.
        rewrite H in Hcontra. rewrite Hleq in Hcontra.
        inversion Hcontra.
      + rewrite addnK. reflexivity.
  Qed.

  Lemma cancel_inv_sigma_from_bigger_dom_sigma_from_bigger_dom :
    cancel inv_sigma_from_bigger_dom sigma_from_bigger_dom.
  Proof.
    unfold cancel. intros [c [cid bid]]. destruct c; simpl.
    - pose proof leq_addl bid count_blocks_to_shift_per_comp.
      assert (bid + count_blocks_to_shift_per_comp <? count_blocks_to_shift_per_comp = false)
        as Hfalse.
      { rewrite Nat.ltb_ge. apply/leP. assumption. }
      rewrite Hfalse. rewrite addnK. reflexivity.
    - destruct (bid <? count_blocks_to_shift_per_comp) eqn:HNatlt;
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

  Lemma sigma_from_bigger_dom_cid_constant x:
    (sigma_from_bigger_dom x).2.1 = x.2.1.
  Proof.
    destruct x as [c [cid bid]]. unfold sigma_from_bigger_dom.
    destruct (c =? care); destruct (bid <? count_blocks_to_shift_per_comp); simpl; auto.
  Qed.

  Lemma inv_sigma_from_bigger_dom_cid_constant x:
    (inv_sigma_from_bigger_dom x).2.1 = x.2.1.
  Proof.
    destruct x as [c [cid bid]]. unfold inv_sigma_from_bigger_dom.
    destruct (c =? care); destruct (bid <? count_blocks_to_shift_per_comp); simpl; auto.
  Qed.
  
End ShiftingAsPartialBijection.

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

Definition addr_of_value (v: value) : {fset addr_t} :=
  match v with
  | Ptr (perm, cid, bid, _) =>
    if perm =? Permission.data then fset1 (cid, bid) else fset0
  | _ => fset0
  end.

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

Section PredicateOnReachableAddresses.

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

Section SigmaShifting.

  Variable metadata_size_lhs: nat.
  Variable metadata_size_rhs: nat.
  
  Let num_extra_blocks_of_lhs : Z :=
    Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs.

  Definition sigma_shifting :=
    if (num_extra_blocks_of_lhs >=? 0)%Z
    then (sigma_from_bigger_dom (Z.to_nat num_extra_blocks_of_lhs))
    else (inv_sigma_from_bigger_dom (Z.to_nat (- num_extra_blocks_of_lhs))).

  Definition inv_sigma_shifting :=
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

  Definition left_addr_good_for_shifting (left_addr: addr_t) : Prop :=
    match left_addr with
    | (_, bid) => bid >= metadata_size_lhs
    end.

  Definition right_addr_good_for_shifting (right_addr: addr_t) : Prop :=
    match right_addr with
    | (_, bid) => bid >= metadata_size_rhs
    end.

  Lemma sigma_left_good_right_good left_addr:
    left_addr_good_for_shifting left_addr ->
    exists right_addr,
      sigma_shifting (care, left_addr) = (care, right_addr) /\
      right_addr_good_for_shifting right_addr.
  Proof.
    destruct left_addr as [lcid lbid].
    unfold left_addr_good_for_shifting, sigma_shifting, right_addr_good_for_shifting.
    intros Hleft_good.
    unfold num_extra_blocks_of_lhs.
    destruct (Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs >=? 0)%Z eqn:Hge0.
    - eexists. simpl.
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
      rewrite Hcond. rewrite simplify_minus in Hcond.
      assert ((metadata_size_lhs - metadata_size_rhs) <= lbid)%coq_nat as Hall.
      { rewrite <- Nat.ltb_ge. exact Hcond. }
      assert (metadata_size_rhs <= lbid) as rhs_lbid.
      { apply leq_trans with (n := metadata_size_lhs); auto. apply/leP. auto. }
      split.
      + reflexivity.
      + simpl. rewrite simplify_minus. rewrite minusE.
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
    - eexists. simpl. split; try reflexivity. simpl.
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
      rewrite !Nat2Z.id addnC. SearchAbout addn subn.
      rewrite <- leq_subLR. SearchAbout subn subn.
      rewrite subKn; assumption.
  Qed.
                                                
  Lemma inv_sigma_right_good_left_good right_addr:
    right_addr_good_for_shifting right_addr ->
    exists left_addr,
      inv_sigma_shifting (care, right_addr) = (care, left_addr) /\
      left_addr_good_for_shifting left_addr.
  Admitted.

End SigmaShifting.

Section SigmaShiftingProperties.
  
  Lemma sigma_shifting_cid_constant:
    forall n1 n2 x, (sigma_shifting n1 n2 x).2.1 = x.2.1.
  Admitted.
(*  Proof. intros. unfold sigma_shifting.
         destruct (n >=? 0)%Z;
           try apply sigma_from_bigger_dom_cid_constant;
           apply inv_sigma_from_bigger_dom_cid_constant.
  Qed.*)

  Lemma inv_sigma_shifting_cid_constant:
    forall n1 n2 x, (inv_sigma_shifting n1 n2 x).2.1 = x.2.1.
  Admitted.
(*  Proof. intros. unfold inv_sigma_shifting.
         destruct (n >=? 0)%Z;
           try apply sigma_from_bigger_dom_cid_constant;
           apply inv_sigma_from_bigger_dom_cid_constant.
  Qed.
 *)
  (*
  Lemma sigma_shifting_0_id:
    forall x, sigma_shifting 0 x = x.
  Proof.
    intros [c_dc [cid bid]]. unfold sigma_shifting, sigma_from_bigger_dom. simpl.
    destruct c_dc eqn:H; simpl.
    - rewrite subn0. reflexivity.
    - rewrite addn0. reflexivity.
  Qed.

  Lemma inv_sigma_shifting_0_id:
    forall x, inv_sigma_shifting 0 x = x.
  Proof.
    intros [c_dc [cid bid]]. unfold inv_sigma_shifting, inv_sigma_from_bigger_dom. simpl.
    destruct c_dc eqn:H; simpl.
    - rewrite addn0. reflexivity.
    - rewrite subn0. reflexivity.
  Qed.

  Lemma inv_sigma_shifting_n_sigma_shifting_minus_n:
    forall n x,
      inv_sigma_shifting n x = sigma_shifting (- n) x.
  Proof.
    intros n [cdc [cid bid]].
    unfold inv_sigma_shifting, sigma_shifting,
    sigma_from_bigger_dom, inv_sigma_from_bigger_dom.
    destruct (n >=? 0)%Z eqn:Hn; destruct (- n >=? 0)%Z eqn:Hoppn;
      destruct (cdc =? care) eqn:Hcdc; try reflexivity.
    - (* Here, n = 0 *)
      assert (Z.le n Z0) as Hn0.
      { rewrite <- Z.opp_nonneg_nonpos. rewrite <- Z.geb_le. assumption. }
      assert (Z.le Z0 n) as H0n.
      { rewrite <- Z.geb_le. assumption. }
      assert (n = Z0) as Hneq0.
      { apply Z.le_antisymm; assumption. }
      subst. simpl. rewrite addn0 subn0. reflexivity.
    - (* Here, n = 0 *)
      assert (Z.le n Z0) as Hn0.
      { rewrite <- Z.opp_nonneg_nonpos. rewrite <- Z.geb_le. assumption. }
      assert (Z.le Z0 n) as H0n.
      { rewrite <- Z.geb_le. assumption. }
      assert (n = Z0) as Hneq0.
      { apply Z.le_antisymm; assumption. }
      subst. simpl. rewrite addn0 subn0. reflexivity.
    - rewrite Z.opp_involutive. reflexivity.
    - rewrite Z.opp_involutive. reflexivity.
    - (* This case is impossible. *)
      assert ((Z.leb Z0 n) = false) as Hfalse.
      { rewrite <- Z.geb_leb. assumption. }
      assert ((Z.leb Z0 (Z.opp n)) = false) as Hfalse'.
      { rewrite <- Z.geb_leb. assumption. }
      assert (Z.ltb n Z0) as Hcontra.
      { rewrite Z.ltb_antisym. rewrite Hfalse. simpl. auto. }
      assert (Z.lt Z0 n) as Hcontra'.
      { rewrite Z.opp_lt_mono. simpl. rewrite <- Z.nle_gt.
        rewrite <- Z.leb_nle. exact Hfalse'. }
      assert (not (Z.lt n Z0)) as Hnot.
      { apply Z.lt_asymm. exact Hcontra'. }
      assert (Z.ltb n Z0 = false) as Hfinally.
      { rewrite Z.ltb_nlt. exact Hnot. }
      rewrite Hfinally in Hcontra. inversion Hcontra.
    - (* This case is impossible. *)
      assert ((Z.leb Z0 n) = false) as Hfalse.
      { rewrite <- Z.geb_leb. assumption. }
      assert ((Z.leb Z0 (Z.opp n)) = false) as Hfalse'.
      { rewrite <- Z.geb_leb. assumption. }
      assert (Z.ltb n Z0) as Hcontra.
      { rewrite Z.ltb_antisym. rewrite Hfalse. simpl. auto. }
      assert (Z.lt Z0 n) as Hcontra'.
      { rewrite Z.opp_lt_mono. simpl. rewrite <- Z.nle_gt.
        rewrite <- Z.leb_nle. exact Hfalse'. }
      assert (not (Z.lt n Z0)) as Hnot.
      { apply Z.lt_asymm. exact Hcontra'. }
      assert (Z.ltb n Z0 = false) as Hfinally.
      { rewrite Z.ltb_nlt. exact Hnot. }
      rewrite Hfinally in Hcontra. inversion Hcontra.
  Qed.

  Lemma sigma_shifting_transitive n12 n23 a:
    left_addr_good_for_shifting n12 a ->
    left_addr_good_for_shifting (n12 + n23) a ->
    left_addr_good_for_shifting n23 ((sigma_shifting n12 (care, a)).2) ->
    sigma_shifting n23 (care, (sigma_shifting n12 (care, a)).2) =
    sigma_shifting (n12 + n23) (care, a).
  Proof.
    intros good_n12_bid good_n12_n23_bid good_n23_sigma_n12_a.
    destruct (sigma_left_good_right_good _ _ good_n12_bid) as
        [sigma_n12_a [Hsigma_n12_a H_good_sigma_n12_a]].
    destruct (sigma_left_good_right_good _ _ good_n12_n23_bid) as
        [sigma_n12_n23_a [Hsigma_n12_n23_a H_good_sigma_n12_n23_a]].
    destruct (sigma_left_good_right_good _ _ good_n23_sigma_n12_a) as
        [sigma_n23_sigma_n12_a [Hsigma_n23_sigma_n12_a H_good_sigma_n23_sigma_n12_a]].
    destruct a as [cid bid].

    rewrite Hsigma_n12_a in Hsigma_n23_sigma_n12_a. simpl in Hsigma_n23_sigma_n12_a.
    rewrite Hsigma_n12_a. simpl.
    destruct sigma_n12_a as [sigma_n12_a_cid sigma_n12_a_bid].
    destruct sigma_n12_n23_a as [sigma_n12_n23_a_cid sigma_n12_n23_a_bid].
    destruct sigma_n23_sigma_n12_a 
      as [sigma_n23_sigma_n12_a_cid sigma_n23_sigma_n12_a_bid].
    unfold sigma_shifting, left_addr_good_for_shifting, right_addr_good_for_shifting(*,
      sigma_from_bigger_dom, inv_sigma_from_bigger_dom*) in *.
    destruct (n23 >=? 0)%Z eqn:Hn23; simpl in *.
    - destruct (sigma_n12_a_bid <? Z.to_nat n23) eqn:H_sigma_n12_a_bid_n23; simpl in *.
      + unfold dontcare, care in Hsigma_n23_sigma_n12_a. discriminate.
      + destruct (n12 + n23 >=? 0)%Z eqn:Hn12_n23; simpl in *.
        assert (bid <? Z.to_nat (n12 + n23) = false) as Hnecessary.
        {
          rewrite Nat.ltb_antisym. unfold negb.
          assert (Z.to_nat (n12 + n23) <=? bid = true) as Hnecessary'.
          { apply leb_correct. apply/leP. apply good_n12_n23_bid. auto. }
          rewrite Hnecessary'. auto.
        }
        rewrite Hnecessary.
        SearchAbout sigma_n12_a_bid.
        destruct (n12 >=? 0)%Z eqn:Hn12.
        * SearchAbout sigma_n12_a_bid.
          SearchAbout sigma_from_bigger_dom.
        rewrite Hsigma_n23_sigma_n12_a.
        SearchAbout sigma_n23_sigma_n12_a_bid.
        assert (sigma_n12_a_cid = cid) as Hproperty_of_sigma.
        { admit. (* Prove this as a property of any sigma. *) }
        rewrite Hproperty_of_sigma.
        
        assert (bid <? Z.to_nat (n12 + n23)) as Hnecessary.
    unfold right_addr_good_for_shifting in *.
    clear good_n12_bid good_n12_n23_bid. simpl.
    unfold sigma_shifting.
    destruct (n23 >=? 0)%Z eqn:Hn23. simpl.
    destruct (n23 >=? 0)%Z eqn:Hn23; destruct (n12 >=? 0)%Z eqn:Hn12.
    - assert (n12 + n23 >=? 0)%Z as Hpos.
      {
        rewrite Z.geb_leb. unfold is_true.
        rewrite <- Zle_bool_plus_mono with (n := Z0) (p := Z0) (m := n12) (q := n23).
        + auto.
        + rewrite <- Z.geb_leb. assumption.
        + rewrite <- Z.geb_leb. assumption.
      }
      rewrite Hpos. unfold sigma_from_bigger_dom. simpl.
      destruct (bid <? Z.to_nat n12) eqn:H_bid_n12; simpl.
      + destruct (bid <? Z.to_nat n23) eqn:H_bid_n23.
        * (* Here, know that bid <? Z.to_nat (n12 + n23) *)
          (* First, show that Z.to_nat (n12 + n23) = Z.to_nat n12 + Z.to_nat n23 *)
          (* Then, use some lemma about <? and +. *)
          assert (bid <? Z.to_nat (n12 + n23)) as H_bid_n12_n23.
          { admit. }
          rewrite H_bid_n12_n23. reflexivity.
        * (* Here, know that bid - Z.to_nat n23 must be 0 because of H_bid_n23. *)
          assert (bid - Z.to_nat n23 = 0) as H_minus_0.
          { admit. }
          rewrite H_minus_0.
          (* Also because of H_bid_n23, know that bid <? Z.to_nat (n12 + n23) can't hold. *)
          assert (bid <? Z.to_nat (n12 + n23) = false) as H_bid_n12_n23.
          { admit. }
          rewrite H_bid_n12_n23.
          (* As a consequence of H_bid_n12_n23, know that bid - Z.to_nat (n12 + n23) must
           be 0. *)
          assert (bid - Z.to_nat (n12 + n23) = 0) as H_minus_0'.
          { admit. }
          rewrite H_minus_0'. reflexivity.
      + assert (0 <? Z.to_nat n23 = false) as Hn23'.
        { admit. (* follows from Hn23 *) }
        rewrite Hn23'.
        assert (bid <? Z.to_nat (n12 + n23) = false) as Hnecessary.
        {
          SearchAbout Z.to_nat.
          rewrite Z2Nat.inj_add.
          * SearchAbout Nat.ltb.
            rewrite Nat.ltb_antisym negb_false_iff.
            SearchAbout Nat.ltb false.
            assert (Z.to_nat n12 <= bid)%coq_nat as H_n12_bid.
            { rewrite <- Nat.ltb_ge. assumption. }
            SearchAbout le.
            rewrite Nat.ltb_ge in H_bid_n12.
            SearchAbout Init.Nat.add Init.Nat.sub.
          * rewrite <- Z.geb_le. exact Hn12.
          * rewrite <- Z.geb_le. exact Hn23.
        }

  Abort.
      
*)
End SigmaShiftingProperties.

Section Renaming.

  Variable sigma: addr_t -> addr_t (*{fmap addr_t -> addr_t}*).
  Variable inverse_sigma: addr_t -> addr_t.

  (*Hypothesis cancel_inverse_sigma_sigma: cancel inverse_sigma sigma.
  Hypothesis cancel_sigma_inverse_sigma: cancel sigma inverse_sigma.
  Hypothesis sigma_injective: injective sigma.*)

  (*Definition inverse_sigma (addr: addr_t) : addr_t :=
  let dom_sigma := domm sigma in
  if has (fun y => sigma y == Some addr) dom_sigma
  then nth (0,0) dom_sigma (find (fun y => sigma y == Some addr) dom_sigma)
  else addr.
   *)

  Definition rename_addr (addr: addr_t) : addr_t := sigma addr.
  (*  match sigma addr with
  | Some addr' => addr'
  | None => addr
  end.
   *)

  Definition inverse_rename_addr (addr: addr_t) := inverse_sigma addr.

  Definition rename_value_template (rnm_addr : addr_t -> addr_t) (v: value) : value :=
    match v with
    | Ptr (perm, cid, bid, off) =>
      let (cid', bid') := rnm_addr (cid, bid) in
      Ptr (perm, cid', bid', off)
    | _ => v
    end.

  Definition rename_value (v: value) : value := rename_value_template rename_addr v.
  
  Definition inverse_rename_value (v: value) : value :=
    rename_value_template inverse_rename_addr v.

  Definition rename_list_values (s: list value) : list value := map rename_value s.

  Definition inverse_rename_list_values (s: list value) : list value :=
    map inverse_rename_value s.

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

  Definition option_rename_value option_v := omap rename_value option_v.
  Definition option_inverse_rename_value option_v := omap inverse_rename_value option_v.

  Definition event_renames_event_at_addr addr e e' : Prop :=
    forall offset,
      Memory.load (mem_of_event e')
                  (
                    Permission.data,
                    (rename_addr addr).1,
                    (rename_addr addr).2,
                    offset
                  )
      =
      option_rename_value
        (
          Memory.load (mem_of_event e)
                      (Permission.data,
                       addr.1,
                       addr.2,
                       offset)
        ).

  Definition event_inverse_renames_event_at_addr addr' e e' : Prop :=
    forall offset,
      option_inverse_rename_value
        (
          Memory.load (mem_of_event e')
                      (Permission.data,
                       addr'.1,
                       addr'.2,
                       offset
                      )
        )
      =
      Memory.load (mem_of_event e)
                  (Permission.data,
                   (inverse_rename_addr addr').1,
                   (inverse_rename_addr addr').2,
                   offset
                  ).

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
        traces_rename_each_other (rcons tprefix e) (rcons tprefix' e').


  Lemma traces_rename_each_other_nil_rcons t x:
    traces_rename_each_other [::] (rcons t x) -> False.
  Proof. intros H. inversion H as [y Hy|tp e ? ? ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- Hy. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp e) = 0) as Hcontra.
           { rewrite Ha. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_rcons_nil t x:
    traces_rename_each_other (rcons t x) [::] -> False.
  Proof. intros H. inversion H as [y Hy|tp e tp' e' ? ? ? Ha Hb].
         - assert (0 = size (rcons t x)) as Hcontra.
           { rewrite <- y. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
         - assert (size (rcons tp' e') = 0) as Hcontra.
           { rewrite Hb. reflexivity. }
           rewrite size_rcons in Hcontra. discriminate.
  Qed.

  Lemma traces_rename_each_other_same_size t1 t2:
    traces_rename_each_other t1 t2 -> size t1 = size t2.
   Admitted.

    
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

End Renaming.

Section TheShiftRenaming.

  
  Variable metadata_size_lhs: nat.
  Variable metadata_size_rhs: nat.

  Let num_extra_blocks_of_lhs : Z :=
    Z.of_nat metadata_size_lhs - Z.of_nat metadata_size_rhs.

  Check sigma_shifting.
    
  Definition sigma_shifting_addr (a: addr_t) : addr_t :=
    match sigma_shifting metadata_size_lhs metadata_size_rhs (care, a) with
    | (_, a') => a'
    end.

  Definition inv_sigma_shifting_addr (a: addr_t) : addr_t :=
    match inv_sigma_shifting metadata_size_lhs metadata_size_rhs (care, a) with
    | (_, a') => a'
    end.

  Inductive traces_shift_each_other : trace event -> trace event -> Prop :=
  | shifting_is_special_case_of_renaming:
      forall t t',
        traces_rename_each_other sigma_shifting_addr inv_sigma_shifting_addr t t' ->
        traces_shift_each_other t t'.
  
End TheShiftRenaming.

Section PropertiesOfTheShiftRenaming.

  Lemma rename_addr_inverse_rename_addr n1 n2 a:
    rename_addr (sigma_shifting_addr n1 n2) a =
    inverse_rename_addr (inv_sigma_shifting_addr n2 n1) a.
  Admitted.
(*  Proof.
    unfold rename_addr, inverse_rename_addr, sigma_shifting_addr, inv_sigma_shifting_addr.
    erewrite inv_sigma_shifting_n_sigma_shifting_minus_n. reflexivity.
  Qed.
*)
  Lemma option_rename_value_option_inverse_rename_value n2 n1 v:
    option_inverse_rename_value (inv_sigma_shifting_addr n2 n1) v =
    option_rename_value (sigma_shifting_addr n1 n2) v.
  Admitted.
(*  Proof.
    destruct v as [[ | [[[perm cid] bid] o] | ] | ]; auto. simpl.
    rewrite rename_addr_inverse_rename_addr. reflexivity.
  Qed.*)

  Lemma event_rename_inverse_event_rename n1 n2 addr' e e':
    event_inverse_renames_event_at_addr (inv_sigma_shifting_addr n1 n2) addr' e e' <->
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
    rename_addr (sigma_shifting_addr n2 n3) (rename_addr (sigma_shifting_addr n1 n2) addr) =
    rename_addr (sigma_shifting_addr n1 n3) addr.
  Abort.

  Lemma event_rename_transitive n1 n2 n3 addr e1 e2 e3:
     event_renames_event_at_addr (sigma_shifting_addr n1 n2) addr e1 e2 ->
     event_renames_event_at_addr (sigma_shifting_addr n2 n3)
                                 (rename_addr (sigma_shifting_addr n1 n2) addr) e2 e3 ->
     event_renames_event_at_addr (sigma_shifting_addr n1 n3) addr e1 e3.
  Abort.

  Lemma traces_shift_each_other_reflexive n t:
    traces_shift_each_other n n t t.
  Admitted.
(*  Proof.
    apply shifting_is_special_case_of_renaming.
    induction t using last_ind.
    - apply nil_renames_nil.
    - apply rcons_renames_rcons.
      + assumption.
      + intros addr Hshrsfr. split.
        * unfold event_renames_event_at_addr, rename_addr, sigma_shifting_addr,
          option_rename_value, omap, obind, oapp, rename_value, rename_value_template,
          rename_addr. simpl.
          intros. rewrite !sigma_shifting_0_id.
          destruct (Memory.load (mem_of_event x) (Permission.data, addr.1, addr.2, offset));
            auto.
          destruct v as [| [[[perm cid] bid] o] |]; auto. rewrite subn0. reflexivity.
        * unfold rename_addr, sigma_shifting_addr. rewrite sigma_shifting_0_id. assumption.
      + intros addr' Hshrsfr. split.
        * unfold event_inverse_renames_event_at_addr, inverse_rename_addr,
          inv_sigma_shifting_addr,
          option_inverse_rename_value, omap, obind, oapp, inverse_rename_value,
          rename_value_template,
          inverse_rename_addr. simpl.
          intros. rewrite !inv_sigma_shifting_0_id.
          destruct (Memory.load (mem_of_event x) (Permission.data, addr'.1, addr'.2, offset));
            auto.
          destruct v as [| [[[perm cid] bid] o] |]; auto. rewrite addn0. reflexivity.
        * unfold inverse_rename_addr, inv_sigma_shifting_addr.
          rewrite inv_sigma_shifting_0_id. assumption.
  Qed.
*)

  Lemma traces_shift_each_other_symmetric t1 t2 n1 n2:
    traces_shift_each_other n1 n2 t1 t2 ->
    traces_shift_each_other n2 n1 t2 t1.
  Admitted.
(*  Proof.
    intros Ht1t2. apply shifting_is_special_case_of_renaming.
    inversion Ht1t2. subst. induction H as [|tprefix e tprefix' e' Hprefix_rename IH He He'].
    - apply nil_renames_nil.
    - apply rcons_renames_rcons.
      + apply IH. apply shifting_is_special_case_of_renaming. exact Hprefix_rename.
      + intros [cid bid] Hshrsfr. destruct (He' (cid, bid) Hshrsfr) as [G1 G2]. split.
        * rewrite <- event_rename_inverse_event_rename. exact G1.
        * rewrite rename_addr_inverse_rename_addr. exact G2.
      + intros [cid bid] Hshrsfr. destruct (He (cid, bid) Hshrsfr) as [G1 G2]. split.
        * rewrite event_rename_inverse_event_rename. rewrite Z.opp_involutive. exact G1.
        * rewrite <- rename_addr_inverse_rename_addr. rewrite Z.opp_involutive. exact G2.
  Qed.
*)

  Lemma rcons_trace_event_eq_inversion (tp1 tp2: trace event) (e1 e2: event):
    rcons tp1 e1 = rcons tp2 e2 -> tp1 = tp2 /\ e1 = e2.
  Proof.
    intros rconseq. assert (rcons tp1 e1 == rcons tp2 e2) as rconseq'. apply/eqP. assumption.
    rewrite eqseq_rcons in rconseq'. destruct (andP rconseq') as [G1 G2].
    split; apply/eqP; assumption.
  Qed.

  (*
  Variable num_extra_blocks_t1_t2 : Z.
  Variable num_extra_blocks_t2_t3 : Z.

  Lemma traces_shift_each_other_transitive_with_size:
    forall n t1 t2 t3,
      size t1 = n ->
      (
        traces_shift_each_other num_extra_blocks_t1_t2 t1 t2 ->
        traces_shift_each_other num_extra_blocks_t2_t3 t2 t3 ->
        traces_shift_each_other (num_extra_blocks_t1_t2 + num_extra_blocks_t2_t3) t1 t3
      ).
  Proof.
    intros n.
    induction n.
    - intros. admit.
    - intros. inversion H0. inversion H1. subst. clear H0 H1.
      assert (size t2 = n.+1) as Hsizet2.
      {
        symmetry. rewrite <- H.
        apply (traces_rename_each_other_same_size _ _ t1 t2 H2).
      }
      assert (size t3 = n.+1) as Hsizet3.
      {
        symmetry. rewrite <- Hsizet2.
        apply (traces_rename_each_other_same_size _ _ t2 t3 H5).
      }
      induction t1 using last_ind; try discriminate.
      induction t2 using last_ind; try discriminate.
      induction t3 using last_ind; try discriminate.
      clear IHt1 IHt2 IHt3.
      inversion H2.
      + (* impossible case *) admit.
      + inversion H5.
        * (* impossible case *) admit.
        * destruct (rcons_trace_event_eq_inversion _ _ _ _ H8) as [eq1 eq2]. subst. clear H8.
          destruct (rcons_trace_event_eq_inversion _ _ _ _ H7) as [eq1 eq2]. subst. clear H7.
          destruct (rcons_trace_event_eq_inversion _ _ _ _ H1) as [eq1 eq2]. subst. clear H1.
          destruct (rcons_trace_event_eq_inversion _ _ _ _ H0) as [eq1 eq2]. subst. clear H0.
          apply shifting_is_special_case_of_renaming, rcons_renames_rcons.
          -- assert (traces_shift_each_other
                       (num_extra_blocks_t1_t2 + num_extra_blocks_t2_t3) t1 t3) as Hsh.
             {
               apply IHn with (t2 := t2).
               ++ rewrite size_rcons in H. inversion H. reflexivity.
               ++ apply shifting_is_special_case_of_renaming. assumption.
               ++ apply shifting_is_special_case_of_renaming. assumption.
             }
             inversion Hsh. assumption.
          -- intros addr Hshrsfr_t1_x.
             (* Use H4 then H10. Then use transitivity property of 
                event_renames_event_at_addr. *)
             destruct (H4 addr Hshrsfr_t1_x) as [x_renames_x0 Hshrsfr_t2_x0].
             destruct (H10 (rename_addr (sigma_shifting_addr num_extra_blocks_t1_t2) addr)
                           Hshrsfr_t2_x0) as [x0_renames_x1 Hshrsfr_t3_x1].
      - 
      assert (size t2 = size t3) as Hsize23.
      {
        apply (traces_rename_each_other_same_size _ _ t2 t3 H2).
      }
      assert (size t1 = size t3) as Hsize13.
      {
        rewrite Hsize12. assumption.
      }

    Hsize H12 H23. inversion H12. inversion H23. subst.
    move: H12 H23.
    pose (n := size t1).
    induction n eqn:Hn.
    - unfold n in Hn. admit.
    - unfold n in Hn.
    induction (size t1).
    - assert (t2 = nil).
      { apply size0nil. auto. }
      assert (t3 = nil).
      { apply size0nil. auto. }
      subst. intros.
                               

  Lemma traces_shift_each_other_transitive:
    traces_shift_each_other num_extra_blocks_t1_t2 t1 t2 ->
    (forall t3 num_extra_blocks_t2_t3,
        traces_shift_each_other num_extra_blocks_t2_t3 t2 t3 ->
        traces_shift_each_other (num_extra_blocks_t1_t2 + num_extra_blocks_t2_t3) t1 t3
    ).
  Proof.
    induction t1 using last_ind; induction t2 using last_ind; intros.
    - induction t3 using last_ind.
      + apply shifting_is_special_case_of_renaming. apply nil_renames_nil.
      + inversion H0. exfalso. exact (traces_rename_each_other_nil_rcons _ _ _ _ H1).
    - inversion H. exfalso. exact (traces_rename_each_other_nil_rcons _ _ _ _ H1).
    - inversion H. exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H1).
    - induction t3 using last_ind.
      + inversion H0. exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H1).
      + apply shifting_is_special_case_of_renaming. apply rcons_renames_rcons.
        * assert (traces_shift_each_other
                    (num_extra_blocks_t1_t2 + num_extra_blocks_t2_t3) t t3) as Gshift.
          {
            apply IHt.
            
          }
    
    intros H12. inversion H12. subst.
    induction H as [|tprefix1 e1 tprefix2 e2 Hprefix_rename' IH' He1 He2].
    - intros ? ? ?. inversion H. induction t3 using last_ind. subst.
      + apply shifting_is_special_case_of_renaming. apply nil_renames_nil.
      + inversion H. exfalso.
        exact (traces_rename_each_other_nil_rcons _ _ _ _ H3).
    - intros ? ? ?. inversion H. induction t3 using last_ind. subst.
      + inversion H. exfalso.
        exact (traces_rename_each_other_rcons_nil _ _ _ _ H0).
      + induction H0.
        * inversion H12. exfalso.
          exact (traces_rename_each_other_rcons_nil _ _ _ _ H0).
        * inversion H12. inversion H5.
          -- assert (0 = size (rcons tprefix e)) as Hcontra.
             { rewrite <- H10. reflexivity.  }
             rewrite size_rcons in Hcontra. discriminate.
          --destruct (rcons_trace_event_eq_inversion _ _ _ _ H8) as [eq1 eq2]. subst. clear H8.
            destruct (rcons_trace_event_eq_inversion _ _ _ _ H9) as [eq1 eq2]. subst. clear H9.
            assert (traces_shift_each_other num_extra_blocks_t1_t2 tprefix1 tprefix2) as Hsh.
            {
              apply shifting_is_special_case_of_renaming. assumption.
            }
            pose proof (IH' Hsh) as IH''.
            apply shifting_is_special_case_of_renaming.
            apply rcons_renames_rcons.
            ++ assert (traces_shift_each_other
                         (num_extra_blocks_t1_t2 + num_extra_blocks_t2_t3) tprefix1 tprefix')
                as Hsh'.
               {                 
                 apply IH''.
                 assert (traces_shift_each_other (- num_extra_blocks_t1_t2) tprefix2 tprefix1)
                   as H_tp2_tp1.
                 { apply traces_shift_each_other_symmetric. assumption. }
                 (* Here, have tprefix2 -> tprefix1, 
                    tprefix1 -> tprefix, and tprefix -> tprefix'*)
                 (* We do not have the suitable induction hypotheses though. *)
                 SearchAbout tprefix.
                 SearchAbout tprefix2.
                 SearchAbout tprefix'.
                 SearchAbout tprefix.
                 SearchAbout tprefix1 tprefix.
                 SearchAbout tprefix1 tprefix.
                 
                 subst.
                 
                 (*Have 1 -> tprefix and tprefix -> tprefix'*)
               }
        (* Here, H12 is an inconsistent assumption. Or rather, it tells us that
           num_extra_blocks_t1_t2 must be 0.
         *)
        assert (num_extra_blocks_t1_t2 = 0)%Z.
        { admit. }
        (*subst. rewrite Z.add_0_l.*)
        subst. apply shifting_is_special_case_of_renaming. apply rcons_renames_rcons.
        * assert (traces_shift_each_other (0 + num_extra_blocks_t2_t3)
                                          tprefix tprefix') as Hshift.
          {
            apply IHtraces_rename_each_other.
            -- apply traces_shift_each_other_reflexive.
            -- apply shifting_is_special_case_of_renaming. assumption.
          }
          inversion Hshift. assumption.
        * admit.
        * admit.
    - intros ? ? H. inversion H. induction H0. subst.
      + inversion H12. exfalso.
        exact (traces_rename_each_other_rcons_nil _ _ _ _ H0).
      + (* Here, use  IH', not IHtraces_rename_each_other. *)
    (*as [H12'' H12''' H12']*)
    intros ? ? H23. inversion H23. subst. (*as [H23'' H23''' H23']*)
    apply shifting_is_special_case_of_renaming.
    induction H0 as [|tprefix2' e2' tprefix3 e3 Hprefix_rename' IH' He2' He3].
    - induction t1 using last_ind; try apply nil_renames_nil.
      exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H).
    - induction t1 using last_ind.
      + exfalso. exact (traces_rename_each_other_nil_rcons _ _ _ _ H).
    Abort.
    (*
    induction H12 (*as [|tprefix1 e1 tprefix2 e2 Hprefix_rename IH He1 He2]*);
      induction H23' (*as [|tprefix2' e2' tprefix3 e3 Hprefix_rename' IH' He2' He3]*).
    - apply nil_renames_nil.
    - apply rcons_renames_rcons.
      + apply IHH23'.
    induction t1 using last_ind; induction t2 using last_ind; induction t3 using last_ind;
      try apply nil_renames_nil.
    - exfalso. exact (traces_rename_each_other_nil_rcons _ _ _ _ H23').
    - exfalso. exact (traces_rename_each_other_nil_rcons _ _ _ _ H12').
    - exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H12').
    - exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H12').
    - exfalso. exact (traces_rename_each_other_rcons_nil _ _ _ _ H23').
    - apply IHt0.
      + SearchAbout rcons t x t0.
      + assert (0 = size (rcons t3 x)) as Hcontra.
        { rewrite <- H. reflexivity. }
        rewrite size_rcons in Hcontra. discriminate.
      + assert (size (rcons tprefix e) = 0) as Hcontra.
        { rewrite H. reflexivity. }
        rewrite size_rcons in Hcontra. discriminate.
    - inversion 
    induction H12' as [|tprefix1 e1 tprefix2 e2 Hprefix_rename IH He1 He2];
      intros ? ? H23; inversion H23 as [H23'' H23''' H23']; subst;
        apply shifting_is_special_case_of_renaming.
    - induction t3 using last_ind.
      + apply nil_renames_nil. inversion H23'; try apply nil_renames_nil.
        assert (size (rcons tprefix e) = 0) as Hcontra.
        { rewrite H. reflexivity. }
        rewrite size_rcons in Hcontra. discriminate.
        induction H23' as [|tprefix2' e2' tprefix3 e3 Hprefix_rename' IH' He2' He3].
      + inversion H12 as [x y H]. inversion H.
        * assert (0 = size (rcons tprefix1 e1)) as Hcontra.
          { rewrite <- H3. reflexivity.  }
          rewrite size_rcons in Hcontra. discriminate.
        * assert (size (rcons tprefix' e') = 0) as Hcontra.
          { rewrite H3. reflexivity. }
          rewrite size_rcons in Hcontra. discriminate.
    - apply rcons_renames_rcons.
        
    - apply nil_renames_nil.
    - admit. (* This should be an invalid case. *)
    - admit. (* This should be an invalid case. *)
    - 
      apply rcons_renames_rcons.
      + apply IH'. 
        * apply traces_shift_each_other_reflexive.
        *)

*)
End PropertiesOfTheShiftRenaming.


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
                                
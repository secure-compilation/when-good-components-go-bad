Require Import Psatz.
Require Import Lia.
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
      rewrite !Nat2Z.id addnC. rewrite <- leq_subLR. rewrite subKn; assumption.
  Qed.
                                                
  Lemma inv_sigma_right_good_left_good right_addr:
    right_addr_good_for_shifting right_addr ->
    exists left_addr,
      inv_sigma_shifting (care, right_addr) = (care, left_addr) /\
      left_addr_good_for_shifting left_addr.
  Proof.
    destruct right_addr as [lcid lbid].
    unfold right_addr_good_for_shifting, inv_sigma_shifting, left_addr_good_for_shifting.
    intros Hright_good.
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
      assert (lbid <? metadata_size_rhs - metadata_size_lhs = false) as Hnecessary.
      {
        rewrite Nat.ltb_ge. apply/leP. apply leq_trans with (n := metadata_size_rhs); auto.
        apply leq_subr.
      }
      rewrite Hnecessary. split; eauto. simpl.
      destruct (lbid == metadata_size_rhs) eqn:Heq.
      + assert (lbid = metadata_size_rhs) as Heq'.
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
    
End SigmaShifting.

Section SigmaShiftingProperties.
  
  Lemma sigma_shifting_cid_constant:
    forall n1 n2 x, (sigma_shifting n1 n2 x).2.1 = x.2.1.
  Proof. intros. unfold sigma_shifting.
         destruct ((Z.of_nat n1 - Z.of_nat n2 >=? 0)%Z);
           try apply sigma_from_bigger_dom_cid_constant;
           apply inv_sigma_from_bigger_dom_cid_constant.
  Qed.

  Lemma inv_sigma_shifting_cid_constant:
    forall n1 n2 x, (inv_sigma_shifting n1 n2 x).2.1 = x.2.1.
  Proof. intros. unfold inv_sigma_shifting.
         destruct ((Z.of_nat n1 - Z.of_nat n2 >=? 0)%Z);
           try apply sigma_from_bigger_dom_cid_constant;
           apply inv_sigma_from_bigger_dom_cid_constant.
  Qed.

  Lemma sigma_from_bigger_dom_0_id x: sigma_from_bigger_dom 0 x = x.
  Proof. destruct x as [c [cid bid]]. unfold sigma_from_bigger_dom.
         assert (bid <? 0 = false) as Himposs.
         { rewrite Nat.ltb_ge. apply Nat.le_0_l. }
         rewrite Himposs. rewrite subn0 addn0. destruct c; simpl; reflexivity.
  Qed.

  Lemma inv_sigma_from_bigger_dom_0_id x: inv_sigma_from_bigger_dom 0 x = x.
  Proof. destruct x as [c [cid bid]]. unfold inv_sigma_from_bigger_dom.
         assert (bid <? 0 = false) as Himposs.
         { rewrite Nat.ltb_ge. apply Nat.le_0_l. }
         rewrite Himposs. rewrite subn0 addn0. destruct c; simpl; reflexivity.
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
    intros n1 n2 [cdc [cid bid]].
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

  Lemma sigma_shifting_transitive n1 n2 n3 a:
    left_addr_good_for_shifting n1 a ->
    sigma_shifting n2 n3 (care, (sigma_shifting n1 n2 (care, a)).2) =
    sigma_shifting n1 n3 (care, a).
  Proof.
    intros lgood_a.
    destruct (sigma_left_good_right_good n1 n2 a lgood_a) as [a' [Ha'1 Ha'2]].
    assert (left_addr_good_for_shifting n2 a') as lgood_a'.
    { unfold left_addr_good_for_shifting. unfold right_addr_good_for_shifting in Ha'2. auto. }
    unfold sigma_shifting in *.
    destruct (Z.of_nat n2 - Z.of_nat n3 >=? 0)%Z eqn:n2n3;
      destruct (Z.of_nat n1 - Z.of_nat n2 >=? 0)%Z eqn:n1n2;
      destruct (Z.of_nat n1 - Z.of_nat n3 >=? 0)%Z eqn:n1n3.
    - (* n1 >= n2, n2 >= n3, thus n1 >= n3  *)
      move: Ha'1.
      rewrite <- !Nat2Z.inj_sub;
        try (rewrite Nat2Z.inj_le; apply Zle_0_minus_le, Z.geb_le; assumption).
      rewrite !Nat2Z.id.
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
      move=> Ha'1. rewrite Ha'1.
      unfold sigma_from_bigger_dom, inv_sigma_from_bigger_dom in *. simpl in *.
      destruct a as [cid bid]. destruct a' as [cid' bid'].
      unfold left_addr_good_for_shifting, right_addr_good_for_shifting in *.
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
    
  Definition sigma_shifting_addr (a: addr_t) : addr_t :=
    match sigma_shifting metadata_size_lhs metadata_size_rhs (care, a) with
    | (_, a') => a'
    end.

  Definition inv_sigma_shifting_addr (a: addr_t) : addr_t :=
    match inv_sigma_shifting metadata_size_lhs metadata_size_rhs (care, a) with
    | (_, a') => a'
    end.

  Definition left_value_good_for_shifting (v: value) : Prop :=
    match v with
    | Ptr (_, cid, bid, _) => left_addr_good_for_shifting metadata_size_lhs (cid, bid)
    | _ => True
    end.

  Definition right_value_good_for_shifting (v: value) : Prop :=
    match v with
    | Ptr (_, cid, bid, _) => right_addr_good_for_shifting metadata_size_rhs (cid, bid)
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

  Inductive traces_shift_each_other : trace event -> trace event -> Prop :=
  | shifting_is_special_case_of_renaming:
      forall t t',
        traces_rename_each_other sigma_shifting_addr inv_sigma_shifting_addr t t' ->
        traces_shift_each_other t t'.
  
End TheShiftRenaming.

Section PropertiesOfTheShiftRenaming.

  Lemma rename_addr_reflexive n a:
    rename_addr (sigma_shifting_addr n n) a = a.
  Proof. unfold rename_addr, sigma_shifting_addr. rewrite sigma_shifting_n_n_id. auto. Qed.

  Lemma rename_value_reflexive n v:
    rename_value (sigma_shifting_addr n n) v = v.
  Proof. unfold rename_value, rename_value_template.
         destruct v as [ | [[[perm cid] bid] o] | ]; auto. rewrite rename_addr_reflexive. auto.
  Qed.

  Lemma option_rename_value_reflexive n ov:
    option_rename_value (sigma_shifting_addr n n) ov = ov.
  Proof. unfold option_rename_value, omap, obind, oapp. destruct ov as [ | ]; auto.
         by rewrite rename_value_reflexive.
  Qed.
  
  Lemma rename_addr_inverse_rename_addr n1 n2 a:
    rename_addr (sigma_shifting_addr n1 n2) a =
    inverse_rename_addr (inv_sigma_shifting_addr n2 n1) a.
  Proof. unfold rename_addr, inverse_rename_addr, sigma_shifting_addr, inv_sigma_shifting_addr.
         rewrite inv_sigma_shifting_sigma_shifting. auto.
  Qed.

  Lemma option_rename_value_option_inverse_rename_value n2 n1 v:
    option_inverse_rename_value (inv_sigma_shifting_addr n2 n1) v =
    option_rename_value (sigma_shifting_addr n1 n2) v.
  Proof.
    destruct v as [[ | [[[perm cid] bid] o] | ] | ]; auto. simpl.
    rewrite rename_addr_inverse_rename_addr. reflexivity.
  Qed.
  
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
   left_addr_good_for_shifting n1 addr ->
   rename_addr (sigma_shifting_addr n2 n3) (rename_addr (sigma_shifting_addr n1 n2) addr) =
   rename_addr (sigma_shifting_addr n1 n3) addr.
 Proof. intros. unfold rename_addr, sigma_shifting_addr.
        rewrite <- (sigma_shifting_transitive n1 n2 n3); auto.
 Qed.

 Lemma rename_value_transitive n1 n2 n3 v:
   left_value_good_for_shifting n1 v ->
   rename_value (sigma_shifting_addr n2 n3)
                       (rename_value (sigma_shifting_addr n1 n2) v) =
   rename_value (sigma_shifting_addr n1 n3) v.
 Proof.
   unfold left_value_good_for_shifting.
   intros Hgood. destruct v as [ | [[[perm cid] bid] o] | ]; auto. simpl.
   destruct (rename_addr (sigma_shifting_addr n1 n2) (cid, bid)) eqn:Hn1n2. simpl.
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
 Proof. unfold event_renames_event_at_addr. rewrite !rename_addr_reflexive. intros.
        rewrite option_rename_value_reflexive. auto.
 Qed.
 
 Lemma event_rename_transitive n1 n2 n3 addr e1 e2 e3:
   left_addr_good_for_shifting n1 addr ->
   (forall offset, option_left_value_good_for_shifting n1
                                       (Memory.load
                                          (mem_of_event e1)
                                          (Permission.data, addr.1, addr.2, offset)
                                       )
   ) ->
   event_renames_event_at_addr (sigma_shifting_addr n1 n2) addr e1 e2 ->
   event_renames_event_at_addr (sigma_shifting_addr n2 n3)
                               (rename_addr (sigma_shifting_addr n1 n2) addr) e2 e3 ->
   event_renames_event_at_addr (sigma_shifting_addr n1 n3) addr e1 e3.
  Proof.
    intros Haddr_good Hloads_good.
    unfold event_renames_event_at_addr. intros Hn1n2 Hn2n3 offset.
    pose proof Hn2n3 offset as Hn2n3'.
    erewrite rename_addr_transitive, (Hn1n2 offset) in Hn2n3'; auto. erewrite Hn2n3'.
    apply option_rename_value_transitive; auto.
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
  Admitted.

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

Section BehaviorsRelated.

Inductive behavior_rel_behavior (size_meta_t1: nat) (size_meta_t2: nat)
  : @finpref_behavior Events.event -> @finpref_behavior Events.event -> Prop :=
| Terminates_rel_Terminates:
    forall t1 t2,
      traces_shift_each_other size_meta_t1 size_meta_t2 t1 t2 ->
      behavior_rel_behavior size_meta_t1 size_meta_t2 (FTerminates t1) (FTerminates t2)
| Tbc_rel_Tbc:
    forall t1 t2,
      traces_shift_each_other size_meta_t1 size_meta_t2 t1 t2 ->
      behavior_rel_behavior size_meta_t1 size_meta_t2 (FTbc t1) (FTbc t2).
    
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
                                
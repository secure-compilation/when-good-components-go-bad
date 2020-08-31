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

  Variable num_extra_blocks_of_lhs : Z.

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
    | (_, bid) => ((num_extra_blocks_of_lhs >=? 0)%Z ->
                   (bid >= Z.to_nat num_extra_blocks_of_lhs))
    end.

  Definition right_addr_good_for_shifting (right_addr: addr_t) : Prop :=
    match right_addr with
    | (_, bid) => ((~ (num_extra_blocks_of_lhs >=? 0)%Z) ->
                   (bid >= Z.to_nat (- num_extra_blocks_of_lhs)))
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
    destruct (num_extra_blocks_of_lhs >=? 0)%Z eqn:Hge0.
    - eexists. simpl.
      assert (lbid <? Z.to_nat num_extra_blocks_of_lhs = false) as Hcond.
      { rewrite Nat.ltb_ge. apply/leP. apply Hleft_good. trivial. }
      rewrite Hcond. split.
      + reflexivity.
      + simpl. intros H.
        pose proof (@negP true) as H0. assert (~~ true) as H1. apply/H0. apply H.
        simpl in H1. inversion H1.
    - eexists. simpl. split.
      + reflexivity.
      + simpl. intros. apply leq_addl.
  Qed.
                                                
  Lemma inv_sigma_right_good_left_good right_addr:
    right_addr_good_for_shifting right_addr ->
    exists left_addr,
      inv_sigma_shifting (care, right_addr) = (care, left_addr) /\
      left_addr_good_for_shifting left_addr.
  Proof.
    destruct right_addr as [rcid rbid].
    unfold right_addr_good_for_shifting, inv_sigma_shifting, left_addr_good_for_shifting.
    intros Hright_good.
    destruct (num_extra_blocks_of_lhs >=? 0)%Z eqn:Hge0.
    - eexists. simpl. split.
      + reflexivity.
      + simpl. intros. apply leq_addl.
    - eexists. simpl.
      assert (rbid <? Z.to_nat (- num_extra_blocks_of_lhs) = false) as Hcond.
      { rewrite Nat.ltb_ge. apply/leP. apply Hright_good. trivial. }
      rewrite Hcond. split.
      + reflexivity.
      + simpl. intros. inversion H.
  Qed.
    
End SigmaShifting.

Section Renaming.

  Variable sigma: addr_t -> addr_t (*{fmap addr_t -> addr_t}*).
  Variable inverse_sigma: addr_t -> addr_t.

  Hypothesis cancel_inverse_sigma_sigma: cancel inverse_sigma sigma.
  Hypothesis cancel_sigma_inverse_sigma: cancel sigma inverse_sigma.
  Hypothesis sigma_injective: injective sigma.

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

  Lemma inverse_rename_addr_left_inverse addr: inverse_rename_addr (rename_addr addr) = addr.
  Proof.
    unfold inverse_rename_addr, rename_addr. pose proof (cancel_sigma_inverse_sigma addr). auto.
  Qed.

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


  Lemma inverse_rename_addr_right_inverse addr:
    rename_addr (inverse_rename_addr addr) = addr.
  Proof.
    unfold inverse_rename_addr, rename_addr. pose proof (cancel_inverse_sigma_sigma addr). auto.
  Qed.



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
                                
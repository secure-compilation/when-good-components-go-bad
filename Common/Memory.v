Require Import Common.Definitions.
Require Import Common.Values.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : {fmap Block.id -> nat + list value} -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.

  Axiom load_prealloc:
    forall bufs b i,
      load (prealloc bufs) b i =
      if (0 <=? i)%Z then
        match bufs b with
        | Some (inl size) =>
          if (i <? Z.of_nat size)%Z then Some Undef else None
        | Some (inr chunk) => nth_error chunk (Z.to_nat i)
        | None => None
        end
      else None.

  Axiom load_after_alloc:
    forall m m' n b,
      alloc m n = (m',b) ->
    forall b' i,
      b' <> b -> load m' b' i = load m b' i.

  Axiom load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      ((b' <> b \/ i' <> i) /\ load m' b' i' = load m b' i') \/
      load m' b' i' = Some v.

  Axiom store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.

End AbstractComponentMemory.

Module ComponentMemory : AbstractComponentMemory.
  Definition block := list value.

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := mem.

  Definition prealloc (bufs: {fmap Block.id -> nat + list value}) : t :=
    let init_block x := match x with
                        | inl size => repeat Undef size
                        | inr chunk => chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (domm bufs) 0) |}.

  Definition empty :=
    {| content := emptym; nextblock := 0 |}.

  Definition reserve_block (m: t) : t * Block.id :=
    ({| content := content m; nextblock := (1 + nextblock m)%nat |},
     nextblock m).

  Definition alloc m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat Undef size in
    ({| content := setm (content m) fresh_block chunk;
        nextblock := (1 + nextblock m) |},
     fresh_block).

  Definition load m b i : option value :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then nth_error chunk (Z.to_nat i)
      else None
    | None => None
    end.

  Fixpoint block_update data offset val : option block :=
    match data with
    | [] => None (* store out of bounds *)
    | val' :: rest =>
      match offset with
      | O => Some (val :: rest)
      | S offset' =>
        match block_update rest offset' val with
        | Some rest' => Some (val' :: rest')
        | None       => None (* propagate store out of bounds *)
        end
      end
    end.

  Definition store m b i v : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then
        match block_update chunk (Z.to_nat i) v with
        | Some chunk' =>
          Some {| content := setm (content m) b chunk';
                  nextblock := nextblock m |}
        | _ => None
        end
      else None
    | None => None
    end.

  Lemma load_prealloc:
    forall bufs b i,
      load (prealloc bufs) b i =
      if (0 <=? i)%Z then
        match bufs b with
        | Some (inl size) =>
          if (i <? Z.of_nat size)%Z then Some Undef else None
        | Some (inr chunk) => nth_error chunk (Z.to_nat i)
        | None => None
        end
      else None.
  Proof.
    intros bufs b i. unfold load, prealloc. simpl.
    rewrite mapmE. unfold Block.id in *.
    destruct (Z.leb_spec0 0 i) as [i_pos|i_neg].
    - simpl. destruct (bufs b) as [buf|]; trivial.
      simpl. destruct buf as [size|chunk]; trivial.
      destruct (Z.ltb_spec0 i (Z.of_nat size)) as [i_lt_size|i_ge_size].
      + rewrite <- (Z2Nat.id _ i_pos) in i_lt_size.
        rewrite <- Nat2Z.inj_lt in i_lt_size.
        rewrite <- (repeat_length Undef size) in i_lt_size.
        rewrite <- nth_error_Some in i_lt_size.
        destruct (nth_error (repeat Undef size) (Z.to_nat i)) as [v|] eqn:get_i; try congruence.
        apply nth_error_In in get_i.
        apply repeat_spec in get_i.
        now rewrite get_i.
      + rewrite nth_error_None repeat_length Nat2Z.inj_le.
        now rewrite Z2Nat.id // -Z.nlt_ge.
    - simpl. now destruct (bufs b).
  Qed.

  Lemma load_after_alloc:
    forall (m m' : mem) (n : nat) b,
      alloc m n = (m',b) ->
    forall b' i,
      b' <> b -> load m' b' i = load m b' i.
  Proof.
    intros m m' n b Halloc b' i Hb'.
    unfold alloc in Halloc. inversion Halloc. subst.
    unfold load. simpl.
    rewrite setmE.
    now rewrite (introF (b' =P nextblock m :> nat) Hb').
  Qed.

  Ltac inv H := (inversion H; subst; clear H).

  Lemma load_after_update_same:
    forall blk o v blk',
      block_update blk o v = Some blk' ->
      nth_error blk' o = Some v.
  Proof.
    induction blk; intros; inv H.
    destruct o.
    + inv H1; auto.
    + destruct (block_update blk o v) eqn:?; inv H1.
      simpl.
      eapply IHblk; eauto.
  Qed.

  Lemma load_after_update_other:
    forall blk o v o' blk',
      block_update blk o v = Some blk' ->
      o <> o' ->
      nth_error blk' o' = nth_error blk o'.
  Proof.
    induction blk; intros; inv H.
    destruct o.
    + inv H2.
      destruct o'.
      - intuition.
      - auto.
    + destruct (block_update blk o v) eqn:?.
      - inv H2.
        destruct o'.
        * auto.
        * simpl. eauto.
      - inv H2.
  Qed.

  Lemma load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      ((b' <> b \/ i' <> i) /\ load m' b' i' = load m b' i') \/
      load m' b' i' = Some v.
  Proof.
    intros m m' b i v Hstore b' i'.
    (*
    destruct (PMapFacts.eq_dec b b').
    + destruct (Z.eq_dec i i').
      - subst. right.
         unfold load.  unfold store in Hstore.
         destruct (PMap.find (elt:=block) b' (content m)) eqn:?; [| inv Hstore].
         destruct i'; [| |inv Hstore].
         * destruct (block_update b (Z.to_nat 0) v) eqn: E; inv Hstore.
           simpl. (* can't stop from unfolding nth_error...argh *)
           rewrite PMapFacts.add_eq_o; auto.
           apply load_after_update_same in E. apply E.
         * destruct (block_update b (Z.to_nat (Z.pos p)) v) eqn: E; inv Hstore.
           simpl.
           rewrite PMapFacts.add_eq_o; auto.
           eapply load_after_update_same; eauto.
      - left. subst b'. intuition.
        unfold load.  unfold store in Hstore.
        destruct (PMap.find (elt:=block) b (content m)) eqn:?; [| inv Hstore].
        destruct i; [| | inv Hstore].
        * destruct (block_update b0 (Z.to_nat 0) v) eqn: E; inv Hstore.
          simpl.
          rewrite PMapFacts.add_eq_o; auto.
          destruct i'.
          ** intuition.
          ** erewrite load_after_update_other; eauto.
             rewrite Z2Nat.inj_pos. simpl. pose proof (Pos2Nat.is_pos p). omega.
          ** auto.
        * destruct (block_update b0 (Z.to_nat (Z.pos p)) v) eqn: E; inv Hstore.
          simpl.
          rewrite PMapFacts.add_eq_o; auto.
          destruct i'.
          ** erewrite load_after_update_other; eauto.
             rewrite Z2Nat.inj_pos. simpl. pose proof (Pos2Nat.is_pos p). omega.
          ** erewrite load_after_update_other; eauto.
             simpl.
             intro. apply Pos2Nat.inj_iff in H.
             subst.  intuition.
          ** auto.
    +  left. intuition.
       unfold load. unfold store in Hstore.
       destruct (PMap.find (elt:=block) b (content m)) eqn:?; [| inv Hstore].
       destruct i; [| | inv Hstore].
       * destruct (block_update b0 (Z.to_nat 0) v) eqn: E; inv Hstore.
         simpl.
         rewrite PMapFacts.add_neq_o; auto.
       * destruct (block_update b0 (Z.to_nat (Z.pos p)) v) eqn: E; inv Hstore.
         simpl.
         rewrite PMapFacts.add_neq_o; auto.
  Qed.
     *)
  Admitted.

  (** AAA: TODO *)
  Lemma store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.
  Proof. Admitted.

End ComponentMemory.

Module Memory.
  Definition t := NMap ComponentMemory.t.

  Fixpoint empty (cs : list Component.id) :=
    match cs with
    | [] => emptym
    | c::cs' => setm (empty cs') c ComponentMemory.empty
    end.

  Definition alloc (mem : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    match getm mem C with
    | Some memC =>
      let '(memC', b) := ComponentMemory.alloc memC size in
      Some (setm mem C memC', (C, b, 0%Z))
    | None => None
    end.

  Definition load (mem: t) (ptr: Pointer.t) : option value :=
    match getm mem (Pointer.component ptr) with
    | Some memC => ComponentMemory.load memC (Pointer.block ptr) (Pointer.offset ptr)
    | None => None
    end.

  Definition store (mem: t) (ptr: Pointer.t) (v: value) : option t :=
    match getm mem (Pointer.component ptr) with
    | Some memC =>
      match ComponentMemory.store memC (Pointer.block ptr) (Pointer.offset ptr) v with
      | Some memC' => Some (setm mem (Pointer.component ptr) memC')
      | None => None
      end
    | None => None
    end.

  Lemma load_after_store_eq mem ptr v mem' :
    store mem  ptr v = Some mem' ->
    load  mem' ptr   = Some v.
  Proof. Admitted.

  Lemma load_after_store_neq mem ptr v mem' ptr' :
    ptr <> ptr' ->
    store mem  ptr  v = Some mem' ->
    load  mem' ptr'   = load mem ptr'.
  Proof. Admitted.

  Lemma store_after_load mem ptr v v' :
    load mem ptr = Some v ->
    exists mem', store mem ptr v' = Some mem'.
  Proof. Admitted.
End Memory.

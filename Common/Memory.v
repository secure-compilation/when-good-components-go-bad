Require Import Common.Definitions.
Require Import Common.Values.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : list (Block.id * (nat + list value)) -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.

  (* AAA: We need to add some missing lemmas here:

     - The specifications of prealloc, empty, reserve_block.

     - The fact that alloc does not overwrite the contents of existing blocks
       (cf. the comment before [ComponentMemory.t]).

     - Something about the length of the allocated blocks of alloc

  *)

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

  (* AAA: The representation of component memories is problematic, because there
     is nothing that guarantees that [nextblock] is undefined in [content].
     Without this, there is no way of proving the following fact:

     forall m b i v n m',
       load m b i = Some v ->
       alloc m n = Some m' ->
       load m' b i = Some v

     There are two solutions:

     1- Remove the [nextblock] field and change the definition of [alloc] so
        that it allocates the new block under the successor of the greatest
        [positive] in the domain of the memory.

     2- Add the folliwing field to mem:

        forall b, nextblock <= b -> PMap.find b content = None

   *)

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := mem.

  Definition prealloc (bufs: list (Block.id * (nat + list value))) : t :=
    let fix prepare m bs :=
        match bs with
        | [] => m
        | (b, inl size) :: bs' =>
          let chunk := repeat Undef size in
          let m' := {| content := setm (content m) b chunk;
                       nextblock := Nat.max (1+b) (nextblock m) |} in
          prepare m' bs'
        | (b, inr chunk) :: bs' =>
          let m' := {| content := setm (content m) b chunk;
                       nextblock := Nat.max (1+b) (nextblock m) |} in
          prepare m' bs'
        end
    in prepare {| content := emptym;
                  nextblock := 1%nat |} bufs.

  Definition empty := prealloc [].

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
      match i with
      | Z.neg _ => None
      | _ => nth_error chunk (Z.to_nat i)
      end
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
      match i with
      | Z.neg _ => None
      | _ => match block_update chunk (Z.to_nat i) v with
            | Some chunk' =>
              Some {| content := setm (content m) b chunk';
                      nextblock := nextblock m |}
            | _ => None
            end
      end
    | None => None
    end.

  Lemma load_after_alloc:
    forall (m m' : mem) (n : nat) b,
      alloc m n = (m',b) ->
    forall b' i,
      b' <> b -> load m' b' i = load m b' i.
  Proof.
    intros m m' n b Halloc b' i Hb'.
    unfold alloc in Halloc. inversion Halloc. subst.
    unfold load. simpl.
    (*
    erewrite PMapFacts.add_neq_o; auto.
  Qed.
     *)
  Admitted.

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

  (* AAA: Destructing the pointer in the definitions of [load] and [store] is
     not a good idea, because it causes Coq to unfold any expression of the forms
     [load mem (C, b, o)] and [store mem (C, b, o) v]. *)

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

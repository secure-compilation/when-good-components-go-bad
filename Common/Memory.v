Require Import Common.Definitions.
Require Import Common.Values.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : list (Block.id * nat) -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.

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
End AbstractComponentMemory.

Module ComponentMemory : AbstractComponentMemory.
  Definition block := list value.

  Record mem := mkMem {
    content : PMap.t block;
    nextblock : Block.id;
  }.
  Definition t := mem.

  Definition prealloc (bufs: list (Block.id * nat)) : t :=
    let fix prepare m bs :=
        match bs with
        | [] => m
        | (b, size) :: bs' =>
          let chunk := repeat Undef size in
          let m' := {| content := PMap.add b chunk (content m);
                       nextblock := Pos.max (1+b) (nextblock m) |} in
          prepare m' bs'
        end
    in prepare {| content := @PMap.empty block;
                  nextblock := 1%positive |} bufs.

  Definition empty := prealloc [].

  Definition reserve_block (m: t) : t * Block.id :=
    ({| content := content m; nextblock := (1 + nextblock m)%positive |},
     nextblock m).

  Definition alloc m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat Undef size in
    ({| content := PMap.add fresh_block chunk (content m);
        nextblock := (1 + nextblock m)%positive |},
     fresh_block).

  Definition load m b i : option value :=
    match PMap.find b (content m) with
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
    match PMap.find b (content m) with
    | Some chunk =>
      match i with
      | Z.neg _ => None
      | _ => match block_update chunk (Z.to_nat i) v with
            | Some chunk' =>
              Some {| content := PMap.add b chunk' (content m);
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
    erewrite PMapFacts.add_neq_o; auto.
  Qed.

  Ltac inv H := (inversion H; subst; clear H).

  Lemma load_after_update_same:
    forall b o v b',
      block_update b o v = Some b' ->
      nth_error b' o = Some v.
  Proof.
    induction b; intros; inv H.
    destruct o.
    + inv H1; auto.  
    + destruct (block_update b o v) eqn:?; inv H1.
      simpl. 
      eapply IHb; eauto.
  Qed.

  Lemma load_after_update_other:
    forall b o v o' b',
      block_update b o v = Some b' ->
      o <> o' ->
      nth_error b' o' = nth_error b o'.
  Proof.
    induction b; intros; inv H.
    destruct o.
    + inv H2. 
      destruct o'. 
      - intuition.
      - auto.
    + destruct (block_update b o v) eqn:?.
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

End ComponentMemory.

Module Memory.
  Definition t := PMap.t ComponentMemory.t.

  Fixpoint empty (cs: list Component.id) :=
    match cs with
    | [] => @PMap.empty (ComponentMemory.t)
    | c::cs' => PMap.add c ComponentMemory.empty (empty cs')
    end.

  Definition alloc (mem : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    match PMap.find C mem with
    | Some memC =>
      let '(memC', b) := ComponentMemory.alloc memC size in
      Some (PMap.add C memC' mem, (C, b, 0))
    | None => None
    end.

  Definition load (mem : t) (ptr : Pointer.t) : option value :=
    let '(C, b, o) := ptr in
    match PMap.find C mem with
    | Some memC => ComponentMemory.load memC b o
    | None => None
    end.

  Definition store (mem :t) (ptr : Pointer.t) (v : value) : option t :=
    let '(C, b, o) := ptr in
    match PMap.find C mem with
    | Some memC =>
      match ComponentMemory.store memC b o v with
      | Some memC' => Some (PMap.add C memC' mem)
      | None => None
      end
    | None => None
    end.
End Memory.
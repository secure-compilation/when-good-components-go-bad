Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Fixpoint fold_max (l: list (Component.id * Block.id)) : Component.id * Block.id :=
  match l with
  | nil => (0, 0)
  | x :: vs => let maxvs := fold_max vs in (maxn x.1 maxvs.1, maxn x.2 maxvs.2)
  end.

Lemma fold_max_In_leq :
  forall l x,
    In x l ->
    (x.1 <= (fold_max l).1) /\ (x.2 <= (fold_max l).2).
Proof.
  induction l.
  - intros x Hin. exfalso. apply (List.in_nil Hin).
  - intros x Hin. simpl.
    destruct (in_inv Hin) as [xEqa | xInl].
    + subst x. split; apply leq_maxl.
    + destruct (IHl x xInl) as [Ihll Ihlr].
      split; match goal with |- is_true (leq _ (maxn _ ?y)) =>
                             apply leq_trans with (n := y); auto; apply leq_maxr end.
Qed.

Module Type AbstractComponentMemory.
  Parameter t : eqType.

  Parameter prealloc : {fmap Block.id -> nat + list value} -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.
  Parameter load_all : t -> Block.id -> option (list value).
  Parameter store_all : t -> Block.id -> list value -> option t.
  Parameter domm : t -> {fset Block.id}.
  Parameter load_block : t -> Block.id -> list (Component.id * Block.id).
  Parameter next_block : t -> Block.id.
  Parameter max_ptr : t -> Component.id * Block.id.
  Parameter transfer_memory_block : t -> Block.id -> t -> Block.id -> t.
  (*Parameter mem_eqType : eqType.*)

  Axiom load_load_all:
    forall m b i v,
      load m b i = Some v ->
      exists vs, load_all m b = Some vs /\ nth_error vs (Z.to_nat i) = Some v.
  
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

  Axiom load_all_after_alloc:
    forall m m' n b,
      alloc m n = (m', b) ->
      forall b',
        b' <> b -> load_all m' b' = load_all m b'.

  Axiom load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      load m' b' i' =
      if (b', i') == (b, i) then Some v else load m b' i'.

  Axiom load_all_after_store_all:
    forall m m' b vs,
      store_all m b vs = Some m' ->
      forall b',
      load_all m' b' =
      if b' == b then Some vs else load_all m b'.
  
  Axiom load_after_transfer_memory_block:
    forall m b m' b' mres i,
      mres = transfer_memory_block m b m' b' ->
      load m b i = load mres b' i.

  Axiom load_all_after_transfer_memory_block:
    forall m b m' b' mres,
      mres = transfer_memory_block m b m' b' ->
      load_all m b = load_all mres b'.

  Axiom load_unwritten_addr_after_transfer_memory_block:
    forall m b m' b' bl i,
      bl != b' ->
      load m' bl i =
      load (transfer_memory_block m b m' b') bl i.
  
  Axiom load_all_unwritten_addr_after_transfer_memory_block:
    forall m b m' b' bl,
      bl != b' ->
      load_all m' bl =
      load_all (transfer_memory_block m b m' b') bl.
  
  Axiom store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.

  Axiom store_some_load_some:
    forall m b i v',
    (exists v,
        load m b i = Some v)
    <->
    (exists m',
        store m b i v' = Some m').
  
  Axiom store_all_after_load_all:
    forall m b vs vs',
      load_all m b = Some vs ->
      length vs = length vs' ->
      exists m',
        store_all m b vs' = Some m'.
    
  Axiom domm_prealloc :
    forall bufs m,
      prealloc bufs = m ->
      domm m = fmap.domm bufs.

  Axiom domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.

  Axiom max_ptr_load_block_out :
    forall m b x,
      In x (load_block m b) ->
      (x.1 <= (max_ptr m).1 /\ x.2 <= (max_ptr m).2).

  Axiom load_block_load :
    forall m b ptrc ptrb,
      In (ptrc, ptrb) (load_block m b) <->
      exists ptro i, load m b i = Some (Ptr (Permission.data, ptrc, ptrb, ptro)).

  Axiom load_domm :
    forall m b i v,
      load m b i = Some v ->
      In b (domm m).

  Axiom next_block_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      (b = next_block m /\ next_block m' = next_block m + 1).

  Axiom next_block_store_stable :
    forall m m' b i v,
      store m b i v = Some m' ->
      next_block m = next_block m'.
  
End AbstractComponentMemory.

Module ComponentMemory : AbstractComponentMemory.
  Definition block := list value.

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  (*Definition t := mem.*)

  Definition eqCompMem compMem1 compMem2 :=
    (content compMem1 == content compMem2) && (nextblock compMem1 == nextblock compMem2).
  
  Lemma eqCompMemP : Equality.axiom eqCompMem.
  Proof.
    move. intros x y. apply iff_reflect. unfold eqCompMem. split.
    - intros. subst. rewrite !eq_refl. auto.
    - intros. pose proof (andP H) as [Hcontent Hnextblock].
      destruct x, y. simpl in *.
      pose proof (eqP Hcontent). pose proof (eqP Hnextblock). subst. reflexivity.
  Qed.
  
  Definition compMem_eqMixin: Equality.mixin_of mem := EqMixin eqCompMemP.
  Canonical t := Eval hnf in EqType mem compMem_eqMixin.

  Definition next_block (m: t) := nextblock m.
  
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

  Definition store m b i v : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then
        match list_upd chunk (Z.to_nat i) v with
        | Some chunk' =>
          Some {| content := setm (content m) b chunk';
                  nextblock := nextblock m |}
        | _ => None
        end
      else None
    | None => None
    end.

  Definition load_all m b : option (list value) := getm (content m) b.

  Definition store_all m b vs : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if length chunk == length vs then
        Some {| content := setm (content m) b vs; nextblock := nextblock m |}
      else None
    | None => None
    end.

  Definition domm (m : t) := @domm nat_ordType block (content m).

  Fixpoint block_ids_in_chunk chunk : list (Component.id * Block.id) :=
    match chunk with
    | nil => nil
    | v :: vs => match v with
                 | Ptr (ptrp, ptrc, ptrb, _) =>
                   if Nat.eqb ptrp Permission.data then
                     [(ptrc, ptrb)] ++ block_ids_in_chunk vs
                   else
                     block_ids_in_chunk vs
                 | _ => block_ids_in_chunk vs
                 end
    end.
  
  Definition load_block (m: t) (b: Block.id) : list (Component.id * Block.id) :=
    match getm (content m) b with
    | Some chunk => block_ids_in_chunk chunk
    | None => nil
    end.

  Lemma In_load_block_block_in_domm :
    forall m b x,
      In x (load_block m b) -> b \in domm m.
  Proof.
    intros m b x Hin.
    unfold domm. apply/dommP. unfold load_block in Hin.
    destruct (getm (content m) b) eqn:e.
    - exists b0. auto.
    - exfalso. pose (List.in_nil Hin). auto.
  Qed.
  
  Definition max_ptr_of_block (m: t) (b: Block.id) : Component.id * Block.id :=
    fold_max (load_block m b).

  Definition max_ptr_per_block (m: t) := map (max_ptr_of_block m) (domm m).
  
  Definition max_ptr (m: t) : Component.id * Block.id :=
    fold_max (max_ptr_per_block m).
    
  Lemma max_ptr_of_block_In_leq :
    forall m b x,
      In x (load_block m b) ->
      x.1 <= (max_ptr_of_block m b).1 /\ x.2 <= (max_ptr_of_block m b).2.
  Proof.
    unfold max_ptr_of_block.
    intros m b x Hin. apply fold_max_In_leq. trivial.
  Qed.

  Lemma max_ptr_In_leq :
    forall m x,
    (exists y, In y (max_ptr_per_block m) /\ x.1 <= y.1 /\ x.2 <= y.2)
    ->
    x.1 <= (max_ptr m).1 /\ x.2 <= (max_ptr m).2.
  Proof.
    unfold max_ptr.
    intros m x [y [Hin [H1 H2]]].
    - split.
      + apply leq_trans with (n := y.1). trivial. apply fold_max_In_leq. trivial.
      + apply leq_trans with (n := y.2). trivial. apply fold_max_In_leq. trivial.
  Qed.

  Lemma max_ptr_of_block_In_max_ptr_per_block :
    forall m b,
      b \in domm m -> In (max_ptr_of_block m b) (max_ptr_per_block m).
  Proof.
    intros m b bIn.
    pose (In_in' := In_in (max_ptr_of_block m b) (max_ptr_per_block m)).
    rewrite <- In_in'.
    unfold max_ptr_per_block.
    apply map_f.
    exact bIn.
  Qed.
  
  Lemma In_load_block_In_max_ptr_per_block_or_less :
    forall m b x,
      In x (load_block m b) ->
      exists y, In y (max_ptr_per_block m) /\ x.1 <= y.1 /\ x.2 <= y.2.
  Proof.
    intros m b x Hinload.
    pose (bIndomm := In_load_block_block_in_domm m b x Hinload).
    destruct (max_ptr_of_block_In_leq m b x Hinload) as [Hl Hr].
    pose (Inyperblock := max_ptr_of_block_In_max_ptr_per_block m b bIndomm).
    exists (max_ptr_of_block m b). auto.
  Qed.
    
  Lemma max_ptr_load_block_out :
    forall m b x,
      In x (load_block m b) ->
      (x.1 <= (max_ptr m).1 /\ x.2 <= (max_ptr m).2).
  Proof.
    intros m b x Hloadblock.
    apply max_ptr_In_leq.
    apply In_load_block_In_max_ptr_per_block_or_less with (b := b). trivial.
  Qed.

  Lemma nth_error_block_ids_in_chunk :
    forall ch c b off i,
      nth_error ch i = Some (Ptr (Permission.data, c, b, off)) ->
      In (c, b) (block_ids_in_chunk ch).
  Proof.
    intros ch c b off i Hnth.
    apply nth_error_In in Hnth. induction ch as [| a ch' Ich]; simpl.
    - apply (List.in_nil Hnth).
    - destruct a as [v | p |]; destruct (in_inv Hnth) as [equu | Hch'].
      + discriminate.
      + exact (Ich Hch').
      + inversion equu. simpl. left. reflexivity.
      + destruct p as [[[ptrp ptrc] ptrb] ptro].
        destruct (ptrp =? Permission.data).
        * apply List.in_cons. exact (Ich Hch').
        * exact (Ich Hch').
      + discriminate.
      + exact (Ich Hch').
  Qed.
  
  Lemma block_ids_in_chunk_nth_error :
    forall ch c b,
      In (c, b) (block_ids_in_chunk ch) ->
      exists off i, nth_error ch i = Some (Ptr (Permission.data, c, b, off)).
  Proof.
    induction ch; simpl; intros c b H.
    - exfalso. auto.
    - destruct a as [v | p |].
      + destruct (IHch c b H) as [off [i ntherrorEq]]. exists off.
        apply In_nth_error. apply List.in_cons. apply nth_error_In with (n := i). auto.
      + destruct p as [[[ptrp ptrc] ptrb] ptro].
        destruct (ptrp =? Permission.data) eqn:ptrpE.
        * apply in_inv in H. destruct H as [Heq | HIH].
          -- exists ptro. exists 0. inversion Heq.
             apply Nat.eqb_eq in ptrpE. rewrite ptrpE. auto.
          -- destruct (IHch c b HIH) as [off [i ntherrorEq]]. exists off.
             apply In_nth_error. apply List.in_cons. apply nth_error_In with (n := i). auto.
        * destruct (IHch c b H) as [off [i ntherrorEq]]. exists off.
          apply In_nth_error. apply List.in_cons. apply nth_error_In with (n := i). auto.
      + destruct (IHch c b H) as [off [i ntherrorEq]]. exists off.
        apply In_nth_error. apply List.in_cons. apply nth_error_In with (n := i). auto.
  Qed.
  
  Lemma load_block_load :
    forall m b ptrc ptrb,
      In (ptrc, ptrb) (load_block m b) <->
      exists ptro i, load m b i = Some (Ptr (Permission.data, ptrc, ptrb, ptro)).
  Proof.
    intros m b ptrc ptrb. unfold load_block. unfold load.
    split.
    - intros Hin.
      destruct (content m b) eqn:e.
      + pose (exNat := block_ids_in_chunk_nth_error b0 ptrc ptrb Hin).
        destruct exNat as [off [iNat g]].
        pose (pfnonneg := N2Z.is_nonneg (N.of_nat iNat)).
        exists off. exists (Z.of_N (N.of_nat iNat)).
        destruct (0 <=? Z.of_N (N.of_nat iNat))%Z eqn:ee.
        * rewrite nat_N_Z. rewrite Nat2Z.id. auto.
        * erewrite <- Z.leb_le in pfnonneg. rewrite pfnonneg in ee. discriminate.
      + exfalso. pose (F := List.in_nil Hin). auto.
    - intros [ptro [i Hload]].
      destruct (content m b) eqn:e.
      + apply nth_error_block_ids_in_chunk with (off := ptro) (i := Z.to_nat i).
        destruct ((0 <=? i)%Z); auto. discriminate.
      + discriminate.
  Qed.

  Definition transfer_memory_block (src: t) (src_b: Block.id) (dst: t) (dst_b: Block.id) : t :=
    match getm (content src) src_b with
    | Some chunk =>
      {| content := setm (content dst) dst_b chunk;
         nextblock := nextblock dst (* What is the right value of nextblock? *)
      |}
    | None =>
      {| content := remm (content dst) dst_b;
         nextblock := nextblock dst (* What is the right value of nextblock? *)
      |}
    end.

  Lemma load_domm :
    forall m b i v,
      load m b i = Some v ->
      In b (domm m).
  Proof.
    intros m b i v Hload. unfold load in Hload. unfold domm.
    destruct ((content m) b) eqn:e; try discriminate.
    rewrite <- In_in with (s := fmap.domm (content m)).
    apply/dommP. exists b0. auto.
  Qed.
  
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

  Lemma load_load_all:
    forall m b i v,
      load m b i = Some v ->
      exists vs, load_all m b = Some vs /\ nth_error vs (Z.to_nat i) = Some v.
  Proof.
    intros ? ? ? ?. unfold load, load_all.
    destruct ((content m) b); intros Hload; try discriminate.
    eexists. split; try reflexivity. rewrite <- Hload.
    destruct (0 <=? i)%Z; auto. discriminate.
  Qed.

  Lemma load_all_after_alloc:
    forall m m' n b,
      alloc m n = (m', b) ->
      forall b',
        b' <> b -> load_all m' b' = load_all m b'.
  Admitted.

  Lemma load_all_after_store_all:
    forall m m' b vs,
      store_all m b vs = Some m' ->
      forall b',
      load_all m' b' =
      if b' == b then Some vs else load_all m b'.
  Admitted.
  
  Lemma load_all_after_transfer_memory_block:
    forall m b m' b' mres,
      mres = transfer_memory_block m b m' b' ->
      load_all m b = load_all mres b'.
  Admitted.
    
  Lemma load_all_unwritten_addr_after_transfer_memory_block:
    forall m b m' b' bl,
      bl != b' ->
      load_all m' bl =
      load_all (transfer_memory_block m b m' b') bl.
  Admitted.
  
  Lemma store_all_after_load_all:
    forall m b vs vs',
      load_all m b = Some vs ->
      length vs = length vs' ->
      exists m',
        store_all m b vs' = Some m'.
  Admitted.

  Ltac inv H := (inversion H; subst; clear H).

  Lemma load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      load m' b' i' =
      if (b', i') == (b, i) then Some v else load m b' i'.
  Proof.
    move=> m m' b i v Hstore b' i'.
    move: Hstore; rewrite /store /load.
    case m_b: (content m b) => [chunk|] //=.
    case: (Z.leb_spec0 0 i)=> [i_pos|//] /=.
    case upd_chunk: (list_upd chunk (Z.to_nat i) v) => [chunk'|] // [<- {m'}] /=.
    rewrite setmE xpair_eqE; case: (b' =P b) => [-> {b'}|] //=.
    case: (i' =P i) => [-> {i'}|i'_ne_i] /=.
    - move/Z.leb_spec0: i_pos => ->; exact: list_upd_nth_error_same upd_chunk.
    - rewrite m_b; case: (Z.leb_spec0 0 i')=> [i'_pos|] //=.
      apply: list_upd_nth_error_other; eauto.
      contradict i'_ne_i; symmetry; exact: Z2Nat.inj i'_ne_i.
  Qed.

  Lemma load_after_transfer_memory_block:
    forall m b m' b' mres i,
      mres = transfer_memory_block m b m' b' ->
      load m b i = load mres b' i.
  Proof.
    move=> m b m' b' mres i Hres. rewrite Hres /transfer_memory_block /setmE /load.
    case m_b: (content m b)=> [chunk|] //.
    - now rewrite setmE eq_refl.
    - now rewrite remmE eq_refl.
  Qed.

  Lemma load_unwritten_addr_after_transfer_memory_block:
    forall m b m' b' bl i,
      bl != b' ->
      load m' bl i =
      load (transfer_memory_block m b m' b') bl i.
  Proof.
    move=> m b m' b' bl i Hneq. rewrite /transfer_memory_block /setmE /load.
    case m_b: (content m b)=> [chunk|] //;
                                       case m'bl: (content m' bl)=> [chunkbl|] //.
    - simpl. rewrite setmE. case blb': (bl == b')=> //.
      + rewrite blb' in Hneq. easy.
      + rewrite m'bl //.
    - simpl. rewrite setmE. case blb': (bl == b')=> //.
      + rewrite blb' in Hneq. easy.
      + rewrite m'bl //.
    - simpl. rewrite remmE. case blb': (bl == b')=> //.
      + rewrite blb' in Hneq. easy.
      + rewrite m'bl //.
    - simpl. rewrite remmE. case blb': (bl == b')=> //. rewrite m'bl //.
  Qed.
      
  Lemma store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.
  Proof.
    move=> m b i v v'; rewrite /load /store.
    case m_b: (content m b)=> [chunk|] //.
    case: (Z.leb_spec0 0 i)=> [i_pos|] //= chunk_i.
    suffices [? ->] :
      exists chunk', list_upd chunk (Z.to_nat i) v' = Some chunk' by eauto.
    elim: {m_b i i_pos} chunk (Z.to_nat i) chunk_i => [|v'' chunk IH] [|i] //=.
    - by eauto.
    - by move=> /IH [chunk' ->]; eauto.
  Qed.

  Lemma list_upd_some_nth_error_some {T: Type}:
    forall chunk n v' chunk',
    list_upd chunk n v' = Some chunk' ->
    exists v : T, nth_error chunk n = Some v.
  Proof.
    intros chunk.
    induction chunk as [|v_ih]; try discriminate.
    intros n v' chunk' Hsome.
    simpl in Hsome.
    destruct n as [|n'] eqn:Hn.
    - eexists. by simpl.
    - destruct (list_upd chunk n' v') as [rest'|] eqn:Hrest'; try discriminate.
      specialize (IHchunk _ _ _ Hrest') as [v'' Hv''].
      eexists. simpl. eassumption.
  Qed.
  
  Lemma store_some_load_some:
    forall m b i v',
    (exists v,
        load m b i = Some v)
    <->
    (exists m',
        store m b i v' = Some m').
  Proof.
    intros. split; intros [e Hsome].
    - eapply store_after_load; eauto.
    - rewrite /load. rewrite /store in Hsome.
      case m_b: (content m b)=> [chunk|] //; rewrite m_b in Hsome; try discriminate.
      destruct (0 <=? i)%Z eqn:ei; try discriminate.
      destruct (list_upd chunk (Z.to_nat i) v') as [chunk'|] eqn:echunk;
        try discriminate.
      by specialize (list_upd_some_nth_error_some _ _ _ _ echunk).
  Qed.
      
  Lemma domm_prealloc :
    forall bufs m,
      prealloc bufs = m ->
      domm m = fmap.domm bufs.
  Admitted.

  Lemma domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.
  Admitted.

  Lemma next_block_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      (b = next_block m /\ next_block m' = next_block m + 1).
  Proof.
    unfold alloc. intros ? ? ? ? Halloc. inversion Halloc. subst.
    intuition. simpl. unfold next_block. by intuition.
  Qed.
    
  Lemma next_block_store_stable :
    forall m m' b i v,
      store m b i v = Some m' ->
      next_block m = next_block m'.
  Proof.
    unfold store, next_block. intros ? ? ? ? ? Hstore.
    destruct (content m b) as [ch|]; try discriminate.
    destruct (0 <=? i)%Z; try discriminate.
    destruct (list_upd ch (Z.to_nat i) v); try discriminate.
    inversion Hstore. by subst.
  Qed.
  
End ComponentMemory.

Module ComponentMemoryExtra.
  Import ComponentMemory.
  (* RB: NOTE: Prove composition as needed. Blocks are emitted in the same order
     as the sequence of single calls. *)
  Definition reserve_blocks (mem : t) (n : nat) : t * list Block.id :=
    let acc '(mem, bs) :=
        let '(mem', b) := reserve_block mem in
        (mem', bs ++ [b]) in
    iter n acc (mem, []).

  Lemma reserve_blocks_length (mem mem' : t) (n : nat) (bs : list Block.id) :
    ComponentMemoryExtra.reserve_blocks mem n = (mem', bs) ->
    length bs = n.
  Proof.
    generalize dependent mem'. generalize dependent n.
    induction bs using rev_ind.
    - intros n mem' H.
      destruct n; auto.
      unfold reserve_blocks in H.
      simpl in H.
      destruct (iter n (fun '(mem, bs) => let '(mem', b) := reserve_block mem in (mem', bs ++ [b])) (mem, [])).
      destruct (reserve_block s).
      inversion H. symmetry in H2; now apply app_cons_not_nil in H2.
    - intros n mem' H.
      destruct n; auto.
      + simpl in *. inversion H. now apply app_cons_not_nil in H2.
      + rewrite app_length plus_comm. simpl.
        unfold reserve_blocks in H.
        simpl in H.
        destruct (iter n (fun '(mem, bs) => let '(mem', b) := reserve_block mem in (mem', bs ++ [b])) (mem, []))
          as [mem'' bs'] eqn:Hiter.
        rewrite (IHbs n mem'').
        reflexivity.
        destruct (reserve_block mem''). simpl in H.
        inversion H.
        assert (bs' = bs).
        {
          clear -H2. generalize dependent bs'.
          induction bs; destruct bs'; intros H; auto.
          - inversion H. symmetry in H2; now apply app_cons_not_nil in H2.
          - inversion H; subst; now apply app_cons_not_nil in H2.
          - inversion H; subst. simpl in *. rewrite (IHbs _ H2); reflexivity.
        }
        subst bs'.
        rewrite -Hiter. reflexivity.
  Qed.
  
End ComponentMemoryExtra.

Module Memory.
  
    Definition tt := NMap ComponentMemory.t.
  
    Definition eqMem (m1 m2: tt) := m1 == m2.
  
    Lemma eqMemP : Equality.axiom eqMem.
    Proof. move. intros x y. unfold eqMem. apply/eqP. Qed.
  
    Definition mem_eqMixin: Equality.mixin_of tt := EqMixin eqMemP.
    Canonical t := Eval hnf in EqType tt mem_eqMixin.
  
  Fixpoint empty (cs : list Component.id) :=
    match cs with
    | [] => emptym
    | c::cs' => setm (empty cs') c ComponentMemory.empty
    end.

  Definition alloc (mem : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    match mem C with
    | Some memC =>
      let '(memC', b) := ComponentMemory.alloc memC size in
      Some (setm mem C memC', (Permission.data, C, b, 0%Z))
    | None => None
    end.

  Definition load (mem: t) (ptr: Pointer.t) : option value :=
    if Pointer.permission ptr =? Permission.data then
      match mem (Pointer.component ptr) with
      | Some memC => ComponentMemory.load memC (Pointer.block ptr) (Pointer.offset ptr)
      | None => None
      end
    else None.

  Definition store (mem: t) (ptr: Pointer.t) (v: value) : option t :=
    if Pointer.permission ptr =? Permission.data then
      match mem (Pointer.component ptr) with
      | Some memC =>
        match ComponentMemory.store memC (Pointer.block ptr) (Pointer.offset ptr) v with
        | Some memC' => Some (setm mem (Pointer.component ptr) memC')
        | None => None
        end
      | None => None
      end
    else None.

  Definition load_all (mem: t) (addr: Component.id * Block.id) : option (list value) :=
    match mem (addr.1) with
    | Some memC => ComponentMemory.load_all memC addr.2
    | None => None
    end.

  Definition store_all (mem: t) (addr: Component.id * Block.id) (vs: list value)
    : option Memory.t :=
    match mem (addr.1) with
    | Some memC => match ComponentMemory.store_all memC addr.2 vs with
                   | Some memC' => Some (setm mem (addr.1) memC')
                   | None => None
                   end
    | None => None
    end.

  Lemma load_after_store mem ptr v mem' ptr' :
    store mem  ptr v = Some mem' ->
    load mem' ptr' =
    if ptr' == ptr then Some v else load mem ptr'.
  Proof.
    case: ptr ptr'=> [[[p c] b] off] [[[p' c'] b'] off']; rewrite /store /load /=.
    case perm_data: (p =? Permission.data) => //.
    case perm_data': (p' =? Permission.data) => //.
    - case mem_c: (mem c) => [bs|] //.
      case bs_ptr: (ComponentMemory.store bs b off v) => [bs'|] //= [<- {mem'}].
      rewrite !xpair_eqE setmE; case: (c' =P c) => [-> {c'}|] //=.
      + pose (ComponentMemory.load_after_store _ _ _ _ _ bs_ptr) as compLoad.
        erewrite compLoad. erewrite mem_c.
        apply Nat.eqb_eq in perm_data. apply Nat.eqb_eq in perm_data'.
        rewrite <- perm_data in perm_data'. rewrite perm_data' eq_refl. auto.
      + rewrite andbF. auto.
    - destruct ((p', c', b', off') == (p, c, b, off)) eqn:p'p; auto.
      pose (eqP p'p) as e. inversion e as [pp'e]. rewrite pp'e in perm_data'.
      rewrite perm_data in perm_data'. discriminate.
  Qed.

  Lemma load_all_after_store_all mem addr vs mem' addr' :
    store_all mem addr vs = Some mem' ->
    load_all mem' addr' = if addr' == addr then Some vs else load_all mem addr'.
  Admitted.

  Lemma load_after_store_eq mem ptr v mem' :
    store mem  ptr v = Some mem' ->
    load  mem' ptr   = Some v.
  Proof. by move=> /load_after_store ->; rewrite eqxx. Qed.


  Lemma load_after_store_neq mem ptr v mem' ptr' :
    ptr <> ptr' ->
    store mem  ptr  v = Some mem' ->
    load  mem' ptr'   = load mem ptr'.
  Proof. by move=> /eqP/negbTE ne /load_after_store ->; rewrite eq_sym ne. Qed.

  Lemma load_after_alloc mem cid sz mem' ptr' ptr:
    alloc mem cid sz = Some (mem', ptr') ->
    (Pointer.component ptr, Pointer.block ptr) <> (Pointer.component ptr', Pointer.block ptr') ->
    load mem' ptr = load mem ptr.
  Proof.
    unfold alloc, load.
    destruct (mem cid) as [cMem | ] eqn:Hmemcid.
    - destruct (ComponentMemory.alloc cMem sz) as [new_cMem newb] eqn:Hcomp_alloc.
      intros H. inversion H. subst.
      destruct (Pointer.permission ptr =? Permission.data) ; auto.
      rewrite setmE.
      intros Hptr_cid_or_bid.
      destruct (Pointer.component ptr == cid) eqn:Hptr_eq_cid; rewrite Hptr_eq_cid; auto;
        destruct (Pointer.block ptr == newb) eqn:Hptr_block_eq.
      + (* true, true. contradiction to Hptr_cid_or_bid *)
        assert (Pointer.component ptr = cid). by apply/eqP.
        assert (Pointer.block ptr = newb). by apply/eqP. subst.
          by simpl in *.
      + (* true, false *)
        assert (Pointer.component ptr = cid). by apply/eqP. subst.
        rewrite Hmemcid. eapply ComponentMemory.load_after_alloc; eauto.
    - by intros.
  Qed.

  Lemma component_of_alloc_ptr mem cid sz mem' ptr':
    alloc mem cid sz = Some (mem', ptr') ->
    Pointer.component ptr' = cid.
  Proof. unfold alloc. intros H. destruct (mem cid) as [c |] eqn:Hmemcid; try discriminate.
         destruct (ComponentMemory.alloc c sz). by inversion H.
  Qed.
         
  Lemma store_after_load mem ptr v v' :
    load mem ptr = Some v ->
    exists mem', store mem ptr v' = Some mem'.
  Proof.
    case: ptr=> [[[p c] b] off]; rewrite /load /store /=.
    case perm_data: (p =? Permission.data) => //.
    case mem_c: (mem c)=> [bs|] //=.
    case/(ComponentMemory.store_after_load _ _ _ _ v')=> [bs' ->].
    by eauto.
  Qed.

  Lemma store_some_load_some:
    forall m ptr v',
    (exists v,
        load m ptr = Some v)
    <->
    (exists m',
        store m ptr v' = Some m').
  Proof.
    intros m [[[perm cid] bid] off] v'. unfold load, store.
    simpl. destruct (perm =? Permission.data) eqn:eperm; simpl.
    - destruct (m cid) as [compMem|] eqn:emcid; simpl.
      + split; intros H.
        * assert (exists compMem',
                     ComponentMemory.store compMem bid off v' = Some compMem') as [? G].
            by eapply ComponentMemory.store_some_load_some.
            rewrite G. eexists. reflexivity.
        * eapply ComponentMemory.store_some_load_some.
          destruct (ComponentMemory.store compMem bid off v') as [compMem'|] eqn:G.
          -- exists compMem'. exact G.
          -- destruct H. discriminate.
      + split; intros [? ?]; discriminate.
    - split; intros [? ?]; discriminate.
  Qed.
      
  Lemma load_some_permission mem ptr v :
    load mem ptr = Some v -> Pointer.permission ptr = Permission.data.
  Proof.
    unfold load.
    destruct (Pointer.permission ptr =? Permission.data) eqn:eperm; try discriminate.
    intros ?. apply/eqP. auto.
  Qed.

  Lemma store_some_permission mem ptr v mem' :
    store mem ptr v = Some mem' -> Pointer.permission ptr = Permission.data.
  Proof.
    unfold store.
    destruct (Pointer.permission ptr =? Permission.data) eqn:eperm; try discriminate.
    intros ?. apply/eqP. auto.
  Qed.

  Definition addresses_of_compMems mem : NMap {fset Block.id} :=
    mapm ComponentMemory.domm mem.

  Definition cid_blocks_to_seq_of_addresses (cid_blocks : Component.id * {fset Block.id})
    : {fset (Component.id * Block.id)} :=
    fset (map (fun bid => (cid_blocks.1, bid)) cid_blocks.2).

  Definition addresses_of_mem mem : {fset (Component.id  * Block.id)} :=
    (\bigcup_(cid_blocks <- (elementsm (addresses_of_compMems mem)))
     cid_blocks_to_seq_of_addresses cid_blocks)%fset.

  Lemma load_Some_addresses_of_compMems (mem: Memory.t) cid compMem bid off addresses_compMem:
    mem cid = Some compMem ->
    ComponentMemory.load compMem bid off ->
    (addresses_of_compMems mem) cid = Some addresses_compMem ->
    bid \in addresses_compMem.
  Proof.
    intros Hmem Hload Haddrs.
    destruct (ComponentMemory.load compMem bid off) as [v|] eqn:Hv; try discriminate.
    pose proof (ComponentMemory.load_domm _ _ _ _ Hv) as HIn.
    pose proof (In_in bid (ComponentMemory.domm compMem)) as HIn_in.
    rewrite <- HIn_in in HIn.
    unfold addresses_of_compMems in Haddrs.
    rewrite mapmE in Haddrs. unfold omap, obind, oapp in Haddrs.
    rewrite Hmem in Haddrs. inversion Haddrs. subst. assumption.
  Qed.
  
  Lemma load_Some_addresses_of_mem mem cid bid off:
    load mem (Permission.data, cid, bid, off) ->
    (cid, bid) \in addresses_of_mem mem.
  Proof.
    intros H_isSome. unfold load in *. simpl in H_isSome.
    destruct (mem cid) as [compMem|] eqn:Hmem_cid; try discriminate.
    unfold addresses_of_mem. apply/bigcupP.
    destruct ((addresses_of_compMems mem) cid) as [addresses_cid|] eqn:e_addr_cid.
    - apply BigCupSpec with (i := (cid, addresses_cid)); auto.
      + simpl. unfold addresses_of_compMems in *.
        rewrite mapmE in e_addr_cid.
        unfold omap, obind, oapp in e_addr_cid. rewrite Hmem_cid in e_addr_cid.
        inversion e_addr_cid. subst.
        pose (f := fun (p: (Component.id * ComponentMemory.t)%type) =>
                     (p.1, ComponentMemory.domm p.2)).
        pose proof (@map_f _ _ f mem) as Hmap_f.
        assert (f (cid, compMem) = (cid, ComponentMemory.domm compMem)) as Hfx by auto.
        rewrite <- Hfx. apply Hmap_f. apply/getmP. assumption.
      + unfold cid_blocks_to_seq_of_addresses. rewrite in_fset.
        apply/mapP. eexists; auto. simpl.
        apply (load_Some_addresses_of_compMems mem cid compMem bid off); assumption.
    - unfold addresses_of_compMems in e_addr_cid. rewrite mapmE in e_addr_cid.
      unfold omap, obind, oapp in e_addr_cid. rewrite Hmem_cid in e_addr_cid. discriminate.
  Qed.        
  
End Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Clean these lemmas and their weak variants *)

Definition to_partial_memory (mem : Memory.t) (ctx : {fset Component.id}) :=
  filterm (fun k _ => negb (k \in ctx)) mem.

Definition transfer_memory_block (src: Memory.t) (src_addr: Component.id * Block.id)
           (dst: Memory.t) (dst_addr: Component.id * Block.id) : Memory.t :=
  match src (src_addr.1), dst (dst_addr.1) with
  | Some src_cmem, Some dst_cmem =>
    let res_cmem :=
        ComponentMemory.transfer_memory_block src_cmem src_addr.2 dst_cmem dst_addr.2 in
    (setm dst (dst_addr.1) res_cmem)
  | _, _ => dst
  end.

Fixpoint transfer_memory_blocks_helper (src: Memory.t) (dst: Memory.t)
         (sdaddrs: seq ((Component.id * Block.id) * (Component.id * Block.id))) : Memory.t :=
  match sdaddrs with
  | nil => dst
  | (sa, da) :: sdtl =>
    transfer_memory_blocks_helper src (transfer_memory_block src sa dst da) sdtl
  end.

Definition transfer_memory_blocks (src: Memory.t) (src_addrs: seq (Component.id * Block.id))
         (dst: Memory.t) (dst_addrs: seq (Component.id * Block.id)) : Memory.t :=
  transfer_memory_blocks_helper src dst (zip src_addrs dst_addrs).

Lemma transfer_memory_block_preserves_domm src srca (dst: Memory.t) dsta a:
  a \in domm dst <-> a \in domm (transfer_memory_block src srca dst dsta).
Proof.
  split;
    rewrite /transfer_memory_block;
    destruct (src srca.1) as [srcC|]; auto;
      destruct (dst dsta.1) as [dstC|] eqn:ed; auto;
        rewrite domm_set in_fsetU1; move=> Ha.
  - rewrite Ha orbT. auto.
  - destruct (orP Ha) as [Hadsta | Hauto]; auto.
    pose proof (eqP Hadsta) as H. rewrite <- H in ed.
    apply/dommP. exists dstC. assumption.
Qed.

Lemma transfer_memory_blocks_helper_preserves_domm:
  forall z src (dst: Memory.t) a,
  a \in domm dst <-> a \in domm (transfer_memory_blocks_helper src dst z).
Proof.
  move=> z. induction z; simpl; auto; move => src dst a0.
  - split; auto.
  - destruct a as [sa da]. simpl.
    pose proof transfer_memory_block_preserves_domm src sa as H.
    pose proof IHz src (transfer_memory_block src sa dst da) a0 as [IHlr IHrl].
    split.
    + intros Ha0_dst. apply IHlr, H. auto.
    + intros Ha0. apply IHrl in Ha0. rewrite H. auto.
Qed.

Lemma transfer_memory_blocks_preserves_domm src sas (dst: Memory.t) das a:
  a \in domm dst <-> a \in domm (transfer_memory_blocks src sas dst das).
Proof.
  unfold transfer_memory_blocks. apply transfer_memory_blocks_helper_preserves_domm.
Qed.

Lemma load_after_transfer_memory_block src src_addr dst dst_addr i:
  src_addr.1 \in domm src ->
  dst_addr.1 \in domm dst ->
                 Memory.load src (Permission.data, src_addr.1, src_addr.2, i) =
                 Memory.load (transfer_memory_block src src_addr dst dst_addr)
                             (Permission.data, dst_addr.1, dst_addr.2, i).
Proof.
  move=> Hs_in Hd_in.
  pose proof (transfer_memory_block_preserves_domm src src_addr dst dst_addr dst_addr.1)
    as [Hlr _].
  pose proof Hlr Hd_in as Htr_in.
  rewrite /Memory.load. simpl.
  unfold transfer_memory_block in *.
  destruct (src src_addr.1) as [srcC|] eqn:es; rewrite es; rewrite es in Htr_in.
  - destruct (dst dst_addr.1) as [dstC|] eqn:ed; rewrite ed; rewrite ed mem_domm in Htr_in.
    + destruct ((setm dst dst_addr.1
                     (ComponentMemory.transfer_memory_block srcC src_addr.2 dstC dst_addr.2))
                  dst_addr.1) as [memC|] eqn:et; rewrite et in Htr_in; rewrite et.
      * rewrite setmE eq_refl in et. inversion et.
        now apply ComponentMemory.load_after_transfer_memory_block with (m' := dstC).
      * simpl in Htr_in. easy.
    + rewrite ed in Htr_in. easy.
  - rewrite mem_domm es in Hs_in. easy.
Qed.

Lemma load_unwritten_addr_after_transfer_memory_block src src_addr dst dst_addr load_addr i:
  src_addr.1 \in domm src ->
  dst_addr.1 \in domm dst ->
  load_addr.1 \in domm dst ->
  load_addr != dst_addr ->                               
  Memory.load dst (Permission.data, load_addr.1, load_addr.2, i) =
  Memory.load (transfer_memory_block src src_addr dst dst_addr)
              (Permission.data, load_addr.1, load_addr.2, i).
Proof.
  move=> Hs_in Hd_in Hl_in Hneq.
  pose proof (transfer_memory_block_preserves_domm src src_addr dst dst_addr dst_addr.1)
               as [Hlr Hrl].
  pose proof Hlr Hd_in as Htr_in.
  rewrite /Memory.load. simpl. unfold transfer_memory_block in *.
  pose proof @dommP _ _ _ _ Hs_in as [src_addrMem Hsrc_addr].
  pose proof @dommP _ _ _ _ Hd_in as [dst_addrMem Hdst_addr].
  pose proof @dommP _ _ _ _ Hl_in as [load_addrMem Hload_addr].
  rewrite !Hsrc_addr !Hdst_addr !Hload_addr.
  rewrite Hsrc_addr Hdst_addr in Htr_in.
  rewrite setmE. unfold negb in Hneq.
  destruct (load_addr.1 == dst_addr.1) eqn:e1; rewrite e1;
    destruct (load_addr.2 == dst_addr.2) eqn:e2.
  - (* derive a contradiction to Hneq. *)
    destruct load_addr as [l1 l2], dst_addr as [d1 d2].
    rewrite xpair_eqE in Hneq. simpl in *. rewrite e1 e2 in Hneq. easy.
  - (* Here, use lemma ComponentMemory.load_different_addr_after_transfer_memory_block. *)
    rewrite <- (ComponentMemory.load_unwritten_addr_after_transfer_memory_block
                  src_addrMem src_addr.2 _ dst_addr.2).
    + rewrite (eqP e1) in Hload_addr. rewrite Hload_addr in Hdst_addr.
      inversion Hdst_addr. subst. reflexivity.
    + unfold negb. rewrite e2. auto.
  - rewrite Hload_addr. reflexivity.
  - rewrite Hload_addr. reflexivity.
Qed.

Lemma transfer_memory_block_component_memory_transfer_memory_block_Some
      (src: Memory.t) saddr (dst: Memory.t) daddr src_cmem dst_cmem:
  src (saddr.1) = Some src_cmem ->
  dst (daddr.1) = Some dst_cmem ->
  (transfer_memory_block src saddr dst daddr) daddr.1 =
  Some (ComponentMemory.transfer_memory_block src_cmem saddr.2 dst_cmem daddr.2).
Proof.
  intros Hsrc Hdst. unfold transfer_memory_block. rewrite Hsrc Hdst.
  rewrite setmE. rewrite eq_refl. reflexivity.
Qed.

Lemma transfer_memory_block_component_memory_transfer_memory_block_None
      (src: Memory.t) saddr (dst: Memory.t) daddr cid:
  (src (saddr.1) = None \/ dst (daddr.1) = None) ->
  (transfer_memory_block src saddr dst daddr) cid = dst cid.
Proof.
  intros [Hnone | Hnone]; unfold transfer_memory_block; rewrite Hnone; auto.
  destruct (src saddr.1) eqn:e; rewrite e; reflexivity.
Qed.
  
Lemma load_unwritten_addr_after_transfer_memory_blocks_helper
      (sdaddrs: seq ((Component.id * Block.id) * (Component.id * Block.id))):
  forall src (dst: Memory.t) load_addr i,
    load_addr \notin (map snd sdaddrs) ->
    Memory.load dst (Permission.data, load_addr.1, load_addr.2, i) =
    Memory.load (transfer_memory_blocks_helper src dst sdaddrs)
                             (Permission.data, load_addr.1, load_addr.2, i).
Proof.
  induction sdaddrs as [|[saddr daddr] sdrec IHsdrec]; auto.
  intros src dst [ld1 ld2] i Hld. simpl in *. unfold Memory.load. simpl.
  destruct (ld1 \in domm dst) eqn:Hld1.
  - pose proof @transfer_memory_block_preserves_domm src saddr dst daddr ld1 as [Hlr Hrl];
      pose proof Hlr Hld1 as Hdomm1;
      pose proof transfer_memory_blocks_helper_preserves_domm sdrec src
           (transfer_memory_block src saddr dst daddr) ld1 as [Hlr' Hrl'];
      pose proof Hlr' Hdomm1 as Hdomm.
    pose proof @dommP _ _ _ _ Hld1 as [cMem HcMem].
    pose proof @dommP _ _ _ _ Hdomm as [cMem' HcMem'].
    rewrite HcMem. rewrite HcMem'.
    rewrite in_cons in Hld. rewrite negb_or in Hld.
    destruct (andP Hld) as [Hneq_daddr Hnotin].
    pose proof IHsdrec src (transfer_memory_block src saddr dst daddr) (ld1, ld2) i as IH'.
    simpl in IH'.
    pose proof IH' Hnotin as IH. unfold Memory.load in IH. simpl in IH.
    pose proof @dommP _ _ _ _ Hdomm1 as [cMem'' HcMem''].
    rewrite HcMem'' in IH.
    rewrite HcMem' in IH.
    rewrite <- IH.
    destruct (src saddr.1) eqn:Hsrc_saddr1;
      destruct (dst daddr.1) eqn:Hdst_daddr1;
      try (
          (* This try block should leave us with one 
             subgoal and should solve all remaining 3. 
           *)
          assert (src saddr.1 = None \/ dst daddr.1 = None) as H;
          try (right; assumption); try (left; assumption);
          pose proof transfer_memory_block_component_memory_transfer_memory_block_None
               ld1 H as H';
          rewrite H' HcMem in HcMem''; inversion HcMem''; reflexivity
        ).
    (* Just one subgoal remains: *)
    pose proof transfer_memory_block_component_memory_transfer_memory_block_Some Hsrc_saddr1
         Hdst_daddr1 as Htrans_comp_trans.
    destruct (ld1 == daddr.1) eqn:Hld1_daddr1.
    + pose proof (eqP Hld1_daddr1) as Hld1_daddr1'. subst.
      rewrite HcMem'' in Htrans_comp_trans. inversion Htrans_comp_trans as [HcMem''eq]. subst.
      rewrite HcMem in Hdst_daddr1. inversion Hdst_daddr1 as [HcMemeq]. subst.
      destruct (ld2 == daddr.2) eqn:Hld2_daddr2.
      * pose proof (eqP Hld2_daddr2) as Hld2_daddr2'. subst.
        rewrite <- surjective_pairing in Hneq_daddr. rewrite eq_refl in Hneq_daddr. easy.
      * apply ComponentMemory.load_unwritten_addr_after_transfer_memory_block.
        unfold negb. rewrite Hld2_daddr2. easy.
    + pose proof @load_unwritten_addr_after_transfer_memory_block
           src saddr dst daddr (ld1, ld2) i as H. simpl in H.
      unfold Memory.load in H. simpl in H.
      rewrite !mem_domm Hsrc_saddr1 Hdst_daddr1 Hneq_daddr HcMem HcMem'' in H. simpl in H.
      apply H; easy.
  - assert (ld1 \notin domm dst) as H.
    {
      unfold negb. rewrite Hld1. easy.
    }
    pose proof @dommPn _ _ _ _ H as Hnone. rewrite Hnone.
    pose proof transfer_memory_blocks_helper_preserves_domm sdrec src
         (transfer_memory_block src saddr dst daddr) ld1 as [_ Hrl'].
    destruct (ld1
           \in domm
                 (transfer_memory_blocks_helper
                    src (transfer_memory_block src saddr dst daddr) sdrec)) eqn:e.
    + rewrite e in Hrl'.
      assert (ld1 \in domm dst) as Hcntra.
      {
        rewrite transfer_memory_block_preserves_domm. apply Hrl'. easy.
      }
      rewrite Hcntra in H. easy.
    + assert ((transfer_memory_blocks_helper
                 src (transfer_memory_block src saddr dst daddr) sdrec) ld1 = None) as Hmatch.
      {
        apply/dommPn. unfold negb. rewrite e. easy.
      }
      rewrite Hmatch. reflexivity.
Qed.
    
Lemma load_after_transfer_memory_blocks_helper
      (sdaddrs: seq ((Component.id * Block.id) * (Component.id * Block.id))):
  forall src dst saddr1 saddr2 ld1 ld2 i,
    uniq (map snd sdaddrs) ->
    ((saddr1, saddr2), (ld1, ld2)) \in sdaddrs ->
    saddr1 \in domm src ->
    ld1 \in domm dst ->                                              
    Memory.load src (Permission.data, saddr1, saddr2, i) =
    Memory.load (transfer_memory_blocks_helper src dst sdaddrs)
                (Permission.data, ld1, ld2, i).
Proof.
  induction sdaddrs as [|sd sdrec IHsdrec];
    intros src dst saddr1 saddr2 ld1 ld2 i Huniq Hin Hdomm_src Hdomm_dst.
  - rewrite in_nil in Hin. easy.
  - rewrite map_cons cons_uniq in Huniq.
    destruct (andP Huniq) as [Hnotin Hsdrec_uniq].
    destruct sd as [[saddr1' saddr2'] [ld1' ld2']]. simpl.
    destruct ((saddr1, saddr2, (ld1, ld2)) \in sdrec) eqn:Htail.
    + apply IHsdrec; auto.
      apply transfer_memory_block_preserves_domm. auto.
    + rewrite in_cons in Hin. remember Hin as Hin'.
      destruct (orP Hin') as [Heq | Hauto].
      * pose proof eqP Heq as Heq'. inversion Heq'. subst.
        pose proof @load_unwritten_addr_after_transfer_memory_blocks_helper
             sdrec src (transfer_memory_block src (saddr1', saddr2') dst (ld1', ld2'))
             (ld1', ld2') i Hnotin as H.
        simpl in H. rewrite <- H.
        pose proof @load_after_transfer_memory_block
             src (saddr1', saddr2') dst (ld1', ld2') i as Hsrc.
        simpl in Hsrc. apply Hsrc; auto.
      * rewrite Hauto in Htail; easy.
Qed.

Lemma load_unwritten_addr_after_transfer_memory_blocks
      (src: Memory.t) (src_addrs: seq (Component.id * Block.id))
      (dst: Memory.t) (dst_addrs: seq (Component.id * Block.id)):
  forall load_addr i,
    load_addr \notin dst_addrs ->
    size dst_addrs <= size src_addrs ->
    Memory.load dst (Permission.data, load_addr.1, load_addr.2, i) =
    Memory.load (transfer_memory_blocks src src_addrs dst dst_addrs)
                             (Permission.data, load_addr.1, load_addr.2, i).
Proof.
  unfold transfer_memory_blocks. intros ? ? Hnotin Hsize.
  apply load_unwritten_addr_after_transfer_memory_blocks_helper.
  pose proof unzip2_zip Hsize. unfold unzip2 in H. rewrite H. assumption.
Qed.

Lemma load_after_transfer_memory_blocks
      (src: Memory.t) (src_addrs: seq (Component.id * Block.id))
      (dst: Memory.t) (dst_addrs: seq (Component.id * Block.id)):
  forall saddr1 saddr2 ld1 ld2 i,
    uniq dst_addrs ->
    size dst_addrs <= size src_addrs ->
    ((saddr1, saddr2), (ld1, ld2)) \in zip src_addrs dst_addrs ->
    saddr1 \in domm src ->
    ld1 \in domm dst ->                                              
    Memory.load src (Permission.data, saddr1, saddr2, i) =
    Memory.load (transfer_memory_blocks src src_addrs dst dst_addrs)
                (Permission.data, ld1, ld2, i).
Proof.
  intros ? ? ? ? ? Huniq Hsizelt Hinzip Hsrc Hdst.
  unfold transfer_memory_blocks.
  apply load_after_transfer_memory_blocks_helper; auto.
  pose proof unzip2_zip Hsizelt. unfold unzip2 in H. rewrite H. assumption.
Qed.
  
Definition merge_memories (mem1 mem2: Memory.t): Memory.t :=
  unionm mem1 mem2.

(* RB: NOTE: An equality relation could be used to contain the usual partial
   equality. *)

Lemma program_allocation_in_partialized_memory_strong :
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall C size mem1' ptr,
    C \notin ctx ->
    Memory.alloc mem1 C size = Some (mem1', ptr) ->
  exists2 mem2',
    Memory.alloc mem2 C size = Some (mem2', ptr) &
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 /eq_fmap Hfilter C size mem1' ptr nin_ctx.
rewrite /Memory.alloc; move/(_ C): (Hfilter); rewrite !filtermE nin_ctx.
case: (mem1 C) (mem2 C)=> [memC|] // [_|] //= [<-].
case: (ComponentMemory.alloc memC size)=> [memC' b] [<- <-].
eexists; eauto; apply/eq_fmap=> C'; rewrite !filtermE !setmE.
case: eqP=> [-> {C'}|_] //=.
by move/(_ C'): Hfilter; rewrite !filtermE.
Qed.

Lemma program_allocation_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall C size mem1' mem2' ptr1 ptr2,
    C \notin ctx ->
    Memory.alloc mem1 C size = Some (mem1', ptr1) ->
    Memory.alloc mem2 C size = Some (mem2', ptr2) ->
    ptr1 = ptr2 /\
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 Hfilter C size mem1' mem2' ptr1 ptr2 nin_ctx e_mem1.
case: (program_allocation_in_partialized_memory_strong Hfilter nin_ctx e_mem1).
by move=> mem2'' -> e' [<- <-]; eauto.
Qed.

Lemma program_load_in_partialized_memory_strong:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall P C b o v,
    C \notin ctx ->
    Memory.load mem1 (P, C, b, o) = Some v ->
    Memory.load mem2 (P, C, b, o) = Some v.
Proof.
move=> ctx mem1 mem2 /eq_fmap Hfilter P C b o v nin_ctx.
rewrite /Memory.load /=; move/(_ C): Hfilter; rewrite !filtermE nin_ctx.
by case: (mem1 C) (mem2 C)=> [memC|] // [_|] //= [<-].
Qed.

Lemma program_load_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall P C b o v1 v2,
    C \notin ctx ->
    Memory.load mem1 (P, C, b, o) = Some v1 ->
    Memory.load mem2 (P, C, b, o) = Some v2 ->
    v1 = v2.
Proof.
move=> ctx mem1 mem2 Hfilter P C b o v1 v2 nin_ctx e_mem.
rewrite (program_load_in_partialized_memory_strong Hfilter nin_ctx e_mem).
by case.
Qed.

Lemma program_store_in_partialized_memory_strong:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall P C b o v mem1',
    C \notin ctx ->
    Memory.store mem1 (P, C, b, o) v = Some mem1' ->
  exists2 mem2',
    Memory.store mem2 (P, C, b, o) v = Some mem2' &
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 /eq_fmap Hfilter P C b o v mem1' nin_ctx.
rewrite /Memory.store /=; move/(_ C): (Hfilter); rewrite !filtermE nin_ctx.
case: (P =? Permission.data) => //.
case: (mem1 C) (mem2 C)=> [memC|] // [_|] //= [<-].
case: (ComponentMemory.store memC b o v)=> [memC'|] //= [<-].
eexists; eauto; apply/eq_fmap=> C'; rewrite !filtermE !setmE.
case: eqP=> [-> {C'}|_] //.
by move/(_ C'): Hfilter; rewrite !filtermE.
Qed.

Lemma program_store_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall P C b o v mem1' mem2',
    C \notin ctx ->
    Memory.store mem1 (P, C, b, o) v = Some mem1' ->
    Memory.store mem2 (P, C, b, o) v = Some mem2' ->
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 Hfilter P C b o v mem1' mem2' nin_ctx e_mem.
case: (program_store_in_partialized_memory_strong Hfilter nin_ctx e_mem).
move=> *; congruence.
Qed.

Lemma context_allocation_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem C size mem' ptr,
    C \in ctx ->
    Memory.alloc mem C size = Some (mem', ptr) ->
    to_partial_memory mem' ctx = to_partial_memory mem ctx.
Proof.
  move=> ctx mem C size mem' ptr HC_in_ctx.
  rewrite /Memory.alloc => Halloc.
  case mem_C: (mem C) => [memC|];
    rewrite mem_C // in Halloc.
  case memC_alloc: (ComponentMemory.alloc memC size);
    rewrite memC_alloc // in Halloc.
  injection Halloc.
  move=> Hptr <-.
  apply/eq_fmap => C'.
  rewrite filtermE filtermE setmE.
  case: (@eqP _ C' C) => [-> | _] //.
  by rewrite HC_in_ctx mem_C /=.
Qed.

Lemma context_store_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem P C b o v mem',
    C \in ctx ->
    Memory.store mem (P, C, b, o) v = Some mem' ->
    to_partial_memory mem' ctx = to_partial_memory mem ctx.
Proof.
  move=> ctx mem P C b o v mem' C_in_ctx.
  rewrite /Memory.store /= => Hstore.
  case perm_data: (P =? Permission.data) => //;
    rewrite perm_data // in Hstore.
  case mem_C: (mem C) => [memC|];
    rewrite mem_C // in Hstore.
  case memC_store: (ComponentMemory.store memC b o v);
    rewrite memC_store // in Hstore.
  injection Hstore.
  move=> <-.
  apply/eq_fmap => C'.
  rewrite filtermE filtermE setmE.
  case: (@eqP _ C' C) => [-> | _] //.
  by rewrite C_in_ctx mem_C /=.
Qed.

(* RB: TODO: More properly, this seems to belong in Machine.Memory. However, it
   is natural to resort to a notion of partial memory that seems logically
   related to the supporting components of PS. Again, note, however, that this
   notion of partial memory is already used in the Memory module, and it may be
   a good idea to relocate our compact definitions there.

   Otherwise, this is a more convenient wrapper for
   context_store_in_partialized_memory which does not require the destruction of
   pointers, and could conceivably replace the wrappee throughout the
   development. *)
Lemma program_store_to_partialized_memory
      ptr (iface : Program.interface) mem mem' v :
  Pointer.component ptr \in domm iface ->
  Memory.store mem ptr v = Some mem' ->
  to_partial_memory mem (domm iface) = to_partial_memory mem' (domm iface).
Proof.
  destruct ptr as [[C b] o]. simpl.
  intros Hdome Hsome.
  unfold to_partial_memory. symmetry.
  eapply context_store_in_partialized_memory; eassumption.
Qed.

(* RB: TODO: Same notes as above.
   Cf.  program_allocation_in_partialized_memory_strong. *)
Lemma program_allocation_to_partialized_memory
      C (iface : Program.interface) size mem mem' ptr :
  C \in domm iface ->
  Memory.alloc mem C size = Some (mem', ptr) ->
  to_partial_memory mem (domm iface) = to_partial_memory mem' (domm iface).
Proof.
  destruct ptr as [[[P C'] b] o]. simpl.
  intros Hdome Hsome.
  unfold to_partial_memory. symmetry.
  eapply context_allocation_in_partialized_memory; eassumption.
Qed.

(* The following two lemmas manipulate memory stores and partialized memories
   more conveniently than the full-fledged "partialized" results. Note naming
   conventions for some of those are currently somewhat confusing.  *)
Lemma partialize_program_store :
  forall mem mem' (ctx : Program.interface) ptr v,
    Pointer.component ptr \notin domm ctx ->
    Memory.store mem ptr v = Some mem' ->
    Memory.store (to_partial_memory mem (domm ctx)) ptr v =
    Some (to_partial_memory mem' (domm ctx)).
Proof.
  unfold Memory.store, to_partial_memory.
  intros mem mem' ctx ptr v Hnotin Hstore.
  destruct (Pointer.permission ptr =? Permission.data) eqn:Hperm_data;
    last discriminate.
  destruct (mem (Pointer.component ptr)) as [memC |] eqn:HmemC;
    last discriminate.
  destruct (ComponentMemory.store memC (Pointer.block ptr) (Pointer.offset ptr) v)
    as [memC' |] eqn:HmemC';
    last discriminate.
  inversion Hstore as [[Hstore']].
  now rewrite (getm_filterm_notin_domm _ Hnotin) HmemC HmemC'
      (setm_filterm_notin_domm _ _ Hnotin).
Qed.

Lemma unpartialize_program_store :
  forall mem1 mem1' mem2 ptr v,
    Memory.store mem1 ptr v = Some mem1' ->
    Memory.store (merge_memories mem1 mem2) ptr v =
    Some (merge_memories mem1' mem2).
Proof.
  unfold Memory.store.
  intros mem1 mem1' mem2 ptr v Hstore.
  unfold merge_memories. rewrite unionmE.
  destruct (Pointer.permission ptr =? Permission.data) eqn:Hperm_data;
    last discriminate.
  destruct (mem1 (Pointer.component ptr)) eqn:Hcase1;
    rewrite Hcase1 || idtac "ExStructures 0.1 legacy rewrite inactive";
    last discriminate.
  simpl.
  destruct (ComponentMemory.store s (Pointer.block ptr) (Pointer.offset ptr) v) eqn:Hcase2;
    last discriminate.
  rewrite setm_union. now inversion Hstore.
Qed.

Lemma partialize_program_alloc :
  forall mem mem' (ctx : Program.interface) C ptr size,
    C \notin domm ctx ->
    Memory.alloc mem C size = Some (mem', ptr) ->
    Memory.alloc (to_partial_memory mem (domm ctx)) C size =
    Some (to_partial_memory mem' (domm ctx), ptr).
Proof.
  unfold Memory.alloc, to_partial_memory.
  intros mem mem' ctx C ptr size Hnotin Halloc.
  destruct (mem C) as [memC |] eqn:HmemC;
    last discriminate.
  destruct (ComponentMemory.alloc memC size) as [memC' b] eqn:HmemC'.
  inversion Halloc; subst.
  now rewrite (getm_filterm_notin_domm _ Hnotin) HmemC HmemC'
      (setm_filterm_notin_domm _ _ Hnotin).
Qed.

Lemma unpartialize_program_alloc :
  forall mem1 mem1' mem2 C ptr size,
    Memory.alloc mem1 C size = Some (mem1', ptr) ->
    Memory.alloc (merge_memories mem1 mem2) C size =
    Some (merge_memories mem1' mem2, ptr).
Proof.
  unfold Memory.alloc.
  intros mem1 mem1' mem2 C ptr size Halloc.
  unfold merge_memories. rewrite unionmE.
  destruct (mem1 C) as [memC |] eqn:Hcase1;
    rewrite Hcase1 || idtac "ExStructures 0.1 legacy rewrite inactive";
    last discriminate.
  simpl.
  destruct (ComponentMemory.alloc memC size) as [memC' b].
  rewrite setm_union. now inversion Halloc.
Qed.

(* (* JT: TODO: clean proof *) *)
(* Lemma mem_store_different_component : forall mem mem' C b o val Cid, *)
(*               Memory.store mem (C, b, o) val = Some mem' -> *)
(*               Cid <> C -> *)
(*               mem Cid = mem' Cid. *)
(* Proof. *)
(*   intros mem mem' C b o val Cid Hmem Hneq. *)
(*   unfold Memory.store in Hmem. *)
(*   simpl in *. *)
(*   destruct (mem C) eqn:HmemC. *)
(*   - destruct (ComponentMemory.store t b o val). *)
(*     + inversion Hmem; subst. *)
(*       rewrite setmE. *)
(*       rewrite eqtype.eqE. simpl. *)
(*       destruct (ssrnat.eqn Cid C) eqn:Heq; *)
(*         last reflexivity. *)
(*       assert (Cid = C). *)
(*       { clear -Heq. revert C Heq. *)
(*         induction Cid; intros C Heq; destruct C; eauto; *)
(*           inversion Heq. *)
(*       } *)
(*       contradiction. *)
(*     + inversion Hmem. *)
(*   - inversion Hmem. *)
(* Qed. *)

Section Partial.
  Lemma to_partial_memory_in ip ic mem Cid :
    mergeable_interfaces ip ic ->
    Cid \in domm ip ->
    (to_partial_memory mem (domm ic)) Cid = mem Cid.
  Proof.
    intros Hmerge HCid.
    unfold to_partial_memory.
    apply getm_filterm_notin_domm.
    eapply domm_partition_notin_r; eassumption.
  Qed.

  Lemma to_partial_memory_notin ip ic mem Cid :
    mergeable_interfaces ip ic ->
    Cid \in domm ic ->
    (to_partial_memory mem (domm ic)) Cid = None.
  Proof.
    intros Hmerge HCid.
    unfold to_partial_memory.
    rewrite filtermE.
    unfold obind, oapp.
    destruct (mem Cid) eqn:Hmem;
      rewrite Hmem || idtac "ExStructures 0.1 legacy rewrite inactive".
    now rewrite HCid.
    now reflexivity.
  Qed.

  (* RB: NOTE: We should rename these, and probably use this instead of the
     weaker version (currently, [in], confusingly). *)
  Lemma to_partial_memory_notin_strong ip ic mem Cid :
    mergeable_interfaces ip ic ->
    Cid \notin domm ic ->
    (to_partial_memory mem (domm ic)) Cid = mem Cid.
  Proof.
    intros Hmerge HCid.
    unfold to_partial_memory.
    rewrite filtermE.
    unfold obind, oapp.
    destruct (mem Cid) eqn:Hmem;
      rewrite Hmem || idtac "ExStructures 0.1 legacy rewrite inactive".
    now rewrite HCid.
    now reflexivity.
  Qed.
End Partial.

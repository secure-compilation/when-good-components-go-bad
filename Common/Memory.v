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

  Record mem := mkMem {
    content : PMap.t block;
    nextblock : Block.id;
  }.
  Definition t := mem.

  Definition prealloc (bufs: list (Block.id * (nat + list value))) : t :=
    let fix prepare m bs :=
        match bs with
        | [] => m
        | (b, inl size) :: bs' =>
          let chunk := repeat Undef size in
          let m' := {| content := PMap.add b chunk (content m);
                       nextblock := Pos.max (1+b) (nextblock m) |} in
          prepare m' bs'
        | (b, inr chunk) :: bs' =>
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

  (** AAA: TODO *)
  Lemma store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.
  Proof. Admitted.

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

  (* AAA: Destructing the pointer in the definitions of [load] and [store] is
     not a good idea, because it causes Coq to unfold any expression of the forms
     [load mem (C, b, o)] and [store mem (C, b, o) v]. *)

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

  Lemma program_changes_are_preserved:
    forall ctx mem C CI,
      ~ PMap.In C ctx ->
      PMap.Equal
        (PMap.add C CI (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem))
        (PMapExtra.filter (elt:=ComponentMemory.t)
                          (fun k _ => negb (PMap.mem (elt:=Component.interface) k ctx)) (PMap.add C CI mem)).
  Proof.
    intros ctx mem C CI Hnot_in_ctx.
    unfold PMap.Equal.
    intros C'.
    rewrite PMapFacts.add_o.
    destruct (PMapFacts.eq_dec C C') eqn:HCeqC'.
    - subst. symmetry.
      apply PMap.find_1.
      apply PMapExtra.filter_iff.
      + unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
      + split.
        * apply PMap.add_1; auto.
        * apply PMapFacts.not_mem_in_iff in Hnot_in_ctx.
          rewrite Hnot_in_ctx. reflexivity.
    - destruct (PMap.find C' (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem)) eqn:Hfind.
      + symmetry.
        apply PMap.find_2 in Hfind.
        apply PMapExtra.filter_iff in Hfind.
        * destruct Hfind as [Hmapsto Hcond].
          apply PMap.find_1.
          apply PMapExtra.filter_iff.
          ** unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
          ** split.
             *** apply PMap.add_2; auto.
             *** auto.
        * unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
      + symmetry.
        apply PMapFacts.not_find_in_iff.
        apply PMapFacts.not_find_in_iff in Hfind.
        unfold not. intro contra.
        apply Hfind.
        destruct contra.
        exists x.
        apply PMapExtra.filter_iff in H.
        * apply PMapExtra.filter_iff.
          ** unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
          ** destruct H.
             split.
             *** eapply PMap.add_3; eauto.
             *** auto.
        * unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
  Qed.

  Lemma program_allocation_is_preserved:
    forall (ctx: PMap.t Component.interface) mem pmem mem' pmem' C size ptr1 ptr2,
      ~ PMap.In C ctx ->
      Memory.alloc mem C size = Some (mem', ptr1) ->
      Memory.alloc pmem C size = Some (pmem', ptr2) ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      PMap.Equal pmem' (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem').
  Proof.
    intros ctx mem pmem mem' pmem' C size ptr1 ptr2.
    intros Hnot_in_ctx Halloc1 Halloc2 Hequal.
    unfold Memory.alloc in *.
    destruct (PMap.find C mem)
             eqn:Hmem_find1; try discriminate.
    destruct (ComponentMemory.alloc t0 size)
             eqn:Hmem_alloc1; try discriminate.
    inversion Halloc1; subst.
    destruct (PMap.find C pmem)
             eqn:Hmem_find2; try discriminate.
    destruct (ComponentMemory.alloc t2 size)
             eqn:Hmem_alloc2; try discriminate.
    inversion Halloc2; subst.
    rewrite Hequal.
    assert (t1 = t3). {
      specialize (Hequal C). rewrite Hequal in Hmem_find2.
      apply PMapFacts.find_mapsto_iff in Hmem_find2.
      apply PMapExtra.filter_iff in Hmem_find2.
      destruct Hmem_find2.
      apply PMap.find_1 in H. rewrite H in Hmem_find1.
      inversion Hmem_find1. subst.
      rewrite Hmem_alloc1 in Hmem_alloc2.
      inversion  Hmem_alloc2. subst.
      reflexivity.
      (* morphisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful.
      intros. subst. reflexivity.
    }
    subst.
    eapply program_changes_are_preserved; auto.
  Qed.

  Lemma context_changes_are_filtered:
    forall (ctx: PMap.t Component.interface) mem C Cmem,
      PMap.In C ctx ->
      PMap.Equal (PMapExtra.filter (fun k (_ : ComponentMemory.t) => negb (PMap.mem k ctx)) (PMap.add C Cmem mem))
                 (PMapExtra.filter (fun k (_ : ComponentMemory.t) => negb (PMap.mem k ctx)) mem).
  Proof.
    intros ctx mem C Cmem Hin_ctx.
    apply PMapFacts.mem_in_iff in Hin_ctx.
    intros C'.
    destruct (PMap.find C' (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx))
                                             (PMap.add C Cmem mem)))
             eqn:Hfind1;
    destruct (PMap.find C' (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx))
                                             mem))
             eqn:Hfind2.
    - apply PMap.find_2 in Hfind1.
      apply PMap.find_2 in Hfind2.
      apply PMapExtra.filter_iff in Hfind1.
      apply PMapExtra.filter_iff in Hfind2.
      destruct Hfind1 as [Hmapsto1 Hcond1].
      destruct Hfind2 as [Hmapsto2 Hcond2].
      destruct (Pos.eqb C C') eqn:HCeqC'.
      + apply Pos.eqb_eq in HCeqC'. subst.
        rewrite Hin_ctx in *. discriminate.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst.
        apply PMapFacts.add_neq_mapsto_iff in Hmapsto1.
        * rewrite (PMapFacts.MapsTo_fun Hmapsto1 Hmapsto2).
          reflexivity.
        * apply Pos.eqb_neq; auto.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - exfalso.
      apply PMapFacts.not_find_in_iff in Hfind2.
      apply PMapFacts.find_mapsto_iff in Hfind1.
      apply PMapExtra.filter_iff in Hfind1.
      destruct Hfind1.
      + assert (C <> C'). {
          destruct (Pos.eqb C C') eqn:HCeqC'.
          - apply Pos.eqb_eq in HCeqC'. subst.
            rewrite Hin_ctx in H0. discriminate.
          - apply Pos.eqb_neq; auto.
        }
        apply PMapFacts.add_mapsto_iff in H.
        destruct H.
        * destruct H; subst.
          rewrite Hin_ctx in H0. discriminate.
        * destruct H; subst.
          apply Hfind2. eexists.
          apply PMapExtra.filter_iff.
          ** (* morphisms stuff *)
            unfold Morphisms.Proper, Morphisms.respectful.
            intros. subst. reflexivity.
          ** split; eauto.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - exfalso.
      apply PMapFacts.not_find_in_iff in Hfind1.
      apply PMapFacts.find_mapsto_iff in Hfind2.
      apply PMapExtra.filter_iff in Hfind2.
      destruct Hfind2.
      + assert (C <> C'). {
          destruct (Pos.eqb C C') eqn:HCeqC'.
          - apply Pos.eqb_eq in HCeqC'. subst.
            rewrite Hin_ctx in H0. discriminate.
          - apply Pos.eqb_neq; auto.
        }
        apply Hfind1. eexists.
        apply PMapExtra.filter_iff.
        * (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        * split; eauto.
          apply PMapFacts.add_neq_mapsto_iff; eauto.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - reflexivity.
  Qed.

  Lemma context_allocation_is_filtered:
    forall (ctx: PMap.t Component.interface) mem pmem mem' C size ptr1,
      PMap.In C ctx ->
      Memory.alloc mem C size = Some (mem', ptr1) ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem').
  Proof.
    intros ctx mem pmem mem' C size ptr1.
    intros Hin_ctx Halloc Hequal.
    unfold Memory.alloc in *.
    destruct (PMap.find C mem)
             eqn:Hmem_find; try discriminate.
    destruct (ComponentMemory.alloc t0 size)
             eqn:Hmem_alloc; try discriminate.
    inversion Halloc; subst.
    rewrite Hequal. rewrite context_changes_are_filtered; auto.
    apply PMapFacts.Equal_refl.
  Qed.

  Lemma program_store_is_preserved:
    forall (ctx: PMap.t Component.interface) mem pmem mem' pmem' ptr v,
      ~ PMap.In (Pointer.component ptr) ctx ->
      Memory.store mem ptr v = Some mem' ->
      Memory.store pmem ptr v = Some pmem' ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      PMap.Equal pmem' (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem').
  Proof.
    intros ctx mem pmem mem' pmem' ptr v.
    intros Hnot_in_ctx Hstore1 Hstore2 Hequal.
    unfold Memory.store in *. destruct ptr. destruct p.
    destruct (PMap.find i mem)
             eqn:Hmem_find1; try discriminate.
    destruct (ComponentMemory.store t0 i0 o v)
             eqn:Hmem_store1; try discriminate.
    inversion Hmem_store1; subst.
    destruct (PMap.find i pmem)
             eqn:Hmem_find2; try discriminate.
    destruct (ComponentMemory.store t2 i0 o v)
             eqn:Hmem_store2; try discriminate.
    inversion Hmem_store2; subst.
    assert (t0 = t2). {
      specialize (Hequal i). rewrite Hequal in Hmem_find2.
      apply PMapFacts.find_mapsto_iff in Hmem_find2.
      apply PMapExtra.filter_iff in Hmem_find2.
      destruct Hmem_find2.
      apply PMap.find_1 in H. rewrite H in Hmem_find1.
      inversion Hmem_find1. subst.
      rewrite Hmem_store1 in Hmem_store2.
      inversion  Hmem_store2. subst.
      reflexivity.
      (* morphisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful.
      intros. subst. reflexivity.
    }
    subst. rewrite H0 in H1.
    inversion H1. subst.
    inversion Hstore1; subst. inversion Hstore2; subst.
    rewrite Hequal.
    eapply program_changes_are_preserved; auto.
  Qed.

  Lemma context_store_is_filtered:
    forall (ctx: PMap.t Component.interface) mem pmem mem' ptr v,
      PMap.In (Pointer.component ptr) ctx ->
      Memory.store mem ptr v = Some mem' ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem').
  Proof.
    intros ctx mem pmem mem' ptr v.
    intros Hin_ctx Hstore Hequal.
    unfold Memory.store in *.
    destruct ptr. destruct p.
    destruct (PMap.find i mem)
             eqn:Hmem_find; try discriminate.
    destruct (ComponentMemory.store t0 i0 o v)
             eqn:Hmem_store; try discriminate.
    inversion Hstore; subst.
    rewrite Hequal. rewrite context_changes_are_filtered; auto.
    apply PMapFacts.Equal_refl.
  Qed.

  Lemma impossible_program_store_failure:
    forall (ctx: PMap.t Component.interface) mem pmem mem' ptr v,
      ~ PMap.In (Pointer.component ptr) ctx ->
      Memory.store mem ptr v = Some mem' ->
      Memory.store pmem ptr v = None ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      False.
  Proof.
    intros.
    unfold Memory.store in *.
    destruct ptr as [[]].
    destruct (PMap.find i mem) eqn:Hmem_find; try discriminate.
    destruct (PMap.find i pmem) eqn:Hpmem_find; try discriminate.
    - specialize (H2 i).
      rewrite Hpmem_find in H2.
      destruct (ComponentMemory.store t0 i0 o v) eqn:Hmem_store; try discriminate.
      inversion H0. subst.
      symmetry in H2.
      apply PMap.find_2 in H2.
      apply PMapExtra.filter_iff in H2.
      destruct H2 as [Hmapsto Hcond].
      apply PMapFacts.find_mapsto_iff in Hmapsto.
      rewrite Hmapsto in Hmem_find.
      inversion Hmem_find. subst.
      rewrite Hmem_store in H1. discriminate.
      (* morpshisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
    - specialize (H2 i).
      rewrite Hpmem_find in H2.
      symmetry in H2. apply PMapFacts.not_find_in_iff in H2.
      apply H2. eexists.
      eapply PMapExtra.filter_iff.
      + (* morpshisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
      + split.
        * apply PMap.find_2 in Hmem_find.
          eauto.
        * simpl in *.
          apply PMapFacts.not_mem_in_iff in H.
          unfold negb. rewrite H. reflexivity.
  Qed.

  Lemma impossible_program_allocation_failure:
    forall (ctx: PMap.t Component.interface) mem pmem mem' C size ptr1,
      ~ PMap.In C ctx ->
      Memory.alloc mem C size = Some (mem', ptr1) ->
      Memory.alloc pmem C size = None ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      False.
  Proof.
    intros.
    unfold Memory.alloc in *.
    destruct (PMap.find C mem) eqn:Hmem_find; try discriminate.
    destruct (PMap.find C pmem) eqn:Hpmem_find; try discriminate.
    - specialize (H2 C).
      rewrite Hpmem_find in H2.
      destruct (ComponentMemory.alloc t0 size) eqn:Hmem_alloc; try discriminate.
      inversion H0. subst.
      symmetry in H2.
      apply PMap.find_2 in H2.
      apply PMapExtra.filter_iff in H2.
      destruct H2 as [Hmapsto Hcond].
      apply PMapFacts.find_mapsto_iff in Hmapsto.
      rewrite Hmapsto in Hmem_find.
      inversion Hmem_find. subst.
      rewrite Hmem_alloc in H1. discriminate.
      (* morpshisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
    - specialize (H2 C).
      rewrite Hpmem_find in H2.
      symmetry in H2. apply PMapFacts.not_find_in_iff in H2.
      apply H2. eexists.
      eapply PMapExtra.filter_iff.
      + (* morpshisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful. intros. subst. auto.
      + split.
        * apply PMap.find_2 in Hmem_find.
          eauto.
        * simpl in *.
          apply PMapFacts.not_mem_in_iff in H.
          unfold negb. rewrite H. reflexivity.
  Qed.

  Lemma filter_identity:
    forall (mem: Memory.t),
      PMap.Equal (PMapExtra.filter (fun _ _ => true) mem) mem.
  Proof.
    intros mem C.
    destruct (PMap.find C (PMapExtra.filter (fun _ _ => true) mem)) eqn:Hfind.
    - apply PMap.find_2 in Hfind.
      apply PMapExtra.filter_iff in Hfind.
      + destruct Hfind as [Hfound []].
        apply PMap.find_1 in Hfound.
        rewrite Hfound. reflexivity.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - apply PMapFacts.not_find_in_iff in Hfind.
      symmetry. apply PMapFacts.not_find_in_iff.
      intro contra. apply Hfind.
      destruct contra as [Cmem contra].
      eexists. apply PMapExtra.filter_iff.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
      + split; eauto.
  Qed.

  Theorem equivalence_under_filter:
    forall (mem1 mem2: t) f,
      PMap.Equal mem1 mem2 ->
      PMap.Equal (PMapExtra.filter f mem1) (PMapExtra.filter f mem2).
  Proof.
    intros mem1 mem2 f Heq C.
    destruct (PMap.find C (PMapExtra.filter f mem1)) eqn:Hfind1;
    destruct (PMap.find C (PMapExtra.filter f mem2)) eqn:Hfind2.
    - apply PMap.find_2 in Hfind1.
      apply PMap.find_2 in Hfind2.
      apply PMapExtra.filter_iff in Hfind1.
      apply PMapExtra.filter_iff in Hfind2.
      destruct Hfind1 as [Hmapsto1 Hcond1].
      destruct Hfind2 as [Hmapsto2 Hcond2].
      rewrite Heq in Hmapsto1.
      erewrite (PMapFacts.MapsTo_fun Hmapsto1 Hmapsto2).
      reflexivity.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - apply PMap.find_2 in Hfind1.
      apply PMapFacts.not_find_in_iff in Hfind2.
      apply PMapExtra.filter_iff in Hfind1.
      destruct Hfind1 as [Hmapsto1 Hcond1].
      exfalso.
      apply Hfind2.
      eexists. apply PMapExtra.filter_iff.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
      + rewrite Heq in Hmapsto1.
        split; eauto.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - apply PMap.find_2 in Hfind2.
      apply PMapFacts.not_find_in_iff in Hfind1.
      apply PMapExtra.filter_iff in Hfind2.
      destruct Hfind2 as [Hmapsto2 Hcond2].
      exfalso.
      apply Hfind1.
      eexists. apply PMapExtra.filter_iff.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
      + rewrite <- Heq in Hmapsto2.
        split; eauto.
      + (* morphisms stuff *)
        unfold Morphisms.Proper, Morphisms.respectful.
        intros. subst. reflexivity.
    - reflexivity.
  Qed.
End Memory.

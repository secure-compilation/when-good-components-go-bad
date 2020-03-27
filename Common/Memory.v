Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Lib.Extra.
Require Import Lia.
Require Import Coq.Logic.ClassicalFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype path fingraph fintype.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : {fmap Block.id -> nat + list value} -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.
  Parameter domm : t -> {fset Block.id}.
  Parameter load_block : t -> Block.id -> list (Component.id * Block.id).
  Parameter next_block : t -> Block.id.

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
      load m' b' i' =
      if (b', i') == (b, i) then Some v else load m b' i'.

  Axiom store_after_load:
    forall m b i v v',
      load m b i = Some v ->
      exists m',
        store m b i v' = Some m'.

  Axiom domm_prealloc :
    forall bufs m,
      prealloc bufs = m ->
      size (domm m) = size bufs.

  Axiom domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.

End AbstractComponentMemory.

Module ComponentMemory : AbstractComponentMemory.
  Definition block := list value.

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := mem.

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

  Definition domm (m : t) := @domm nat_ordType block (content m).

  Fixpoint block_ids_in_chunk chunk : list (Component.id * Block.id) :=
    match chunk with
    | nil => nil
    | v :: vs => match v with
                 | Ptr p => [(Pointer.component p, Pointer.block p)] ++ block_ids_in_chunk vs
                 | _ => block_ids_in_chunk vs
                 end
    end.
  
  Definition load_block (m: t) (b: Block.id) : list (Component.id * Block.id) :=
    match getm (content m) b with
    | Some chunk => block_ids_in_chunk chunk
    | None => nil
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

  Lemma domm_prealloc :
    forall bufs m,
      prealloc bufs = m ->
      size (domm m) = size bufs.
  Admitted.

  Lemma domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.
  Admitted.  
End ComponentMemory.

Module ComponentMemoryExtra.
  Import ComponentMemory.
  (* RB: NOTE: Prove composition as needed. Blocks are emitted in the same order
     as the sequence of single calls. *)
  Fixpoint reserve_blocks (mem : t) (n : nat) : t * list Block.id :=
    let acc '(mem, bs) :=
        let '(mem', b) := reserve_block mem in
        (mem', bs ++ [b]) in
    iter n acc (mem, []).
End ComponentMemoryExtra.

Module Memory.
  Definition t := NMap ComponentMemory.t.
  
  Fixpoint empty (cs : list Component.id) :=
    match cs with
    | [] => emptym
    | c::cs' => setm (empty cs') c ComponentMemory.empty
    end.

  Definition alloc (mem : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    match mem C with
    | Some memC =>
      let '(memC', b) := ComponentMemory.alloc memC size in
      Some (setm mem C memC', (C, b, 0%Z))
    | None => None
    end.

  Definition load (mem: t) (ptr: Pointer.t) : option value :=
    match mem (Pointer.component ptr) with
    | Some memC => ComponentMemory.load memC (Pointer.block ptr) (Pointer.offset ptr)
    | None => None
    end.

  Definition store (mem: t) (ptr: Pointer.t) (v: value) : option t :=
    match mem (Pointer.component ptr) with
    | Some memC =>
      match ComponentMemory.store memC (Pointer.block ptr) (Pointer.offset ptr) v with
      | Some memC' => Some (setm mem (Pointer.component ptr) memC')
      | None => None
      end
    | None => None
    end.

  (* Define reachability using the ssreflect fingraph library. *)
  Definition node_t : Type := Component.id * Block.id.

  Definition apply_load_block_seq (m: t) (pair: node_t)
    : seq node_t :=
    match m (fst pair) with
    | None => nil
    | Some compMem => ComponentMemory.load_block compMem (snd pair)
    end.
  
  Definition apply_load_block (m: t) (pair: node_t) : list (node_t) :=
    match m (fst pair) with
    | None => nil
    | Some compMem => ComponentMemory.load_block compMem (snd pair)
    end.

  Definition per_component_next_block (m: t) (cid: Component.id) : Block.id :=
    match (m cid) with
    | None => 0
    | Some compMem => ComponentMemory.next_block compMem
    end.
  
  Fixpoint max_next_block_helper (m: t) (max_so_far: Block.id) (l : seq Component.id) : Block.id :=
    match l with
    | nil => max_so_far
    | c :: cs => max_next_block_helper m (max max_so_far (per_component_next_block m c)) cs
    end.

  Definition max_next_block (m: t) : Block.id := (max_next_block_helper m 0 (domm m)) + 1.

  Lemma per_component_next_block_max_next_block :
    forall (m : t) (cid : Component.id),
      per_component_next_block m cid < max_next_block m.
  Admitted.
  
  Definition component_ptrs_upperbound (m: t) (cid: Component.id) (bid: Block.id) : Prop :=
    forall (n1 n2 : node_t) (l : list node_t),
      apply_load_block m n1 = l ->
      In n2 l ->
      fst n2 = cid ->
      snd n2 < bid.
  
  Definition component_ptrs_upper_next_block (m: t) (cid: Component.id) : Prop :=
    component_ptrs_upperbound m cid (per_component_next_block m cid).

  Definition component_ptrs_upper_max_next_block (m: t) (cid: Component.id) : Prop :=
    component_ptrs_upperbound m cid (max_next_block m).
  
  Definition memory_upper_next_blocks (m: t) : Prop :=
    forall (cid : Component.id),
      In cid (domm m) ->
      component_ptrs_upper_next_block m cid.

  Definition memory_upper_max_next_block (m: t) : Prop :=
    forall (cid : Component.id),
      In cid (domm m) ->
      component_ptrs_upper_max_next_block m cid.
  
  Lemma lt_upper_upper :
    forall (m: t) (cid: Component.id) (b1 b2: Block.id),
      b1 < b2 ->
      component_ptrs_upperbound m cid b1 ->
      component_ptrs_upperbound m cid b2.
  Proof.
    intros m cid b1 b2 Hlt.
    unfold component_ptrs_upperbound.
    intros Hupper n1 n2 l Happly Hin Hcid.
    pose (HupperI := Hupper n1 n2 l Happly Hin Hcid).
    apply leq_trans with (n := S n2.2).
    - apply eq_leq.
      reflexivity.
    - apply leq_trans with (m := S n2.2) (n := b1).
      + eapply HupperI.
      + apply leq_trans with (n := S b1).
        apply leqnSn.
        exact Hlt.
  Qed.    
  
  Lemma upper_next_block_upper_max_next_block :
    forall (m: t) (cid: Component.id),
      component_ptrs_upper_next_block m cid ->
      component_ptrs_upper_max_next_block m cid.
  Proof.
    intros m cid.
    unfold component_ptrs_upper_next_block, component_ptrs_upper_max_next_block.
    apply lt_upper_upper.
    apply per_component_next_block_max_next_block.
  Qed.

  Definition load_block_valid_cid (m: t) : Prop :=
    forall n nload,
      In nload (apply_load_block_seq m n) ->
      In (fst nload) (domm m).

  Definition mem_ncomp (m: t) (ncomp: nat) : Prop :=
    forall cid,
      In cid (domm m) -> cid < ncomp.

  (* Definition graph_of_mem (m: t) := apply_load_block_seq m. *)

  Definition finblockid (m: t) : Type := ordinal (max_next_block m).
  Definition fincompid (ncomp: nat) : Type := ordinal ncomp.
  Definition finnode_t (m: t) (ncomp: nat) : Type := (fincompid ncomp) * (finblockid m).
  
  Lemma obviously_false : forall n m, n < max_next_block m. Admitted.
  Lemma very_obviously_false : forall n m, n < m. Admitted.

  SearchAbout In.
  Check List.in_cons.
  Check sig.
  Check exist.
  
  Fixpoint nth_default_or_In_proof T (x_default: T) s n : T + sig (fun (x:T) => In x s) :=
    match s with
    | nil => inl x_default
    | x0 :: s' =>
      match n with
      | 0 => inr
               (exist
                  (fun x => In x (x0 :: s'))
                  x0
                  (in_eq x0 s')
               )
      | S n' =>
        match nth_default_or_In_proof T x_default s' n' with
        | inl x => inl x
        | inr (exist x's' x'Ins') => inr
                                       (exist
                                          (fun x => In x (x0 :: s'))
                                          x's'
                                          (List.in_cons x0 x's' s' x'Ins')
                                       )
        end
      end
    end.

  Lemma nlt0_False :
    forall n, n < 0 -> False.
  Proof.
    intros n. induction n.
    - intros nlt0. unfold is_true in nlt0.
      pose (zeroeq1 := anti_leq (andb_true_intro (conj nlt0 (leqnSn 0)))).
      discriminate.
    - intros n1lt0. pose (nlt0 := leq_trans (leqnSn n.+1) n1lt0). auto.
  Qed.

  (* 
     Here, we get rid of the default value 
     (i.e., get rid of the left value of the return type of nth_default_or_In_proof) 
     by passing a proof that n < length s, thus that n is a valid index.

     So, let's define "nth with an In-proof" using the proof mode first.
   *)
  Fixpoint nth_In_proof T s n (pf_nlt : n < length s) : sig (fun (x:T) => In x s).
  Proof.
    induction s.
    - simpl in pf_nlt.
      exfalso.
      apply nlt0_False with (n := n). auto.
    - destruct (n < length s).
      + assert (IHs' : {x : T | In x s}) by now auto.
        destruct IHs' as [x' x'In].
        exact (exist (fun x => In x (a :: s)) x' (List.in_cons a x' s x'In)).
      + exact (exist
                  (fun x => In x (a :: s))
                  a
                  (in_eq a s)).
  Defined.

  Print nth_In_proof.
  
  (* Next, this was an attempt to define nth_In_proof but WITHOUT using the proof mode.

     The reason I wanted to do it without the proof mode is to have more control
     over the term that is generated.

     This control may be needed if we want to prove something about nth_In_proof.
   *)

  (*
  Fixpoint nth_In_proof T (x_default: T) s n (pf_nlt : n < length s) : sig (fun (x:T) => In x s) :=
    match s return sig (fun (x:T) => In x s) with
    | nil => let x_pf := False_ind (In x_default nil) (nlt0_False n pf_nlt) in
             (* x_pf does not type-check. In particular, the information that we are in
                the nil case is not substituted in the type of pf_nlt.*)
             exist (fun x => In x nil) x_default x_pf
    | a :: s' => exist
                   (fun x => In x (a :: s'))
                   a
                   (in_eq a s')
                   (* This is the wrong return value, but it is here just to pass the syntax check. *)
    end.
  *)


  Lemma nth_len_inr :
    forall T x_default s n,
      n < length s ->
      exists pf, nth_default_or_In_proof T x_default s n = inr pf.
  Proof.
    induction s.
    - simpl. intros n nlt0. pose (F := nlt0_False n nlt0). discriminate.
    - intros n nlt.
      destruct (n < length s) eqn:e.
      + pose (pfIns := IHs n e).
        destruct pfIns as [[memberS proofInS] pf_s_eq_inr].
        SearchAbout In cons.
        pose (proofInAS := List.in_cons a memberS s proofInS).
        exists (exist (fun x => In x (a :: s)) memberS proofInAS).
        unfold nth_default_or_In_proof.
        simpl.
        admit.
      + admit.
  Admitted.
  
  Definition nth_with_nth_proof T (x_default: T) s n : sig (fun (x:T) => x = nth x_default s n).
  Proof.
    eexists (nth x_default s n). auto.
  Qed.

  Print nth_with_nth_proof.

  SearchAbout nth.

  (*
  Lemma graph_of_mem_exists :
    forall (m: t) (ncomp: nat) (pf_mem_ncomp: mem_ncomp m ncomp)
           (pf_load_valid_cid: load_block_valid_cid m),
    exists graph_of_mem: (finnode_t m ncomp) -> (seq (finnode_t m ncomp)),
    forall a,
      map
        (fun x => (nat_of_ord (fst x), nat_of_ord (snd x)))
        (graph_of_mem a)
      =
      apply_load_block_seq m (nat_of_ord (fst a), nat_of_ord (snd a)).
  Proof.
    intros m ncomp pf_mem_ncomp pf_load_valid_cid.
    eexists.
    intros a.
    induction (apply_load_block_seq m (nat_of_ord a.1, nat_of_ord a.2)).
    - 
   *)

  
  (*
  Definition apply_load_block_seq_fin
             (m: t)
             (ncomp: nat)
             (pf_mem_ncomp: mem_ncomp m ncomp)
             (pf_load_valid_cid: load_block_valid_cid m)
             (pair: finnode_t m ncomp)
    : seq (finnode_t m ncomp).
  Proof.
    pose (conv_node := (nat_of_ord (fst pair), nat_of_ord (snd pair))).
    pose (lblock := apply_load_block_seq m conv_node).
    induction lblock.
    - exact nil.
    - assert (fst a \in domm m).
      {
        unfold load_block_valid_cid in pf_load_valid_cid.
        eapply pf_load_valid_cid with (n := conv_node).
        SearchAbout in_mem.
        apply mem_head.
        SearchAbout in_mem cons.
        exact (a \in l).
      }
  *)

  Check Ordinal.
  Check obviously_false.
  
  Definition apply_load_block_seq_fin (m: t) (ncomp: nat) (pair : finnode_t m ncomp)
    : seq (finnode_t m ncomp) :=
    map
      (fun x => (Ordinal (very_obviously_false (fst x) ncomp),
                 Ordinal (obviously_false (snd x) m)))
      (apply_load_block_seq m (nat_of_ord (fst pair), nat_of_ord (snd pair)))
  .
  
  Definition fingraph_of_mem (m: t) (ncomp: nat) := apply_load_block_seq_fin m ncomp.

  Check fingraph_of_mem.

  Lemma proof_of_concept :
    forall m ncomp x y,
      reflect (dfs_path (fingraph_of_mem m ncomp) nil x y)
              (y \in dfs (fingraph_of_mem m ncomp) (ncomp * (max_next_block m)) nil x).
  Proof.
    intros m ncomp x y.
    apply dfs_pathP.
    - simpl.
      rewrite card_prod. rewrite card_ord. rewrite card_ord.
      rewrite card0. rewrite add0n. apply leqnn.
    - auto.
  Qed.

  
  (* START DEFINING REACHABILITY INDUCTIVELY *)
  Inductive Reachable (m: t) (bs : {fset node_t}) : node_t -> Prop :=
  | Reachable_refl : forall b, b \in bs -> Reachable m bs b
  | Reachable_step : forall cid bid b' compMem,
      Reachable m bs (cid, bid) -> 
      m (cid) = Some compMem ->
      b' \in ComponentMemory.load_block compMem bid ->
      Reachable m bs b'.
                            
  (* END DEFINING REACHABILITY INDUCTIVELY *)

  (* Taking inspiration from mathcomp.ssreflect.path, make path be the type of
     non-empty sequences.
     A path is thus a head and a tail. The head is of type node_t, and the tail of type
     seq node_t.
     Our path is also uniq, i.e., no cycles.
   *)
  Definition path_t : Type := node_t * (seq node_t).
  (* uniq means that it does not contain cycles. *)
  Definition uniq_path_t (p : path_t) : bool := uniq (p.1 :: p.2).
  Definition size_of_path (p : path_t) : nat := (size p.2) + 1.
  Hint Unfold size_of_path.

  Lemma count_of_distinct_blocks_in_uniq_path_is_same_as_its_size :
    forall p : path_t,
      uniq_path_t p ->
      size (fset (p.1 :: p.2)) = size_of_path p.
  Proof.
    rewrite /uniq_path_t /size_of_path.
    move => p.
    rewrite (uniq_size_fset (p.1 :: p.2)).
    rewrite eqE => H.
    pose (H' := eqnP H).
    erewrite <- H'.
    simpl.
    rewrite addn1.
    reflexivity.
  Qed.

  Definition extend_path' (m : t) (p : path_t) : list path_t :=
    map (fun x => (x, p.1 :: p.2))
        (filter (fun x => (x \notin p.2) && (x != p.1)) (apply_load_block m p.1)).

  Lemma extend_path'_returns_extensions :
    forall m p ps,
      extend_path' m p = ps -> all (fun x => (x.2 == p.1 :: p.2)) ps.
  Proof.
    intros. subst ps. unfold extend_path'.
    rewrite all_map. simpl.
    unfold preim. simpl.
    rewrite eq_refl.
    apply all_predT.
  Qed.

  Lemma extension_of_path_increases_its_size_by_one :
    forall x p,
      x.2 == p.1 :: p.2 ->
      size_of_path x =? size_of_path p + 1.
  Proof.
    intros x p H.
    simpl.
    pose (H' := eqP H).
    unfold size_of_path.
    rewrite H'.
    apply/Nat.eqb_spec.
    assert (size (p.1 :: p.2) = size p.2 + 1).
    {
      destruct (p.1 :: p.2) eqn:e.
      - discriminate e.
      - simpl.
        assert (s :: l == p.1 :: p.2).
        {
          rewrite e. apply eq_refl. 
        }
        rewrite eqseq_cons in H0.
        pose (H1 := andP H0).
        destruct H1 as [_ H2].
        pose (H3 := eqP H2).
        rewrite H3.
        rewrite addn1.
        reflexivity.
    }
    rewrite H0.
    reflexivity.
  Qed.

  Lemma extend_path'_increases_length :
    forall m p lp,
      extend_path' m p = lp ->
      all (fun x => size_of_path x =? size_of_path p + 1) lp.
  Proof.
    intros m p lp H.
    pose (H' := extend_path'_returns_extensions m p lp H).
    eapply sub_all with
        (a1 := fun x : node_t * seq_eqType (prod_eqType nat_eqType nat_eqType) => x.2 == p.1 :: p.2).
    unfold subpred.
    intros x.
    apply extension_of_path_increases_its_size_by_one.
    apply H'.
  Qed.
      
  Lemma extend_path'_preserves_uniq :
    forall m p0 ps,
      uniq_path_t p0 ->
      extend_path' m p0 = ps ->
      all uniq_path_t ps.
  Proof.
    move => m p0 ps. rewrite /uniq_path_t cons_uniq => /andP[??] <-.
    unfold extend_path'.
    rewrite all_map. simpl.
    unfold preim. simpl.
    
    apply/allP => x /=. rewrite mem_filter.
    move => /andP [/andP[/negP H1 /negP H2] H3].
    apply/and3P. split; auto.
    apply/memPn => y Hnotin. apply/negP => /eqP?. subst y.
    move: Hnotin. rewrite in_cons => /orP[?|]; auto.
  Qed.

  Definition access_step_paths' (m: t) (ps: {fset path_t}) (cur_path_size: nat) : {fset path_t} :=
    fsetU ps (fset
                (concat (List.map (extend_path' m)
                                  (filter (fun p => size_of_path p =? cur_path_size) ps)
                        )
                )
             ).

  Lemma access_step_paths'_expansive :
  forall m ps sz,
    fsubset ps (access_step_paths' m ps sz).
  Proof.
    intros. unfold access_step_paths'. apply fsubsetUl.
  Qed.

  Corollary access_step_paths'_never_produces_cycles :
  forall m (ps: {fset path_t}) (sz: nat),
    all uniq_path_t (val ps) ->
    all uniq_path_t (val (access_step_paths' m ps sz)).
  Proof.
    move => m ps sz H.
    apply/allP => p.
    rewrite /access_step_paths' in_fsetU => pHyp.
    pose (pHypProp := orb_prop _ _ pHyp).
    destruct pHypProp as [inPs | inExtend].
    - move: inPs.
      apply/allP; auto.
    - rewrite <- flat_map_concat_map in inExtend.
      (* Want to use in_flat_map. Wanted: In p (flat_map (exte..) ps) *)
      rewrite in_fset in inExtend.
      apply In_in in inExtend.
      apply in_flat_map in inExtend.
      destruct inExtend as [p0 [p0InPs pInExtendPs]].
      rewrite <- (In_in p0) in p0InPs.
      rewrite mem_filter in p0InPs.
      pose (p0InPs' := andb_prop _ _ p0InPs).
      destruct p0InPs' as [_ p0InPs''].
      apply/allP.
      apply (extend_path'_preserves_uniq m p0).
      apply/allP.
      exact H.
      auto.
      reflexivity.
      rewrite <- (In_in p) in pInExtendPs.
      exact pInExtendPs.
  Qed.

  (* 
     The fuel decreases, and the count of steps increases.
  *)
  Fixpoint reachable_paths_with_fuel' (m: t) (ps: {fset path_t})
           (fuel: nat) (cur_path_length: nat) : {fset path_t} :=
  match fuel with
  | 0 => ps
  | S fuel_1 => reachable_paths_with_fuel'
                  m (access_step_paths' m ps cur_path_length) fuel_1 (S cur_path_length)
  end.

  Definition component_memories_of_memory (m: t) : seq ComponentMemory.t :=
    map snd (elementsm m).
  
  Definition list_of_per_component_set_of_block_ids (m: t) : seq {fset Block.id} :=
    map ComponentMemory.domm (component_memories_of_memory m).
  
  Definition count_of_allocated_blocks_of_memory (m: t) : nat :=
    sumn (map (fun (x:{fset Block.id}) => size x) (list_of_per_component_set_of_block_ids m)).

  (* Presumably, the size of a path in ps is 1.*)
  Definition reachable_paths' (m: t) (ps: {fset path_t}) :=
    reachable_paths_with_fuel' m ps (count_of_allocated_blocks_of_memory m) 1.

  Definition max_path_size_in_seq (s: seq path_t) : nat :=
    foldl max 0 (map size_of_path s).
  
  Definition max_path_size_in_set (ps : {fset path_t}) : nat :=
    max_path_size_in_seq (val ps).

  (*Lemma reachable_paths_with_fuel'_expansive :
    forall m ps fuel cur_path_length,
      fsubset
        reachable_paths_with_fuel' m () fuel_1 (S cur_path_length)
        reachable_paths_with_fuel' m ps (S fuel1) cur_path_length
  *)

  Lemma foldl_max_default :
    forall l mx d,
      mx = foldl max d l -> max d mx = mx.
  Proof.
    intros l. induction l; simpl.
    - intros mx d H. subst mx. rewrite Nat.max_idempotent. reflexivity.
    - intros mx d H.
      destruct (max d a =? d) eqn:da.
      + move : da. rewrite Nat.eqb_eq. move => da. rewrite da in H.
        apply IHl with (mx := mx) (d := d). exact H.
      + move : da. rewrite Nat.eqb_neq. move => da.
        pose (dec := Nat.max_dec d a).
        destruct dec as [F | T].
        * rewrite F in da. pose (contra := Nat.eq_refl d). pose (bot := da contra). contradiction.
        * rewrite T in H.
          destruct (max d mx =? a) eqn:dmx.
          -- move : dmx. rewrite Nat.eqb_eq. move => dmx.
             rewrite dmx.
             pose (IHlinst := IHl mx a).
             pose (IHlinst2 := IHlinst H).
             assert (alemx : (a <= mx)%coq_nat).
             {
               ++ rewrite <- IHlinst2.
                  apply Nat.le_max_l.
             }
             apply Nat.le_antisymm.
             ++ exact alemx.
             ++ rewrite <- dmx.
                apply Nat.le_max_r.
          -- pose (IHlinst := IHl mx a H).
             apply Nat.max_r.
             apply Nat.le_trans with (m := a).
             ++ pose (dlea := Nat.le_max_l d a). erewrite T in dlea. exact dlea.
             ++ pose (alemx := Nat.le_max_l a mx). erewrite IHlinst in alemx. exact alemx.
  Qed.
 (* 
  Lemma foldl_max_cons_foldl :
    forall a l d,
      a = foldl max d (a :: l) ->
      foldl max a l = a.
  Proof.
    unfold foldl. simpl
    intros a l d H.
    pose (maxda := foldl_max_default (a :: l) a d H).
    unfold foldl in H.
    erewrite maxda in H.
    rewrite <- cat1s in H.
    rewrite foldl_cat in H.
    simpl in H.
    SearchAbout foldl.
    SearchAbout cons.
  *)
  Lemma max_in_seq_has :
    forall l default mx,
      mx = foldl max default l ->
      mx != default ->
      (has (fun x => x =? mx) l
       /\ forall lelem, has (fun x => x =? lelem) l -> max lelem mx = mx).
  Proof.
    intros l. simpl. induction l.
    - simpl. intros mx default Hmx Hmx0. rewrite Hmx in Hmx0.
      (* Show false from Hmx0. Should be able to simplify this proof. *)
      unfold is_true in Hmx0.
      pose (iff := negb_true_iff (mx == mx)).
      destruct iff as [Hif _].
      pose (F:= eq_true_false_abs (mx == mx) (eq_refl mx) (Hif Hmx0)). contradiction.
    - intros default mx Hmx Hmxdefault.
      rewrite Hmx in Hmxdefault.
      destruct (a =? mx) eqn:mxa.
      + simpl. rewrite mxa. simpl. split.
        * auto.
        * intros lelem H.
          apply Is_true_eq_left in H.
          apply orb_prop_elim in H.
          destruct H as [H1 | H2].
          -- move : mxa.
             rewrite Nat.eqb_eq.
             apply Is_true_eq_true in H1.
             move : H1.
             rewrite Nat.eqb_eq.
             intros H0 H1. subst a. rewrite H1.
             apply Nat.max_idempotent.
          -- move : mxa.
             rewrite Nat.eqb_eq.
             move => mxa.
             rewrite <- mxa.
             rewrite <- mxa in Hmx.
             pose (IHlInst := IHl a a).
             SearchAbout "max".
  Admitted.


  (* Use the lemma has_fset together with max_in_seq_has to prove "max_in_fset_has" *)
      
  Lemma foldl_max_property :
    forall l n new_max mx_so_far,
      foldl max n l = mx_so_far ->
      new_max > mx_so_far ->
      foldl max n (l ++ [new_max]) = new_max.
  Proof.
    intros l.
    induction l.
    - simpl. intros n new_max mx_so_far H Hnewmax. rewrite H.
      pose (max_spec := Nat.max_spec mx_so_far new_max).
      destruct max_spec as [[Truth Concl] | [Falsity _]]; auto.
      + admit (* Here, derive false from Falsity and Hnewmax. *).
      + unfold foldl. Search "" "foldl".
    Admitted.
  
  Lemma max_path_size_in_set_spec :
    forall ps sz,
      sz != 0 ->
      (max_path_size_in_set ps = sz <->
       ((has (fun p => size_of_path p =? sz) ps) = true /\
        (has (fun p => size_of_path p > sz) ps) = false)).
  Proof.
    intros.
  Admitted.

  Lemma max_path_size_in_set_distributes :
    forall bs bs',
      max_path_size_in_set (bs :|: bs')%fset =
      max (max_path_size_in_set bs) (max_path_size_in_set bs').
  Proof.
    move => bs bs'.
    rewrite /max_path_size_in_set.
    Search "" "fsetU".
    Search "" "map".
  Admitted.


  (* Not sure if needed. *)
  Lemma max_path_size_in_set_seq :
    forall bs,
      max_path_size_in_set (fset (val bs)) = max_path_size_in_set bs.
  Proof.
    unfold max_path_size_in_set.
    (* Here, need to cancel out "val fset val" *)
    SearchAbout fsubset.
  Admitted.

  Lemma notsubset_exists_in :
    forall (T:ordType) (s: {fset T}) (t: {fset T}),
      ~~fsubset t s ->
      exists x, x \in t /\ x \notin s.
  Proof.
    SearchAbout "fsubsetPn".
    (* This is exactly what we need. Why is it not available in?
       It is available here: https://github.com/math-comp/finmap/blob/48c1330c43194c566410bb1dcb1af623b679cc2e/finmap.v#L1834
     *)
    Admitted.
  
  (* The following lemma is needed because max_path_size_in_set is the metric for progress.
     It is important to show that this metric never decreases by making a step.
     This lemma asserts this fact.
   *)

  Lemma access_step_never_decreases_path_length :
    forall m p ps ps' sz,
      sz != 0 ->
      access_step_paths' m ps sz = ps' ->
      p \in ps' ->
            (p \in ps \/ size_of_path p = sz + 1).
  Proof.
    intros m p ps ps' sz Hsz Hps' Hp.
    destruct (size_of_path p =? sz + 1) eqn:sz_p.
    - right.
      apply/Nat.eqb_spec. auto.
    - left.
      subst ps'. unfold access_step_paths' in Hp.
      (* move: Hp. *)
      (* apply/fsetUP => Hp. *)
      (* TODO: Cannot apply view fsetUP. Any idea how to deal with this error? *)
      (* SearchAbout "fsetUP". *)
      assert (Hp_fsetUP_applied : p \in ps \/
                                         p \in fset (concat
                                                       (List.map
                                                          (extend_path' m)
                                                          [seq p0 <- ps | size_of_path p0 =? sz]
                                                       )
                                                    )
             ).
      {
        admit.
      }
      destruct Hp_fsetUP_applied.
      + assumption.
      + assert (all_sz1 : all (fun x => size_of_path x =? sz + 1)
                              (concat
                                 (List.map
                                    (extend_path' m)
                                    [seq p0 <- ps | size_of_path p0 =? sz]))).
        {
          * (* SearchAbout concat. *)
            (* TODO: Don't know how to deal with concat. *)
            admit.
        }
        (* erewrite <- all_fset in all_sz1. *)
        (* Search "" "all_fset". *)
        (* TODO: Found no subterm matching "all ?M1660 ?M1661" in all_sz1. Why?*)

        (* TODO: Do not know how to write "all" for fset. It expects a seq. *)
        (*
        assert (all_sz1_rewritten: all (fun x => size_of_path x =? sz + 1)
                                       fset (concat
                                               (List.map
                                                  (extend_path' m)
                                                  [seq p0 <- ps | size_of_path p0 =? sz]
                                               )
                                            )
               ).
        *)
        (*Use /allP*)

        Admitted.
  
  Lemma access_step_never_decreases_max_path_length :
    forall m ps ps' sz,
      sz != 0 ->
      max_path_size_in_set ps = sz ->
      access_step_paths' m ps sz = ps' ->
      (ps = ps' /\
       max_path_size_in_set ps' = sz)
      \/
      max_path_size_in_set ps' = sz + 1.
  Proof.
    intros m ps ps' sz Hsz H H0.
    destruct (ps == ps') eqn:e.
    - pose (e' := eqP e).
      left. split. trivial. rewrite <- H. rewrite e'. trivial.
    - right.
      rewrite eqEfsubset in e.
      pose (e1 := access_step_paths'_expansive m ps sz).
      erewrite H0 in e1.
      pose (subOrsub := andb_false_iff (fsubset ps ps') (fsubset ps' ps)).
      edestruct subOrsub as [H1 _].
      pose (subOrsubConc := H1 e).
      destruct subOrsubConc as [psSubps'f | ps'Subpsf].
    - pose (F := eq_true_false_abs (fsubset ps ps') e1 psSubps'f).
      contradiction.
      (* Here, there are two reasons why this goal is true.
         The first reason is extend_path'_increases_length.
         The second reason is H. 
       *)

      (* Use ps'Subpsf to obtain a path that is not in ps *)
      assert (existsPath: exists p, p \in ps' /\ p \notin ps).
      {
        - apply notsubset_exists_in. apply eq_true_not_negb.
          rewrite not_true_iff_false. exact ps'Subpsf.
      }
      subst ps'.
      unfold access_step_paths' in existsPath.
      destruct existsPath as [p [pInU pNotin]].
      rewrite in_fsetU in pInU.
      apply orb_prop in pInU.
      destruct pInU as [pInps | pInConcat].
      + rewrite <- negb_false_iff in pInps.
        unfold is_true in pNotin.
        pose (F := eq_true_false_abs (p \notin ps) pNotin pInps).
        contradiction.
      + unfold access_step_paths'.
        rewrite max_path_size_in_set_distributes.
        pose (maxSpec := Max.max_spec
                           (max_path_size_in_set ps)
                           (max_path_size_in_set
                              (fset (concat (List.map (extend_path' m) [seq p0 <- ps | size_of_path p0 =? sz]))))).
        destruct maxSpec as [[TrueCond Rewr] | [Impossible _]].
        * rewrite Rewr.
          (* Search "" "map" "all". *)


          (*
          assert (all_all_size1:
                    all (all (fun x => size_of_path x =? size_of_path p + 1))
                        (List.map (extend_path' m) [seq p0 <- ps | size_of_path p0 =? sz])).
                 {
                   -- rewrite all_map.
                      unfold preim.
                      (* SearchAbout all. *)
                      assert (HpredT:
                                [pred x |
                                 all
                                   (fun x0 : path_t => size_of_path x0 =? size_of_path p + 1)
                                   (extend_path' m x)
                                ] = predT).
                      unfold predT.
                      assert (extIncLen:
                                forall pth,
                                  all
                                    (fun x0 : path_t => size_of_path x0 =? size_of_path pth + 1)
                                    (extend_path' m pth)
                                = true).
                      {
                        ++ intros pth.
                           pose (goal :=
                                   extend_path'_increases_length m pth (extend_path' m pth)).
                           unfold is_true in goal.
                           eapply goal.
                           reflexivity.
                      }
                      unfold simpl_pred.
                     (*
                      SearchAbout pred.
                      rewrite extIncLen.
                      SearchAbout pred.
                      apply all_predT.
                      Search "" "all" "filter".
                      *)
                 }
           *)

          
          (* SearchAbout Init.Nat.max.*)
          (* Probably do not need this assertion anymore. *)
          assert (sizeOfFilter: size [seq p <- ps | size_of_path p =? sz] > 0).
          {
            - assert (existsPsz: exists p, p \in ps /\ size_of_path p = sz).
              {
                (* This should follow from H somehow. *)
                - admit.
              }
              rewrite size_filter.
              rewrite <- has_count.
              apply/hasP.
              destruct existsPsz as [pMx [pInps pSz]].
              eexists pMx.
              + exact pInps.
              + apply/Nat.eqb_spec. exact pSz.
          }
      
  (*rewrite (andb_false_iff (fsubset ps ps') (fsubset ps' ps)) in e.
      rewrite <- negb_true_iff in e.
      unfold negb.
      Search "" "fsubset".
      assert (ps <> ps)
      Search "" "_ != _".
      pose (e' := eqP e).

      
    
    destruct (fsubset ps' ps) eqn:e.
    - left.
      assert (pseqps': ps = ps').
      apply: fsubset_sizeP.
      * pose (e1 := access_step_paths'_expansive m ps).
        erewrite H in e1.
        pose (e1size := fsubset_leq_size e1).
        pose (esize := fsubset_leq_size e).
        SearchAbout "<=".
        apply anti_leq.
        SearchAbout "<=".
        Print antisymmetric.
        SearchAbout "&&".
        SearchAbout is_true.
        unfold is_true in e1size.
        unfold is_true in esize.
        rewrite e1size. rewrite esize. auto.
      * pose (e1 := access_step_paths'_expansive m ps).
        erewrite H in e1. trivial.
        split.
      + trivial.
      + rewrite pseqps'. trivial.
    - right.
      pose (e1 := access_step_paths'_expansive m ps).
      erewrite H in e1.
      SearchAbout fsubset.
      pose (eqn := eqEfsubset ps ps').
      erewrite e in eqn.
      SearchAbout andb.
      erewrite andb_false_r in eqn.
      subst ps'.
      unfold access_step_paths' in eqn.
      SearchAbout fset.
      (* Attempting to prove that the RHS of the union is not empty *)
      destruct (size(fset (concat [seq extend_path' m i | i <- val ps])%fset)) eqn:isEmpty.
      SearchAbout size fset.
      SearchAbout fsubset.
      unfold max_path_size_in_set.
      
      SearchAbout Init.Nat.max.*)
  Admitted.

  (*
  Lemma reachable_paths_with_fuel_increases_max_path_by_fuel :
    forall mem ps ps' fuel,
      reachable_paths_with_fuel' mem ps fuel = ps' ->
      max_path_size_in_set ps' <= fuel + max_path_size_in_set ps.
  Proof.
    unfold reachable_paths_with_fuel'.
    intros.
    induction fuel.
    - subst ps'.
      induction (max_path_size_in_set ps); auto.
    - subst ps'.
    Admitted.
  *)
  (*
    Definition extend_set_of_paths_one_step (m: t) (ps: {fset path}) : {fset path} :=
    fsetU ps (fset ).
   *)


  
  (* DEPRECATED: ACCESS WITHOUT PATHS *)

  Definition access_step (m: t) (bs: {fset (Component.id * Block.id)}) :
    {fset (Component.id * Block.id)} :=
    fsetU bs (fset (concat (map (apply_load_block m) (val bs)))).
  
  Fixpoint reachable_blocks_with_fuel (m: t) (bs: {fset (Component.id * Block.id)}) (n: nat) :=
    match n with
    | 0 => bs
    | S n => reachable_blocks_with_fuel m (access_step m bs) n
    end.
  
  Definition reachable_blocks (m : t) (bs: {fset (Component.id * Block.id)}) :
    {fset (Component.id * Block.id)} :=
    reachable_blocks_with_fuel m bs (size (domm m)).

  Print idempotent.
  Lemma access_step_expansive m bs bs' :
    access_step m bs = bs' ->
    fsubset bs bs'.
  Proof. intros H. unfold access_step in H. rewrite <- H. unfold fsubset. rewrite fsetUA.
         rewrite fsetUid. auto.
  Qed.

  Lemma reachable_blocks_with_fuel_expansive:
    forall n m bs bs',
    reachable_blocks_with_fuel m bs n = bs' ->
    fsubset bs bs'.
  Proof.
    induction n.
    - simpl. intros. rewrite H. unfold fsubset. rewrite fsetUid. auto.
    - intros.
      simpl in H. apply IHn in H.
      remember (access_step m bs) as bs''.
      symmetry in Heqbs''.
      apply access_step_expansive in Heqbs''.
      Search fsubset.
      eapply fsubset_trans.
      + exact Heqbs''.
      + exact H.
  Qed.
  
  Lemma reachable_blocks_expansive:
    forall m bs bs',
      reachable_blocks m bs = bs' ->
      fsubset bs bs'.
  Proof.
    intros. unfold reachable_blocks in H.
    apply reachable_blocks_with_fuel_expansive with (size (domm m)) m. auto.
  Qed.

  Lemma access_step_additive m bs1 bs1' bs2 bs2':
    access_step m bs1 = bs1' ->
    access_step m bs2 = bs2' ->
    access_step m (fsetU bs1 bs2) = fsetU bs1' bs2'.
  Proof.
    unfold access_step. intros H1 H2.
    subst bs1' bs2'.
    rewrite <- ?fsetUA.
    (* Here, instead of the assert,
       try to cancel out bs1 with bs1 on both sides of the equation. *)
    assert  ( ((bs2 :|: fset (concat [seq apply_load_block m i | i <- val (bs1 :|: bs2)])))%fset =
              ((fset (concat [seq apply_load_block m i | i <- val bs1])
                     :|: (bs2 :|: fset (concat [seq apply_load_block m i | i <- val bs2]))))%fset).
    {
      rewrite -> fsetUA with (y := bs2).
      rewrite -> fsetUC with (y := bs2). (* unintended consequence *)
      rewrite -> fsetUC with (y := bs2). (* intended consequence *)
      rewrite <- fsetUA with (x := bs2).
      (* Here, instead of the assert, 
         again try to cancel out bs2 with bs2 on both sides of the equation. *)
      assert (  fset (concat [seq apply_load_block m i | i <- val (bs2 :|: bs1)])%fset =
                ((fset (concat [seq apply_load_block m i | i <- val bs1]))%fset
                      :|: fset (concat [seq apply_load_block m i | i <- val bs2]))%fset
             ).
      {
        rewrite fsetUC. (* fix the unintended consequence *)
        rewrite <- fset_cat.
        unfold fsetU.
        (* Here, need to cancel out "val fset" of the LHS, then try to show additivity of
           apply_load_block, I guess. *)
        Admitted.
     (* }*)
    (*} *)

  Lemma reachable_blocks_with_fuel_additive:
    forall m n bs1 bs2 bs1' bs2',
    reachable_blocks_with_fuel m bs1 n = bs1' ->
    reachable_blocks_with_fuel m bs2 n = bs2' ->
    reachable_blocks_with_fuel m (fsetU bs1 bs2) n = fsetU bs1' bs2'.
  Proof.
    induction n.
    - simpl. intros. subst bs1' bs2'. auto.
    - simpl. intros.
      erewrite access_step_additive.
      + eapply IHn.
        * exact H.
        * exact H0.
      + auto.
      + auto.
  Qed.
  
  Lemma reachable_blocks_additive:
    forall m bs1 bs1' bs2 bs2',
      reachable_blocks m bs1 = bs1' ->
      reachable_blocks m bs2 = bs2' ->
      reachable_blocks m (fsetU bs1 bs2) = fsetU bs1' bs2'.
    unfold reachable_blocks. intros.
    apply reachable_blocks_with_fuel_additive; auto.
  Qed.

  Lemma reachable_blocks_maximal:
    forall m bs bs',
      reachable_blocks m bs = bs' ->
      reachable_blocks m bs' = bs'.
  Proof. Admitted.

  Lemma reachable_blocks_invariant_to_unreachable_store:
    forall m m' bs bs' b i v,
      reachable_blocks m bs = bs' ->
      b \notin bs' ->
      store m i v = Some m' ->
      reachable_blocks m' bs = bs'.
  Admitted.

  Lemma stores_to_block_does_not_affect_its_own_reachability:
    forall m m' bs b i v,
      b \in reachable_blocks m bs ->
      store m i v = Some m' ->
      b \in reachable_blocks m' bs.
  Admitted.
  
  Lemma load_after_store mem ptr v mem' ptr' :
    store mem  ptr v = Some mem' ->
    load mem' ptr' =
    if ptr' == ptr then Some v else load mem ptr'.
  Proof.
    case: ptr ptr'=> [[c b] off] [[c' b'] off']; rewrite /store /load /=.
    case mem_c: (mem c) => [bs|] //.
    case bs_ptr: (ComponentMemory.store bs b off v) => [bs'|] //= [<- {mem'}].
    rewrite !xpair_eqE setmE; case: (c' =P c) => [-> {c'}|] //=.
    by rewrite (ComponentMemory.load_after_store _ _ _ _ _ bs_ptr) mem_c.
  Qed.

  Lemma load_after_store_eq mem ptr v mem' :
    store mem  ptr v = Some mem' ->
    load  mem' ptr   = Some v.
  Proof. by move=> /load_after_store ->; rewrite eqxx. Qed.


  Lemma load_after_store_neq mem ptr v mem' ptr' :
    ptr <> ptr' ->
    store mem  ptr  v = Some mem' ->
    load  mem' ptr'   = load mem ptr'.
  Proof. by move=> /eqP/negbTE ne /load_after_store ->; rewrite eq_sym ne. Qed.

  Lemma store_after_load mem ptr v v' :
    load mem ptr = Some v ->
    exists mem', store mem ptr v' = Some mem'.
  Proof.
    case: ptr=> [[c b] off]; rewrite /load /store /=.
    case mem_c: (mem c)=> [bs|] //=.
    case/(ComponentMemory.store_after_load _ _ _ _ v')=> [bs' ->].
    by eauto.
  Qed.

End Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Clean these lemmas and their weak variants *)

Definition to_partial_memory (mem : Memory.t) (ctx : {fset Component.id}) :=
  filterm (fun k _ => negb (k \in ctx)) mem.

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
  forall C b o v,
    C \notin ctx ->
    Memory.load mem1 (C, b, o) = Some v ->
    Memory.load mem2 (C, b, o) = Some v.
Proof.
move=> ctx mem1 mem2 /eq_fmap Hfilter C b o v nin_ctx.
rewrite /Memory.load /=; move/(_ C): Hfilter; rewrite !filtermE nin_ctx.
by case: (mem1 C) (mem2 C)=> [memC|] // [_|] //= [<-].
Qed.

Lemma program_load_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall C b o v1 v2,
    C \notin ctx ->
    Memory.load mem1 (C, b, o) = Some v1 ->
    Memory.load mem2 (C, b, o) = Some v2 ->
    v1 = v2.
Proof.
move=> ctx mem1 mem2 Hfilter C b o v1 v2 nin_ctx e_mem.
rewrite (program_load_in_partialized_memory_strong Hfilter nin_ctx e_mem).
by case.
Qed.

Lemma program_store_in_partialized_memory_strong:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall C b o v mem1',
    C \notin ctx ->
    Memory.store mem1 (C, b, o) v = Some mem1' ->
  exists2 mem2',
    Memory.store mem2 (C, b, o) v = Some mem2' &
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 /eq_fmap Hfilter C b o v mem1' nin_ctx.
rewrite /Memory.store /=; move/(_ C): (Hfilter); rewrite !filtermE nin_ctx.
case: (mem1 C) (mem2 C)=> [memC|] // [_|] //= [<-].
case: (ComponentMemory.store memC b o v)=> [memC'|] //= [<-].
eexists; eauto; apply/eq_fmap=> C'; rewrite !filtermE !setmE.
case: eqP=> [-> {C'}|_] //.
by move/(_ C'): Hfilter; rewrite !filtermE.
Qed.

Lemma program_store_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    to_partial_memory mem1 ctx = to_partial_memory mem2 ctx ->
  forall C b o v mem1' mem2',
    C \notin ctx ->
    Memory.store mem1 (C, b, o) v = Some mem1' ->
    Memory.store mem2 (C, b, o) v = Some mem2' ->
    to_partial_memory mem1' ctx = to_partial_memory mem2' ctx.
Proof.
move=> ctx mem1 mem2 Hfilter C b o v mem1' mem2' nin_ctx e_mem.
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
  forall (ctx: {fset Component.id}) mem C b o v mem',
    C \in ctx ->
    Memory.store mem (C, b, o) v = Some mem' ->
    to_partial_memory mem' ctx = to_partial_memory mem ctx.
Proof.
  move=> ctx mem C b o v mem' C_in_ctx.
  rewrite /Memory.store /= => Hstore.
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
  destruct ptr as [[C' b] o]. simpl.
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
  destruct (mem1 (Pointer.component ptr)) eqn:Hcase1; rewrite Hcase1;
    last discriminate.
  simpl.
  destruct (ComponentMemory.store t (Pointer.block ptr) (Pointer.offset ptr) v) eqn:Hcase2;
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
  destruct (mem1 C) as [memC |] eqn:Hcase1; rewrite Hcase1;
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
    destruct (mem Cid) eqn:Hmem; rewrite Hmem.
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
    destruct (mem Cid) eqn:Hmem; rewrite Hmem.
    now rewrite HCid.
    now reflexivity.
  Qed.
End Partial.

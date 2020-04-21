  (* Define reachability using the ssreflect fingraph library. *)
  Definition node_t : Type := Component.id * Block.id.

  Definition apply_load_block_seq (m: t) (pair: node_t) : seq node_t :=
    match m (fst pair) with
    | None => nil
    | Some compMem => ComponentMemory.load_block compMem (snd pair)
    end.

  Lemma apply_load_block_load :
    forall m nd ndres,
      In ndres (apply_load_block_seq m nd) <->
      exists ndresoff ndoff,
        load m (nd.1, nd.2, ndoff) = Some (Ptr (ndres.1, ndres.2, ndresoff)).
  Proof.
    intros m nd ndres.
    unfold apply_load_block_seq. unfold load. simpl.
    split; destruct (m nd.1) as [compMem |].
    - destruct (ComponentMemory.load_block_load compMem nd.2 ndres.1 ndres.2) as [l r].
      rewrite <- surjective_pairing in l. rewrite <- surjective_pairing.
      intros Hin. apply l. exact Hin.
    - intros Hin. exfalso. apply (List.in_nil Hin).
    - intros [ndresoff [ndoff Hload]].
      destruct (ComponentMemory.load_block_load compMem nd.2 ndres.1 ndres.2) as [l r].
      rewrite <- surjective_pairing in r. apply r.
      rewrite <- surjective_pairing in Hload. exists ndresoff. exists ndoff. exact Hload.
    - intros [ndresoff [_ contra]]. discriminate.
  Qed.
      
  Definition apply_load_block (m: t) (pair: node_t) : list (node_t) :=
    match m (fst pair) with
    | None => nil
    | Some compMem => ComponentMemory.load_block compMem (snd pair)
    end.
  
  Definition max_ptr_per_compMem (m: t) :=
    mapm ComponentMemory.max_ptr m.

  Definition max_ptr (m: t) : node_t :=
    fold_max (map snd (max_ptr_per_compMem m)).

  Lemma apply_load_block_max_ptr_per_compMem_or_less :
    forall x x0 m,
      In x (apply_load_block_seq m x0) ->
      exists n nd, (max_ptr_per_compMem m) n = Some nd /\ x.1 <= nd.1 /\ x.2 <= nd.2.
  Proof.
    unfold apply_load_block_seq.
    intros x x0 m Hinloadblock.
    destruct (m x0.1) eqn:e.
    - exists x0.1.
      exists (ComponentMemory.max_ptr t0).
      split.
      + unfold max_ptr_per_compMem.
        unfold mapm. simpl. rewrite mapimE. rewrite e. auto.
      + apply ComponentMemory.max_ptr_load_block_out with (b := x0.2). auto.
    - exfalso. pose (List.in_nil Hinloadblock). auto.
  Qed.
  
  Lemma max_ptr_In_leq :
    forall m x,
      (exists n nd, (max_ptr_per_compMem m) n = Some nd /\ x.1 <= nd.1 /\ x.2 <= nd.2) ->
      x.1 <= (max_ptr m).1 /\ x.2 <= (max_ptr m).2.
  Proof.
    unfold max_ptr.
    intros m x [n [nd [Hin [H1 H2]]]].
    SearchAbout domm.
    - pose (In_innd := In_in nd (map snd (max_ptr_per_compMem m))).
      split.
      + apply leq_trans with (n := nd.1). trivial. apply fold_max_In_leq.
        erewrite <- In_innd. apply/mapP. exists (n, nd).
        * apply/getmP. exact Hin.
        * auto.
      + apply leq_trans with (n := nd.2). trivial. apply fold_max_In_leq.
        erewrite <- In_innd. apply/mapP. exists (n, nd).
        * apply/getmP. exact Hin.
        * auto.
  Qed.
  
  Lemma In_apply_load_block_seq_max_ptr :
    forall x x0 m,
      In x (apply_load_block_seq m x0) ->
      x.1 <= (max_ptr m).1 /\ x.2 <= (max_ptr m).2.
  Proof.
    intros x x0 m Hin.
    unfold max_ptr.
    apply max_ptr_In_leq.
    apply apply_load_block_max_ptr_per_compMem_or_less with (x0 := x0). trivial.
  Qed.

  Lemma In_apply_load_block_seq_max_ptr_less :
    forall x x0 m,
      In x (apply_load_block_seq m x0) ->
      x.1 < S (max_ptr m).1 /\ x.2 < S (max_ptr m).2.
  Proof.
    intros x x0 m Hinload.
    pose (Hleq := In_apply_load_block_seq_max_ptr x x0 m Hinload).
    destruct Hleq as [H1 H2].
    split; rewrite ltnS; trivial.
  Qed.
  
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

  Fixpoint construct_seq_using_nth_In_proof T s n (pf_nlt: n < length s) :
    seq (sig (fun (x:T) => In x s)).
  Proof.
    induction n.
    - exact [nth_In_proof T s 0 pf_nlt].
    - assert (n_len_s: n < length s).
      {
        auto.
      }
      exact (cons (nth_In_proof T s (n.+1) pf_nlt) (IHn n_len_s)).
  Defined.

  Definition proofize_seq T s : seq (sig (fun (x:T) => In x s)).
  Proof.
    pose (n := length s).
    destruct (length s) eqn:e.
    - exact nil.
    - apply construct_seq_using_nth_In_proof with (n := n0).
      rewrite e. auto.
  Defined.

  Compute (proofize_seq nat (5 :: (6 :: (4 :: nil)))).

  Lemma size_proofize_seq : forall T s, size (proofize_seq T s) = size s.
  Proof.
    intros.
    induction s.
    - auto.
    - simpl.
      unfold proofize_seq.
      simpl.
      SearchAbout nat_rect.
  Admitted.

  SearchAbout sig.
  
  Definition deproofize_one A P y := @proj1_sig A P y.

  SearchAbout proj1_sig.
  Check sval.

  (*TODO: Check the lemmas about proj1_sig and sval. They may help in
   proving a spec for proofize_seq. *)

  Lemma proofize_seq_cons :
    forall T a s,
    exists ap sp, proofize_seq T (a :: s) = ap :: sp.
  Proof.
    intros T a s. simpl. eexists. eexists.
    unfold proofize_seq.
    (* destruct (length (a :: s)) *) (* Does not work. *)
  Admitted.
  
  Lemma proofize_seq_spec :
    forall T s spf,
      spf = proofize_seq T s ->
      map (@proj1_sig T _) spf = s.
  Proof.
    induction s as [| a s IHs]; simpl; intros spf H.
    - rewrite H. auto.
    - (* PROBLEM: The induction hypothesis IHs expects a sequence with proofs of In x s
       instead of proofs of In x (a :: s) *)
      destruct (proofize_seq_cons T a s) as [ap [sp pr_eq]].
      rewrite H. rewrite pr_eq.
      rewrite map_cons.
  Admitted.
      
  
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
  
  Definition finitize_ptr (ptr : Component.id * Block.id) :
    ordinal (S (fst ptr)) * ordinal (S (snd ptr)) :=
    (inord (fst ptr), inord (snd ptr)).

  Definition cast_to_bigger_ordinal_right {l1 : nat} {r1 : nat} (l2: nat) (r2: nat)
             (ptr : ordinal l1 * ordinal r1) :
    (ordinal (ssrnat.maxn l1 l2) * ordinal (ssrnat.maxn r1 r2)).
    destruct ptr as [l r].
    destruct l. destruct r.
    assert (lp: ssrnat.leq (S m) (ssrnat.maxn l1 l2)).
    {
      apply ssrnat.leq_trans with (n := l1).
      - exact i.
      - apply ssrnat.leq_maxl.
    }
    assert (rp: ssrnat.leq (S m0) (ssrnat.maxn r1 r2)).
    {
      apply ssrnat.leq_trans with (n := r1).
      - exact i0.
      - apply ssrnat.leq_maxl.
    }
    exact (Ordinal lp, Ordinal rp).
  Defined.

  Definition cast_to_bigger_ordinal_left {l2 : nat} {r2 : nat} (l1: nat) (r1: nat)
             (ptr : ordinal l2 * ordinal r2) :
    (ordinal (ssrnat.maxn l1 l2) * ordinal (ssrnat.maxn r1 r2)).
    destruct ptr as [l r].
    destruct l. destruct r.
    assert (lp: ssrnat.leq (S m) (ssrnat.maxn l1 l2)).
    {
      apply ssrnat.leq_trans with (n := l2).
      - exact i.
      - apply ssrnat.leq_maxr.
    }
    assert (rp: ssrnat.leq (S m0) (ssrnat.maxn r1 r2)).
    {
      apply ssrnat.leq_trans with (n := r2).
      - exact i0.
      - apply ssrnat.leq_maxr.
    }
    exact (Ordinal lp, Ordinal rp).
  Defined.

  (* FINITIZE MEMORY USING MAX_PTR *)

  Definition apply_load_block_seq_fin
             (m: t) 
             (nd1: nat) (nd2: nat)
             (nd : ordinal (ssrnat.maxn (S (max_ptr m).1) nd1) *
                   ordinal (ssrnat.maxn (S (max_ptr m).2) nd2))
    : seq (ordinal (ssrnat.maxn (S (max_ptr m).1) nd1) *
           ordinal (ssrnat.maxn (S (max_ptr m).2) nd2)) :=
    map
      (fun node_inPf =>
         match node_inPf with | exist x In_x_applyloadblock =>
                                cast_to_bigger_ordinal_right nd1 nd2
                                               (Ordinal (
                                                    (In_apply_load_block_seq_max_ptr_less
                                                       x
                                                       (nat_of_ord nd.1, nat_of_ord nd.2)
                                                       m
                                                       In_x_applyloadblock).1
                                                  ),
                                 Ordinal
                                   (
                                     (In_apply_load_block_seq_max_ptr_less
                                        x
                                        (nat_of_ord nd.1, nat_of_ord nd.2)
                                        m
                                        In_x_applyloadblock).2
                                   )
                                )
         end)
      (proofize_seq node_t (apply_load_block_seq m (nat_of_ord nd.1, nat_of_ord nd.2)))
  .

  Definition fingraph_of_mem
             (m: t)
             (nd1: nat) (nd2: nat)
    := apply_load_block_seq_fin m nd1 nd2.
  
  Definition reachable_nodes m (x: Component.id * Block.id)
    := dfs
         (fingraph_of_mem m (S x.1) (S x.2))
         ((maxn (S (max_ptr m).1) x.1.+1) * (maxn (S (max_ptr m).2) x.2.+1))
         nil
         (cast_to_bigger_ordinal_left
            (S (max_ptr m).1)
            (S (max_ptr m).2)
            (finitize_ptr x)
         ).
  
  Lemma dfs_path_fin_mem:
    forall m x y,
      reflect (dfs_path
                 (fingraph_of_mem m (S x.1) (S x.2))
                 nil
                 (cast_to_bigger_ordinal_left
                    (S (max_ptr m).1)
                    (S (max_ptr m).2)
                    (finitize_ptr x)
                 )
                 y
              )
              (y \in reachable_nodes m x).
  Proof.
    intros m x y.
    apply dfs_pathP.
    - simpl.
      rewrite card_prod. rewrite card_ord. rewrite card_ord.
      rewrite card0. rewrite add0n. auto.
    - auto.
  Qed.

  Lemma dfs_path_fin_mem_iff:
    forall m x y,
      (dfs_path
         (fingraph_of_mem m (S x.1) (S x.2))
         nil
         (cast_to_bigger_ordinal_left
            (S (max_ptr m).1)
            (S (max_ptr m).2)
            (finitize_ptr x)
         )
         y
      )
      <->
      (y \in reachable_nodes m x).
  Proof.
    split; intros H; apply/dfs_path_fin_mem; auto.
  Qed.

  Definition nat_node_of_ord_node {n: nat} {m: nat} (x: ordinal n * ordinal m) :=
    let (cid, bid) := x in (nat_of_ord cid, nat_of_ord bid).
  
  Definition reachable_nodes_nat m x := map nat_node_of_ord_node (reachable_nodes m x).

  Lemma reachable_nodes_reachable_nodes_nat :
    forall x m y,
      y \in reachable_nodes m x ->
      nat_node_of_ord_node y \in reachable_nodes_nat m x.
  Proof.
    intros. unfold reachable_nodes_nat. apply map_f. auto.
  Qed.

  Lemma reachable_nodes_nat_reachable_nodes :
    forall x m y_nat,
      y_nat \in reachable_nodes_nat m x ->
      exists y, y \in reachable_nodes m x /\ nat_node_of_ord_node y = y_nat.
  Proof.
    unfold reachable_nodes_nat. intros x m y_nat Hreachnat.
    destruct (mapP Hreachnat) as [x0 Hx0 Hx0nat].
    exists x0. split; auto.
  Qed.

  (*Definition is_reachable_from m y x := y \in reachable_nodes_nat m x.

  Lemma get_path_from_to m x y ()
   *)
  (*In order to write this lemma properly, one would need to rely on the
   fact that the finitized graph and the original graph are equal.*)
 
  Lemma eq_reachable_eq_path :
    forall m m' x y,
      (reachable_nodes_nat m x = reachable_nodes_nat m' x)
      ->
      dfs_path
        (fingraph_of_mem m (S x.1) (S x.2))
        nil
        (cast_to_bigger_ordinal_left
           (S (max_ptr m).1)
           (S (max_ptr m).2)
           (finitize_ptr x)
        )
        y
      ->
      exists y',
        dfs_path
          (fingraph_of_mem m' (S x.1) (S x.2))
          nil
          (cast_to_bigger_ordinal_left
             (S (max_ptr m').1)
             (S (max_ptr m').2)
             (finitize_ptr x)
          )
          y'
        /\
        nat_node_of_ord_node y = nat_node_of_ord_node y'.
  Proof.
    intros m m' x y Hreacheq Hdfs_path.
    apply dfs_path_fin_mem_iff in Hdfs_path.
    apply reachable_nodes_reachable_nodes_nat in Hdfs_path.
    rewrite Hreacheq in Hdfs_path.
    remember (nat_node_of_ord_node y) as z.
    destruct (reachable_nodes_nat_reachable_nodes x m' z  Hdfs_path) as [x0 [P H]].
    exists x0.
    split.
    - apply/dfs_path_fin_mem. exact P.
    - auto.
  Qed.

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

  (*
  Definition nth_with_nth_proof T (x_default: T) s n : sig (fun (x:T) => x = nth x_default s n).
  Proof.
    eexists (nth x_default s n). auto.
  Qed.

  Print nth_with_nth_proof.
  *)

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

(******************************************************************************)

  (* START FOR-BACKUP-ONLY *)
  (* START DEFINING REACHABILITY INDUCTIVELY *)
  Inductive Reachable (m: t) (bs : {fset node_t}) : node_t -> Prop :=
  | Reachable_refl : forall b, b \in bs -> Reachable m bs b
  | Reachable_step : forall cid bid b' compMem,
      Reachable m bs (cid, bid) -> 
      m (cid) = Some compMem ->
      b' \in ComponentMemory.load_block compMem bid ->
      Reachable m bs b'.

  (* END DEFINING REACHABILITY INDUCTIVELY *)

(******************************************************************************)

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

(******************************************************************************)

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

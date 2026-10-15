Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Local Open Scope fset_scope.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : {fmap Block.id -> nat + list value} -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.
  Parameter domm : t -> {fset Block.id}.

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
      domm m = fmap.domm bufs.

  Axiom domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.

  (* ------------------------------------------------------------------ *)
  (* Extensions for the S2I forward-simulation proof (block injection).  *)

  (* Every memory reachable from the exported constructors keeps its
     allocated block ids below the internal allocation cursor; [wf] is that
     residual invariant, exported abstractly so that freshness of [alloc]
     becomes usable from outside the module. *)
  Parameter wf : t -> Prop.

  Axiom wf_prealloc: forall bufs, wf (prealloc bufs).
  Axiom wf_empty: wf empty.
  Axiom wf_alloc:
    forall m m' n b, wf m -> alloc m n = (m', b) -> wf m'.
  Axiom wf_store:
    forall m m' b i v, wf m -> store m b i v = Some m' -> wf m'.
  Axiom wf_reserve_block:
    forall m m' b, wf m -> reserve_block m = (m', b) -> wf m'.

  Axiom alloc_fresh:
    forall m m' n b, wf m -> alloc m n = (m', b) -> b \notin domm m.

  (* The allocation cursor is monotone: every EXISTING block id strictly
     precedes a freshly allocated one (the stack-chain descent's measure). *)
  Axiom alloc_gt:
    forall m m' n b b', wf m -> alloc m n = (m', b) -> b' \in domm m -> b' < b.

  Axiom domm_alloc_eq:
    forall m m' n b, alloc m n = (m', b) -> domm m' = b |: domm m.

  Axiom load_after_alloc_eq:
    forall m m' n b,
      alloc m n = (m', b) ->
    forall i,
      load m' b i =
      if (0 <=? i)%Z && (i <? Z.of_nat n)%Z then Some Undef else None.

  Axiom domm_store:
    forall m m' b i v, store m b i v = Some m' -> domm m' = domm m.

  Axiom load_domm:
    forall m b i v, load m b i = Some v -> b \in domm m.

  Axiom load_notin_domm:
    forall m b i, b \notin domm m -> load m b i = None.

  Axiom store_load:
    forall m m' b i v,
      store m b i v = Some m' -> exists v', load m b i = Some v'.

  Axiom load_after_reserve_block:
    forall m m' b,
      reserve_block m = (m', b) ->
    forall b' i, load m' b' i = load m b' i.

  Axiom domm_reserve_block:
    forall m m' b, reserve_block m = (m', b) -> domm m' = domm m.

  (* The allocation cursor, exposed: consecutive reservations/allocations
     return the successive cursor values (hence DISTINCT block ids — the fact
     the compiled-code anchors need). *)
  Parameter next_block : t -> Block.id.

  Axiom reserve_block_next:
    forall m m' b,
      reserve_block m = (m', b) ->
      b = next_block m /\ next_block m' = S (next_block m).

  Axiom alloc_next_block:
    forall m m' n b,
      alloc m n = (m', b) ->
      b = next_block m /\ next_block m' = S (next_block m).

  Axiom next_block_store:
    forall m m' b i v,
      store m b i v = Some m' -> next_block m' = next_block m.
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

  Definition domm (m : t) := @domm nat block (content m).

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
      domm m = fmap.domm bufs.
  Proof.
    move=> bufs m <-. by rewrite /domm /prealloc /= domm_map.
  Qed.

  (* Provable only for cursor-consistent memories (see [wf] below); kept as in
     the original development. Unused by the codebase. *)
  Lemma domm_alloc :
    forall m m' n b,
      alloc m n = (m', b) ->
      size (domm m') = size (domm m) + 1.
  Admitted.

  (* ------------------------------------------------------------------ *)
  (* Extensions for the S2I forward-simulation proof (block injection).  *)

  Definition wf (m : t) : Prop :=
    forall b, b \in domm m -> b < nextblock m.

  Lemma fold_left_max_ge (l : seq nat) (acc b : nat) :
    (b <= acc) || (b \in l) -> b <= fold_left Nat.max l acc.
  Proof.
    elim: l acc => [|x l IH] acc /=; first by rewrite orbF.
    rewrite in_cons => Hb. apply: IH.
    case/orP: Hb => [Hacc|/orP[/eqP ->|Hin]].
    - apply/orP; left. lia.
    - apply/orP; left. lia.
    - by rewrite Hin orbT.
  Qed.

  Lemma wf_prealloc: forall bufs, wf (prealloc bufs).
  Proof.
    move=> bufs b. rewrite /domm /prealloc /= domm_map => Hin.
    rewrite ltnS. apply: fold_left_max_ge. by rewrite Hin orbT.
  Qed.

  Lemma wf_empty: wf empty.
  Proof. by move=> b; rewrite /domm /empty /= domm0 in_fset0. Qed.

  Lemma wf_alloc:
    forall m m' n b, wf m -> alloc m n = (m', b) -> wf m'.
  Proof.
    move=> m m' n b Hwf [<- _] b' /=.
    rewrite /domm /= domm_set in_fsetU1 => /orP[/eqP ->|Hin].
    - by rewrite addnC addn1 ltnSn.
    - have := Hwf _ Hin. lia.
  Qed.

  Lemma wf_store:
    forall m m' b i v, wf m -> store m b i v = Some m' -> wf m'.
  Proof.
    move=> m m' b i v Hwf. rewrite /store.
    case Hb: (content m b) => [chunk|] //.
    case: (0 <=? i)%Z => //.
    case: (list_upd chunk (Z.to_nat i) v) => [chunk'|] // [<-] b' /=.
    rewrite /domm /= domm_set in_fsetU1 => /orP[/eqP ->|Hin].
    - apply: Hwf. by rewrite /domm mem_domm Hb.
    - exact: Hwf.
  Qed.

  Lemma wf_reserve_block:
    forall m m' b, wf m -> reserve_block m = (m', b) -> wf m'.
  Proof.
    move=> m m' b Hwf [<- _] b' /= Hin.
    have := Hwf _ Hin. rewrite /domm /=. lia.
  Qed.

  Lemma alloc_fresh:
    forall m m' n b, wf m -> alloc m n = (m', b) -> b \notin domm m.
  Proof.
    move=> m m' n b Hwf [_ <-].
    apply/negP => /Hwf. by rewrite ltnn.
  Qed.

  Lemma alloc_gt:
    forall m m' n b b', wf m -> alloc m n = (m', b) -> b' \in domm m -> b' < b.
  Proof.
    move=> m m' n b b' Hwf [_ <-]. exact: Hwf.
  Qed.

  Lemma domm_alloc_eq:
    forall m m' n b, alloc m n = (m', b) -> domm m' = b |: domm m.
  Proof.
    move=> m m' n b [<- <-]. by rewrite /domm /= domm_set.
  Qed.

  Lemma load_after_alloc_eq:
    forall m m' n b,
      alloc m n = (m', b) ->
    forall i,
      load m' b i =
      if (0 <=? i)%Z && (i <? Z.of_nat n)%Z then Some Undef else None.
  Proof.
    move=> m m' n b [<- <-] i. rewrite /load /= setmE eqxx.
    case: (Z.leb_spec0 0 i) => [i_pos|] //=.
    case: (Z.ltb_spec0 i (Z.of_nat n)) => [i_lt|i_ge].
    - rewrite <- (Z2Nat.id _ i_pos) in i_lt.
      rewrite <- Nat2Z.inj_lt in i_lt.
      rewrite <- (repeat_length Undef n) in i_lt.
      rewrite <- nth_error_Some in i_lt.
      destruct (nth_error (repeat Undef n) (Z.to_nat i)) as [v|] eqn:get_i;
        try congruence.
      apply nth_error_In in get_i. apply repeat_spec in get_i.
      now rewrite get_i.
    - apply (proj2 (nth_error_None _ _)). rewrite repeat_length. lia.
  Qed.

  Lemma domm_store:
    forall m m' b i v, store m b i v = Some m' -> domm m' = domm m.
  Proof.
    move=> m m' b i v. rewrite /store.
    case Hb: (content m b) => [chunk|] //.
    case: (0 <=? i)%Z => //.
    case: (list_upd chunk (Z.to_nat i) v) => [chunk'|] // [<-].
    rewrite /domm /= domm_set.
    apply/eq_fset => b'. rewrite in_fsetU1.
    case: (b' =P b) => [->|] //=. by rewrite mem_domm Hb.
  Qed.

  Lemma load_domm:
    forall m b i v, load m b i = Some v -> b \in domm m.
  Proof.
    move=> m b i v. rewrite /load /domm mem_domm.
    by case: (content m b).
  Qed.

  Lemma load_notin_domm:
    forall m b i, b \notin domm m -> load m b i = None.
  Proof.
    move=> m b i. rewrite /load /domm mem_domm.
    by case: (content m b).
  Qed.

  Lemma store_load:
    forall m m' b i v,
      store m b i v = Some m' -> exists v', load m b i = Some v'.
  Proof.
    move=> m m' b i v. rewrite /store /load.
    case Hb: (content m b) => [chunk|] //.
    case: (0 <=? i)%Z => //.
    case Hupd: (list_upd chunk (Z.to_nat i) v) => [chunk'|] // _.
    move: Hupd. move: (Z.to_nat i) chunk' => k chunk'.
    elim: chunk k chunk' {Hb} => [|v'' chunk IH] [|k] chunk' //=.
    - by move=> _; eauto.
    - case Hupd: (list_upd chunk k v) => [chunk''|] //= _.
      exact: IH Hupd.
  Qed.

  Lemma load_after_reserve_block:
    forall m m' b,
      reserve_block m = (m', b) ->
    forall b' i, load m' b' i = load m b' i.
  Proof. by move=> m m' b [<- _] b' i. Qed.

  Lemma domm_reserve_block:
    forall m m' b, reserve_block m = (m', b) -> domm m' = domm m.
  Proof. by move=> m m' b [<- _]. Qed.

  Definition next_block (m : t) : Block.id := nextblock m.

  Lemma reserve_block_next:
    forall m m' b,
      reserve_block m = (m', b) ->
      b = next_block m /\ next_block m' = S (next_block m).
  Proof. by move=> m m' b [<- <-]. Qed.

  Lemma alloc_next_block:
    forall m m' n b,
      alloc m n = (m', b) ->
      b = next_block m /\ next_block m' = S (next_block m).
  Proof. by move=> m m' n b [<- <-]. Qed.

  Lemma next_block_store:
    forall m m' b i v,
      store m b i v = Some m' -> next_block m' = next_block m.
  Proof.
    move=> m m' b i v. rewrite /store.
    case: (content m b) => [chunk|] //.
    case: (0 <=? i)%Z => //.
    case: (list_upd chunk (Z.to_nat i) v) => [chunk'|] //.
    by move=> [<-].
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
      destruct (reserve_block t0).
      inversion H. symmetry in H2; now apply app_cons_not_nil in H2.
    - intros n mem' H.
      destruct n; auto.
      + simpl in *. inversion H. now apply app_cons_not_nil in H2.
      + rewrite app_length Nat.add_comm. simpl.
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
  destruct (mem1 (Pointer.component ptr)) eqn:Hcase1;
    rewrite Hcase1 || idtac "ExStructures 0.1 legacy rewrite inactive";
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
  destruct (mem1 C) as [memC |] eqn:Hcase1;
    rewrite Hcase1 || idtac "ExStructures 0.1 legacy rewrite inactive";
    last discriminate.
  simpl.
  destruct (ComponentMemory.alloc memC size) as [memC' b].
  rewrite setm_union. now inversion Halloc.
Qed.


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

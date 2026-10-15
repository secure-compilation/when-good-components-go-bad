(* Buffer-layout kernel: the data segment [initial_memory pb] (Merged.v) lays the cells of
   [linearize_bufs pb] CONTIGUOUSLY at addresses [word_of_nat 0 .. word_of_nat (total-1)],
   total = size (linearize_bufs pb).  This file proves the generic [Tmp.mapk] toolkit
   (lifted verbatim from RecompositionInit, which will import it from here) and the layout
   facts needed to DISCHARGE the former RecInit hypotheses [initial_memory_domm] /
   [alloc_label_not_in_initial_memory] and to bound [size (initial_memory pb)].

   Word discipline: never compute 2^32; all mod/val reasoning via WordExtra's
   [valw_as_word]/[word_nat_inj] and [val_word_of_nat]-style bounds. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype ssrint ssralg.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import fmap fset.
Require Import Coq.micromega.Lia.

Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import I2MP.Tmp.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Merged.
Import DoNotation.
Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MapkToolkit.

(* Tmp.mapk preserves values: if mapk f m k' = Some v, then
   exists k such that f k = k' and m k = Some v *)
Lemma foldl_unionm_In: forall {T : ordType} {S : Type} (ms : seq {fmap T -> S}) k v,
  foldl unionm emptym ms k = Some v ->
  exists mi, List.In mi ms /\ mi k = Some v.
Proof.
  intros T0 S0 ms. induction ms as [| m0 ms IH] using last_ind.
  - intros k0 v0. simpl. rewrite emptymE. discriminate.
  - intros k0 v0. rewrite foldl_rcons.
    rewrite unionmE.
    case Hacc: (foldl unionm emptym m0 k0) => [v' |].
    + (* accumulator has a value — it came from ms *)
      move=> [<-].
      destruct (IH _ _ Hacc) as [mi [Hmi Hmi_k]].
      exists mi. split; [| exact Hmi_k].
      rewrite -cats1.
      apply List.in_or_app. left. exact Hmi.
    + (* accumulator is None — value comes from m0 *)
      move=> Hm0. simpl in Hm0.
      eexists; split; [| eassumption].
      rewrite -cats1.
      apply List.in_or_app. right. left. reflexivity.
Qed.

Lemma List_In_mem: forall {T: eqType} (l: seq T) x,
    List.In x l -> x \in l.
Proof.
  intros T0 l x. induction l as [| a rest IH].
  - intro. contradiction.
  - simpl. intros [<- | Hin].
    + rewrite in_cons. apply/orP. left. exact (eq_refl _).
    + rewrite in_cons. apply/orP. right. exact (IH Hin).
Qed.

Lemma In_unzip2_exists: forall {T: ordType} {S: Type} (m: {fmap T -> S}) v,
    List.In v (unzip2 m) -> exists k, List.In (k, v) m.
Proof.
  intros T0 S0 m v Hin.
  destruct m as [s Hs]. simpl in *.
  induction s as [| [k0 v0] rest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + exists k0. left. reflexivity.
    + destruct (IH) as [k1 Hk1].
      simpl in Hs. eapply path.path_sorted; eauto.
      eauto.
      exists k1. right. exact Hk1.
Qed.

Lemma In_fmap_getm: forall {T: ordType} {S: Type} (m: {fmap T -> S}) k v,
    List.In (k, v) m -> m k = Some v.
Proof.
  intros T0 S0 m k v Hin.
  destruct m as [s Hs]. simpl in *.
  (* s is a sorted list of (T0 * S0) pairs, Hin : List.In (k, v) s *)
  (* getm_def scans left-to-right: if k == p.1 then Some p.2 else recurse *)
  (* Since s is sorted with unique keys, (k, v) in s means getm_def finds it *)
  induction s as [| [k0 v0] rest IH].
  - contradiction.
  - simpl. simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq => <- <-.
      rewrite /getm. simpl. rewrite eqxx. reflexivity.
    + rewrite /getm. simpl.
      case Hkeq: (k == k0).
      * (* k = k0 but (k, v) is in rest — contradicts sorted/unique *)
        move/eqP : Hkeq => Hkeq. subst k0.
        exfalso.
        have Hpath := Hs.
        (* path.sorted Ord.lt (k :: unzip1 rest) — since unzip1 ((k,v0)::rest) = k :: unzip1 rest *)
        simpl in Hpath.
        (* Hpath should be: path Ord.lt k (unzip1 rest) *)
        (* From (k, v) ∈ rest, k ∈ unzip1 rest *)
        have Hkin: List.In k (unzip1 rest).
        { clear -Hin. induction rest as [| [k1 v1] rest' IH].
          - contradiction.
          - simpl in *. destruct Hin as [[= -> ->] | Hin].
            + left. reflexivity.
            + right. exact (IH Hin). }
        (* Convert to \in *)
        apply Extra.In_in in Hkin.
        (* Hs gives path Ord.lt k (unzip1 rest) *)
        simpl in Hs.
        have := path.order_path_min (@Ord.lt_trans T0) Hs.
        move=> /allP /(_ _ Hkin).
        by rewrite Ord.ltxx.
      * eapply IH. eauto.
        Unshelve.
        simpl in Hs. eapply path.path_sorted. eauto.
Qed.

Lemma mapk_Some: forall {T T' : ordType} {S : Type}
                   (f : T -> T') (m : {fmap T -> S}) k' v,
  Tmp.mapk f m k' = Some v -> exists k, f k = k' /\ m k = Some v.
Proof.
  intros T0 T0' S0 f m k' v.
  unfold Tmp.mapk.
  intros H. apply foldl_unionm_In in H as [mi [Hmi Hmi_k']].
  (* Hmi : List.In mi (unzip2 (mapim (fun k x => mkfmap [:: (f k, x)]) m)) *)
  (* Hmi_k' : mi k' = Some v *)
  set mm := mapim (fun k x => mkfmap [:: (f k, x)]) m in Hmi.
  destruct (In_unzip2_exists Hmi) as [k0 Hpair].
  apply In_fmap_getm in Hpair.
  (* move/getmP : Hpair => Hpair. *)
  (* Hpair : mm k0 = Some mi *)
  rewrite /mm mapimE in Hpair.
  destruct (m k0) as [x0 |] eqn:Hmk0; simpl in Hpair; [| discriminate].
  injection Hpair => Hmi_eq.
  (* mi = mkfmap [:: (f k0, x0)] *)
  rewrite -Hmi_eq /= in Hmi_k'.
  rewrite setmE in Hmi_k'.
  (* rewrite -Hmi_eq mkfmapE /= in Hmi_k'. *)
  (* Hmi_k' : (if k' == f k0 then Some x0 else None) = Some v *)
  case: ifP Hmi_k' => [/eqP Hfk | //].
  move=> [<-].
  exists k0. split.
  - symmetry. exact Hfk.
  - exact Hmk0.
Qed.

(* Converse: if m k = Some v and f is injective ON THE KEYS OF m, then mapk f m (f k) = Some v.
   [injective f] (globally) was too strong — the actual key relabel word_of_nat(·+pc0) is NOT
   globally injective (it wraps); it is injective only on the positions [< size], which is what
   [encode_code_nth] supplies. *)
(* converse of In_fmap_getm *)
Lemma getm_In: forall {T : ordType} {S : Type} (m : {fmap T -> S}) k v,
    m k = Some v -> List.In (k, v) m.
Proof.
  move=> T0 S0 [s Hs] k v. rewrite /getm /=. clear Hs. elim: s => [|[k0 v0] s IH] //=.
  case Hkeq: (k == k0).
  - move/eqP: Hkeq => ->. by move=> [->]; left.
  - by move=> H; right; apply: IH.
Qed.

(* a key in some member of the list is in the domain of the folded union *)
Lemma domm_foldl_unionm_In: forall {T : ordType} {S : Type} (ms : seq {fmap T -> S}) mi j,
    List.In mi ms -> j \in domm mi -> j \in domm (foldl unionm emptym ms).
Proof.
  intros T0 S0 ms. induction ms as [| ms0 m0 IH] using last_ind.
  - intros mi j Hin. contradiction.
  - intros mi j Hin Hj. rewrite foldl_rcons domm_union in_fsetU.
    move: Hin; rewrite -cats1 => Hin.
    apply List.in_app_or in Hin. case: Hin => [Hin | Hin].
    + apply/orP; left. exact: (IH mi j Hin Hj).
    + apply/orP; right. move: Hin => /= [Heq | F]; [subst mi; exact Hj | exact (False_ind _ F)].
Qed.

Lemma mapk_Some_inv: forall {T T' : ordType} {S : Type} (f : T -> T') (m : {fmap T -> S}) k v,
  {in domm m &, injective f} -> m k = Some v -> Tmp.mapk f m (f k) = Some v.
Proof.
  move=> T0 T0' S0 f m k v Hinj Hmk.
  have Hkdom : k \in domm m by apply/dommP; exists v.
  have Hfkdom : f k \in domm (Tmp.mapk f m).
  { rewrite /Tmp.mapk.
    apply: (domm_foldl_unionm_In (mi := mkfmap [:: (f k, v)])).
    - have Hmm : (mapim (fun k0 x => mkfmap [:: (f k0, x)]) m) k = Some (mkfmap [:: (f k, v)]).
      { by rewrite mapimE Hmk. }
      have Hpair := getm_In Hmm.
      exact: (List.in_map snd _ _ Hpair).
    - by rewrite (domm_mkfmap [:: (f k, v)]) in_cons eqxx. }
  move/dommP: Hfkdom => [v' Hv']. rewrite Hv'.
  destruct (mapk_Some Hv') as [k0 [Hfk0 Hmk0]].
  have Hk0dom : k0 \in domm m by apply/dommP; exists v'.
  have Hk0k : k0 = k by apply: Hinj; [exact Hk0dom | exact Hkdom | exact Hfk0].
  subst k0. rewrite Hmk0 in Hmk. by case: Hmk => ->.
Qed.


(* getm through a BIJECTIVE key relabel. *)
Lemma mapk_bijE {T T' : ordType} {S : Type} (f : T -> T') (g : T' -> T)
    (m : {fmap T -> S}) (k' : T') :
  cancel f g -> cancel g f -> Tmp.mapk f m k' = m (g k').
Proof.
move=> fgK gfK.
have Hinj : {in domm m &, injective f}.
{ move=> x y _ _ E. by rewrite -(fgK x) E fgK. }
case E: (m (g k')) => [v|].
- rewrite <- (gfK k'). exact: (mapk_Some_inv Hinj E).
- case E': (Tmp.mapk f m k') => [v|] //.
  have [k [Hfk Hmk]] := mapk_Some E'.
  move: E. rewrite -Hfk fgK Hmk. by [].
Qed.

End MapkToolkit.

(* ===== The (c,b,o) key space of [linearize_bufs] ===== *)

Definition tunflat (x : nat * nat * nat) : nat * (nat * nat) :=
  match x with (a, b, c) => (a, (b, c)) end.
Definition tflat (x : nat * (nat * nat)) : nat * nat * nat :=
  match x with (a, (b, c)) => (a, b, c) end.

Lemma tflatK : cancel tflat tunflat.
Proof. by move=> [a [b c]]. Qed.
Lemma tunflatK : cancel tunflat tflat.
Proof. by move=> [[a b] c]. Qed.

(* Pointwise lookup of [linearize_bufs]. *)
Lemma linearize_bufsE pb c b o :
  linearize_bufs pb (c, b, o)
  = match pb c with
    | Some map => match map b with
                  | Some _ => nth None [seq Some x | x <- linearize_buf pb c b] o
                  | None => None
                  end
    | None => None
    end.
Proof.
rewrite /linearize_bufs (mapk_bijE _ _ tflatK tunflatK) /=.
rewrite uncurrymE /= mapmE mapimE.
case Epc: (pb c) => [map|] //=.
rewrite uncurrymE /= mapimE.
case Emb: (map b) => [blk|] //=.
by rewrite fmap_of_seqE.
Qed.

(* Key membership <-> in-range offset of a declared block. *)
Lemma linearize_bufs_key (pb : NMap {fmap Values.Block.id -> nat + seq Values.value}) (c b o : nat) :
  reflect (exists (map : {fmap Values.Block.id -> nat + seq Values.value})
                  (blk : nat + seq Values.value),
              [/\ pb c = Some map, map b = Some blk
                & o < size (linearize_buf pb c b)])
          ((c, b, o) \in domm (linearize_bufs pb)).
Proof.
apply/(iffP dommP).
- move=> [v Hv]. move: Hv; rewrite linearize_bufsE.
  case Epc: (pb c) => [map|] //; case Emb: (map b) => [blk|] // Hnth.
  exists map, blk; split=> //.
  case Hlt: (o < size (linearize_buf pb c b)) => //.
  move: Hnth. rewrite nth_default; first by [].
  rewrite size_map. by lia.
- move=> [map [blk [Hpc Hmb Hlt]]].
  have Hnth : nth None [seq Some x | x <- linearize_buf pb c b] o
              = Some (nth (Undef, def_mem_tag c false) (linearize_buf pb c b) o).
  { rewrite (nth_map (Undef, def_mem_tag c false)) //. }
  exists (nth (Undef, def_mem_tag c false) (linearize_buf pb c b) o).
  by rewrite linearize_bufsE Hpc Hmb Hnth.
Qed.

(* ===== The contiguous address layout ===== *)

(* [size (domm m) = size m] (lifted from RecompositionInit; will be deduped there). *)
Lemma size_domm_fmap (T : ordType) (S : Type) (m : {fmap T -> S}) :
  size (domm m) = size m.
Proof. by rewrite val_domm size_map. Qed.

(* [encode_int] is faithful on nats (lifted from RecompositionInit). *)
Lemma nat_of_pos_succ : forall m, ssrnat.nat_of_pos (Pos.of_succ_nat m) = m.+1.
Proof. elim=> [//|m IH] /=. by rewrite nat_of_succ_pos IH. Qed.

Lemma encode_int_of_nat : forall n, encode_int (Z.of_nat n) = ssrint.Posz n.
Proof.
case=> [//|n] /=. by rewrite nat_of_pos_succ.
Qed.

Section Layout.

Variable pb : NMap {fmap Values.Block.id -> nat + seq Values.value}.

Local Notation bufs := (linearize_bufs pb).
Local Notation total := (size (linearize_bufs pb)).

(* The block-order predicates used by [Merged.initial_memory]'s base address. *)
Definition blk_before (c b : nat) : pred (nat * nat * nat) :=
  fun x => match x with (c', b', _) => (c' < c) || ((c' == c) && (b' < b)) end.
Definition blk_at (c b : nat) : pred (nat * nat * nat) :=
  fun x => match x with (c', b', _) => (c' == c) && (b' == b) end.

Definition bl_base (c b : nat) : nat := count (blk_before c b) (domm bufs).

Definition nat_addr (k : nat * nat * nat) : nat :=
  match k with (c, b, o) => o + bl_base c b end.

(* Bridge to [initial_memory]'s [filterm]-based base address. *)
Lemma base_filterm c b :
  size (domm (filterm (fun x (_ : Values.value * mem_tag) => blk_before c b x) bufs))
  = bl_base c b.
Proof.
rewrite (@domm_filter_eq _ _ (blk_before c b) bufs) /bl_base.
by rewrite /= val_fset_filter size_filter.
Qed.

(* [blk_before] and [blk_at] are disjoint, and both are below any later block. *)
Lemma blk_before_at_disjoint c b k : blk_before c b k -> blk_at c b k -> False.
Proof. case: k => [[c' b'] o'] /= H1 /andP[/eqP ? /eqP ?]; subst. by lia. Qed.

(* The keys of block (c,b) are exactly (c,b,o) for o < the block length. *)
Lemma blk_at_key c b k :
  k \in domm bufs -> blk_at c b k ->
  exists o, k = (c, b, o) /\ o < size (linearize_buf pb c b).
Proof.
case: k => [[c' b'] o'] Hk /= /andP[/eqP ? /eqP ?]; subst c' b'.
exists o'; split=> //.
by case/linearize_bufs_key: Hk => map [blk [_ _ Hlt]].
Qed.

(* Counting the block (c,b): exactly its length, when declared. *)
Lemma blk_at_count c b map blk :
  pb c = Some map -> map b = Some blk ->
  count (blk_at c b) (domm bufs) = size (linearize_buf pb c b).
Proof.
move=> Hpc Hmb.
rewrite -size_filter.
have Hperm : perm_eq [seq k <- domm bufs | blk_at c b k]
                     [seq (c, b, o) | o <- iota 0 (size (linearize_buf pb c b))].
{ apply: uniq_perm.
  - apply: filter_uniq. exact: uniq_fset.
  - rewrite map_inj_uniq ?iota_uniq //. by move=> x y [].
  - move=> k. rewrite mem_filter.
    apply/andP/mapP.
    + move=> [Hat Hk]. have [o [-> Hlt]] := blk_at_key Hk Hat.
      exists o => //. by rewrite mem_iota /= add0n.
    + move=> [o]. rewrite mem_iota /= add0n => Hlt ->.
      split; first by rewrite /= !eqxx.
      apply/linearize_bufs_key. by exists map, blk. }
by rewrite (perm_size Hperm) size_map size_iota.
Qed.

(* Monotonicity: a whole earlier block fits below a later block's base. *)
Lemma base_block_leq c1 b1 c2 b2 map blk :
  pb c1 = Some map -> map b1 = Some blk ->
  blk_before c2 b2 (c1, b1, 0) ->
  bl_base c1 b1 + size (linearize_buf pb c1 b1) <= bl_base c2 b2.
Proof.
move=> Hpc Hmb Hbefore.
rewrite -(blk_at_count Hpc Hmb) /bl_base.
have HI : count (predI (blk_before c1 b1) (blk_at c1 b1)) (domm bufs) = 0.
{ rewrite (@eq_count _ _ pred0) ?count_pred0 //.
  move=> k /=. apply/negbTE/negP => /andP[H1 H2].
  exact: (blk_before_at_disjoint H1 H2). }
have HU := count_predUI (blk_before c1 b1) (blk_at c1 b1) (domm bufs).
rewrite HI addn0 in HU. rewrite -HU.
apply: sub_count => k /=.
case: k => [[c' b'] o'] /orP[H1|/andP[/eqP ? /eqP ?]]; subst => /=.
- move: H1 Hbefore => /=. by lia.
- move: Hbefore => /=. by lia.
Qed.

(* A whole block fits below the total. *)
Lemma base_len_leq_total c b map blk :
  pb c = Some map -> map b = Some blk ->
  bl_base c b + size (linearize_buf pb c b) <= total.
Proof.
move=> Hpc Hmb.
rewrite -(blk_at_count Hpc Hmb) /bl_base.
have HI : count (predI (blk_before c b) (blk_at c b)) (domm bufs) = 0.
{ rewrite (@eq_count _ _ pred0) ?count_pred0 //.
  move=> k /=. apply/negbTE/negP => /andP[H1 H2].
  exact: (blk_before_at_disjoint H1 H2). }
have HU := count_predUI (blk_before c b) (blk_at c b) (domm bufs).
rewrite HI addn0 in HU. rewrite -HU.
apply: (leq_trans (count_size _ _)).
by rewrite size_domm_fmap.
Qed.

(* (A) Every key's address is below the total. *)
Lemma nat_addr_lt k : k \in domm bufs -> nat_addr k < total.
Proof.
case: k => [[c b] o] Hk.
have/linearize_bufs_key [map [blk [Hpc Hmb Hlt]]] := Hk.
rewrite /nat_addr.
have Hle := base_len_leq_total Hpc Hmb.
by lia.
Qed.

(* (B) The address map is injective on the key set. *)
Lemma nat_addr_inj k1 k2 :
  k1 \in domm bufs -> k2 \in domm bufs -> nat_addr k1 = nat_addr k2 -> k1 = k2.
Proof.
case: k1 => [[c1 b1] o1]; case: k2 => [[c2 b2] o2] Hk1 Hk2 Heq.
have/linearize_bufs_key [map1 [blk1 [Hpc1 Hmb1 Hlt1]]] := Hk1.
have/linearize_bufs_key [map2 [blk2 [Hpc2 Hmb2 Hlt2]]] := Hk2.
case Hcb : ((c1 == c2) && (b1 == b2)).
- case/andP: Hcb => /eqP ? /eqP ?; subst c2 b2.
  move: Heq; rewrite /nat_addr => Heq.
  by have -> : o1 = o2 by lia.
- exfalso.
  have Htri : blk_before c2 b2 (c1, b1, 0) \/ blk_before c1 b1 (c2, b2, 0).
  { move: Hcb => /andP Hcb. rewrite /blk_before. by lia. }
  case: Htri => Hbef.
  + have Hle := base_block_leq Hpc1 Hmb1 Hbef.
    move: Heq; rewrite /nat_addr. by lia.
  + have Hle := base_block_leq Hpc2 Hmb2 Hbef.
    move: Heq; rewrite /nat_addr. by lia.
Qed.

(* (C) Every address below the total is hit. *)
Lemma nat_addr_onto n :
  n < total -> exists2 k, k \in domm bufs & nat_addr k = n.
Proof.
move=> Hn.
set im := [seq nat_addr k | k <- domm bufs].
have Huniq : uniq im.
{ rewrite map_inj_in_uniq ?uniq_fset //.
  move=> x y Hx Hy. exact: nat_addr_inj. }
have Hsub : {subset im <= iota 0 total}.
{ move=> x /mapP[k Hk ->]. rewrite mem_iota /= add0n.
  apply: nat_addr_lt. exact: Hk. }
have Hsize : size (iota 0 total) <= size im.
{ by rewrite size_iota size_map size_domm_fmap. }
have [_ Hmem] := uniq_min_size Huniq Hsub Hsize.
have : n \in im by rewrite Hmem mem_iota /= add0n.
move=> /mapP[k Hk Hnk]. by exists k.
Qed.

End Layout.

(* ===== Transport to [initial_memory] ===== *)

(* [Tmp.mapk] only looks at [f] pointwise. *)
Lemma eq_mapk {T T' : ordType} {S : Type} (f g : T -> T') (m : {fmap T -> S}) :
  f =1 g -> Tmp.mapk f m = Tmp.mapk g m.
Proof.
move=> Efg. rewrite /Tmp.mapk.
suff -> : mapim (fun k x => mkfmap [:: (f k, x)]) m
        = mapim (fun k x => mkfmap [:: (g k, x)]) m by [].
apply/eq_fmap => k. rewrite !mapimE. case: (m k) => //= v.
by rewrite Efg.
Qed.

(* word_of_nat is injective below 2^k. *)
Lemma won_inj (k : nat) (a b : nat) :
  a < 2 ^ k -> b < 2 ^ k ->
  @word_of_nat k a = word_of_nat b -> a = b.
Proof.
move=> Ha Hb H.
have H' := congr1 (fun w : word k => nat_of_ord (val w)) H.
by move: H'; rewrite /word_of_nat !valw_as_word !modn_small.
Qed.

Lemma size_length (T : Type) (l : seq T) : length l = size l.
Proof. by elim: l => [//|x l /= ->]. Qed.

Section InitMem.

Variable pb : NMap {fmap Values.Block.id -> nat + seq Values.value}.

Local Notation bufs := (linearize_bufs pb).
Local Notation total := (size (linearize_bufs pb)).

(* [initial_memory] IS a [mapk] with our canonical address as the key map. *)
Lemma initial_memory_as_mapk :
  {enc : Values.value * mem_tag -> Types.atom (mword mt) mem_tag |
    initial_memory pb
    = Tmp.mapk (fun k => @word_of_nat (word_size mt) (nat_addr pb k)) (mapm enc bufs)}.
Proof.
rewrite /initial_memory; cbv zeta.
eexists.
apply: eq_mapk => -[[c b] o] /=.
rewrite encode_int_of_nat /=.
congr as_word. congr ssrint.Posz. congr addn.
rewrite size_length. exact: (base_filterm pb c b).
Qed.

Hypothesis Hbound : total < 2 ^ (word_size mt).

(* The key map is injective on the buffer keys. *)
Let won_addr_inj :
  {in domm bufs &, injective (fun k => @word_of_nat (word_size mt) (nat_addr pb k))}.
Proof.
move=> k1 k2 Hk1 Hk2 E.
have Hb1 : nat_addr pb k1 < 2 ^ (word_size mt)
  by exact: (leq_trans (nat_addr_lt Hk1) (ltnW Hbound)).
have Hb2 : nat_addr pb k2 < 2 ^ (word_size mt)
  by exact: (leq_trans (nat_addr_lt Hk2) (ltnW Hbound)).
exact: (nat_addr_inj Hk1 Hk2 (won_inj Hb1 Hb2 E)).
Qed.

(* Key membership of the data segment. *)
Lemma initial_memory_key w :
  (w \in domm (initial_memory pb))
  <-> (exists2 k, k \in domm bufs & w = @word_of_nat (word_size mt) (nat_addr pb k)).
Proof.
have [enc ->] := initial_memory_as_mapk.
split.
- move=> /dommP [v Hv].
  have [k [Hfk Hmk]] := mapk_Some Hv.
  exists k; last by rewrite Hfk.
  by rewrite -(domm_map enc bufs); apply/dommP; exists v.
- move=> [k Hk ->].
  have Hk' : k \in domm (mapm enc bufs) by rewrite domm_map.
  case/dommP: Hk' => v Hv.
  have Hinj : {in domm (mapm enc bufs) &,
               injective (fun k0 => @word_of_nat (word_size mt) (nat_addr pb k0))}.
  { move=> x y; rewrite !domm_map => Hx Hy. exact: won_addr_inj. }
  apply/dommP. exists v.
  exact: (mapk_Some_inv Hinj Hv).
Qed.

(* The three headline facts. *)
Lemma initial_memory_domm_iota :
  domm (initial_memory pb)
  = fset [seq @word_of_nat (word_size mt) n | n <- iota 0 total].
Proof.
apply/eq_fset => w. rewrite in_fset.
apply/idP/idP.
- move=> Hw. have [k Hk ->] := proj1 (initial_memory_key w) Hw.
  apply/mapP. exists (nat_addr pb k) => //.
  rewrite mem_iota /= add0n. exact: nat_addr_lt.
- move=> /mapP [n]. rewrite mem_iota /= add0n => Hn ->.
  apply/(proj2 (initial_memory_key _)).
  have [k Hk Hnk] := nat_addr_onto Hn.
  exists k; first exact: Hk.
  by rewrite Hnk.
Qed.

Lemma initial_memory_size_eq : size (initial_memory (mt := mt) pb) = total.
Proof.
rewrite -size_domm_fmap initial_memory_domm_iota.
have Hinj : {in iota 0 total &, injective (@word_of_nat (word_size mt))}.
{ move=> x y; rewrite !mem_iota /= !add0n => Hx Hy H.
  have Hx' : x < 2 ^ (word_size mt) by exact: (ltn_trans Hx Hbound).
  have Hy' : y < 2 ^ (word_size mt) by exact: (ltn_trans Hy Hbound).
  exact: (won_inj Hx' Hy' H). }
have Huniq : uniq [seq @word_of_nat (word_size mt) n | n <- iota 0 total].
{ rewrite (map_inj_in_uniq Hinj). exact: iota_uniq. }
have Hperm : perm_eq (fset [seq @word_of_nat (word_size mt) n | n <- iota 0 total])
                     [seq @word_of_nat (word_size mt) n | n <- iota 0 total].
{ apply: uniq_perm => //; first exact: uniq_fset.
  move=> x. by rewrite in_fset. }
by rewrite (perm_size Hperm) size_map size_iota.
Qed.

Lemma alloc_label_not_in_initial_memory_bl :
  total < alloc_label ->
  initial_memory pb (@word_of_nat (word_size mt) alloc_label) = None.
Proof.
move=> Htot.
have Hal : alloc_label < 2 ^ (word_size mt)
  by rewrite /alloc_label ltn_exp2l.
case E: (initial_memory pb (word_of_nat alloc_label)) => [v|] //.
exfalso.
have Hin : @word_of_nat (word_size mt) alloc_label \in domm (initial_memory pb)
  by apply/dommP; exists v.
case/initial_memory_key: Hin => k Hk Hw.
have Hlt := nat_addr_lt Hk.
have Hb2 : nat_addr pb k < 2 ^ (word_size mt)
  by apply: (leq_trans Hlt (ltnW Hbound)).
have Heq := won_inj Hal Hb2 Hw.
by lia.
Qed.

End InitMem.

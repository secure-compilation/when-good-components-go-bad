(** * The keystone [memory_lengths_bl_base]: on declared blocks the
    compile-time base map [Merged.memory_lengths] (baked into pointer
    immediates) equals the run-time data-segment base [bl_base].  Proved
    by splitting the sorted association lists at (c, b): a fold half and
    a count half. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.LinearizeMerged.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ================================================================== *)
(* 0. Generic helpers.                                                *)
(* ================================================================== *)

(* extructures' generic strict order, on nat, is ssrnat's *)
Lemma Ord_lt_nat (x y : nat) : Ord.lt x y = (x < y).
Proof. by rewrite /Ord.lt /= ltn_neqAle andbC eq_sym. Qed.

(* everything on a strictly ascending path is above its head *)
Lemma path_all_gt (T : Type) (c : nat) (l : seq (nat * T)) :
  path Ord.lt c (unzip1 l) -> all (fun t => c < t.1) l.
Proof.
elim: l c => [|a l IH] c //= /andP [Hlt Hp].
apply/andP; split.
- by rewrite -Ord_lt_nat.
- have Hall := IH _ Hp.
  apply: sub_all Hall => t /= Ht.
  move: Hlt. rewrite Ord_lt_nat => Hlt. by lia.
Qed.

(* keys strictly below [c] never contain [c] *)
Lemma all_map_fst_notin (T : Type) (l : seq (nat * T)) (c : nat) :
  all (fun t => t.1 < c) l -> c \notin [seq t.1 | t <- l].
Proof.
elim: l => [|a l IH] //= /andP [Hlt Hall].
rewrite in_cons negb_or IH // andbT.
apply/negP => /eqP Ec. by move: Hlt; rewrite Ec ltnn.
Qed.

(* split a sorted association list at a present key: everything before is
   strictly smaller, everything after strictly larger *)
Lemma sorted_assoc_split (T : Type) (l : seq (nat * T)) (c : nat) (v : T) :
  sorted Ord.lt (unzip1 l) ->
  List.In (c, v) l ->
  exists l1 l2,
    [/\ l = l1 ++ (c, v) :: l2,
        all (fun t => t.1 < c) l1
      & all (fun t => c < t.1) l2].
Proof.
elim: l => [|a l IH] //= Hsort HIn.
have Hpath : path Ord.lt a.1 (unzip1 l) by [].
case: HIn => [Ea | HIn].
-  exists [::], l. split=> //=.
  + by rewrite Ea.
  + apply: path_all_gt. by move: Hpath; rewrite Ea.
- have Hsort' : sorted Ord.lt (unzip1 l) by apply: (path_sorted Hpath).
  have [l1 [l2 [El Hall1 Hall2]]] := IH Hsort' HIn.
  exists (a :: l1), l2. split=> //=.
  + by rewrite El.
  + rewrite Hall1 andbT.    have Hall := path_all_gt Hpath.
    rewrite El all_cat /= in Hall.
    by case/andP: Hall => _ /= /andP [Hac _].
Qed.

(* keys of an [elementsm] are sorted *)
Lemma elementsm_sorted (T : Type) (m : NMap T) :
  sorted Ord.lt (unzip1 (Maps.elementsm m)).
Proof. by case: m. Qed.

(* [sumn] with associated re-bracketing, used to thread accumulators *)
Lemma sumn_cat_acc (s1 : seq nat) (n acc : nat) :
  sumn s1 + (n + acc) = (sumn s1 + n) + acc.
Proof. by lia. Qed.

(* ================================================================== *)
(* 1. The fold half.                                                  *)
(* ================================================================== *)

Section FoldHalf.

(* the inner fold body of [memory_lengths] *)
Local Notation FB :=
  (fun (acc' : nat) (a : Datatypes_nat__canonical__Ord_Ord * (nat + seq value)) =>
     match a.2 with
     | inl n => ((a.1, acc'), n + acc')
     | inr s => ((a.1, acc'), size s + acc')
     end).

Lemma FB_snd acc (a : nat * (nat + seq value)) :
  (FB acc a).2 = bsize a.2 + acc.
Proof. by case: a => x [n|s]. Qed.

Lemma FB_fst acc (a : nat * (nat + seq value)) :
  (FB acc a).1 = (a.1, acc).
Proof. by case: a => x [n|s]. Qed.

(* the running total of the inner fold *)
Lemma flmb_snd acc (bl : seq (nat * (nat + seq value))) :
  (fold_left_map_bis FB acc bl).2
  = sumn [seq bsize a.2 | a <- bl] + acc.
Proof.
elim: bl acc => [|a bl IH] acc //=.
case E: (FB acc a) => [va aa] /=.
case E2: (fold_left_map_bis FB aa bl) => [res r] /=.
have -> : r = (fold_left_map_bis FB aa bl).2 by rewrite E2.
rewrite IH.
have -> : aa = bsize a.2 + acc by rewrite -(FB_snd acc a) E.
by lia.
Qed.

(* looking up the first occurrence of [b] in the inner fold's output:
   the assigned base is the accumulated size of the earlier blocks *)
Lemma flmb_get acc (l1 l2 : seq (nat * (nat + seq value))) b bf :
  b \notin [seq a.1 | a <- l1] ->
  getm_def (fold_left_map_bis FB acc (l1 ++ (b, bf) :: l2)).1 b
  = Some (sumn [seq bsize a.2 | a <- l1] + acc).
Proof.
elim: l1 acc => [|a l1 IH] acc /=.
-  move=> _.
  case E: (FB acc (b, bf)) => [vb ab] /=.
  case E2: (fold_left_map_bis FB ab l2) => [res r] /=.
  have -> : vb = (b, acc) by rewrite -(FB_fst acc (b, bf)) E.
  by rewrite /= eqxx.
- rewrite in_cons negb_or => /andP [Hne Hnin].
  case E: (FB acc a) => [va aa] /=.
  case E2: (fold_left_map_bis FB aa (l1 ++ (b, bf) :: l2)) => [res r] /=.
  have Eva : va = (a.1, acc) by rewrite -(FB_fst acc a) E.
  have Eaa : aa = bsize a.2 + acc by rewrite -(FB_snd acc a) E.
  have -> : res = (fold_left_map_bis FB aa (l1 ++ (b, bf) :: l2)).1
    by rewrite E2.
  rewrite Eva /= (negbTE Hne).
  rewrite (IH aa Hnin) Eaa.
  congr Some. by lia.
Qed.

(* the outer fold body of [memory_lengths] *)
Local Notation FOUT :=
  (fun (acc : nat)
       (s : Datatypes_nat__canonical__Ord_Ord
            * seq (Datatypes_nat__canonical__Ord_Ord * (nat + seq value))) =>
     let (flat, count) := fold_left_map_bis FB acc s.2 in
     ((s.1, mkfmap flat), count)).

(* size contributed by one component entry *)
Definition osum (s : nat * seq (nat * (nat + seq value))) : nat :=
  sumn [seq bsize a.2 | a <- s.2].

Lemma flm_get acc
    (L1 L2 : seq (nat * seq (nat * (nat + seq value))))
    (c : nat) (bl : seq (nat * (nat + seq value))) :
  c \notin [seq s.1 | s <- L1] ->
  getm_def (fold_left_map FOUT acc (L1 ++ (c, bl) :: L2)) c
  = Some (mkfmap (fold_left_map_bis FB
                    (sumn [seq osum s | s <- L1] + acc) bl).1).
Proof.
elim: L1 acc => [|s L1 IH] acc /=.
- move=> _.
  case E: (fold_left_map_bis FB acc bl) => [flat count] /=.
  by rewrite eqxx.
- rewrite in_cons negb_or => /andP [Hne Hnin].
  case E: (fold_left_map_bis FB acc s.2) => [flat count] /=.
  rewrite (negbTE Hne).
  have Ecount : count = osum s + acc.
  { by rewrite /osum -(flmb_snd acc s.2) E. }
  rewrite (IH count Hnin) Ecount.
  congr (Some (mkfmap (fold_left_map_bis FB _ bl).1)).
  by lia.
Qed.

End FoldHalf.

(* ================================================================== *)
(* 2. The count half.                                                 *)
(* ================================================================== *)

Section CountHalf.

Variable pb : NMap {fmap Block.id -> nat + seq value}.

Lemma size_linearize_buf c b bmap bf :
  pb c = Some bmap -> bmap b = Some bf ->
  size (linearize_buf pb c b) = bsize bf.
Proof.
move=> Hc Hb.
rewrite /linearize_buf Hc /= Hb /=.
case: bf {Hb} => [n|l] //=.
- by elim: n => //= n ->.
- by rewrite size_map.
Qed.

(* the linearized keys of a list of (component, block) pairs *)
Definition keyset (ts : seq (nat * nat)) : seq (nat * nat * nat) :=
  flatten [seq [seq (t.1, t.2, o)
               | o <- iota 0 (size (linearize_buf pb t.1 t.2))]
          | t <- ts].

Lemma keyset_mem (ts : seq (nat * nat)) x y o :
  ((x, y, o) \in keyset ts)
  = ((x, y) \in ts) && (o < size (linearize_buf pb x y)).
Proof.
elim: ts => [|t ts IH] //=.
rewrite mem_cat IH in_cons.
have -> : ((x, y, o) \in [seq (t.1, t.2, o') | o' <- iota 0 (size (linearize_buf pb t.1 t.2))])
          = ((x, y) == t) && (o < size (linearize_buf pb t.1 t.2)).
{ apply/mapP/andP.
  - move=> [o'] Ho' [= -> -> ->].
    split; first by rewrite -surjective_pairing eqxx.
    by move: Ho'; rewrite mem_iota /= add0n.
  - move=> [/eqP Et Ho].
    case: t Et Ho {IH} => tx ty /= [= -> ->] Ho.
    exists o => //. by rewrite mem_iota /= add0n. }
case E: ((x, y) == t) => /=.
- move/eqP: E => E. rewrite -E /=.
  set P := (o < _).
  by case: P => //=; rewrite andbF.
- by [].
Qed.

Lemma keyset_uniq (ts : seq (nat * nat)) : uniq ts -> uniq (keyset ts).
Proof.
elim: ts => [|t ts IH] //= /andP [Hnin Hu].
rewrite cat_uniq IH // andbT.
apply/andP; split.
- rewrite map_inj_uniq ?iota_uniq //.
  by move=> o1 o2 [=].
- apply/hasPn => k Hk.
  apply/negP => /mapP [o' Ho' Ek].
  move: Hk. rewrite Ek keyset_mem -surjective_pairing.
  move=> /andP [Hin _].
  by rewrite Hin in Hnin.
Qed.

Lemma size_keyset (ts : seq (nat * nat)) :
  size (keyset ts) = sumn [seq size (linearize_buf pb t.1 t.2) | t <- ts].
Proof.
elim: ts => [|t ts IH] //=.
by rewrite size_cat IH size_map size_iota.
Qed.

(* THE count half: if [ts] lists exactly the declared pairs lexicographically
   before (c, b), without repetition, then [bl_base] sums their sizes. *)
Lemma bl_base_count (c b : nat) (ts : seq (nat * nat)) :
  uniq ts ->
  (forall x y,
      ((x, y) \in ts)
      <-> [/\ exists bmap bf, pb x = Some bmap /\ bmap y = Some bf
            & (x < c) || ((x == c) && (y < b))]) ->
  bl_base pb c b
  = sumn [seq size (linearize_buf pb t.1 t.2) | t <- ts].
Proof.
move=> Hu Hchar.
rewrite /bl_base -size_filter -size_keyset.
apply: perm_size.
apply: uniq_perm.
- apply: filter_uniq. exact: uniq_fset.
- exact: keyset_uniq.
- move=> k. case: k => [[x y] o].
  rewrite mem_filter keyset_mem.
  apply/andP/andP.
  + move=> [Hbef Hdom].
    have /linearize_bufs_key [bmap [bf [Hx Hy Hlt]]] := Hdom.
    split=> //.
    apply/Hchar. split; first by exists bmap, bf.
    by move: Hbef => /=.
  + move=> [Hin Hlt].
    have [[bmap [bf [Hx Hy]]] Hbef] := proj1 (Hchar x y) Hin.
    split; first by move: Hbef => /=.
    apply/linearize_bufs_key. by exists bmap, bf.
Qed.

End CountHalf.

(* ================================================================== *)
(* 3. Assembly: THE KEYSTONE.                                         *)
(* ================================================================== *)

Section Keystone.

Variable pb : NMap {fmap Block.id -> nat + seq value}.

(* [all] specialized to List membership (the S-carrying lists here have no
   eqType — [value] has none — so the boolean \in is unavailable on them) *)
Local Lemma all_In (T : Type) (p : T -> bool) (l : seq T) x :
  all p l -> List.In x l -> p x.
Proof.
elim: l => [|a l IH] //= /andP [Hp Hall] [<- | HIn] //.
exact: (IH Hall HIn).
Qed.

(* boolean membership in the (nat-typed) first projection, List-style *)
Local Lemma unzip1_mem_In (S : Type) (l : seq (nat * S)) y :
  reflect (exists a, List.In a l /\ y = a.1) (y \in [seq a.1 | a <- l]).
Proof.
elim: l => [|a l IH] /=.
- rewrite in_nil. constructor. by move=> [? [[] _]].
- rewrite in_cons.
  apply: (iffP orP).
  + move=> [/eqP Ey | Hy].
    * exists a. split=> //. by left.
    * have [a' [Ha' Ey]] := elimT IH Hy.
      exists a'. split=> //. by right.
  + move=> [a' [[Ea | HIn] Ey]].
    * left. by rewrite Ey Ea.
    * right. apply: (introT IH). by exists a'.
Qed.

(* membership in the two-level pair flattening *)
Lemma pairs_flatten_mem (S : Type)
    (L : seq (nat * seq (nat * S)))
    (x y : nat) :
  reflect (exists s a, [/\ List.In s L, List.In a s.2, x = s.1 & y = a.1])
          ((x, y) \in flatten [seq [seq (s.1, a.1) | a <- s.2] | s <- L]).
Proof.
elim: L => [|s L IH] /=.
- rewrite in_nil. constructor. by move=> [? [? [[] ? ?]]].
- rewrite mem_cat.
  have Ehd : [seq (s.1, a.1) | a <- s.2] = [seq (s.1, y0) | y0 <- [seq a.1 | a <- s.2]].
  { by elim: (s.2) => //= a t ->. }
  apply: (iffP orP).
  + move=> [Hhd | Htl].
    * move: Hhd. rewrite Ehd => /mapP [y0 Hy0 [= -> ->]].
      have [a' [Ha' Ey]] := elimT (unzip1_mem_In _ _) Hy0.
      exists s, a'. split=> //. by left.
    * have [s' [a' [Hs' Ha' -> ->]]] := elimT IH Htl.
      exists s', a'. split=> //. by right.
  + move=> [s' [a' [[Es | Hs'] Ha' Ex Ey]]].
    * left. rewrite Ehd. apply/mapP.
      exists a'.1.
      -- apply: (introT (unzip1_mem_In _ _)).
         exists a'. split=> //. by rewrite Es.
      -- by rewrite Ex Ey -Es.
    * right. apply: (introT IH). exists s', a'. by split.
Qed.

(* uniqueness of the two-level pair flattening *)
Lemma pairs_flatten_uniq (S : Type)
    (L : seq (nat * seq (nat * S))) :
  uniq [seq s.1 | s <- L] ->
  (forall s, List.In s L -> uniq [seq a.1 | a <- s.2]) ->
  uniq (flatten [seq [seq (s.1, a.1) | a <- s.2] | s <- L]).
Proof.
elim: L => [|s L IH] //= /andP [Hnin Hu] Hinner.
rewrite cat_uniq.
apply/and3P; split.
-  have -> : [seq (s.1, a.1) | a <- s.2] = [seq (s.1, y) | y <- [seq a.1 | a <- s.2]].
  { by elim: (s.2) => //= a t ->. }
  rewrite map_inj_uniq; last by move=> y1 y2 [=].
  apply: Hinner. by left.
- apply/hasPn => k Hk.
  apply/negP => Hk1.
  case: k Hk1 Hk => kx ky Hk1 Hk.
  have Ehd : [seq (s.1, a.1) | a <- s.2] = [seq (s.1, y0) | y0 <- [seq a.1 | a <- s.2]].
  { by elim: (s.2) => //= a t ->. }
  move: Hk1. rewrite Ehd => /mapP [y0 _ [= Ekx _]].
  have [s' [a' [Hs' Ha' Ex _]]] := elimT (pairs_flatten_mem _ _ _) Hk.
  move/negP: Hnin; apply.
  apply: (introT (unzip1_mem_In _ _)).
  exists s'. split=> //.
  by rewrite -Ekx Ex.
- apply: IH => //.
  move=> s0 Hs0. apply: Hinner. by right.
Qed.

(* pointwise-equal maps have equal sums (List-membership form) *)
Local Lemma sumn_map_In_eq (T : Type) (f g : T -> nat) (l : seq T) :
  (forall x, List.In x l -> f x = g x) ->
  sumn [seq f x | x <- l] = sumn [seq g x | x <- l].
Proof.
elim: l => //= a l IH H.
rewrite H; last by left.
rewrite IH //.
move=> x Hx. apply: H. by right.
Qed.

Local Lemma sumn_flattenE (ss : seq (seq nat)) :
  sumn (flatten ss) = sumn [seq sumn s | s <- ss].
Proof.
elim: ss => //= s ss IH. by rewrite sumn_cat IH.
Qed.

(* declared components of the outer list are fmaps with sorted keys *)
Local Lemma olist_inner_sorted
    (s : Datatypes_nat__canonical__Ord_Ord
         * seq (Datatypes_nat__canonical__Ord_Ord * (nat + seq value))) :
  List.In s (Maps.elementsm (mapm Maps.elementsm pb)) ->
  exists bmx, pb s.1 = Some bmx /\ s.2 = Maps.elementsm bmx.
Proof.
case: s => x v /= HIn.
have Hget : mapm Maps.elementsm pb x = Some v.
{ by apply/In_elementsm. }
move: Hget. rewrite mapmE.
case E: (pb x) => [bmx|] //= [<-].
by exists bmx.
Qed.

(* THE KEYSTONE: on declared blocks, the compile-time base map agrees with
   the run-time base of the data segment. *)
Theorem memory_lengths_bl_base c bmap b bf :
  pb c = Some bmap ->
  bmap b = Some bf ->
  exists m,
    memory_lengths pb c = Some m /\ m b = Some (bl_base pb c b).
Proof.
move=> Hc Hb.
set olist := Maps.elementsm (mapm Maps.elementsm pb).
have Hoin : List.In (c, Maps.elementsm bmap) olist.
{ apply/In_elementsm. by rewrite mapmE Hc. }
have Hosort : sorted Ord.lt (unzip1 olist) := elementsm_sorted _.
have [L1 [L2 [Eo Ha1 Ha2]]] := sorted_assoc_split Hosort Hoin.
have Hbin : List.In (b, bf) (Maps.elementsm bmap).
{ by apply/In_elementsm. }
have Hbsort : sorted Ord.lt (unzip1 (Maps.elementsm bmap))
  := elementsm_sorted _.
have [B1 [B2 [Eb Hb1 Hb2]]] := sorted_assoc_split Hbsort Hbin.
have HcL1 : c \notin [seq s.1 | s <- L1] := all_map_fst_notin Ha1.
have HbB1 : b \notin [seq a.1 | a <- B1] := all_map_fst_notin Hb1.
have Hml : memory_lengths pb c
           = getm_def
               (fold_left_map
                  (fun acc s =>
                     let (flat, count) :=
                       fold_left_map_bis
                         (fun acc' (a : Datatypes_nat__canonical__Ord_Ord
                                        * (nat + seq value)) =>
                            match a.2 with
                            | inl n => ((a.1, acc'), n + acc')
                            | inr s0 => ((a.1, acc'), size s0 + acc')
                            end) acc s.2
                     in ((s.1, mkfmap flat), count)) 0 olist) c.
{ by rewrite /memory_lengths mkfmapE. }
rewrite Eo in Hml.
rewrite (flm_get 0 L2 (Maps.elementsm bmap) HcL1) in Hml.
eexists. split; first exact: Hml.
rewrite mkfmapE Eb (flmb_get _ B2 bf HbB1).
congr Some.
set part1 := flatten [seq [seq (s.1, a.1) | a <- s.2] | s <- L1].
set part2 := [seq (c, x.1) | x <- B1].
have Hou : uniq (unzip1 olist).
{ apply: sorted_uniq Hosort; [exact: (@Ord.lt_trans _) | exact: (@Ord.ltxx _)]. }
have HouL1 : uniq (unzip1 L1).
{ move: Hou. rewrite Eo /unzip1 map_cat cat_uniq => /and3P [H _ _].
  exact: H. }
have Hbu : uniq (unzip1 (Maps.elementsm bmap)).
{ apply: sorted_uniq Hbsort; [exact: (@Ord.lt_trans _) | exact: (@Ord.ltxx _)]. }
have HbuB1 : uniq (unzip1 B1).
{ move: Hbu. rewrite Eb /unzip1 map_cat cat_uniq => /and3P [H _ _].
  exact: H. }have HinnerL1 : forall s : nat * seq (nat * (nat + seq value)),
    List.In s L1 ->
    exists bmx, pb s.1 = Some bmx /\ s.2 = Maps.elementsm bmx.
{ move=> s Hs. apply: olist_inner_sorted.
  rewrite -/olist Eo. apply: List.in_or_app. by left. }have Hdecl1 : forall s a, List.In s L1 -> List.In a s.2 ->
    exists bmx, pb s.1 = Some bmx
           /\ (bmx : {fmap Block.id -> nat + seq value}) a.1 = Some a.2.
{ move=> s a Hs Ha.
  have [bmx [Hbx Es2]] := HinnerL1 _ Hs.
  exists bmx. split; first exact: Hbx.
  apply/In_elementsm. rewrite -surjective_pairing.
  by rewrite -Es2. }
have Hdecl2 : forall a, List.In a B1 ->
    (bmap : {fmap Block.id -> nat + seq value}) a.1 = Some a.2.
{ move=> a Ha.
  apply/In_elementsm. rewrite -surjective_pairing Eb.
  apply: List.in_or_app. by left. }have Hcount : bl_base pb c b
    = sumn [seq size (linearize_buf pb t.1 t.2) | t <- part1 ++ part2].
{ have Epart2 : part2 = [seq (c, y0) | y0 <- [seq a.1 | a <- B1]].
  { by rewrite /part2; elim: (B1) => //= a t ->. }
  apply: bl_base_count.
  -    rewrite cat_uniq. apply/and3P; split.
    + apply: pairs_flatten_uniq; first exact: HouL1.
      move=> s Hs.
      have [bmx [_ ->]] := HinnerL1 _ Hs.
      apply: sorted_uniq (elementsm_sorted _);
        [exact: (@Ord.lt_trans _) | exact: (@Ord.ltxx _)].
    + apply/hasPn => k Hk2.
      apply/negP => Hk1.
      case: k Hk1 Hk2 => kx ky Hk1 Hk2.
      move: Hk2. rewrite Epart2 => /mapP [y0 _ [= Ekx _]].
      have [s' [a' [Hs' _ Ex _]]] := elimT (pairs_flatten_mem _ _ _) Hk1.
      have Hlt := all_In Ha1 Hs'. move: Hlt => /= Hlt.
      by move: Hlt; rewrite -Ex Ekx ltnn.
    + rewrite Epart2 map_inj_uniq; last by move=> y1 y2 [=].
      exact: HbuB1.
  -    move=> x y. rewrite mem_cat. split.
    + move=> /orP [Hp1 | Hp2].
      * have [s' [a' [Hs' Ha' Ex Ey]]]
          := elimT (pairs_flatten_mem _ _ _) Hp1.
        have [bmx [Hbx Hax]] := Hdecl1 _ _ Hs' Ha'.
        split.
        -- exists bmx, a'.2. rewrite Ex Ey. by split.
        -- apply/orP; left. rewrite Ex.
           exact: (all_In Ha1 Hs').
      * move: Hp2. rewrite Epart2 => /mapP [y0 Hy0 [= Ex Ey]].
        have [a' [Ha' Ey0]] := elimT (unzip1_mem_In _ _) Hy0.
        have Hax := Hdecl2 _ Ha'.
        split.
        -- exists bmap, a'.2. rewrite Ex Ey Ey0. by split.
        -- apply/orP; right. rewrite Ex Ey Ey0 eqxx /=.
           exact: (all_In Hb1 Ha').
    + move=> [[bmx [bfy [Hx Hy]]] Hlex].
      case/orP: Hlex => [Hxc | /andP [/eqP Exc Hyb]].
      *        apply/orP; left.
        have Hxin : List.In (x, Maps.elementsm bmx) olist.
        { apply/In_elementsm. by rewrite mapmE Hx. }
        rewrite Eo in Hxin.
        have HxL1 : List.In (x, Maps.elementsm bmx) L1.
        { case: (List.in_app_or _ _ _ Hxin) => [HIn | HIn] //.
          exfalso. case: HIn => [Emid | HIn2].
          - case: Emid => Exc _. by move: Hxc; rewrite Exc ltnn.
          - have Hgt := all_In Ha2 HIn2. move: Hgt => /= Hgt.
            by move: Hxc Hgt; lia. }
        apply: (introT (pairs_flatten_mem _ _ _)).
        exists (x, Maps.elementsm bmx), (y, bfy).
        split=> //=.
        by apply/In_elementsm.
      *        apply/orP; right.
        have Ebmx : bmx = bmap by move: Hx; rewrite Exc Hc => -[].
        have Hyin : List.In (y, bfy) (Maps.elementsm bmap).
        { apply/In_elementsm. by rewrite -Ebmx. }
        rewrite Eb in Hyin.
        have HyB1 : List.In (y, bfy) B1.
        { case: (List.in_app_or _ _ _ Hyin) => [HIn | HIn] //.
          exfalso. case: HIn => [Emid | HIn2].
          - case: Emid => Eyb _. by move: Hyb; rewrite Eyb ltnn.
          - have Hgt := all_In Hb2 HIn2. move: Hgt => /= Hgt.
            by move: Hyb Hgt; lia. }
        rewrite Epart2. apply/mapP.
        exists y.
        -- apply: (introT (unzip1_mem_In _ _)).
           by exists (y, bfy).
        -- by rewrite Exc. }rewrite Hcount map_cat sumn_cat.
have Hsum2 : sumn [seq size (linearize_buf pb t.1 t.2) | t <- part2]
             = sumn [seq bsize a.2 | a <- B1].
{ rewrite /part2 -map_comp.
  apply: sumn_map_In_eq => a Ha /=.
  exact: (size_linearize_buf Hc (Hdecl2 _ Ha)). }
have Hsum1 : sumn [seq size (linearize_buf pb t.1 t.2) | t <- part1]
             = sumn [seq osum s | s <- L1].
{ rewrite /part1 map_flatten sumn_flattenE -!map_comp.
  apply: sumn_map_In_eq => s Hs /=.
  rewrite -map_comp /osum.
  apply: sumn_map_In_eq => a Ha /=.
  have [bmx [Hbx Hax]] := Hdecl1 _ _ Hs Ha.
  exact: (size_linearize_buf Hbx Hax). }
rewrite Hsum1 Hsum2.
by lia.
Qed.

End Keystone.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Lemma list_upd_size (T : Type) (blk : list T) (o : nat) (v : T)
    (blk' : list T) :
  list_upd blk o v = Some blk' -> size blk' = size blk.
Proof.
elim: blk o blk' => [|x blk IH] [|o] blk' //=.
- by move=> [<-].
- case E: (list_upd blk o v) => [blk''|] // [<-] /=.
  by rewrite (IH _ _ E).
Qed.


Section SumSetm.

Variable T : ordType.
Variable S : Type.
Variable f : S -> nat.

Lemma getm_def_below (s : seq (T * S)) (k b : T) :
  path Ord.lt b (unzip1 s) ->
  Ord.lt k b ->
  getm_def s k = None.
Proof.
elim: s b => [|p s IH] b //= /andP[Hb Hpath] Hk.
have Hkp : Ord.lt k p.1 := Ord.lt_trans Hk Hb.
have Hne : (k == p.1) = false.
{ move: Hkp. rewrite Ord.lt_neqAle => /andP[Hne _].
  exact: negbTE. }
rewrite Hne.
exact: IH Hpath Hkp.
Qed.

Lemma sumn_setm_def_fresh (s : seq (T * S)) (k : T) (v : S) :
  getm_def s k = None ->
  sumn [seq f p.2 | p <- setm_def s k v]
  = f v + sumn [seq f p.2 | p <- s].
Proof.
elim: s => [|p s IH] //= Hget.
move: Hget.
case: (Ord.ltgtP k p.1) => [Hlt|Hgt|Heq] //= Hget.
by rewrite (IH Hget) !addnA (addnC (f v)).
Qed.

Lemma sumn_setm_def_present (s : seq (T * S)) (k : T) (v v0 : S) :
  sorted (@Ord.lt T) (unzip1 s) ->
  getm_def s k = Some v0 ->
  f v = f v0 ->
  sumn [seq f p.2 | p <- setm_def s k v]
  = sumn [seq f p.2 | p <- s].
Proof.
elim: s => [|p s IH] //= Hsort Hget Hf.
move: Hget.
case: (Ord.ltgtP k p.1) => [Hlt|Hgt|Heq] //=.
-
  rewrite (getm_def_below Hsort Hlt) //.
-
  move=> Hget.
  rewrite (IH _ Hget Hf) //.
  exact: path_sorted Hsort.
-
  move=> [Ev0]. subst v0.
  by rewrite Hf.
Qed.

Lemma sumn_fmval_setm_present (m : {fmap T -> S}) (k : T) (v v0 : S) :
  m k = Some v0 ->
  f v = f v0 ->
  sumn [seq f p.2 | p <- FMap.fmval (setm m k v)]
  = sumn [seq f p.2 | p <- FMap.fmval m].
Proof.
case: m => s Ps Hget Hf.
exact: sumn_setm_def_present Ps Hget Hf.
Qed.

Lemma sumn_fmval_setm_fresh (m : {fmap T -> S}) (k : T) (v : S) :
  m k = None ->
  sumn [seq f p.2 | p <- FMap.fmval (setm m k v)]
  = f v + sumn [seq f p.2 | p <- FMap.fmval m].
Proof.
case: m => s Ps Hget.
exact: sumn_setm_def_fresh Hget.
Qed.

End SumSetm.


Lemma heap_used_store_b (cm : Transitional.Memory.mem)
    (b : Block.id) (i : Z) (v : Transitional.tvalue * mem_tag)
    (cm' : Transitional.Memory.mem) :
  Transitional.Memory.store_b cm b i v = Some cm' ->
  MDefs.heap_used cm' = MDefs.heap_used cm.
Proof.
rewrite /Transitional.Memory.store_b.
case Hb: (Transitional.Memory.content cm b) => [chunk|] //.
case: (BinInt.Z.leb BinNums.Z0 i) => //.
case Hu: (list_upd chunk (BinInt.Z.to_nat i) v) => [chunk'|] // [<-] /=.
rewrite /MDefs.heap_used /=.
apply: (sumn_fmval_setm_present (f := fun blk => (size blk).+1) Hb).
by rewrite (list_upd_size Hu).
Qed.

Lemma heap_used_fresh (cm : Transitional.Memory.mem)
    (b : Block.id) (chunk : list (Transitional.tvalue * mem_tag)) :
  Transitional.Memory.content cm b = None ->
  MDefs.heap_used
    {| Transitional.Memory.content :=
         setm (Transitional.Memory.content cm) b chunk;
       Transitional.Memory.nextblock :=
         1 + Transitional.Memory.nextblock cm |}
  = (size chunk).+1 + MDefs.heap_used cm.
Proof.
move=> Hb.
rewrite /MDefs.heap_used /=.
exact: (@sumn_fmval_setm_fresh _ _ (fun blk => (size blk).+1) _ b chunk Hb).
Qed.

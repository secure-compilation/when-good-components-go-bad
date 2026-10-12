(* Task #14 (I→Merged correctness): the GENV block↔procedure-id layer.

   The Intermediate machine's pc addresses procedures by the BLOCK id
   reserved for them ([reserve_component_blocks] zips consecutive fresh
   blocks against the procedure list), while the linearizer's position
   machinery (LinPos) is keyed by PROCEDURE id.  This file characterizes
   [prepare_global_env]'s procedure map and entry points: block
   [nb0 + j] holds the j-th procedure's code (elementsm order), and an
   entry point of P is the block at P's index. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.

Import Intermediate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ==================== reserved blocks are consecutive ==================== *)

Lemma map_iota_rcons (f : nat -> nat) (n : nat) :
  [seq f i | i <- iota 0 n.+1] = rcons [seq f i | i <- iota 0 n] (f n).
Proof.
by rewrite -addn1 iotaD map_cat cats1.
Qed.

Lemma reserve_blocks_vals (m : ComponentMemory.t) (n : nat) :
  forall (m' : ComponentMemory.t) (bs : list Block.id),
  ComponentMemoryExtra.reserve_blocks m n = (m', bs) ->
  bs = [seq ComponentMemory.next_block m + i | i <- iota 0 n]
  /\ ComponentMemory.next_block m' = ComponentMemory.next_block m + n.
Proof.
rewrite /ComponentMemoryExtra.reserve_blocks.
elim: n => [|n IH] m' bs.
- move=> /= [<- <-]. split=> //. by rewrite addn0.
- rewrite iterS.
  case Ei: (iter n _ (m, [::])) => [mn bsn].
  case Er: (ComponentMemory.reserve_block mn) => [m'' b].
  move=> [E1 E2]; subst m' bs.
  have [Ebs En] := IH _ _ Ei.
  have [Eb En'] := ComponentMemory.reserve_block_next _ _ _ Er.
  split.
  + rewrite Ebs Eb En map_iota_rcons cats1. by [].
  + rewrite En' En. by rewrite addnS.
Qed.

(* ==================== small toolkit ==================== *)

Lemma nth_error_iota (m n j : nat) :
  j < n -> List.nth_error (iota m n) j = Some (m + j).
Proof.
elim: n m j => [|n IH] m [|j] //=.
- move=> _. by rewrite addn0.
- move=> Hj.
  have := IH m.+1 j Hj.
  by rewrite addSnnS.
Qed.

Lemma nth_error_zip (A B : Type) (sa : seq A) (sb : seq B) :
  forall (j : nat) (a : A) (b : B),
  List.nth_error sa j = Some a ->
  List.nth_error sb j = Some b ->
  List.nth_error (zip sa sb) j = Some (a, b).
Proof.
elim: sa sb => [|x sa IH] [|y sb] [|j] a b //=.
- by move=> [<-] [<-].
- exact: IH.
Qed.

Lemma In_zip_inv (A B : Type) (sa : seq A) (sb : seq B) (a : A) (b : B) :
  List.In (a, b) (zip sa sb) ->
  exists j, List.nth_error sa j = Some a /\ List.nth_error sb j = Some b.
Proof.
elim: sa sb => [|x sa IH] [|y sb] //= [E|HIn].
- case: E => -> ->. by exists 0.
- have [j [H1 H2]] := IH _ HIn. by exists j.+1.
Qed.

Lemma getm_def_In (A : Type) (s : list (nat * A)) (k : nat) (v : A) :
  getm_def s k = Some v -> List.In (k, v) s.
Proof.
elim: s => [|[k' v'] s IH] //=.
case: ifP => [/eqP Ek|_].
- move=> [Ev]. left. by rewrite Ek Ev.
- move=> /IH HIn. by right.
Qed.

Lemma In_mem_seq (T : eqType) (l : seq T) (x : T) :
  List.In x l -> x \in l.
Proof.
elim: l => [|a l IH] //= [->|/IH H]; rewrite in_cons.
- by rewrite eqxx.
- by rewrite H orbT.
Qed.

Lemma getm_def_In_uniq (A : Type) (s : list (nat * A)) (k : nat) (v : A) :
  uniq (unzip1 s) -> List.In (k, v) s -> getm_def s k = Some v.
Proof.
elim: s => [|[k' v'] s IH] //= /andP [Hk' Hu] [E|HIn].
- case: E => -> ->. by rewrite eqxx.
- case: ifP => [/eqP Ek|_]; last exact: IH.
  exfalso. subst k.
  have Hin : k' \in unzip1 s.
  { apply: In_mem_seq.
    have := List.in_map fst _ _ HIn.
    by []. }
  by rewrite Hin in Hk'.
Qed.

Lemma nth_error_size_list (A : Type) (l : seq A) (o : nat) (x : A) :
  List.nth_error l o = Some x -> o < size l.
Proof.
elim: l o => [|a l IH] [|o] //=.
exact: IH.
Qed.

Lemma map_nth_error_g (A B : Type) (f : A -> B) (n : nat) (l : seq A)
    (d : A) :
  List.nth_error l n = Some d ->
  List.nth_error [seq f x | x <- l] n = Some (f d).
Proof.
elim: l n => [|a l IH] [|n] //=.
- by move=> [= ->].
- exact: IH.
Qed.

Lemma nth_error_map_inv_g (A B : Type) (f : A -> B) (s : seq A) :
  forall (j : nat) (y : B),
  List.nth_error [seq f x | x <- s] j = Some y ->
  exists x, List.nth_error s j = Some x /\ y = f x.
Proof.
elim: s => [|a s IH] [|j] y //=.
- move=> [= <-]. by exists a.
- exact: IH.
Qed.

Lemma length_sizeE (T : Type) (l : seq T) : length l = size l.
Proof. by elim: l => //= x l ->. Qed.

(* ==================== the genv procedure map ==================== *)

(* the first block reserved for component C's procedures *)
Definition proc_nb0 (p : program) (C : Component.id) : Block.id :=
  ComponentMemory.next_block
    (ComponentMemory.prealloc (odflt emptym (prog_buffers p C))).

Lemma genv_procs_spec (p : program) (C : Component.id)
    (Cprocs_src : NMap code) :
  C \in domm (prog_interface p) ->
  prog_procedures p C = Some Cprocs_src ->
  exists CprocsB,
    [/\ genv_procedures (prepare_global_env p) C = Some CprocsB,
        (forall j P Pcode,
           List.nth_error (elementsm Cprocs_src) j = Some (P, Pcode) ->
           getm CprocsB (proc_nb0 p C + j) = Some Pcode)
      & (forall b Pcode,
           getm CprocsB b = Some Pcode ->
           exists j P,
             [/\ b = proc_nb0 p C + j
               & List.nth_error (elementsm Cprocs_src) j = Some (P, Pcode)])].
Proof.
move=> Hin HC.
case Er: (ComponentMemoryExtra.reserve_blocks
            (ComponentMemory.prealloc (odflt emptym (prog_buffers p C)))
            (length (elementsm Cprocs_src))) => [Cmem' bs].
have [Ebs En] := reserve_blocks_vals Er.
have Hszbs : size bs = size (elementsm Cprocs_src).
{ by rewrite Ebs size_map size_iota length_sizeE. }
have Hubs : uniq bs.
{ rewrite Ebs map_inj_uniq ?iota_uniq //.
  move=> x y /addnI. by []. }
have Huz : uniq (unzip1 (zip bs (unzip2 (elementsm Cprocs_src)))).
{ rewrite unzip1_zip //.
  by rewrite Hszbs size_map. }
have Egv : genv_procedures (prepare_global_env p) C
           = Some (mkfmap (zip bs (unzip2 (elementsm Cprocs_src)))).
{ rewrite /prepare_global_env /prepare_procedures_initial_memory
          /prepare_procedures_initial_memory_aux /=.
  rewrite mapmE mkfmapfE Hin /= HC /=.
  rewrite /reserve_component_blocks; cbv zeta.
  by rewrite Er /=. }
exists (mkfmap (zip bs (unzip2 (elementsm Cprocs_src)))).
split=> //.
- (* forward: the j-th procedure sits at block nb0 + j *)
  move=> j P Pcode Hj.
  have Hjn : j < size (elementsm Cprocs_src)
    := nth_error_size_list Hj.
  rewrite mkfmapE.
  apply: getm_def_In_uniq => //.
  apply: (List.nth_error_In _ j).
  apply: nth_error_zip.
  + rewrite Ebs.
    have := map_nth_error_g (fun i => proc_nb0 p C + i)
              (nth_error_iota 0 Hjn).
    by [].
  + have := map_nth_error_g snd Hj.
    by [].
- (* inverse: every block entry is some procedure's code *)
  move=> b Pcode Hb0.
  move: Hb0. rewrite mkfmapE. move=> Hb0.
  have Hb := getm_def_In Hb0.
  have [j [Hjb Hjc]] := In_zip_inv Hb.
  have Hjn : j < size bs := nth_error_size_list Hjb.
  rewrite Ebs in Hjb.
  have [i [Hi Ei]] := nth_error_map_inv_g Hjb.
  have Hjn' : j < size (elementsm Cprocs_src) by rewrite -Hszbs.
  have Hi' : List.nth_error (iota 0 (length (elementsm Cprocs_src))) j
             = Some (0 + j).
  { apply: nth_error_iota. by rewrite length_sizeE. }
  rewrite Hi' in Hi. case: Hi => Ei'.
  have [[P Pc] [Hpair Epc]] := nth_error_map_inv_g Hjc.
  exists j, P.
  split.
  + rewrite Ei -Ei'. by [].
  + rewrite Hpair. by rewrite /= in Epc; rewrite Epc.
Qed.

(* ==================== the entry points ==================== *)

Lemma In_pmap_inv (A B : Type) (f : A -> option B) (s : seq A) (y : B) :
  List.In y (pmap f s) ->
  exists x, List.In x s /\ f x = Some y.
Proof.
elim: s => [|x s IH] //=.
case Ef: (f x) => [y0|] /=.
- move=> [E|HIn].
  + exists x. split; first by left.
    by rewrite Ef E.
  + have [x0 [H1 H2]] := IH HIn.
    exists x0. split; [by right | exact: H2].
- move=> HIn.
  have [x0 [H1 H2]] := IH HIn.
  exists x0. split; [by right | exact: H2].
Qed.

(* an entry point of P is the block at P's position in the procedure list *)
Lemma genv_entry_spec (p : program) (C : Component.id)
    (Cprocs_src : NMap code) (P : Procedure.id) (b : Block.id) :
  C \in domm (prog_interface p) ->
  prog_procedures p C = Some Cprocs_src ->
  EntryPoint.get C P (genv_entrypoints (prepare_global_env p)) = Some b ->
  exists j Pcode,
    [/\ b = proc_nb0 p C + j
      & List.nth_error (elementsm Cprocs_src) j = Some (P, Pcode)].
Proof.
move=> Hin HC.
case Er: (ComponentMemoryExtra.reserve_blocks
            (ComponentMemory.prealloc (odflt emptym (prog_buffers p C)))
            (length (elementsm Cprocs_src))) => [Cmem' bs].
have [Ebs En] := reserve_blocks_vals Er.
rewrite /EntryPoint.get /prepare_global_env /prepare_procedures_initial_memory
        /prepare_procedures_initial_memory_aux /=.
rewrite mapmE mkfmapfE Hin /= HC /=.
rewrite /reserve_component_blocks; cbv zeta.
rewrite Er /=.
rewrite mkfmapE. move=> HgP.
have HbIn := getm_def_In HgP.
have [[P0 b0] [HIn Hf]] := In_pmap_inv HbIn.
move: Hf.
case Eif: (getm (prog_interface p) C) => [Ci|]; last by [].
case: ifP => // _.
move=> [E1 E2]; subst P0 b0.
have [j [HjP Hjb]] := In_zip_inv HIn.
have Hjn : j < size bs := nth_error_size_list Hjb.
rewrite Ebs in Hjb.
have [i [Hi Ei]] := nth_error_map_inv_g Hjb.
have Hjn' : j < length (elementsm Cprocs_src).
{ rewrite length_sizeE.
  by rewrite Ebs size_map size_iota length_sizeE in Hjn. }
have Hi' : List.nth_error (iota 0 (length (elementsm Cprocs_src))) j
           = Some (0 + j).
{ exact: nth_error_iota. }
rewrite Hi' in Hi. case: Hi => Ei'.
have [[P' Pc] [Hpair Efst]] := nth_error_map_inv_g HjP.
exists j, Pc.
split.
- rewrite Ei -Ei'. by [].
- rewrite Hpair.
  rewrite /= in Efst.
  by rewrite Efst.
Qed.

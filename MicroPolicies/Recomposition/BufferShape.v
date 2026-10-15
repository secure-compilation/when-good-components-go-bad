(* Buffer SHAPE determinism of the data segment.

   The flat layout of [Merged.initial_memory pb] — every base address, the
   total size, and the concretization of stored pointers — depends only on
   the buffers' SHAPE (which blocks exist, with which cell counts), never on
   their contents.  Consequently two buffer maps that agree in shape
   everywhere and in CONTENT on some component produce initial memories
   that agree on that component's cells (and have equal domains and sizes).

   This is the kernel for weakening [RecompositionContext]'s buffer axioms
   [prog_buffers_p_p'] / [prog_buffers_c_c'] from content equality to shape
   equality, which is what the back-translated programs can actually
   provide ([bt_ip'_buffers]/[bt_ic'_buffers], see BackTranslation.v).

   Builds directly on BufferLayout.v's address kernel
   ([nat_addr]/[bl_base]/[linearize_bufsE]/[eq_mapk]/[won_inj]). *)

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
Require Import MicroPolicies.Recomposition.BufferLayout.
Import DoNotation.
Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ==================== the shape of a buffer map ==================== *)

Definition bsize (blk : nat + seq Values.value) : nat :=
  match blk with inl n => n | inr l => size l end.

(* forget contents, keep the cell counts *)
Definition bufs_shape (pb : NMap {fmap Values.Block.id -> nat + seq Values.value})
  : NMap {fmap Values.Block.id -> nat} :=
  mapm (mapm bsize) pb.

Section Shape.

Variables pb pb' : NMap {fmap Values.Block.id -> nat + seq Values.value}.
Hypothesis Hsh : bufs_shape pb = bufs_shape pb'.

Lemma shape_domm : domm pb = domm pb'.
Proof.
have H := Hsh. rewrite /bufs_shape in H.
by rewrite -(domm_map (mapm bsize) pb) H domm_map.
Qed.

Lemma shape_at : forall c bm,
  pb c = Some bm ->
  exists2 bm', pb' c = Some bm' & mapm bsize bm = mapm bsize bm'.
Proof.
move=> c bm Hc.
have := congr1 (fun m => getm m c) Hsh.
rewrite /bufs_shape !mapmE Hc /=.
case Hc': (pb' c) => [bm'|] /=.
- move=> /Some_inj E. by exists bm'.
- by [].
Qed.

Lemma shape_none : forall c, pb c = None -> pb' c = None.
Proof.
move=> c Hc. apply/dommPn. rewrite -shape_domm. by apply/dommPn.
Qed.

Lemma size_repeat (T : Type) (x : T) k : size (List.repeat x k) = k.
Proof. by rewrite -size_length List.repeat_length. Qed.

(* block sizes coincide *)
Lemma lb_size_shape : forall c b,
  size (linearize_buf pb c b) = size (linearize_buf pb' c b).
Proof.
move=> c b. rewrite /linearize_buf.
case Hc: (pb c) => [bm|]; last by rewrite (shape_none Hc).
have [bm' -> Ebm] := shape_at Hc.
rewrite /=.
have := congr1 (fun m => getm m b) Ebm.
rewrite !mapmE.
case Hb: (bm b) => [blk|] /=; case Hb': (bm' b) => [blk'|] //=.
move=> /Some_inj Es. clear Hb Hb'.
case: blk Es => [n|l]; case: blk' => [n'|l'] Es;
  by rewrite /= ?size_repeat ?size_map.
Qed.

Lemma lb_domm_shape : domm (linearize_bufs pb) = domm (linearize_bufs pb').
Proof.
apply/eq_fset => -[[c b] o].
apply/idP/idP => /linearize_bufs_key [bm [blk [H1 H2 H3]]];
  apply/linearize_bufs_key.
- have [bm' Hc' Ebm] := shape_at H1.
  have := congr1 (fun m => getm m b) Ebm. rewrite !mapmE H2 /=.
  case Hb': (bm' b) => [blk'|] //= _.
  exists bm', blk'. split=> //.
  by rewrite -lb_size_shape.
- case Hc: (pb c) => [bm0|]; last first.
  { by rewrite (shape_none Hc) in H1. }
  have [bm'' Hc'' Ebm] := shape_at Hc.
  rewrite Hc'' in H1. case: H1 => ?; subst bm''.
  have := congr1 (fun m => getm m b) Ebm. rewrite !mapmE H2 /=.
  case Hb0: (bm0 b) => [blk0|] //= _.
  exists bm0, blk0. split=> //.
  by rewrite lb_size_shape.
Qed.

Lemma total_shape : size (linearize_bufs pb) = size (linearize_bufs pb').
Proof. by rewrite -!size_domm_fmap lb_domm_shape. Qed.

Lemma bl_base_shape : forall c b, bl_base pb c b = bl_base pb' c b.
Proof. move=> c b. by rewrite /bl_base lb_domm_shape. Qed.

Lemma nat_addr_shape : forall k, nat_addr pb k = nat_addr pb' k.
Proof. move=> [[c b] o]. by rewrite /nat_addr bl_base_shape. Qed.

End Shape.

(* ==================== the explicit data-segment encoder ==================== *)

(* verbatim replicas of [Merged.initial_memory]'s let-bound pieces *)
Definition imem_base (pb : NMap {fmap Values.Block.id -> nat + seq Values.value})
    (c b : nat) : nat :=
  length (domm (filterm (fun x (_ : Values.value * mem_tag) =>
    match x with (c', b', _) => (c' < c) || ((c' == c) && (b' < b)) end)
    (linearize_bufs pb))).

Definition imem_concretize (pb : NMap {fmap Values.Block.id -> nat + seq Values.value})
    (p : nat * nat * Z) : ssrint.int :=
  match p with
  | (c, b, o) => ssrint.intZmod.addz (encode_int o) (ssrint.Posz (imem_base pb c b))
  end.

Definition imem_enc (pb : NMap {fmap Values.Block.id -> nat + seq Values.value})
    (x : Values.value * mem_tag) : atom (mword mt) mem_tag :=
  {| vala := match fst x with
             | Int z => word.as_word (encode_int z)
             | Ptr p => word.as_word (imem_concretize pb p)
             | Undef => word.as_word (ssrint.Posz 0)
             end ;
     taga := snd x |}.

Lemma imem_baseE pb c b : imem_base pb c b = bl_base pb c b.
Proof. rewrite /imem_base size_length. exact: base_filterm. Qed.

Lemma imem_base_shape pb pb' c b :
  bufs_shape pb = bufs_shape pb' -> imem_base pb c b = imem_base pb' c b.
Proof. move=> Hsh. by rewrite !imem_baseE (bl_base_shape Hsh). Qed.

Lemma imem_concretize_shape pb pb' p :
  bufs_shape pb = bufs_shape pb' -> imem_concretize pb p = imem_concretize pb' p.
Proof.
move=> Hsh. case: p => [[c b] o] /=. by rewrite (imem_base_shape c b Hsh).
Qed.

Lemma imem_enc_shape pb pb' x :
  bufs_shape pb = bufs_shape pb' -> imem_enc pb x = imem_enc pb' x.
Proof.
move=> Hsh. rewrite /imem_enc. case: x => [v t] /=.
case: v => [z|p|] //=.
by rewrite (imem_concretize_shape p Hsh).
Qed.

(* [initial_memory] as the explicit mapk *)
Lemma initial_memory_encE pb :
  initial_memory (mt := mt) pb
  = Tmp.mapk (fun k => @word_of_nat (word_size mt) (nat_addr pb k))
             (mapm (imem_enc pb) (linearize_bufs pb)).
Proof.
rewrite /initial_memory; cbv zeta.
apply: eq_mapk => -[[c b] o] /=.
rewrite encode_int_of_nat /=.
congr as_word. congr ssrint.Posz. congr addn.
rewrite size_length. exact: base_filterm.
Qed.

(* injectivity of the address map on the cell keys *)
Lemma won_addr_inj_gen pb
    (Hb : size (linearize_bufs pb) < 2 ^ (word_size mt)) :
  {in domm (linearize_bufs pb) &,
   injective (fun k => @word_of_nat (word_size mt) (nat_addr pb k))}.
Proof.
move=> x y Hx Hy E.
exact: (nat_addr_inj Hx Hy
          (won_inj (ltn_trans (nat_addr_lt Hx) Hb)
                   (ltn_trans (nat_addr_lt Hy) Hb) E)).
Qed.

(* forward: a declared cell sits, encoded, at its canonical address *)
Lemma initial_memory_atE pb k cell
    (Hb : size (linearize_bufs pb) < 2 ^ (word_size mt)) :
  linearize_bufs pb k = Some cell ->
  initial_memory (mt := mt) pb (@word_of_nat (word_size mt) (nat_addr pb k))
  = Some (imem_enc pb cell).
Proof.
move=> Hk. rewrite initial_memory_encE.
have Hinj : {in domm (mapm (imem_enc pb) (linearize_bufs pb)) &,
             injective (fun k0 => @word_of_nat (word_size mt) (nat_addr pb k0))}.
{ move=> x y. rewrite !domm_map => Hx Hy. exact: (won_addr_inj_gen Hb Hx Hy). }
have Hmk : mapm (imem_enc pb) (linearize_bufs pb) k = Some (imem_enc pb cell).
{ by rewrite mapmE Hk. }
exact: (mapk_Some_inv Hinj Hmk).
Qed.

(* backward: every data cell comes from a declared cell *)
Lemma initial_memory_invE pb w d :
  initial_memory (mt := mt) pb w = Some d ->
  exists k cell,
    [/\ linearize_bufs pb k = Some cell, d = imem_enc pb cell
      & w = @word_of_nat (word_size mt) (nat_addr pb k)].
Proof.
move=> Hmem. rewrite initial_memory_encE in Hmem.
have [k [Hfk Hmk]] := mapk_Some Hmem.
move: Hmk. rewrite mapmE.
case Hbk: (linearize_bufs pb k) => [cell|] //= [= Hd].
exists k, cell. split.
- by [].
- by rewrite -Hd.
- by rewrite -Hfk.
Qed.

(* ==================== cell tags and per-component contents ==================== *)

Lemma nth_error_nth' (T : Type) (d : T) (l : seq T) i :
  i < size l -> List.nth_error l i = Some (nth d l i).
Proof. elim: l i => [|a l IH] [|i] //=. exact: IH. Qed.

Lemma lb_all_tag pb c b (x : Values.value * mem_tag) :
  List.In x (linearize_buf pb c b) -> x.2 = def_mem_tag c false.
Proof.
rewrite /linearize_buf.
case: (pb c) => [bm|] //=. case: (bm b) => [blk|] //=.
case: blk => [n|l] /=.
- move=> HIn. by have -> := List.repeat_spec _ _ _ HIn.
- rewrite List.in_map_iff. by move=> [v [<- _]].
Qed.

Lemma linearize_bufs_cell_tag pb c b o cell :
  linearize_bufs pb (c, b, o) = Some cell -> cell.2 = def_mem_tag c false.
Proof.
rewrite linearize_bufsE.
case Epc: (pb c) => [bm|] //. case Emb: (bm b) => [blk|] // Hnth.
have Hlt : o < size (linearize_buf pb c b).
{ case Ho: (o < size (linearize_buf pb c b)) => //.
  move: Hnth. rewrite nth_default; first by [].
  rewrite size_map. by lia. }
move: Hnth.
rewrite (nth_map (Undef, def_mem_tag c false)) //.
move=> [= Hc]. rewrite -Hc.
apply: lb_all_tag.
apply: (List.nth_error_In _ o).
exact: (nth_error_nth' _ Hlt).
Qed.

(* [linearize_buf] only reads the component's own entry *)
Lemma linearize_buf_local (pb pb' : NMap {fmap Values.Block.id -> nat + seq Values.value}) c b :
  pb c = pb' c -> linearize_buf pb c b = linearize_buf pb' c b.
Proof. move=> H. by rewrite /linearize_buf H. Qed.

Lemma lb_cell_agree (pb pb' : NMap {fmap Values.Block.id -> nat + seq Values.value}) c b o :
  pb c = pb' c ->
  linearize_bufs pb (c, b, o) = linearize_bufs pb' (c, b, o).
Proof.
move=> H. rewrite !linearize_bufsE H (linearize_buf_local b H). by [].
Qed.

(* ==================== the master agreement lemmas ==================== *)

(* Shape-equal buffer maps that agree in content on a component produce
   initial memories that agree on that component's cells. *)
Lemma initial_memory_shape_agree pb pb' w d :
  bufs_shape pb = bufs_shape pb' ->
  size (linearize_bufs pb) < 2 ^ (word_size mt) ->
  initial_memory (mt := mt) pb w = Some d ->
  pb (color (taga d)) = pb' (color (taga d)) ->
  initial_memory (mt := mt) pb' w = Some d.
Proof.
move=> Hsh Hb Hmem Heq.
have [k [cell [Hk Hd Hw]]] := initial_memory_invE Hmem.
case: k Hk Hw => [[c b] o] Hk Hw.
have Hcol : color (taga d) = c.
{ by rewrite Hd /imem_enc /= (linearize_bufs_cell_tag Hk). }
rewrite Hcol in Heq.
have Hk' : linearize_bufs pb' (c, b, o) = Some cell.
{ by rewrite -(lb_cell_agree b o Heq). }
have Hb' : size (linearize_bufs pb') < 2 ^ (word_size mt).
{ by rewrite -(total_shape Hsh). }
have := initial_memory_atE Hb' Hk'.
by rewrite -(nat_addr_shape Hsh ((c, b, o) : nat * nat * nat))
           -Hw -(imem_enc_shape cell Hsh) -Hd.
Qed.

(* Shape-equal buffer maps produce data segments with the same domain,
   size, and cell tags. *)
Lemma initial_memory_shape_size pb pb' :
  bufs_shape pb = bufs_shape pb' ->
  size (linearize_bufs pb) < 2 ^ (word_size mt) ->
  size (initial_memory (mt := mt) pb) = size (initial_memory (mt := mt) pb').
Proof.
move=> Hsh Hb.
have Hb' : size (linearize_bufs pb') < 2 ^ (word_size mt).
{ by rewrite -(total_shape Hsh). }
by rewrite (initial_memory_size_eq Hb) (initial_memory_size_eq Hb') (total_shape Hsh).
Qed.

Lemma initial_memory_shape_domm pb pb' :
  bufs_shape pb = bufs_shape pb' ->
  size (linearize_bufs pb) < 2 ^ (word_size mt) ->
  domm (initial_memory (mt := mt) pb) = domm (initial_memory (mt := mt) pb').
Proof.
move=> Hsh Hb.
have Hb' : size (linearize_bufs pb') < 2 ^ (word_size mt).
{ by rewrite -(total_shape Hsh). }
rewrite (initial_memory_domm_iota Hb) (initial_memory_domm_iota Hb').
by rewrite (total_shape Hsh).
Qed.

(* ==================== unionm lifting and agreement glue ==================== *)

Lemma bufs_shape_unionm a b :
  bufs_shape (unionm a b) = unionm (bufs_shape a) (bufs_shape b).
Proof.
apply/eq_fmap => c.
rewrite /bufs_shape mapmE !unionmE !mapmE.
by case: (a c).
Qed.

Lemma bufs_shape_unionm_l a a' b :
  bufs_shape a = bufs_shape a' ->
  bufs_shape (unionm a b) = bufs_shape (unionm a' b).
Proof. move=> H. by rewrite !bufs_shape_unionm H. Qed.

Lemma bufs_shape_unionm_r a b b' :
  bufs_shape b = bufs_shape b' ->
  bufs_shape (unionm a b) = bufs_shape (unionm a b').
Proof. move=> H. by rewrite !bufs_shape_unionm H. Qed.

Lemma unionm_agree_l (T : ordType) (S : Type) (a b b' : {fmap T -> S}) k :
  k \in domm a -> unionm a b k = unionm a b' k.
Proof. rewrite !unionmE mem_domm. by case: (a k). Qed.

Lemma unionm_agree_r (T : ordType) (S : Type) (a a' b : {fmap T -> S}) k :
  k \notin domm a -> k \notin domm a' -> unionm a b k = unionm a' b k.
Proof. rewrite !unionmE. by move=> /dommPn -> /dommPn ->. Qed.

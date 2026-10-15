(** * The memory injection: relates T's structured memory
    ([Transitional.Memory.t]) to the me machine's flat word-addressed
    memory.  Provides [vrel]/[amap_ok]/[minj], the initial map [amap0],
    and the load/store/alloc preservation lemmas. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.

Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* code-address map: component × code index ↦ me flat address (static;
   code never moves), instantiated by the linked-layout position map *)
Definition cmap_t := Component.id -> nat -> option nat.

Section Injection.
Variable pb : NMap {fmap Block.id -> nat + seq value}.
Variable cmap : cmap_t.

(* ================================================================== *)
(* 1. The address map.                                                *)
(* ================================================================== *)

(* component ↦ T block id ↦ me base address *)
Definition amap_t := NMap (NMap nat).

Definition addr_of (amap : amap_t) (c b : nat) : option nat :=
  obind (getm ^~ b) (getm amap c).

(* the INITIAL address map: exactly the static bases *)
Definition amap0 : amap_t :=
  mapim (fun c bmap => mapim (fun b _ => bl_base pb c b) bmap) pb.

Lemma amap0_static c bmap b bf :
  pb c = Some bmap -> bmap b = Some bf ->
  addr_of amap0 c b = Some (bl_base pb c b).
Proof.
move=> Hc Hb.
rewrite /addr_of /amap0 mapimE Hc /= mapimE Hb /=.
by [].
Qed.

Lemma amap0_dom c b a :
  addr_of amap0 c b = Some a ->
  exists bmap bf, [/\ pb c = Some bmap, bmap b = Some bf & a = bl_base pb c b].
Proof.
rewrite /addr_of /amap0 mapimE.
case Hc: (pb c) => [bmap|] //=.
rewrite mapimE.
case Hb: (bmap b) => [bf|] //= [<-].
by exists bmap, bf.
Qed.

(* ================================================================== *)
(* 2. The value relation.                                             *)
(* ================================================================== *)

(* the word decodes to z via the composite me's event payloads use
   ([Symbolic.evi]), so payload agreement is definitional *)
Definition wrepr (z : Z) (w : mword mt) : Prop :=
  Symbolic.convert (int_of_word w) = z.

Variant vrel (amap : amap_t) : value -> mword mt -> Prop :=
| VRInt z w :
    wrepr z w ->
    vrel amap (Int z) w
| VRPtr cp bp op (w : mword mt) a :
    addr_of amap cp bp = Some a ->
    BinInt.Z.le 0 op ->
    w = word_of_nat (a + BinInt.Z.to_nat op) ->
    vrel amap (Ptr (cp, bp, op)) w
| VRUndef w :
    vrel amap Undef w.

(* code capabilities: a T value tagged [InternalJump]/[Ret _] is a
   pointer into code; its me image is the flat code address via [cmap].
   [Invalidated] values are dead, hence unconstrained.  The tag
   dispatches the interpretation. *)
Definition code_rel (v : value) (w : mword mt) : Prop :=
  exists cp bp op pos,
    [/\ v = Ptr (cp, bp, op),
        cmap cp (BinInt.Z.to_nat op) = Some pos,
        BinInt.Z.le 0 op
      & w = @word_of_nat (word_size mt) pos].

Definition tvrel (amap : amap_t)
    (tv : Transitional.tvalue) (w : mword mt) : Prop :=
  match Transitional.tvtag tv with
  | Other => vrel amap (Transitional.val tv) w
  | InternalJump | Ret _ => code_rel (Transitional.val tv) w
  | Invalidated => True
  end.

(* per-cell relation: tvalues related, mem tags equal, and the T-side
   tvalue/mem-tag sync [vtag t.2 = tvtag t.1] *)
Definition cellrel (amap : amap_t)
    (tc : Transitional.tvalue * mem_tag) (mc : matom) : Prop :=
  [/\ tvrel amap tc.1 (vala mc),
      taga mc = tc.2
    & vtag tc.2 = Transitional.tvtag tc.1].

(* an event-clobbered cell: T records [tUndef]/vtag [Other] but me
   records [Invalidated] (other tag fields equal).  Written at cross
   entries; [amap]-free, so it transports over store/alloc updates. *)
Definition clobcell (tc : Transitional.tvalue * mem_tag)
    (mc : @matom mt) : Prop :=
  [/\ tc.1 = Transitional.tUndef,
      vtag tc.2 = Other
    & vtag (taga mc) = Invalidated]
  /\ [/\ color (taga mc) = color tc.2,
         entry (taga mc) = entry tc.2
       & is_code (taga mc) = is_code tc.2].

(* the weakened per-cell relation carried by [mj_cell] *)
Definition cellrelw (amap : amap_t)
    (tc : Transitional.tvalue * mem_tag) (mc : matom) : Prop :=
  cellrel amap tc mc \/ clobcell tc mc.

(* ================================================================== *)
(* 3. Address-map well-formedness.                                    *)
(* ================================================================== *)

Definition block_size (tmem : Transitional.Memory.t) (c b : nat) : option nat :=
  match tmem c with
  | Some cm => omap size (Transitional.Memory.content cm b)
  | None => None
  end.

Record amap_ok (amap : amap_t) (tmem : Transitional.Memory.t) : Prop := {  aok_static : forall c bmap b bf,
      pb c = Some bmap -> bmap b = Some bf ->
      addr_of amap c b = Some (bl_base pb c b);  aok_total : forall c cm b blk,
      tmem c = Some cm ->
      Transitional.Memory.content cm b = Some blk ->
      exists a, addr_of amap c b = Some a;  aok_disjoint : forall c1 b1 a1 n1 c2 b2 a2 n2,
      (c1, b1) <> (c2, b2) ->
      addr_of amap c1 b1 = Some a1 -> block_size tmem c1 b1 = Some n1 ->
      addr_of amap c2 b2 = Some a2 -> block_size tmem c2 b2 = Some n2 ->
      0 < n1 -> 0 < n2 ->
      (a1 + n1 <= a2) \/ (a2 + n2 <= a1);  aok_bound : forall c b a n,
      addr_of amap c b = Some a -> block_size tmem c b = Some n ->
      a + n <= 2 ^ word_size mt;  aok_dom : forall c b a,
      addr_of amap c b = Some a ->
      exists cm blk,
        tmem c = Some cm /\
        Transitional.Memory.content cm b = Some blk;  aok_next : forall c cm b blk,
      tmem c = Some cm ->
      Transitional.Memory.content cm b = Some blk ->
      b < Transitional.Memory.nextblock cm
}.

(* ================================================================== *)
(* 4. The memory injection.                                           *)
(* ================================================================== *)

Record minj (amap : amap_t)
    (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom}) : Prop := {
  mj_amap : amap_ok amap tmem;  mj_cell : forall c cm b blk o cell a,
      tmem c = Some cm ->
      Transitional.Memory.content cm b = Some blk ->
      List.nth_error blk o = Some cell ->
      addr_of amap c b = Some a ->
      exists mc,
        mmem (word_of_nat (a + o)) = Some mc /\ cellrelw amap cell mc;  mj_data : forall c cm b blk o cell a mc,
      tmem c = Some cm ->
      Transitional.Memory.content cm b = Some blk ->
      List.nth_error blk o = Some cell ->
      addr_of amap c b = Some a ->
      mmem (word_of_nat (a + o)) = Some mc ->
      [/\ is_code (taga mc) = false, color (taga mc) = c
        & entry (taga mc) = None]
}.

End Injection.

(* ================================================================== *)
(* 5. The signed round-trip: [int_of_word ∘ as_word] is the identity  *)
(*    on the signed window (stated over an abstract width so [simpl]   *)
(*    can't evaluate [2 ^ 32] in unary).                              *)
(* ================================================================== *)

Section WordRoundTrip.

Variable k : nat.
Hypothesis k_gt0 : 0 < k.

Lemma exp_half_lt : 2 ^ k.-1 < 2 ^ k.
Proof. by rewrite ltn_exp2l // -{2}(prednK k_gt0). Qed.

Lemma exp_halfE : 2 ^ k = 2 ^ k.-1 + 2 ^ k.-1.
Proof. by rewrite addnn -mul2n -expnS (prednK k_gt0). Qed.

(* [Transitional.val] shadows the subtype projection here, so the
   ordinal value is spelled with eqtype's [\val] notation *)
Lemma val_as_word_neg (m : nat) :
  m < 2 ^ k ->
  \val (word.as_word (ssrint.Negz m) : word.word k) = (2 ^ k - m.+1)%N :> nat.
Proof.
move=> Hm.
rewrite /word.as_word /=.
rewrite modNz_nat ?expn_gt0 // (modn_small Hm).
have -> : ((2 ^ k)%:Z - 1 - m%:Z)%R = ((2 ^ k - m.+1)%N%:Z)%R.
{ set T := (2 ^ k)%N in Hm *. by lia. }
rewrite absz_nat modn_small //.
by rewrite ltn_subrL expn_gt0.
Qed.

Lemma int_of_word_as_word_pos (n : nat) :
  n < 2 ^ k.-1 ->
  word.int_of_word (word.as_word (ssrint.Posz n) : word.word k) = ssrint.Posz n.
Proof.
move=> Hn.
have Hn' : n < 2 ^ k by exact: (ltn_trans Hn exp_half_lt).
rewrite /word.int_of_word word.as_wordK //.
by rewrite Hn.
Qed.

Lemma int_of_word_as_word_neg (m : nat) :
  m < 2 ^ k.-1 ->
  word.int_of_word (word.as_word (ssrint.Negz m) : word.word k) = ssrint.Negz m.
Proof.
move=> Hm.
have Hm' : m < 2 ^ k by exact: (ltn_trans Hm exp_half_lt).
rewrite /word.int_of_word val_as_word_neg //.
have Hcond : (2 ^ k - m.+1 < 2 ^ k.-1) = false.
{ apply/negbTE/negP => Hlt.
  have := exp_halfE. set A := (2 ^ k.-1)%N in Hlt *.
  set T := (2 ^ k)%N in Hlt Hm' *. by lia. }
rewrite Hcond.
have Hsub : ((2 ^ k - m.+1)%N%:Z - ((2 ^ k)%N)%:Z)%R = ssrint.Negz m.
{ set T := (2 ^ k)%N in Hm' *. by lia. }
by rewrite Hsub.
Qed.

End WordRoundTrip.

(* ================================================================== *)
(* 6. The encoding kernel: buffer values land, related, in the data   *)
(*    segment; [encode_int] is faithful on the whole signed window.   *)
(* ================================================================== *)

Lemma encode_int_neg (n : nat) :
  Merged.encode_int (BinInt.Z.opp (Z.of_nat n.+1)) = ssrint.Negz n.
Proof. by rewrite /= nat_of_pos_succ. Qed.

(* lia treats [Z.pow]/[expn] as opaque atoms, so [Z.pow 2 31] and the
   nat [2 ^ 31] must be bridged explicitly; proved by induction, never
   computed (unary [2 ^ 31] would hang the kernel) *)
Lemma expn_Zpow (n : nat) : Z.of_nat (2 ^ n) = BinInt.Z.pow 2 (Z.of_nat n).
Proof.
elim: n => [//|n IH].
rewrite expnS Nat2Z.inj_succ BinInt.Z.pow_succ_r; last by lia.
rewrite -IH.
by lia.
Qed.

Lemma expn_Zpow31 : Z.of_nat (2 ^ 31) = BinInt.Z.pow 2 31.
Proof. by rewrite expn_Zpow. Qed.

(* the composite the me machine observes values through gives back z *)
Lemma wrepr_encode_int (z : Z) :
  MDefs.int_fits z ->
  wrepr z (word.as_word (Merged.encode_int z) : mword mt).
Proof.
case=> Hlo Hhi.
rewrite /wrepr.
have Hk : 0 < word_size mt by rewrite word_size_mt.
have Hp1 : (word_size mt).-1 = 31 by rewrite word_size_mt.
have Hb := expn_Zpow31.
case: (ZArith_dec.Z_lt_le_dec z 0) => Hsgn.
-  case E: (BinInt.Z.to_nat (BinInt.Z.opp z)) => [|m]; first by lia.
  have Hz : z = BinInt.Z.opp (Z.of_nat m.+1) by lia.
  rewrite {}Hz {E} in Hlo Hsgn *.
  rewrite encode_int_neg.
  have Hm : m < 2 ^ (word_size mt).-1 by rewrite Hp1; lia.
  by rewrite (int_of_word_as_word_neg Hk Hm).
-  have Hz : z = Z.of_nat (BinInt.Z.to_nat z) by lia.
  rewrite {}Hz in Hhi *.
  rewrite encode_int_of_nat.
  have Hn : BinInt.Z.to_nat z < 2 ^ (word_size mt).-1 by rewrite Hp1; lia.
  by rewrite (int_of_word_as_word_pos Hk Hn).
Qed.

(* the me-side encoding of an in-buffer pointer IS flat base + offset *)
Lemma me_encode_val_ptr (pb : NMap {fmap Block.id -> nat + seq value})
    (c' b' : nat) (o' : Z) :
  BinInt.Z.le 0 o' ->
  me_encode_val pb (Ptr (c', b', o'))
  = word_of_nat (bl_base pb c' b' + BinInt.Z.to_nat o').
Proof.
move=> Ho'.
rewrite /me_encode_val.
have -> : o' = Z.of_nat (BinInt.Z.to_nat o') by lia.
rewrite encode_int_of_nat.
have -> : ssrint.intZmod.addz (ssrint.Posz (BinInt.Z.to_nat o'))
            (ssrint.Posz (bl_base pb c' b'))
          = ssrint.Posz (BinInt.Z.to_nat o' + bl_base pb c' b') by [].
rewrite /word_of_nat.
congr word.as_word; congr ssrint.Posz.
by lia.
Qed.

(* ================================================================== *)
(* 7. Little list inversions (Forall-free, List.In-free).             *)
(* ================================================================== *)

Lemma nth_error_nthE (A : Type) (l : seq A) n (v : A) :
  List.nth_error l n = Some v -> nth None [seq Some x | x <- l] n = Some v.
Proof.
elim: l n => [|a l IH] [|n] //=.
exact: IH.
Qed.

Lemma nth_error_repeat_inv (A : Type) (x : A) n o (y : A) :
  List.nth_error (List.repeat x n) o = Some y -> y = x /\ o < n.
Proof.
elim: n o => [|n IH] [|o] //=.
- by move=> [->].
- by move=> /IH [-> Ho].
Qed.

Lemma nth_error_map_inv (A B : Type) (f : A -> B) (l : seq A) n (y : B) :
  List.nth_error [seq f x | x <- l] n = Some y ->
  exists x, List.nth_error l n = Some x /\ y = f x.
Proof.
elim: l n => [|a l IH] [|n] //=.
- move=> [<-]. by exists a.
- exact: IH.
Qed.

(* ================================================================== *)
(* 8. The initial correspondence: [minj (amap0 pb)] holds between the *)
(*    two machines' initial memories, given the fit condition on the  *)
(*    initial buffer contents.                                        *)
(* ================================================================== *)

Section InitialCorrespondence.

Variable pb : NMap {fmap Block.id -> nat + seq value}.
Variable cmap : cmap_t.
Variable cde : @Merged.code mt.
Variable tp : Intermediate.program.
Hypothesis Hpb : Intermediate.prog_buffers tp = pb.
Hypothesis Hbound : size (linearize_bufs pb) + size cde < 2 ^ word_size mt.
Hypothesis Hwf : Intermediate.well_formed_program tp.

Local Notation tmem0 :=
  (Transitional.Memory.prepare_procedures_initial_memory tp).
Local Notation mmem0 :=
  (unionm (encode_code cde (size (initial_memory (mt := mt) pb)))
          (initial_memory (mt := mt) pb)).

(* -------- the T side: what [prepare_procedures_initial_memory] lays down *)

(* reserving procedure blocks only bumps [nextblock] *)
Lemma reserve_blocks_content m n :
  Transitional.Memory.content (Transitional.Memory.reserve_blocks m n).1
  = Transitional.Memory.content m.
Proof.
elim: n => [|n IH] //=.
by case E: (Transitional.Memory.reserve_blocks m n) IH => [m' bs] /= <-.
Qed.

Lemma reserve_blocks_next m n :
  Transitional.Memory.nextblock m
  <= Transitional.Memory.nextblock
       (Transitional.Memory.reserve_blocks m n).1.
Proof.
elim: n => [|n IH] //=.
case E: (Transitional.Memory.reserve_blocks m n) IH => [m' bs] /= IH.
by lia.
Qed.

(* the per-component initial memory IS a reserve-over-prealloc *)
Lemma t_init_shape C cm :
  tmem0 C = Some cm ->
  exists k0,
    cm = (Transitional.Memory.reserve_blocks
            (Transitional.Memory.prealloc
               (mapm (fun a => (C, a)) (odflt emptym (pb C)))) k0).1.
Proof.
rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
        /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
case: ifP => // HC /=.
rewrite /Transitional.Memory.reserve_component_blocks.
case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /= [<-] /=.
have -> : Cmem' = (Transitional.Memory.reserve_blocks
                     (Transitional.Memory.prealloc
                        (mapm (fun a => (C, a))
                           (odflt emptym (Intermediate.prog_buffers tp C))))
                     (length (elementsm (odflt emptym
                        (Intermediate.prog_procedures tp C))))).1
  by rewrite E.
exists (length (elementsm (odflt emptym
          (Intermediate.prog_procedures tp C)))).
by rewrite Hpb.
Qed.

Lemma fold_left_max_acc (l : seq nat) (acc : nat) :
  acc <= List.fold_left Nat.max l acc.
Proof.
elim: l acc => [|a l IH] acc //=.
apply: (leq_trans _ (IH (Nat.max acc a))).
by lia.
Qed.

Lemma fold_left_max_in (l : seq nat) (x0 b : nat) :
  b \in l -> b <= List.fold_left Nat.max l x0.
Proof.
elim: l x0 => [|a l IH] x0 //=.
rewrite inE => /orP[/eqP ->|Hb].
- apply: (leq_trans _ (fold_left_max_acc l (Nat.max x0 a))).
  by lia.
- exact: IH.
Qed.

Lemma t_init_getm C cm :
  tmem0 C = Some cm ->
  Transitional.Memory.content cm
  = mapm (fun x : Component.id * (nat + seq value) =>
            match x with
            | (c, inl n) => List.repeat (Transitional.tUndef, def_mem_tag c false) n
            | (c, inr l) => Transitional.to_tagged_block c l
            end)
      (mapm (fun a => (C, a)) (odflt emptym (pb C))).
Proof.
rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
        /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
case: ifP => // HC /=.
rewrite /Transitional.Memory.reserve_component_blocks.
case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /= [<-] /=.
have -> : Cmem' = (Transitional.Memory.reserve_blocks
                     (Transitional.Memory.prealloc
                        (mapm (fun a => (C, a))
                           (odflt emptym (Intermediate.prog_buffers tp C))))
                     (length (elementsm (odflt emptym
                        (Intermediate.prog_procedures tp C))))).1
  by rewrite E.
rewrite reserve_blocks_content /Transitional.Memory.prealloc /=.
by rewrite Hpb.
Qed.

(* every initial block id is below its component's next-block counter *)
Lemma t_init_next C cm b blk :
  tmem0 C = Some cm ->
  getm (Transitional.Memory.content cm) b = Some blk ->
  b < Transitional.Memory.nextblock cm.
Proof.
move=> Hcm Hb.
have [k0 Ecm] := t_init_shape Hcm.
have Hcont := t_init_getm Hcm.
have Hbin : b \in domm (odflt emptym (pb C)).
{ move: Hb; rewrite Hcont !mapmE.
  case E: (odflt emptym (pb C) b) => [bf|] //= _.
  by rewrite mem_domm E. }
rewrite Ecm.
apply: leq_trans (reserve_blocks_next _ _).
rewrite /Transitional.Memory.prealloc /= ltnS.
apply: fold_left_max_in.
by rewrite domm_map.
Qed.

(* every declared block EXISTS in the initial memory (for [aok_dom]) *)
Lemma t_init_exists C bmap b bf :
  pb C = Some bmap -> bmap b = Some bf ->
  exists cm blk,
    tmem0 C = Some cm /\
    getm (Transitional.Memory.content cm) b = Some blk.
Proof.
move=> HC Hb.
have HCdomm : C \in domm (Intermediate.prog_interface tp).
{ by rewrite (Intermediate.wfprog_defined_buffers Hwf) Hpb mem_domm HC. }
have [cm Hcm] : exists cm, tmem0 C = Some cm.
{ rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
          /Transitional.Memory.prepare_procedures_initial_memory_aux
          mkfmapfE HCdomm /=.
  by eexists. }
exists cm.
have Hcont := t_init_getm Hcm.
eexists.
split; first exact: Hcm.
by rewrite Hcont !mapmE HC /= Hb /=.
Qed.

Lemma t_init_block C cm b blk :
  tmem0 C = Some cm ->
  getm (Transitional.Memory.content cm) b = Some blk ->
  exists bmap bf,
    [/\ pb C = Some bmap, bmap b = Some bf
      & blk = match bf with
              | inl n => List.repeat (Transitional.tUndef, def_mem_tag C false) n
              | inr l => Transitional.to_tagged_block C l
              end].
Proof.
move=> Hcm.
rewrite (t_init_getm Hcm) !mapmE.
case Epb0: (odflt emptym (pb C) b) => [bf|] //= [<-].
have [bmap Hbmap] : exists bmap, pb C = Some bmap.
{ case E: (pb C) Epb0 => [bmap|] /=; first by eexists.
  by rewrite emptymE. }
exists bmap, bf; split=> //.
by move: Epb0; rewrite Hbmap /=.
Qed.

Lemma t_init_size C cm b blk :
  tmem0 C = Some cm ->
  getm (Transitional.Memory.content cm) b = Some blk ->
  size blk = size (linearize_buf pb C b).
Proof.
move=> Hcm Hb.
have [bmap [bf [Hbmap Hbf ->]]] := t_init_block Hcm Hb.
rewrite /linearize_buf Hbmap /= Hbf /=.
case: bf {Hbf} => [n|l] /=.
- by rewrite -!size_length !List.repeat_length.
- by rewrite /Transitional.to_tagged_block !size_map.
Qed.

Lemma t_init_cell C cm b blk o cell :
  tmem0 C = Some cm ->
  getm (Transitional.Memory.content cm) b = Some blk ->
  List.nth_error blk o = Some cell ->
  exists v,
    cell = (Transitional.MVal Other v, def_mem_tag C false) /\
    linearize_bufs pb (C, b, o) = Some (v, def_mem_tag C false).
Proof.
move=> Hcm Hb Hcell.
have [bmap [bf [Hbmap Hbf Hblk]]] := t_init_block Hcm Hb.
have Hlin : linearize_buf pb C b
            = match bf with
              | inl n => List.repeat (Undef, def_mem_tag C false) n
              | inr l => [seq (x, def_mem_tag C false) | x <- l]
              end.
{ by rewrite /linearize_buf Hbmap /= Hbf. }
case: bf Hblk Hlin Hbf => [n|l] Hblk Hlin Hbf.
-  subst blk.
  have [-> Ho] := nth_error_repeat_inv Hcell.
  exists Undef; split=> //.
  rewrite linearize_bufsE Hbmap Hbf.
  apply: nth_error_nthE.
  rewrite Hlin.
  apply: List.nth_error_repeat.
  exact/ltP.
-  subst blk.
  have [x [Hx ->]] := nth_error_map_inv Hcell.
  exists x; split=> //.
  rewrite linearize_bufsE Hbmap Hbf.
  apply: nth_error_nthE.
  rewrite Hlin.
  exact: (List.map_nth_error (fun v => (v, def_mem_tag C false)) _ _ Hx).
Qed.

(* -------- the me side: the same cell, at the flat address *)

Lemma me_init_cell C b o v :
  linearize_bufs pb (C, b, o) = Some (v, def_mem_tag C false) ->
  mmem0 (@word_of_nat (word_size mt) (nat_addr pb (C, b, o)))
  = Some {| vala := me_encode_val pb v; taga := def_mem_tag C false |}.
Proof.
move=> Hlin.
have Htot : size (linearize_bufs pb) < 2 ^ word_size mt.
{ apply: leq_ltn_trans Hbound. exact: leq_addr. }
have Hget := initial_memory_getm Htot Hlin.
apply: me_init_data_fetch => //.
by apply/dommP; eexists; exact: Hlin.
Qed.

(* -------- the theorem *)

Theorem minj_init :
  (forall c cm b blk o cell,
      tmem0 c = Some cm ->
      getm (Transitional.Memory.content cm) b = Some blk ->
      List.nth_error blk o = Some cell ->
      MDefs.value_fits tmem0 (Transitional.val cell.1)) ->
  minj pb cmap (amap0 pb) tmem0 mmem0.
Proof.
move=> Hfit.
constructor.
-  constructor.
  + move=> c bmap b bf Hc Hb. exact: amap0_static Hc Hb.
  + move=> c cm b blk Hc Hb.
    have [bmap [bf [Hbmap Hbf _]]] := t_init_block Hc Hb.
    exists (bl_base pb c b). exact: amap0_static Hbmap Hbf.
  +    move=> c1 b1 a1 n1 c2 b2 a2 n2 Hne Ha1 Hs1 Ha2 Hs2 _ _.
    move: Hs1 Hs2; rewrite /block_size.
    case E1: (tmem0 c1) => [cm1|] //; case E2: (tmem0 c2) => [cm2|] //.
    case F1: (getm (Transitional.Memory.content cm1) b1) => [blk1|] //=.
    case F2: (getm (Transitional.Memory.content cm2) b2) => [blk2|] //=.
    move=> [Hn1] [Hn2]; subst n1 n2.
    have [bm1 [bf1 [Hbm1 Hbf1 _]]] := t_init_block E1 F1.
    have [bm2 [bf2 [Hbm2 Hbf2 _]]] := t_init_block E2 F2.
    rewrite (t_init_size E1 F1) (t_init_size E2 F2).
    have [bmx1 [bfx1 [_ _ Hax1]]] := amap0_dom Ha1.
    have [bmx2 [bfx2 [_ _ Hax2]]] := amap0_dom Ha2.
    subst a1 a2.
    have Hcase : blk_before c2 b2 (c1, b1, 0) \/ blk_before c1 b1 (c2, b2, 0).
    { have Hne' : c1 <> c2 \/ b1 <> b2.
      { case: (altP (c1 =P c2)) => [Ec|Hc]; last by left; apply/eqP.
        right => Eb. by apply: Hne; rewrite Ec Eb. }
      rewrite /blk_before. by lia. }
    case: Hcase => Hbef.
    * left. exact: base_block_leq Hbm1 Hbf1 Hbef.
    * right. exact: base_block_leq Hbm2 Hbf2 Hbef.
  +    move=> c2 b2 a2 n2 Ha2 Hs2.
    have [bm2 [bf2 [Hbm2 Hbf2 Ea2]]] := amap0_dom Ha2.
    subst a2.
    move: Hs2; rewrite /block_size.
    case E2: (Transitional.Memory.prepare_procedures_initial_memory tp c2)
      => [cm2|] //.
    case F2: (Transitional.Memory.content cm2 b2) => [blk2|] //= [En2].
    subst n2.
    have Hsz2 := t_init_size E2 F2.
    have Htot := base_len_leq_total Hbm2 Hbf2.
    rewrite Hsz2. by lia.
  +    move=> c b a Ha.
    have [bm [bf [Hbm Hbf _]]] := amap0_dom Ha.
    have [cm [blk [Hcm Hblk]]] := t_init_exists Hbm Hbf.
    exists cm, blk. by split.
  +    move=> c cm b blk Hcm Hblk.
    exact: t_init_next Hcm Hblk.
-  move=> c cm b blk o cell a Hc Hb Hcell Ha.
  have [v [Hcellv Hlin]] := t_init_cell Hc Hb Hcell.
  have Hme := me_init_cell Hlin.
  have [bmx [bfx [_ _ Hax]]] := amap0_dom Ha. subst a.
  exists {| vala := me_encode_val pb v; taga := def_mem_tag c false |}.
  split.
  + have -> : bl_base pb c b + o = nat_addr pb (c, b, o)
      by rewrite /nat_addr addnC.
    exact: Hme.
  +    left.
    have Hvf := Hfit _ _ _ _ _ _ Hc Hb Hcell.
    rewrite Hcellv /= in Hvf *.
    split=> //=.
    case: v {Hcellv Hme} Hlin Hvf => [z|[[c' b'] o']|] Hlin Hvf.
    * apply: VRInt. exact: wrepr_encode_int.
    *      case: Hvf => Ho' [cm' [blk' [Hc' [Hb' _]]]].
      have [bm' [bf' [Hbm' Hbf' _]]] := t_init_block Hc' Hb'.
      apply: (@VRPtr _ c' b' o' _ (bl_base pb c' b')).
      -- exact: amap0_static Hbm' Hbf'.
      -- exact: Ho'.
      -- exact: me_encode_val_ptr Ho'.
    * exact: VRUndef.
-  move=> c cm b blk o cell a mc Hc Hb Hcell Ha Hmc.
  have [v [Hcellv Hlin]] := t_init_cell Hc Hb Hcell.
  have [bmx [bfx [_ _ Hax]]] := amap0_dom Ha. subst a.
  have Hme := me_init_cell Hlin.
  move: Hmc.
  have -> : bl_base pb c b + o = nat_addr pb (c, b, o)
    by rewrite /nat_addr addnC.
  rewrite Hme. by move=> [<-].
Qed.

End InitialCorrespondence.

(* ================================================================== *)
(* 9. LOAD preservation: a successful T load surfaces, related, at    *)
(*    the flat address.                                               *)
(* ================================================================== *)

Lemma minj_load (pb : NMap {fmap Block.id -> nat + seq value})
    (cmap : cmap_t)
    (amap : amap_t) (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom}) (ptr : Pointer.t) cell :
  minj pb cmap amap tmem mmem ->
  Transitional.Memory.load tmem ptr = Some cell ->
  exists a mc,
    [/\ addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a,
        mmem (word_of_nat (a + BinInt.Z.to_nat (Pointer.offset ptr))) = Some mc,
        cellrelw cmap amap cell mc
      & [/\ is_code (taga mc) = false,
            color (taga mc) = Pointer.component ptr
          & entry (taga mc) = None]].
Proof.
case: ptr => [[c b] o] Hinj.
rewrite /Transitional.Memory.load /=.
case Hc: (tmem c) => [cm|] //=.
rewrite /Transitional.Memory.load_b.
case Hb: (Transitional.Memory.content cm b) => [chunk|] //.
case Ho: (BinInt.Z.leb 0 o) => // Hcell.
have [a Ha] : exists a, addr_of amap c b = Some a
  by exact: (aok_total (mj_amap Hinj) Hc Hb).
have [mc [Hmc Hrel]] := mj_cell Hinj Hc Hb Hcell Ha.
have Hd := mj_data Hinj Hc Hb Hcell Ha Hmc.
by exists a, mc.
Qed.

(* ================================================================== *)
(* 10. STORE preservation: writing a related cell at its flat address *)
(*     preserves the injection; other cells are untouched because     *)
(*     in-range flat addresses are word-injective.                    *)
(* ================================================================== *)

Lemma list_upd_size (A : Type) (l : seq A) k (x : A) l' :
  list_upd l k x = Some l' -> size l' = size l.
Proof.
elim: l k l' => [|a l IH] [|k] l' //=.
- by move=> [<-].
- case E: (list_upd l k x) => [l''|] // [<-] /=.
  by rewrite (IH _ _ E).
Qed.

Lemma list_upd_lt (A : Type) (l : seq A) k (x : A) l' :
  list_upd l k x = Some l' -> k < size l.
Proof.
elim: l k l' => [|a l IH] [|k] l' //=.
case E: (list_upd l k x) => [l''|] // _.
by rewrite ltnS (IH _ _ E).
Qed.

(* nth_error's index bound, in ssr form *)
Lemma nth_error_lt (A : Type) (l : seq A) n (x : A) :
  List.nth_error l n = Some x -> n < size l.
Proof.
elim: l n => [|a l IH] [|n] //=.
exact: IH.
Qed.

Section StorePreservation.

Variable pb : NMap {fmap Block.id -> nat + seq value}.
Variable cmap : cmap_t.

(* in-range flat addresses of DIFFERENT blocks are different words *)
Lemma addr_sep_blocks (amap : amap_t) (tmem : Transitional.Memory.t)
    c1 b1 a1 n1 o1 c2 b2 a2 n2 o2 :
  amap_ok pb amap tmem ->
  (c1, b1) <> (c2, b2) ->
  addr_of amap c1 b1 = Some a1 -> block_size tmem c1 b1 = Some n1 ->
  o1 < n1 ->
  addr_of amap c2 b2 = Some a2 -> block_size tmem c2 b2 = Some n2 ->
  o2 < n2 ->
  (@word_of_nat (word_size mt) (a1 + o1)) <> word_of_nat (a2 + o2).
Proof.
move=> Haok Hne Ha1 Hs1 Ho1 Ha2 Hs2 Ho2 Ew.
have Hb1 := aok_bound Haok Ha1 Hs1.
have Hb2 := aok_bound Haok Ha2 Hs2.
have Hlt1 : a1 + o1 < 2 ^ word_size mt by lia.
have Hlt2 : a2 + o2 < 2 ^ word_size mt by lia.
have Hd := aok_disjoint Haok Hne Ha1 Hs1 Ha2 Hs2
             (leq_ltn_trans (leq0n _) Ho1) (leq_ltn_trans (leq0n _) Ho2).
have HE := won_inj Hlt1 Hlt2 Ew.
by case: Hd => H; lia.
Qed.

(* distinct in-range offsets of the SAME block are different words *)
Lemma addr_sep_offs (amap : amap_t) (tmem : Transitional.Memory.t)
    c b a n o1 o2 :
  amap_ok pb amap tmem ->
  addr_of amap c b = Some a -> block_size tmem c b = Some n ->
  o1 < n -> o2 < n -> o1 <> o2 ->
  (@word_of_nat (word_size mt) (a + o1)) <> word_of_nat (a + o2).
Proof.
move=> Haok Ha Hs Ho1 Ho2 Hne Ew.
have Hb := aok_bound Haok Ha Hs.
have Hlt1 : a + o1 < 2 ^ word_size mt by lia.
have Hlt2 : a + o2 < 2 ^ word_size mt by lia.
have := won_inj Hlt1 Hlt2 Ew. by lia.
Qed.

Theorem minj_store (amap : amap_t) (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom}) (ptr : Pointer.t)
    (cell' : Transitional.tvalue * mem_tag) (mc' : matom)
    (tmem' : Transitional.Memory.t) :
  minj pb cmap amap tmem mmem ->
  Transitional.Memory.store tmem ptr cell' = Some tmem' ->
  cellrelw cmap amap cell' mc' ->
  is_code cell'.2 = false ->
  color cell'.2 = Pointer.component ptr ->
  entry cell'.2 = None ->
  exists a,
    [/\ addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a
      & minj pb cmap amap tmem'
          (setm mmem
             (@word_of_nat (word_size mt)
                (a + BinInt.Z.to_nat (Pointer.offset ptr))) mc')].
Proof.
case: ptr => [[c b] o] /=.
move=> Hinj Hst Hrel Hic Hcol Hent.
move: Hst; rewrite /Transitional.Memory.store /=.
case Hc: (tmem c) => [cm|] //=.
rewrite /Transitional.Memory.store_b.
case Hb: (Transitional.Memory.content cm b) => [chunk|] //.
case Ho: (BinInt.Z.leb 0 o) => //.
case Hupd: (list_upd chunk (BinInt.Z.to_nat o) cell') => [chunk'|] //.
move=> [Etm].
set i := BinInt.Z.to_nat o in Hupd *.
have [a Ha] := aok_total (mj_amap Hinj) Hc Hb.
exists a; split=> //.
have Hlen := list_upd_size Hupd.
have Hi : i < size chunk := list_upd_lt Hupd.
have Hsz : block_size tmem c b = Some (size chunk)
  by rewrite /block_size Hc Hb.
have Etmem' : forall c2,
    tmem' c2 = if c2 == c
               then Some {| Transitional.Memory.content :=
                              setm (Transitional.Memory.content cm) b chunk';
                            Transitional.Memory.nextblock :=
                              Transitional.Memory.nextblock cm |}
               else tmem c2.
{ move=> c2. by rewrite -Etm setmE. }
have Hbs : forall c2 b2, block_size tmem' c2 b2 = block_size tmem c2 b2.
{ move=> c2 b2. rewrite /block_size Etmem'.
  case: (altP (c2 =P c)) => [->|Hne]; last by [].
  rewrite Hc /= setmE.
  case: (altP (b2 =P b)) => [->|Hne2]; last by [].
  by rewrite Hb /= Hlen. }
have Hcontent : forall c2 cm2 b2 blk2,
    tmem' c2 = Some cm2 ->
    Transitional.Memory.content cm2 b2 = Some blk2 ->
    (c2 = c /\ b2 = b /\ blk2 = chunk')
    \/ (~ (c2 = c /\ b2 = b)
        /\ exists cm0, tmem c2 = Some cm0
             /\ Transitional.Memory.content cm0 b2 = Some blk2).
{ move=> c2 cm2 b2 blk2.
  rewrite Etmem'.
  case: (altP (c2 =P c)) => [->|Hne].
  - move=> [<-] /=. rewrite setmE.
    case: (altP (b2 =P b)) => [->|Hne2].
    + move=> [<-]. by left.
    + move=> Hg. right. split.
      * by case=> _ E; move/eqP: Hne2; rewrite E.
      * by exists cm.
  - move=> Hc2 Hg. right. split.
    + by case=> E _; move/eqP: Hne; rewrite E.
    + by exists cm2. }
constructor.
-  constructor.
  + exact: (aok_static (mj_amap Hinj)).
  + move=> c2 cm2 b2 blk2 Hc2 Hb2.
    case: (Hcontent _ _ _ _ Hc2 Hb2) => [[-> [-> _]]|[_ [cm0 [Hc0 Hb0]]]].
    * by exists a.
    * exact: (aok_total (mj_amap Hinj) Hc0 Hb0).
  + move=> c1 b1 a1 n1 c2 b2 a2 n2 Hne Ha1 Hs1 Ha2 Hs2 Hp1 Hp2.
    rewrite !Hbs in Hs1 Hs2.
    exact: (aok_disjoint (mj_amap Hinj) Hne Ha1 Hs1 Ha2 Hs2 Hp1 Hp2).
  + move=> c2 b2 a2 n2 Ha2 Hs2.
    rewrite Hbs in Hs2.
    exact: (aok_bound (mj_amap Hinj) Ha2 Hs2).
  +    move=> c2 b2 a2 Ha2.
    have [cm0 [blk0 [Hc0 Hb0]]] := aok_dom (mj_amap Hinj) Ha2.
    rewrite Etmem'.
    case: (altP (c2 =P c)) => [Ec2|Hne2].
    * subst c2.
      have Ecm0 : cm0 = cm by move: Hc0; rewrite Hc => -[].
      subst cm0.
      case: (altP (b2 =P b)) => [Eb2|Hneb].
      -- subst b2.
         eexists. eexists.
         split; first by [].
         by rewrite /= setmE eqxx.
      -- eexists. eexists.
         split; first by [].
         rewrite /= setmE (negbTE Hneb). exact: Hb0.
    * exists cm0, blk0. by split.
  +    move=> c2 cm2 b2 blk2.
    rewrite Etmem'.
    case: (altP (c2 =P c)) => [Ec2|Hne2].
    * move=> [<-] /=.
      rewrite setmE.
      case: (altP (b2 =P b)) => [Eb2|Hneb].
      -- move=> _. subst b2.
         exact: (aok_next (mj_amap Hinj) Hc Hb).
      -- move=> Hb2. exact: (aok_next (mj_amap Hinj) Hc Hb2).
    * move=> Hc2 Hb2. exact: (aok_next (mj_amap Hinj) Hc2 Hb2).
-  move=> c2 cm2 b2 blk2 o2 cell2 a2 Hc2 Hb2 Hnth Ha2.
  case: (Hcontent _ _ _ _ Hc2 Hb2) => [[Ec [Eb Eblk]]|[Hne [cm0 [Hc0 Hb0]]]].
  + subst c2 b2 blk2.
    have Ea2 : a2 = a by move: Ha2; rewrite Ha => -[].
    subst a2.
    case: (altP (o2 =P i)) => [Eo|Hneo].
    * rewrite Eo (list_upd_nth_error_same Hupd) in Hnth.
      case: Hnth => <-.
      exists mc'. split=> //.
      by rewrite Eo setmE eqxx.
    * have Hne2 : o2 <> i by move: Hneo => /eqP.
      have Hne2' : i <> o2 by move=> E; apply: Hne2; rewrite E.
      have Hnth' : List.nth_error chunk o2 = Some cell2.
      { by rewrite -(list_upd_nth_error_other Hupd Hne2'). }
      have [mc [Hmc Hrelmc]] := mj_cell Hinj Hc Hb Hnth' Ha.
      exists mc. split=> //.
      rewrite setmE.
      have Ho2 : o2 < size chunk := nth_error_lt Hnth'.
      case: (altP ((@word_of_nat (word_size mt) (a + o2))
                   =P word_of_nat (a + i))) => [Ew|_]; last exact: Hmc.
      exfalso.
      exact: (addr_sep_offs (mj_amap Hinj) Ha Hsz Ho2 Hi Hne2 Ew).
  + have [mc [Hmc Hrelmc]] := mj_cell Hinj Hc0 Hb0 Hnth Ha2.
    exists mc. split=> //.
    rewrite setmE.
    have Ho2 : o2 < size blk2 := nth_error_lt Hnth.
    have Hs2 : block_size tmem c2 b2 = Some (size blk2)
      by rewrite /block_size Hc0 Hb0.
    case: (altP ((@word_of_nat (word_size mt) (a2 + o2))
                 =P word_of_nat (a + i))) => [Ew|_]; last exact: Hmc.
    exfalso.
    have Hnepair : (c2, b2) <> (c, b).
    { move=> [E1 E2]. apply: Hne. exact: (conj E1 E2). }
    exact: (addr_sep_blocks (mj_amap Hinj) Hnepair Ha2 Hs2 Ho2 Ha Hsz Hi Ew).
-  move=> c2 cm2 b2 blk2 o2 cell2 a2 mc2 Hc2 Hb2 Hnth Ha2 Hmc2.
  case: (Hcontent _ _ _ _ Hc2 Hb2) => [[Ec [Eb Eblk]]|[Hne [cm0 [Hc0 Hb0]]]].
  + subst c2 b2 blk2.
    have Ea2 : a2 = a by move: Ha2; rewrite Ha => -[].
    subst a2.
    case: (altP (o2 =P i)) => [Eo|Hneo].
    * subst o2.
      move: Hmc2. rewrite setmE eqxx => -[<-].
      case: Hrel => [[_ Etag _]|[_ [Ecol Eent Eic]]];
        [ by rewrite Etag Hic Hcol Hent
        | by rewrite Eic Ecol Eent Hic Hcol Hent ].
    * have Hne2 : o2 <> i by move: Hneo => /eqP.
      have Hne2' : i <> o2 by move=> E; apply: Hne2; rewrite E.
      have Hnth' : List.nth_error chunk o2 = Some cell2.
      { by rewrite -(list_upd_nth_error_other Hupd Hne2'). }
      have Ho2 : o2 < size chunk := nth_error_lt Hnth'.
      move: Hmc2. rewrite setmE.
      case: (altP ((@word_of_nat (word_size mt) (a + o2))
                   =P word_of_nat (a + i))) => [Ew|_].
      -- exfalso.
         exact: (addr_sep_offs (mj_amap Hinj) Ha Hsz Ho2 Hi Hne2 Ew).
      -- move=> Hmc2.
         exact: (mj_data Hinj Hc Hb Hnth' Ha Hmc2).
  + have Ho2 : o2 < size blk2 := nth_error_lt Hnth.
    have Hs2 : block_size tmem c2 b2 = Some (size blk2)
      by rewrite /block_size Hc0 Hb0.
    move: Hmc2. rewrite setmE.
    case: (altP ((@word_of_nat (word_size mt) (a2 + o2))
                 =P word_of_nat (a + i))) => [Ew|_].
    * exfalso.
      have Hnepair : (c2, b2) <> (c, b).
      { move=> [E1 E2]. apply: Hne. exact: (conj E1 E2). }
      exact: (addr_sep_blocks (mj_amap Hinj) Hnepair Ha2 Hs2 Ho2 Ha Hsz Hi Ew).
    * move=> Hmc2.
      exact: (mj_data Hinj Hc0 Hb0 Hnth Ha2 Hmc2).
Qed.

End StorePreservation.

(* ================================================================== *)
(* 11. ALLOC preparation: the address-map extension is monotone: the  *)
(*     fresh block id is unmapped, so existing relation facts          *)
(*     transport verbatim.                                            *)
(* ================================================================== *)

Definition amap_upd (amap : amap_t) (c b base : nat) : amap_t :=
  setm amap c (setm (odflt emptym (amap c)) b base).

Lemma addr_of_upd_same amap c b base :
  addr_of (amap_upd amap c b base) c b = Some base.
Proof.
by rewrite /addr_of /amap_upd setmE eqxx /= setmE eqxx.
Qed.

Lemma addr_of_upd_other amap c b base c0 b0 :
  (c0, b0) <> (c, b) ->
  addr_of (amap_upd amap c b base) c0 b0 = addr_of amap c0 b0.
Proof.
move=> Hne.
rewrite /addr_of /amap_upd setmE.
case: (altP (c0 =P c)) => [Ec|//] /=.
subst c0.
rewrite setmE.
case: (altP (b0 =P b)) => [Eb|Hneb] /=.
- subst b0. by case: Hne.
- by case: (amap c).
Qed.

Lemma vrel_upd amap c b base v w :
  addr_of amap c b = None ->
  vrel amap v w -> vrel (amap_upd amap c b base) v w.
Proof.
move=> Hfresh Hv.
case: Hv => [z w' Hw|cp bp op w' a Ha Hle Hw|w'].
- exact: VRInt.
- apply: (@VRPtr _ _ _ _ _ a) => //.
  rewrite addr_of_upd_other //.
  move=> [Ec Eb]. subst cp bp. by rewrite Hfresh in Ha.
- exact: VRUndef.
Qed.

Lemma tvrel_upd (cmap : cmap_t) amap c b base tv w :
  addr_of amap c b = None ->
  tvrel cmap amap tv w -> tvrel cmap (amap_upd amap c b base) tv w.
Proof.
move=> Hfresh.
rewrite /tvrel.
case: (Transitional.tvtag tv) => //.
exact: vrel_upd.
Qed.

Lemma cellrel_upd (cmap : cmap_t) amap c b base tc mc :
  addr_of amap c b = None ->
  cellrel cmap amap tc mc -> cellrel cmap (amap_upd amap c b base) tc mc.
Proof.
move=> Hfresh [H1 H2 H3].
split=> //.
exact: tvrel_upd H1.
Qed.

Section AllocPreservation.

Variable pb : NMap {fmap Block.id -> nat + seq value}.
Variable cmap : cmap_t.

(* -------- list toolbox -------- *)

Lemma nth_error_lt_ex (A : Type) (l : seq A) o :
  o < size l -> exists x, List.nth_error l o = Some x.
Proof.
elim: l o => [|a l IH] [|o] //=.
- by exists a.
- exact: IH.
Qed.

Lemma repeat_nth (A : Type) (x : A) n o :
  o < n -> List.nth_error (List.repeat x n) o = Some x.
Proof.
elim: n o => [|n IH] [|o] //=.
exact: IH.
Qed.

Lemma size_repeat (A : Type) (x : A) n : size (List.repeat x n) = n.
Proof. by elim: n => //= n ->. Qed.

(* looking up the flat fresh segment *)
Lemma mkfmap_seg_lookup (x : atom (mword mt) mem_tag) (base st n o : nat) :
  base + (st + n) <= 2 ^ word_size mt ->
  st <= o < st + n ->
  mkfmap [seq (@word_of_nat (word_size mt) (base + o'), x) | o' <- iota st n]
    (@word_of_nat (word_size mt) (base + o)) = Some x.
Proof.
elim: n st => [|n IH] st Hbnd /andP[Ho1 Ho2].
- by lia.
- rewrite /= setmE.
  case: (altP (o =P st)) => [Eo|Hneo].
  + subst o. by rewrite eqxx.
  + have Hb1 : base + o < 2 ^ word_size mt by lia.
    have Hb2 : base + st < 2 ^ word_size mt by lia.
    have Hne : (@word_of_nat (word_size mt) (base + o)
                == word_of_nat (base + st)) = false.
    { apply/negbTE; apply/eqP => E.
      have := won_inj Hb1 Hb2 E.
      move/eqP: Hneo => Hneo. by lia. }
    rewrite Hne.
    apply: IH.
    * by lia.
    * apply/andP; split; by lia.
Qed.

(* -------- the theorem -------- *)

Theorem minj_alloc (amap : amap_t) (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom}) (c : Component.id)
    (sz : nat) (tmem' : Transitional.Memory.t) (tptr : Pointer.t)
    (newbase : nat) :
  minj pb cmap amap tmem mmem ->
  Transitional.Memory.alloc tmem c sz = Some (tmem', tptr) ->
  0 < sz ->
  newbase + sz <= 2 ^ word_size mt ->
  (forall o, o < sz ->
     mmem (@word_of_nat (word_size mt) (newbase + o)) = None) ->
  minj pb cmap (amap_upd amap c (Pointer.block tptr) newbase) tmem'
    (unionm mmem
       (mkfmap [seq (@word_of_nat (word_size mt) (newbase + o),
                     Atom (word.as_word 0) (def_mem_tag c false))
               | o <- iota 0 sz])).
Proof.
move=> Hinj Hal Hsz Hbnd Hnone.
move: Hal; rewrite /Transitional.Memory.alloc.
case Hc: (tmem c) => [cm|] //=.
move=> [Etm Etp].
subst tptr; rewrite /=.
set b := Transitional.Memory.nextblock cm.
set chunk := List.repeat (Transitional.tUndef, def_mem_tag c false) sz.
set cm' := {| Transitional.Memory.content :=
                setm (Transitional.Memory.content cm) b chunk;
              Transitional.Memory.nextblock := 1 + b |}.
set mnew := mkfmap
  [seq (@word_of_nat (word_size mt) (newbase + o),
        Atom (word.as_word 0) (def_mem_tag c false)) | o <- iota 0 sz].
have Hfresh : addr_of amap c b = None.
{ case E: (addr_of amap c b) => [a|] //.
  have [cm0 [blk0 [Hc0 Hb0]]] := aok_dom (mj_amap Hinj) E.
  move: Hc0; rewrite Hc => -[Ecm0]; subst cm0.
  have Hlt := aok_next (mj_amap Hinj) Hc Hb0.
  by rewrite ltnn in Hlt. }
have Etmem' : forall c2,
    tmem' c2 = if c2 == c then Some cm' else tmem c2.
{ move=> c2. by rewrite -Etm setmE. }
have Hszchunk : size chunk = sz by rewrite /chunk size_repeat.
have Hcontent : forall c2 cm2 b2 blk2,
    tmem' c2 = Some cm2 ->
    Transitional.Memory.content cm2 b2 = Some blk2 ->
    (c2 = c /\ b2 = b /\ blk2 = chunk)
    \/ ((c2, b2) <> (c, b)
        /\ exists cm0, tmem c2 = Some cm0
             /\ Transitional.Memory.content cm0 b2 = Some blk2).
{ move=> c2 cm2 b2 blk2.
  rewrite Etmem'.
  case: (altP (c2 =P c)) => [->|Hne].
  - move=> [<-] /=. rewrite setmE.
    case: (altP (b2 =P b)) => [->|Hne2].
    + move=> [<-]. by left.
    + move=> Hg. right. split.
      * move=> E.
        have E2 : b2 = b by case: E.
        by rewrite E2 eqxx in Hne2.
      * by exists cm.
  - move=> Hc2 Hg. right. split.
    + move=> E.
      have E1 : c2 = c by case: E.
      by rewrite E1 eqxx in Hne.
    + by exists cm2. }
have Hbs : forall c2 b2,
    block_size tmem' c2 b2
    = if (c2 == c) && (b2 == b) then Some sz else block_size tmem c2 b2.
{ move=> c2 b2. rewrite /block_size Etmem'.
  case: (altP (c2 =P c)) => [->|Hne].
  - rewrite /= setmE.
    case: (altP (b2 =P b)) => [_|_].
    + by rewrite /= Hszchunk.
    + by rewrite Hc.
  - by []. }have Hme_new : forall o, o < sz ->
    unionm mmem mnew (@word_of_nat (word_size mt) (newbase + o))
    = Some (Atom (word.as_word 0) (def_mem_tag c false)).
{ move=> o Ho.
  rewrite unionmE (Hnone _ Ho) /=.
  by apply: mkfmap_seg_lookup => //. }
have Hme_old : forall w mc, mmem w = Some mc -> unionm mmem mnew w = Some mc.
{ move=> w mc Hw. by rewrite unionmE Hw /=. }have Hsep : forall c2 b2 a2 n2,
    (c2, b2) <> (c, b) ->
    addr_of amap c2 b2 = Some a2 -> block_size tmem c2 b2 = Some n2 ->
    0 < n2 ->
    (newbase + sz <= a2) \/ (a2 + n2 <= newbase).
{ move=> c2 b2 a2 n2 Hne Ha2 Hs2 Hn2.
  case: (leqP (newbase + sz) a2) => [|Hlt1]; first by left.
  case: (leqP (a2 + n2) newbase) => [|Hlt2]; first by right.
  exfalso.
  set x := maxn newbase a2.
  have Ho : x - newbase < sz by rewrite /x; lia.
  have Ho' : x - a2 < n2 by rewrite /x; lia.
  move: Hs2; rewrite /block_size.
  case Hc2: (tmem c2) => [cm2|] //.
  case Hb2: (Transitional.Memory.content cm2 b2) => [blk2|] //= [En2].
  have Hox : x - a2 < size blk2 by lia.
  have [cell Hcell] := nth_error_lt_ex Hox.
  have [mc [Hmc _]] := mj_cell Hinj Hc2 Hb2 Hcell Ha2.
  have Ex : a2 + (x - a2) = newbase + (x - newbase) by rewrite /x; lia.
  move: Hmc; rewrite Ex (Hnone _ Ho).
  by []. }
constructor.
-  constructor.
  +    move=> c0 bmap b0 bf Hc0 Hb0.
    have Hne : (c0, b0) <> (c, b).
    { move=> [E1 E2]; subst c0 b0.
      by rewrite (aok_static (mj_amap Hinj) Hc0 Hb0) in Hfresh. }
    rewrite addr_of_upd_other //.
    exact: (aok_static (mj_amap Hinj) Hc0 Hb0).
  +    move=> c2 cm2 b2 blk2 Hc2 Hb2.
    case: (Hcontent _ _ _ _ Hc2 Hb2) => [[-> [-> _]]|[Hne [cm0 [Hc0 Hb0]]]].
    * exists newbase. exact: addr_of_upd_same.
    * have [a0 Ha0] := aok_total (mj_amap Hinj) Hc0 Hb0.
      exists a0. by rewrite addr_of_upd_other.
  +    move=> c1 b1 a1 n1 c2 b2 a2 n2 Hne Ha1 Hs1 Ha2 Hs2 Hp1 Hp2.
    case E1: ((c1 == c) && (b1 == b)); case E2: ((c2 == c) && (b2 == b));
      rewrite Hbs E1 /= in Hs1; rewrite Hbs E2 /= in Hs2.
    *      move: E1 E2 => /andP[/eqP E1a /eqP E1b] /andP[/eqP E2a /eqP E2b].
      exfalso. apply: Hne. by rewrite E1a E1b E2a E2b.
    *      case: Hs1 => En1; subst n1.
      move: E1 => /andP[/eqP Ec1 /eqP Eb1]; subst c1 b1.
      move: Ha1; rewrite addr_of_upd_same => -[Ea1]; subst a1.
      have Hne2 : (c2, b2) <> (c, b).
      { move=> E.
        have EcX : c2 = c by case: E.
        have EbX : b2 = b by case: E.
        move: E2. by rewrite EcX EbX !eqxx. }
      move: Ha2; rewrite addr_of_upd_other // => Ha2.
      exact: Hsep Hne2 Ha2 Hs2 Hp2.
    *      case: Hs2 => En2; subst n2.
      move: E2 => /andP[/eqP Ec2 /eqP Eb2]; subst c2 b2.
      move: Ha2; rewrite addr_of_upd_same => -[Ea2]; subst a2.
      have Hne1 : (c1, b1) <> (c, b).
      { move=> E.
        have EcX : c1 = c by case: E.
        have EbX : b1 = b by case: E.
        move: E1. by rewrite EcX EbX !eqxx. }
      move: Ha1; rewrite addr_of_upd_other // => Ha1.
      case: (Hsep _ _ _ _ Hne1 Ha1 Hs1 Hp1) => H.
      -- by right.
      -- by left.
    *      have Hne1 : (c1, b1) <> (c, b).
      { move=> E.
        have EcX : c1 = c by case: E.
        have EbX : b1 = b by case: E.
        move: E1. by rewrite EcX EbX !eqxx. }
      have Hne2 : (c2, b2) <> (c, b).
      { move=> E.
        have EcX : c2 = c by case: E.
        have EbX : b2 = b by case: E.
        move: E2. by rewrite EcX EbX !eqxx. }
      move: Ha1; rewrite addr_of_upd_other // => Ha1.
      move: Ha2; rewrite addr_of_upd_other // => Ha2.
      exact: (aok_disjoint (mj_amap Hinj) Hne Ha1 Hs1 Ha2 Hs2 Hp1 Hp2).
  +    move=> c2 b2 a2 n2 Ha2 Hs2.
    case E2: ((c2 == c) && (b2 == b)); rewrite Hbs E2 /= in Hs2.
    * case: Hs2 => En2; subst n2.
      move: E2 => /andP[/eqP Ec2 /eqP Eb2]; subst c2 b2.
      move: Ha2; rewrite addr_of_upd_same => -[Ea2]; subst a2.
      exact: Hbnd.
    * have Hne2 : (c2, b2) <> (c, b).
      { move=> E.
        have EcX : c2 = c by case: E.
        have EbX : b2 = b by case: E.
        move: E2. by rewrite EcX EbX !eqxx. }
      move: Ha2; rewrite addr_of_upd_other // => Ha2.
      exact: (aok_bound (mj_amap Hinj) Ha2 Hs2).
  +    move=> c2 b2 a2 Ha2.
    case: (altP ((c2, b2) =P (c, b))) => [E|Hne2].
    * case: E => -> ->.
      exists cm', chunk.
      split; first by rewrite Etmem' eqxx.
      by rewrite /= setmE eqxx.
    * have Hne2' : (c2, b2) <> (c, b) by move/eqP: Hne2.
      move: Ha2; rewrite addr_of_upd_other // => Ha2.
      have [cm0 [blk0 [Hc0 Hb0]]] := aok_dom (mj_amap Hinj) Ha2.
      rewrite Etmem'.
      case: (altP (c2 =P c)) => [Ec2|Hnec].
      -- subst c2.
         move: Hc0; rewrite Hc => -[Ecm0]; subst cm0.
         eexists. eexists.
         split; first by [].
         rewrite /= setmE.
         case: (altP (b2 =P b)) => [Eb2|Hneb].
         ++ subst b2. by case: Hne2'.
         ++ exact: Hb0.
      -- exists cm0, blk0. by split.
  +    move=> c2 cm2 b2 blk2.
    rewrite Etmem'.
    case: (altP (c2 =P c)) => [Ec2|Hnec].
    * move=> [<-] /=.
      rewrite setmE.
      case: (altP (b2 =P b)) => [Eb2|Hneb].
      -- move=> _. subst b2. by lia.
      -- move=> Hb2.
         have := aok_next (mj_amap Hinj) Hc Hb2.
         by lia.
    * move=> Hc2 Hb2. exact: (aok_next (mj_amap Hinj) Hc2 Hb2).
-  move=> c2 cm2 b2 blk2 o2 cell2 a2 Hc2 Hb2 Hnth Ha2.
  case: (Hcontent _ _ _ _ Hc2 Hb2) => [[Ec2 [Eb2 Eblk]]|[Hne [cm0 [Hc0 Hb0]]]].
  + subst c2 b2 blk2.
    move: Ha2; rewrite addr_of_upd_same => -[Ea2]; subst a2.
    have Ho2 : o2 < sz.
    { have := nth_error_lt Hnth. by rewrite Hszchunk. }
    move: Hnth; rewrite /chunk (repeat_nth _ Ho2) => -[Ecell]; subst cell2.
    exists (Atom (word.as_word 0) (def_mem_tag c false)).
    split; first exact: Hme_new.
    left. split=> //=.
    exact: VRUndef.
  + move: Ha2; rewrite addr_of_upd_other // => Ha2.
    have [mc [Hmc Hrel]] := mj_cell Hinj Hc0 Hb0 Hnth Ha2.
    exists mc.
    split; first exact: Hme_old.
    case: Hrel => [Hrel|Hrel].
    * left. exact: cellrel_upd Hfresh Hrel.
    * by right.
-  move=> c2 cm2 b2 blk2 o2 cell2 a2 mc Hc2 Hb2 Hnth Ha2 Hmc.
  case: (Hcontent _ _ _ _ Hc2 Hb2) => [[Ec2 [Eb2 Eblk]]|[Hne [cm0 [Hc0 Hb0]]]].
  + subst c2 b2 blk2.
    move: Ha2; rewrite addr_of_upd_same => -[Ea2]; subst a2.
    have Ho2 : o2 < sz.
    { have := nth_error_lt Hnth. by rewrite Hszchunk. }
    move: Hmc; rewrite (Hme_new _ Ho2) => -[<-].
    by [].
  + move: Ha2; rewrite addr_of_upd_other // => Ha2.
    have [mc0 [Hmc0 _]] := mj_cell Hinj Hc0 Hb0 Hnth Ha2.
    move: Hmc; rewrite (Hme_old _ _ Hmc0) => -[Emc]; subst mc0.
    exact: (mj_data Hinj Hc0 Hb0 Hnth Ha2 Hmc0).
Qed.

End AllocPreservation.

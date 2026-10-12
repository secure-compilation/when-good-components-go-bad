(* The static memory correspondence: the me machine's initial data
   segment (buffers laid flat at [nat_addr] addresses) matches the
   Intermediate machine's preallocated buffers.  Provides the fetch
   ([initial_memory_getm]) and load-correspondence lemmas, with value
   relation [val_rel] (Int ↦ encoded int, static Ptr ↦ flat address,
   Undef ↦ anything). *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require MicroPolicies.Recomposition.BufferShape.
Require Import T2M.MPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the me-side encoding of an initial buffer value (static pointers
   concretized at their flat base address) *)
Definition me_encode_val (pb : NMap {fmap Block.id -> nat + seq value})
    (v : value) : mword mt :=
  match v with
  | Int z => word.as_word (encode_int z)
  | Ptr ptr =>
      word.as_word
        (match ptr with
         | (c', b', o') =>
             ssrint.intZmod.addz (encode_int o')
               (ssrint.Posz (bl_base pb c' b'))
         end)
  | Undef => word.as_word (ssrint.Posz 0)
  end.

(* the value relation of the simulation (static part): Undef is free *)
Definition val_rel (pb : NMap {fmap Block.id -> nat + seq value})
    (v : value) (w : mword mt) : Prop :=
  match v with
  | Undef => True
  | _ => w = me_encode_val pb v
  end.

(* ==================== the pointwise data-segment fetch ==================== *)

Lemma initial_memory_getm (pb : NMap {fmap Block.id -> nat + seq value})
    (c b o : nat) (pairv : value * mem_tag) :
  size (linearize_bufs pb) < 2 ^ word_size mt ->
  linearize_bufs pb (c, b, o) = Some pairv ->
  initial_memory (mt := mt) pb
    (@word_of_nat (word_size mt) (nat_addr pb (c, b, o)))
  = Some {| vala := me_encode_val pb pairv.1; taga := pairv.2 |}.
Proof.
move=> Hbound Hget.
rewrite /initial_memory; cbv zeta.
set F := (X in Tmp.mapk X _).
set ENC := (X in mapm X _).
have EF : forall k : nat * nat * nat,
    F k = @word_of_nat (word_size mt) (nat_addr pb k).
{ move=> [[c0 b0] o0]. rewrite /F /=.
  rewrite encode_int_of_nat /=.
  congr word.as_word. congr ssrint.Posz. congr addn.
  rewrite size_length. exact: (base_filterm pb c0 b0). }have EENC : forall x : value * mem_tag,
    ENC x = {| vala := me_encode_val pb x.1; taga := x.2 |}.
{ move=> [v tg]. rewrite /ENC /=.
  case: v => [z|ptr|] //=.
  case: ptr => [[c0 b0] o0] /=.
  congr Atom.
  congr word.as_word. congr ssrint.intZmod.addz. congr ssrint.Posz.
  rewrite size_length. exact: (base_filterm pb c0 b0). }
rewrite -(EF (c, b, o)) -(EENC pairv).
apply: mapk_Some_inv.
-  move=> x y. rewrite !domm_map => Hx Hy Hxy.
  rewrite !EF in Hxy.
  apply: (nat_addr_inj Hx Hy).
  apply: won_inj Hxy.
  + exact: (ltn_trans (nat_addr_lt Hx) Hbound).
  + exact: (ltn_trans (nat_addr_lt Hy) Hbound).
- by rewrite mapmE Hget.
Qed.

(* ==================== the initial-load correspondence ==================== *)

Lemma initial_load_rel (pb : NMap {fmap Block.id -> nat + seq value})
    (C : Component.id) (bmap : {fmap Block.id -> nat + seq value})
    (b : Block.id) (o : Z) (v : value) :
  size (linearize_bufs pb) < 2 ^ word_size mt ->
  pb C = Some bmap ->
  ComponentMemory.load (ComponentMemory.prealloc bmap) b o = Some v ->
  exists a : matom,
    [/\ initial_memory (mt := mt) pb
          (@word_of_nat (word_size mt) (nat_addr pb (C, b, Z.to_nat o)))
        = Some a,
        taga a = LRC.def_mem_tag C false
      & val_rel pb v (vala a)].
Proof.
move=> Hbound HC.
rewrite ComponentMemory.load_prealloc.
case Ho: (0 <=? o)%Z => //.
case Eb: (bmap b) => [[sz|chunk]|] //.
-  case Hlt: (o <? Z.of_nat sz)%Z => //.
  move=> [Ev]; subst v.
  have Hcell : linearize_bufs pb (C, b, Z.to_nat o)
               = Some (Undef, LRC.def_mem_tag C false).
  { rewrite linearize_bufsE HC Eb.
    have -> : linearize_buf pb C b
              = repeat (Undef, LRC.def_mem_tag C false) sz
      by rewrite /linearize_buf HC /= Eb.
    apply: nth_error_nth_map_Some.
    apply: List.nth_error_repeat.
    move/Z.leb_le: Ho => Ho. move/Z.ltb_lt: Hlt => Hlt.
    by lia. }
  have Hm := initial_memory_getm Hbound Hcell.
  eexists. split.
  + exact: Hm.
  + by [].
  + by [].
-  move=> Hv.
  have Hcell : linearize_bufs pb (C, b, Z.to_nat o)
               = Some (v, LRC.def_mem_tag C false).
  { rewrite linearize_bufsE HC Eb.
    have -> : linearize_buf pb C b
              = [seq (x, LRC.def_mem_tag C false) | x <- chunk]
      by rewrite /linearize_buf HC /= Eb.
    apply: nth_error_nth_map_Some.
    apply: map_nth_error_seq.
    exact: Hv. }
  have Hm := initial_memory_getm Hbound Hcell.
  eexists. split.
  + exact: Hm.
  + by [].
  + by case: (v).
Qed.

(* ==================== glue to the I-machine's initial memory ==================== *)

Lemma prepare_initial_memoryE (p : Intermediate.program) (C : Component.id) :
  Intermediate.prepare_initial_memory p C
  = if C \in domm (Intermediate.prog_interface p)
    then Some (ComponentMemory.prealloc
                 (odflt emptym (Intermediate.prog_buffers p C)))
    else None.
Proof.
by rewrite /Intermediate.prepare_initial_memory
           /Intermediate.alloc_static_buffers mkfmapfE.
Qed.

(* an Intermediate load from the initial static memory is matched by a
   related me value at the injected flat address *)
Lemma prepare_load_rel (p : Intermediate.program)
    (C : Component.id) (b : Block.id) (o : Z) (v : value) :
  size (linearize_bufs (Intermediate.prog_buffers p)) < 2 ^ word_size mt ->
  Memory.load (Intermediate.prepare_initial_memory p) (C, b, o) = Some v ->
  exists a : matom,
    [/\ initial_memory (mt := mt) (Intermediate.prog_buffers p)
          (@word_of_nat (word_size mt)
             (nat_addr (Intermediate.prog_buffers p) (C, b, Z.to_nat o)))
        = Some a,
        taga a = LRC.def_mem_tag C false
      & val_rel (Intermediate.prog_buffers p) v (vala a)].
Proof.
move=> Hbound.
rewrite /Memory.load /= prepare_initial_memoryE.
case: (C \in domm (Intermediate.prog_interface p)) => //.
case Epb: (Intermediate.prog_buffers p C) => [bmap|] /=.
- exact: (initial_load_rel Hbound Epb).
-  rewrite ComponentMemory.load_prealloc.
  by case: (0 <=? o)%Z; rewrite ?emptymE.
Qed.

(* ==================== through procedure-block reservation ==================== *)

(* reserving blocks never touches content *)
Lemma load_reserve_blocks (n : nat) (m : ComponentMemory.t)
    (b : Block.id) (o : Z) :
  ComponentMemory.load (ComponentMemoryExtra.reserve_blocks m n).1 b o
  = ComponentMemory.load m b o.
Proof.
rewrite /ComponentMemoryExtra.reserve_blocks.
elim: n => [|n IH] //.
rewrite iterS.
case Ei: (iter n _ (m, [::])) => [m' bs] /=.
case Er: (ComponentMemory.reserve_block m') => [m'' b''] /=.
rewrite (ComponentMemory.load_after_reserve_block _ _ _ Er).
rewrite Ei /= in IH.
exact: IH.
Qed.

(* the machine's initial memory (with procedure blocks reserved) loads
   exactly like the plain static-buffer memory *)
Lemma prepare_procedures_memory_load (p : Intermediate.program)
    (C : Component.id) (b : Block.id) (o : Z) :
  Memory.load (Intermediate.prepare_procedures_memory p) (C, b, o)
  = Memory.load (Intermediate.prepare_initial_memory p) (C, b, o).
Proof.
rewrite /Memory.load /=.
rewrite prepare_initial_memoryE.
rewrite /Intermediate.prepare_procedures_memory
        /Intermediate.prepare_procedures_initial_memory
        /Intermediate.prepare_procedures_initial_memory_aux.
rewrite mapmE mkfmapfE.
case: (C \in domm (Intermediate.prog_interface p)) => //=.
rewrite /Intermediate.reserve_component_blocks; cbv zeta.
case Er: (ComponentMemoryExtra.reserve_blocks _ _) => [Cmem' bs] /=.
have := load_reserve_blocks
          (length
             (Maps.elementsm
                (odflt emptym (Intermediate.prog_procedures p C))))
          (ComponentMemory.prealloc
             (odflt emptym (Intermediate.prog_buffers p C))) b o.
rewrite Er /=.
by move=> ->.
Qed.

(* the consumable form: a load from the I-machine's true initial memory is
   matched by a related me value at the injected flat address *)
Lemma machine_load_rel (p : Intermediate.program)
    (C : Component.id) (b : Block.id) (o : Z) (v : value) :
  size (linearize_bufs (Intermediate.prog_buffers p)) < 2 ^ word_size mt ->
  Memory.load (Intermediate.prepare_procedures_memory p) (C, b, o) = Some v ->
  exists a : matom,
    [/\ initial_memory (mt := mt) (Intermediate.prog_buffers p)
          (@word_of_nat (word_size mt)
             (nat_addr (Intermediate.prog_buffers p) (C, b, Z.to_nat o)))
        = Some a,
        taga a = LRC.def_mem_tag C false
      & val_rel (Intermediate.prog_buffers p) v (vala a)].
Proof.
move=> Hbound.
rewrite prepare_procedures_memory_load.
exact: prepare_load_rel Hbound.
Qed.

(* ==================== registers ==================== *)

(* decidable equality of small word literals (word arithmetic is Opaque;
   the bounds are decided at concrete exponents) *)
Lemma won_eqE (k : nat) (i j : nat) :
  i < 2 ^ k -> j < 2 ^ k ->
  (@word_of_nat k i == word_of_nat j) = (i == j).
Proof.
move=> Hi Hj.
apply/idP/idP.
- move/eqP=> E.
  have -> := won_inj Hi Hj E.
  by rewrite eqxx.
- move/eqP=> ->.
  by rewrite eqxx.
Qed.

(* registers are indexed by [reg_field_size]-words (5 bits) *)
Lemma small_lt_reg (i : nat) : i < 32 -> i < 2 ^ reg_field_size mt.
Proof.
move=> Hi.
by rewrite reg_field_size_mt.
Qed.

(* the me machine's initial register file is defined (and Other-tagged) at
   every Intermediate register's image *)
Lemma reg0_get (r : register) :
  exists w : mword mt,
    getm (reg0 (mt := mt))
         (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r))
    = Some (Atom w Other).
Proof.
by case: r; rewrite /reg0 mkfmapE /=
   !(won_eqE (small_lt_reg _) (small_lt_reg _)) //=; eexists.
Qed.

(* the register relation (static part): pointwise related values,
   plain Other value tags *)
Definition regs_rel (pb : NMap {fmap Block.id -> nat + seq value})
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall r : register,
    exists a : @ratom mt,
      [/\ getm mregs (@word_of_nat (reg_field_size mt)
                        (Intermediate.Register.to_nat r)) = Some a,
          val_rel pb (Intermediate.Register.get r iregs) (vala a)
        & taga a = Other].

Lemma init_get_Undef (r : register) :
  Intermediate.Register.get r Intermediate.Register.init = Undef.
Proof. by case: r. Qed.

(* the initial register files are related (Register.init is all-Undef) *)
Lemma init_regs_rel (pb : NMap {fmap Block.id -> nat + seq value}) :
  regs_rel pb Intermediate.Register.init (reg0 (mt := mt)).
Proof.
move=> r.
have [w Hw] := reg0_get r.
exists (Atom w Other).
split=> //.
by rewrite init_get_Undef.
Qed.

(* ==================== through the code/data union ==================== *)

(* the me machine's full initial memory is [unionm (encode_code cde pc0) mem0]
   with pc0 = size mem0: data addresses lie strictly below pc0, so the union
   falls through to the data segment *)
Lemma me_init_data_fetch (cde : @Merged.code mt)
    (pb : NMap {fmap Block.id -> nat + seq value}) (k : nat * nat * nat)
    (a : matom) :
  size (linearize_bufs pb) + size cde < 2 ^ word_size mt ->
  k \in domm (linearize_bufs pb) ->
  initial_memory (mt := mt) pb
    (@word_of_nat (word_size mt) (nat_addr pb k)) = Some a ->
  unionm (encode_code cde (size (initial_memory (mt := mt) pb)))
         (initial_memory (mt := mt) pb)
         (@word_of_nat (word_size mt) (nat_addr pb k))
  = Some a.
Proof.
move=> Hbound Hk Ha.
rewrite unionmE.
have Htot : size (linearize_bufs pb) < 2 ^ word_size mt by lia.
have Hsz : size (initial_memory (mt := mt) pb) = size (linearize_bufs pb)
  := initial_memory_size_eq Htot.
case Ecode: (encode_code cde (size (initial_memory (mt := mt) pb))
               (@word_of_nat (word_size mt) (nat_addr pb k))) => [av|].
-  exfalso.
  have [n [Hw [Hn _]]] := encode_code_nth_inv Ecode.
  have Hlt := nat_addr_lt Hk.
  have H1 : nat_addr pb k < 2 ^ word_size mt by lia.
  have H2 : n + size (initial_memory (mt := mt) pb) < 2 ^ word_size mt.
  { rewrite Hsz. by lia. }
  have HE := won_inj H1 H2 Hw.
  rewrite Hsz in HE.
  by lia.
- exact: Ha.
Qed.

(* any address at or above the data segment's size is unmapped there *)
Lemma initial_memory_above (pb : NMap {fmap Block.id -> nat + seq value})
    (n : nat) :
  size (linearize_bufs pb) <= n ->
  n < 2 ^ word_size mt ->
  initial_memory (mt := mt) pb (@word_of_nat (word_size mt) n) = None.
Proof.
move=> Hge Hn32.
case E: (initial_memory _ _) => [d|] //.
exfalso.
have [k [cell [Hlk _ Hwk]]] := BufferShape.initial_memory_invE E.
have Hkin : k \in domm (linearize_bufs pb) by rewrite mem_domm Hlk.
have Hklt := nat_addr_lt Hkin.
have Hk32 : nat_addr pb k < 2 ^ word_size mt by lia.
have := won_inj Hn32 Hk32 Hwk.
by lia.
Qed.

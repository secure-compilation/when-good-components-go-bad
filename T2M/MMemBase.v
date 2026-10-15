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

(* ==================== glue to the I-machine's initial memory ==================== *)

(* ==================== through procedure-block reservation ==================== *)

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

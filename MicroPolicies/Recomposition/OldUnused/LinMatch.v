(* Task #14 (I→Merged correctness): the MEMORY RELATION of the simulation.

   The match relation carries a block-address map [addr_map] (component ->
   block -> flat base): static buffers at BufferLayout's [bl_base], dynamic
   blocks wherever [alloc_fun] placed them.  Values relate pointwise
   ([val_rel_b]; Undef is free — note the gps-based Intermediate machine
   CLOBBERS R_RA at IJal, so the compiled convention's stack cells hold
   Undef on the I side and the whole stack-content correspondence is
   absorbed here).  [mem_rel] packages the load correspondence with the
   address map's injectivity and word-fit; [mem_rel_store] is the STORE
   step's preservation lemma. *)

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
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LinPos.
Require Import MicroPolicies.Recomposition.LinMem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the block-address map: component -> block -> flat base address *)
Definition addr_map := NMap (NMap nat).

Definition amap_get (bmap : addr_map) (C : Component.id) (b : Block.id)
  : option nat :=
  obind (fun m => getm m b) (getm bmap C).

(* value relation, address-map parameterized (pointers may target dynamic
   blocks); Undef relates to anything *)
Definition val_rel_b (bmap : addr_map) (v : value) (w : mword mt) : Prop :=
  match v with
  | Undef => True
  | Int z => w = word.as_word (encode_int z)
  | Ptr ptr =>
      match ptr with
      | (c', b', o') =>
          exists base,
            amap_get bmap c' b' = Some base
            /\ w = word.as_word
                     (ssrint.intZmod.addz (encode_int o') (ssrint.Posz base))
      end
  end.

Definition loadable (imem : Memory.t) (p : Pointer.t) : Prop :=
  exists v, Memory.load imem p = Some v.

(* THE memory relation *)
Record mem_rel (bmap : addr_map) (imem : Memory.t)
    (mmem : {fmap mword mt -> matom}) : Prop := MemRel {
  mr_load : forall (C : Component.id) (b : Block.id) (off : Z) (v : value),
      Memory.load imem (C, b, off) = Some v ->
      exists base a,
        [/\ amap_get bmap C b = Some base,
            getm mmem (@word_of_nat (word_size mt) (base + Z.to_nat off))
              = Some a,
            val_rel_b bmap v (vala a),
            color (taga a) = C
          & is_code (taga a) = false];
  mr_fit : forall (C : Component.id) (b : Block.id) (off : Z) (base : nat),
      loadable imem (C, b, off) ->
      amap_get bmap C b = Some base ->
      base + Z.to_nat off < 2 ^ word_size mt;
  mr_inj : forall (C : Component.id) (b : Block.id) (off : Z)
                  (C' : Component.id) (b' : Block.id) (off' : Z)
                  (base base' : nat),
      loadable imem (C, b, off) ->
      loadable imem (C', b', off') ->
      amap_get bmap C b = Some base ->
      amap_get bmap C' b' = Some base' ->
      (C, b, off) <> (C', b', off') ->
      base + Z.to_nat off <> base' + Z.to_nat off'
}.

(* ==================== store preservation ==================== *)

Lemma Memory_store_loadable (imem : Memory.t) (p : Pointer.t) (v : value)
    (imem' : Memory.t) :
  Memory.store imem p v = Some imem' -> loadable imem p.
Proof.
case: p => [[C b] off].
rewrite /Memory.store /loadable /Memory.load /=.
case E: (imem C) => [mC|] //.
case Est: (ComponentMemory.store mC b off v) => [mC'|] // _.
have [v' Hv'] := ComponentMemory.store_load _ _ _ _ _ Est.
exists v'. by rewrite Hv'.
Qed.

Lemma loadable_after_store (imem : Memory.t) (p : Pointer.t) (v : value)
    (imem' : Memory.t) (p' : Pointer.t) :
  Memory.store imem p v = Some imem' ->
  (loadable imem' p' <-> loadable imem p').
Proof.
move=> Hst.
split.
- move=> [v'].
  rewrite (Memory.load_after_store _ _ _ _ _ Hst).
  case Ep: (p' == p).
  + move/eqP: Ep => -> _.
    exact: Memory_store_loadable Hst.
  + move=> Hl. by exists v'.
- move=> [v' Hl].
  case Ep: (p' == p).
  + exists v. by rewrite (Memory.load_after_store _ _ _ _ _ Hst) Ep.
  + exists v'. by rewrite (Memory.load_after_store _ _ _ _ _ Hst) Ep.
Qed.

(* an Intermediate store is matched by the corresponding me-memory update
   (any colour-C non-code tag — the machine's [switch_val] preserves both) *)
Lemma mem_rel_store (bmap : addr_map) (imem : Memory.t)
    (mmem : {fmap mword mt -> matom}) (C : Component.id) (b : Block.id)
    (off : Z) (v : value) (imem' : Memory.t) (base : nat) (w : mword mt)
    (tg : mem_tag) :
  mem_rel bmap imem mmem ->
  Memory.store imem (C, b, off) v = Some imem' ->
  amap_get bmap C b = Some base ->
  val_rel_b bmap v w ->
  color tg = C ->
  is_code tg = false ->
  mem_rel bmap imem'
    (setm mmem (@word_of_nat (word_size mt) (base + Z.to_nat off))
          (Atom w tg)).
Proof.
move=> [ML MF MI] Hst Hb Hv Hcol Hcode.
have Hldt : loadable imem (C, b, off) := Memory_store_loadable Hst.
constructor.
- (* load correspondence *)
  move=> C0 b0 off0 v0.
  rewrite (Memory.load_after_store _ _ _ _ _ Hst).
  case Ep: ((C0, b0, off0) == (C, b, off)).
  + (* the stored cell *)
    move/eqP: Ep => Ep. case: Ep => ? ? ?; subst C0 b0 off0.
    move=> [<-].
    exists base, (Atom w tg).
    rewrite setmE eqxx.
    by split.
  + (* any other cell: untouched on both sides *)
    move=> Hl0.
    have [base0 [a0 [H1 H2 H3 H4 H5]]] := ML _ _ _ _ Hl0.
    exists base0, a0.
    rewrite setmE.
    case Ew: (@word_of_nat (word_size mt) (base0 + Z.to_nat off0)
              == word_of_nat (base + Z.to_nat off)).
    * exfalso.
      move/eqP: Ew => Ew.
      have Hfit0 : base0 + Z.to_nat off0 < 2 ^ word_size mt.
      { apply: MF H1. by exists v0. }
      have Hfit1 : base + Z.to_nat off < 2 ^ word_size mt.
      { exact: MF Hldt Hb. }
      have Hnat := won_inj Hfit0 Hfit1 Ew.
      have Hneq : (C0, b0, off0) <> (C, b, off).
      { move=> E. by rewrite E eqxx in Ep. }
      exact: (MI _ _ _ _ _ _ _ _ (ex_intro _ v0 Hl0) Hldt H1 Hb Hneq Hnat).
    * by split.
- (* fit *)
  move=> C0 b0 off0 base0 Hld Hb0.
  apply: MF Hb0.
  exact: (proj1 (loadable_after_store _ Hst) Hld).
- (* injectivity *)
  move=> C0 b0 off0 C1 b1 off1 base0 base1 Hld0 Hld1 Hb0 Hb1 Hne.
  apply: (MI _ _ _ _ _ _ _ _ _ _ Hb0 Hb1 Hne).
  + exact: (proj1 (loadable_after_store _ Hst) Hld0).
  + exact: (proj1 (loadable_after_store _ Hst) Hld1).
Qed.

(* ==================== registers, address-map parameterized ==================== *)

Definition regs_rel_b (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall r : register,
    exists a : @ratom mt,
      [/\ getm mregs (@word_of_nat (reg_field_size mt)
                        (Intermediate.Register.to_nat r)) = Some a,
          val_rel_b bmap (Intermediate.Register.get r iregs) (vala a)
        & taga a = Other].

Lemma init_regs_rel_b (bmap : addr_map) :
  regs_rel_b bmap Intermediate.Register.init (reg0 (mt := mt)).
Proof.
move=> r.
have [w Hw] := reg0_get r.
exists (Atom w Other).
split=> //.
by rewrite init_get_Undef.
Qed.

(* ==================== the INITIAL memory relation ==================== *)

(* the static address map: declared blocks at BufferLayout's [bl_base] *)
Definition static_amap (pb : NMap {fmap Block.id -> nat + seq value})
  : addr_map :=
  mapim (fun C bm => mkfmapf (fun b => bl_base pb C b) (domm bm)) pb.

Lemma static_amap_get (pb : NMap {fmap Block.id -> nat + seq value})
    (C : Component.id) (b : Block.id)
    (bm : {fmap Block.id -> nat + seq value}) :
  pb C = Some bm -> b \in domm bm ->
  amap_get (static_amap pb) C b = Some (bl_base pb C b).
Proof.
move=> HC Hb.
rewrite /amap_get /static_amap mapimE HC /=.
by rewrite mkfmapfE Hb.
Qed.

Lemma static_amap_inv (pb : NMap {fmap Block.id -> nat + seq value})
    (C : Component.id) (b : Block.id) (base : nat) :
  amap_get (static_amap pb) C b = Some base ->
  exists bm,
    [/\ pb C = Some bm, b \in domm bm & base = bl_base pb C b].
Proof.
rewrite /amap_get /static_amap mapimE.
case E: (pb C) => [bm|] //=.
rewrite mkfmapfE.
case Eb: (b \in domm bm) => //.
move=> [<-].
by exists bm.
Qed.

(* a loadable initial cell is a declared, in-range buffer cell *)
Lemma initial_loadable_key (p : Intermediate.program)
    (C : Component.id) (b : Block.id) (off : Z) :
  loadable (Intermediate.prepare_procedures_memory p) (C, b, off) ->
  [/\ (0 <= off)%Z,
      (C, b, Z.to_nat off)
        \in domm (linearize_bufs (Intermediate.prog_buffers p))
    & exists bm, Intermediate.prog_buffers p C = Some bm /\ b \in domm bm].
Proof.
move=> [v Hv].
move: Hv.
rewrite prepare_procedures_memory_load /Memory.load /= prepare_initial_memoryE.
case Hin: (C \in domm (Intermediate.prog_interface p)) => //.
rewrite ComponentMemory.load_prealloc.
case Hoff: (0 <=? off)%Z => //.
move/Z.leb_le: Hoff => Hoff.
case Epb: (Intermediate.prog_buffers p C) => [bm|]; last first.
{ by []. }
rewrite /=.
case Eb: (bm b) => [[sz|chunk]|] //.
- (* inl: Undef-filled *)
  case Hlt: (off <? Z.of_nat sz)%Z => // _.
  move/Z.ltb_lt: Hlt => Hlt.
  split=> //.
  + apply/linearize_bufs_key.
    exists bm, (inl sz). split=> //.
    have -> : linearize_buf (Intermediate.prog_buffers p) C b
              = repeat (Undef, LRC.def_mem_tag C false) sz
      by rewrite /linearize_buf Epb /= Eb.
    rewrite -lin_size_length List.repeat_length.
    by lia.
  + exists bm. split=> //.
    by rewrite mem_domm Eb.
- (* inr: explicit contents *)
  move=> Hnth.
  split=> //.
  + apply/linearize_bufs_key.
    exists bm, (inr chunk). split=> //.
    have -> : linearize_buf (Intermediate.prog_buffers p) C b
              = [seq (x, LRC.def_mem_tag C false) | x <- chunk]
      by rewrite /linearize_buf Epb /= Eb.
    rewrite size_map.
    exact: (nth_error_size Hnth).
  + exists bm. split=> //.
    by rewrite mem_domm Eb.
Qed.

(* THE initial memory relation: the I machine's prepared memory relates to
   the me machine's initial memory (code segment unioned on top), through
   the static address map *)
Lemma initial_mem_rel (p : Intermediate.program) (cde : @Merged.code mt) :
  size (linearize_bufs (Intermediate.prog_buffers p)) + size cde
    < 2 ^ word_size mt ->
  (forall C b off c' b' o',
     Memory.load (Intermediate.prepare_procedures_memory p) (C, b, off)
       = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers p c' = Some bm'
       /\ b' \in domm bm') ->
  mem_rel (static_amap (Intermediate.prog_buffers p))
          (Intermediate.prepare_procedures_memory p)
          (unionm (encode_code cde
                     (size (initial_memory (mt := mt)
                              (Intermediate.prog_buffers p))))
                  (initial_memory (mt := mt)
                     (Intermediate.prog_buffers p))).
Proof.
move=> Hbound Hptr.
have Hb1 : size (linearize_bufs (Intermediate.prog_buffers p))
           < 2 ^ word_size mt by lia.
constructor.
- (* mr_load *)
  move=> C b off v Hl.
  have Hld : loadable (Intermediate.prepare_procedures_memory p) (C, b, off)
    by exists v.
  have [Hoff Hkey [bm [Epb Hbm]]] := initial_loadable_key Hld.
  have [a [Hma Htag Hval]] := machine_load_rel Hb1 Hl.
  have Hunion := me_init_data_fetch Hbound Hkey Hma.
  exists (bl_base (Intermediate.prog_buffers p) C b), a.
  have Eaddr : bl_base (Intermediate.prog_buffers p) C b + Z.to_nat off
               = nat_addr (Intermediate.prog_buffers p) (C, b, Z.to_nat off).
  { by rewrite /nat_addr addnC. }
  split.
  + exact: static_amap_get Epb Hbm.
  + by rewrite Eaddr.
  + case: v Hl Hval => [z|[[c' b'] o']|] Hl Hval //=.
    have [bm' [Epb' Hbm']] := Hptr _ _ _ _ _ _ Hl.
    exists (bl_base (Intermediate.prog_buffers p) c' b').
    split; first exact: static_amap_get Epb' Hbm'.
    exact Hval.
  + by rewrite Htag.
  + by rewrite Htag.
- (* mr_fit *)
  move=> C b off base Hld Hb.
  have [Hoff Hkey _] := initial_loadable_key Hld.
  have [bm [Epb Hbm Ebase]] := static_amap_inv Hb.
  have Hlt := nat_addr_lt Hkey.
  rewrite Ebase.
  have Eaddr : bl_base (Intermediate.prog_buffers p) C b + Z.to_nat off
               = nat_addr (Intermediate.prog_buffers p) (C, b, Z.to_nat off).
  { by rewrite /nat_addr addnC. }
  rewrite Eaddr.
  by lia.
- (* mr_inj *)
  move=> C b off C' b' off' base base' Hld Hld' Hb Hb' Hne.
  have [Hoff Hkey _] := initial_loadable_key Hld.
  have [Hoff' Hkey' _] := initial_loadable_key Hld'.
  have [bm [Epb Hbm Ebase]] := static_amap_inv Hb.
  have [bm' [Epb' Hbm' Ebase']] := static_amap_inv Hb'.
  rewrite Ebase Ebase'.
  have Eaddr : bl_base (Intermediate.prog_buffers p) C b + Z.to_nat off
               = nat_addr (Intermediate.prog_buffers p) (C, b, Z.to_nat off).
  { by rewrite /nat_addr addnC. }
  have Eaddr' : bl_base (Intermediate.prog_buffers p) C' b' + Z.to_nat off'
                = nat_addr (Intermediate.prog_buffers p) (C', b', Z.to_nat off').
  { by rewrite /nat_addr addnC. }
  rewrite Eaddr Eaddr' => Enat.
  have := nat_addr_inj Hkey Hkey' Enat.
  case=> E1 E2 E3.
  apply: Hne.
  have Eoff : off = off' by lia.
  by rewrite E1 E2 Eoff.
Qed.

(* ==================== extending the address map (alloc) ==================== *)

Definition amap_set (bmap : addr_map) (C : Component.id) (b : Block.id)
    (base : nat) : addr_map :=
  setm bmap C (setm (odflt emptym (getm bmap C)) b base).

Lemma amap_set_eq (bmap : addr_map) (C : Component.id) (b : Block.id)
    (base : nat) :
  amap_get (amap_set bmap C b base) C b = Some base.
Proof.
by rewrite /amap_get /amap_set setmE eqxx /= setmE eqxx.
Qed.

Lemma amap_set_neq (bmap : addr_map) (C : Component.id) (b : Block.id)
    (base : nat) (C' : Component.id) (b' : Block.id) :
  (C', b') <> (C, b) ->
  amap_get (amap_set bmap C b base) C' b' = amap_get bmap C' b'.
Proof.
move=> Hne.
rewrite /amap_get /amap_set setmE.
case EC: (C' == C); last by [].
move/eqP: EC => ?; subst C'.
rewrite /= setmE.
case Eb: (b' == b).
- move/eqP: Eb => ?; subst b'.
  by case: Hne.
- by case: (getm bmap C).
Qed.

(* ==================== the allocator's post-state shape ==================== *)

(* single-run characterization of [alloc_fun]: the me memory gains a fresh
   [len]-cell block right after [max] (the last used address of the
   component's prefix region), zero-filled and colour-tagged; syscall_ret
   receives the first address; the pc returns through ra *)
Lemma alloc_fun_shape (N : nat)
    (s s' : @Symbolic.state mt LRC.lrc_tags unit) :
  LRC.alloc_fun (NC := N) s = Some s' ->
  exists (c : Component.id) (len : nat) (max : mword mt)
         (rav : @ratom mt) (regs' : {fmap reg mt -> @ratom mt}),
    [/\ getm (Symbolic.regs s) ra = Some rav
        /\ Symbolic.pc s' = (vala rav)@(taga (Symbolic.pc s)),
        c = (match taga (Symbolic.pc s) with LRC.Level _ c0 => c0 end),
        0 < len /\ len + 1 <= 2 ^ (word_size mt - N),
        updm (Symbolic.regs s) syscall_ret
             ((max + as_word (ssrint.Posz 1))%w@LRC.Other) = Some regs'
        /\ Symbolic.regs s' = regs'
      & Symbolic.mem s' = unionm (Symbolic.mem s)
          (mkfmap (mkseq (fun n =>
             ((max + as_word (ssrint.Posz (n + 1)))%w,
              (as_word (ssrint.Posz 0))@(LRC.def_mem_tag c false))) len))].
Proof.
move=> H. move: H. rewrite /LRC.alloc_fun. cbv zeta. move=> H.
case: (obind_inv H) => rav [Hra {}H].
case: (obind_inv H) => u1 [_ {}H].
case: (obind_inv H) => reta [_ {}H].
case: (obind_inv H) => u2 [_ {}H].
case: (obind_inv H) => szv [Hsz {}H].
case: (obind_inv H) => u3 [_ {}H].
case: (obind_inv H) => len [Hlen {}H].
case: (obind_inv H) => u4 [Hbnd {}H].
move: H.
case Hpf: (~~ _) => // H.
case: (obind_inv H) => addr [Haddr {}H].
case: (obind_inv H) => regs' [Hregs' {}H].
move: H => [= HSt]. subst s'.
(* the block is non-empty and addr is its first address *)
case: len Hlen Hbnd Hpf Haddr => [|k] Hlen Hbnd Hpf Haddr.
{ by case: (obind_inv Haddr) => hd [Hhd _]. }
case: (obind_inv Haddr) => hd [Hhd Hfst].
move: Hhd => /= [= Ehd]. subst hd.
move: Hfst => [= Eaddr]. subst addr.
(* the bound check *)
move: Hbnd. case: ifP => // Hle _.
eexists _, k.+1, _, rav, regs'.
split.
- split; [exact: Hra | by []].
- by [].
- split; [by [] | exact: Hle].
- split; [exact: Hregs' | by []].
- by [].
Qed.

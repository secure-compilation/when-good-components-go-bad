(** * T2M sync claims: which registers and memory cells must stay in the
    SYNCED (non-clobbered) arm (me's BINOP faults on Invalidated operands).
    Provides [sync_claims], its per-opcode transport lemmas, and [mm_dsync]. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import zify.
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
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import S2T.TSem.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require Import T2M.MSig.
Require Import T2M.MDisc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section SyncDef.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.
Variable MM : Component.id -> seq sv.
Variable cde : TS.code.
Hypothesis HMM : forall c S,
  getm cde c = Some S -> comp_ok (c, 1, Z0) S (MM c).
Hypothesis Huniq : forall (c : Component.id) (S : TS.tcode) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  getm cde c = Some S ->
  nth_error S m = Some (TrLabel (inl l), t1) ->
  nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.

Local Notation cmapS := (cmapW L P C pra prb PB PI).
Local Notation reg_syncedS := (reg_synced L P C pra prb PB PI).
Local Notation svat := (MDisc.svat MM).
Local Notation asv := (MDisc.asv MM).

(* the cell at (c, b, j) is related through the STRONG arm *)
Definition cell_synced (amap : amap_t) (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom})
    (c : Component.id) (b : Block.id) (j : nat) : Prop :=
  forall cm blk cell a mc,
    tmem c = Some cm ->
    Transitional.Memory.content cm b = Some blk ->
    List.nth_error blk j = Some cell ->
    addr_of amap c b = Some a ->
    mmem (word_of_nat (a + j)) = Some mc ->
    cellrel cmapS amap cell mc.

(* a frame slot class that must stay synced: CU always; CSp only above
   position 0 (the wrapper's inherited scratch); CArg when the frame
   owner's caller kept its arg bit (its R_ARG carried through the callee) *)
Definition synced_slot (parg : bool) (k : class3) (j : nat) : bool :=
  match k with
  | CU => true
  | CSp => 0 < j
  | CArg => parg
  | CRa => false
  end.

(* the kept arg bit of the head suspension (parg_of), resp. of the
   provider of chain act i — its caller, act i+1 (parg_at) *)
Definition parg_of (chain : seq MDisc.act) : bool :=
  match chain with A :: _ => sv_arg (asv A) | [::] => false end.
Definition parg_at (chain : seq MDisc.act) (i : nat) : bool :=
  match nth_error chain i.+1 with
  | Some P => sv_arg (asv P)
  | None => false
  end.

(* no CArg slot in flight (callee prologue before the CArg push, or
   teardown after the pop) — the caller's R_ARG then lives in the
   register, not the frame *)
Definition cargfree (v : sv) : bool :=
  ~~ has (fun k => c3_eqb k CArg) (sv_sig v) &&
  match sv_pend v with Some CArg => false | _ => true end.

Lemma parg_at_cons0 (A : MDisc.act) (ch : seq MDisc.act) :
  parg_at (A :: ch) 0 = parg_of ch.
Proof. by case: ch. Qed.

Record sync_claims (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) : Prop := SyncClaims {

  sy_com : reg_syncedS amap tregs mregs R_COM;
  sy_a1u : forall v, svat pc = Some v -> sv_a1 v = AU ->
    reg_syncedS amap tregs mregs R_AUX1;
  sy_a2u : forall v, svat pc = Some v -> sv_a2 v = AU ->
    reg_syncedS amap tregs mregs R_AUX2;
  sy_a1sp : forall v, svat pc = Some v -> sv_a1 v = ASp ->
    sv_ek v = true \/ sv_sig v <> [::] ->
    reg_syncedS amap tregs mregs R_AUX1;
  sy_a2sp : forall v, svat pc = Some v -> sv_a2 v = ASp ->
    sv_ek v = true \/ sv_sig v <> [::] ->
    reg_syncedS amap tregs mregs R_AUX2;
  sy_arg : forall v, svat pc = Some v -> sv_arg v = true ->
    reg_syncedS amap tregs mregs R_ARG;
  sy_argp : forall v, svat pc = Some v ->
    parg_of chain = true -> cargfree v = true ->
    reg_syncedS amap tregs mregs R_ARG;

  sy_mem : forall c b j, (b \in F c) = false ->
    cell_synced amap tmem mmem c b j;

  sy_frame : forall v b j k, svat pc = Some v -> cur = Some b ->
    nth_error (sv_sig v) j = Some k ->
    synced_slot (parg_of chain) k j = true ->
    cell_synced amap tmem mmem (Pointer.component pc) b j;

  sy_pend : forall v b k, svat pc = Some v -> cur = Some b ->
    sv_pend v = Some k ->
    synced_slot (parg_of chain) k (size (sv_sig v)) = true ->
    cell_synced amap tmem mmem (Pointer.component pc) b
      (size (sv_sig v));

  sy_chain : forall i A j k, nth_error chain i = Some A ->
    nth_error (sv_sig (asv A)) j = Some k ->
    synced_slot (parg_at chain i) k j = true ->
    cell_synced amap tmem mmem (MDisc.a_comp A) (MDisc.a_blk A) j
}.

(* Transport along a pure pc move (nop/label/bnz, no register/memory writes):
   successor claims are [sv_le]-weaker, so each re-keys through the lattice.
   Sync mirror of [MDisc.dinv_pcmove]. *)

Lemma sync_pcmove (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc pc' : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v w : sv) :
  Pointer.component pc' = Pointer.component pc ->
  svat pc = Some v ->
  svat pc' = Some w ->
  sv_le v w ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem tregs mregs mmem pc' cur chain F.
Proof.
move=> Ec Ev Ew Hle HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
have Harg : sv_arg w = true -> sv_arg v = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
constructor.
- exact: (sy_com HS).
- move=> w0. rewrite Ew => -[<-] Hau.
  have Hav : sv_a1 v = AU.
  { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  exact: (sy_a1u HS Ev Hav).
- move=> w0. rewrite Ew => -[<-] Hau.
  have Hav : sv_a2 v = AU.
  { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  exact: (sy_a2u HS Ev Hav).
- move=> w0. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : sv_a1 v = ASp.
  { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
  apply: (sy_a1sp HS Ev Hav).
  move: Hcond. rewrite Eek Esg. exact: id.
- move=> w0. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : sv_a2 v = ASp.
  { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
  apply: (sy_a2sp HS Ev Hav).
  move: Hcond. rewrite Eek Esg. exact: id.
- move=> w0. rewrite Ew => -[<-] Hw.
  exact: (sy_arg HS Ev (Harg Hw)).
- move=> w0. rewrite Ew => -[<-] Hpg Hcf.
  apply: (sy_argp HS Ev Hpg).
  move: Hcf. rewrite /cargfree Esg Epd. exact: id.
- exact: (sy_mem HS).
- move=> w0 b j k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg in Hk.
  exact: (sy_frame HS Ev Hb Hk Hs).
- move=> w0 b k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Epd in Hk. rewrite Esg in Hs.
  rewrite Esg.
  exact: (sy_pend HS Ev Hb Hk Hs).
- exact: (sy_chain HS).
Qed.

(* Transport along a register-writing, memory-preserving step: cell claims
   carry over (sig/pend unchanged by the checker), the caller supplies the
   register claims at the successor's keying.  Sync mirror of [MDisc.dinv_regw]. *)

Lemma sync_regw (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs tregs' : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w : sv) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w ->
  sv_le v' w ->
  sv_sig v' = sv_sig v ->
  sv_pend v' = sv_pend v ->
  reg_syncedS amap tregs' mregs' R_COM ->
  (sv_a1 w = AU -> reg_syncedS amap tregs' mregs' R_AUX1) ->
  (sv_a2 w = AU -> reg_syncedS amap tregs' mregs' R_AUX2) ->
  (sv_a1 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap tregs' mregs' R_AUX1) ->
  (sv_a2 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap tregs' mregs' R_AUX2) ->
  (sv_arg w = true -> reg_syncedS amap tregs' mregs' R_ARG) ->
  (parg_of chain = true -> cargfree w = true ->
     reg_syncedS amap tregs' mregs' R_ARG) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem tregs' mregs' mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Wpd SCOM SA1U SA2U SA1S SA2S SARG SARGP HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
rewrite Wsg in Esg. rewrite Wpd in Epd.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
- exact: SCOM.
- move=> w0; rewrite Ew => -[<-]. exact: SA1U.
- move=> w0; rewrite Ew => -[<-]. exact: SA2U.
- move=> w0; rewrite Ew => -[<-]. exact: SA1S.
- move=> w0; rewrite Ew => -[<-]. exact: SA2S.
- move=> w0; rewrite Ew => -[<-]. exact: SARG.
- move=> w0; rewrite Ew => -[<-]. exact: SARGP.
- exact: (sy_mem HS).
- move=> w0 b j k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg in Hk.
  exact: (sy_frame HS Ev Hb Hk Hs).
- move=> w0 b k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Epd in Hk. rewrite Esg in Hs.
  rewrite Esg.
  exact: (sy_pend HS Ev Hb Hk Hs).
- exact: (sy_chain HS).
Qed.

(* Per-register sync under a both-sides register write. *)

Lemma reg_synced_set_other (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (r r0 : register) (tv : value) (vt : value_tag) (ra : @ratom mt) :
  Intermediate.Register.to_nat r0 <> Intermediate.Register.to_nat r ->
  reg_syncedS amap tregs mregs r0 ->
  reg_syncedS amap
    (Transitional.Register.set r tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) ra) r0.
Proof.
move=> Hne [ra0 [Hra0 Hv0 Ht0]].
have Hlt : forall r1 : register, Intermediate.Register.to_nat r1 < 32
  by case.
exists ra0.
have Hr0ne : r0 <> r by move=> E; apply: Hne; rewrite E.
rewrite (tget_set_neq _ _ _ Hr0ne) setmE
        (won_eqE (small_lt_reg (Hlt r0)) (small_lt_reg (Hlt r))).
have -> : (Intermediate.Register.to_nat r0
           == Intermediate.Register.to_nat r) = false.
{ by apply/eqP. }
by split.
Qed.

Lemma reg_synced_set (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (r : register) (tv : value) (vt : value_tag) (w : mword mt) :
  tvrel cmapS amap (Transitional.MVal vt tv) w ->
  reg_syncedS amap
    (Transitional.Register.set r tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) (Atom w vt)) r.
Proof.
move=> Hv.
exists (Atom w vt).
rewrite tget_set_eq setmE eqxx.
by split.
Qed.

(* The register-write fleet master: both sides write register [r] with a
   SYNCED pair, and the checker output's claim columns differ from [v]'s
   only at [r]'s column.  Covers const/binop/load's register half and mov. *)

Lemma sync_regw_synced (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (r : register) (tv : value) (vt : value_tag)
    (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w0 : sv) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w0 ->
  sv_le v' w0 ->
  sv_sig v' = sv_sig v ->
  sv_pend v' = sv_pend v ->
  (is_r r R_AUX1 = false -> sv_a1 v' = sv_a1 v) ->
  (is_r r R_AUX2 = false -> sv_a2 v' = sv_a2 v) ->
  (is_r r R_ARG = false -> sv_arg v' = sv_arg v) ->
  sv_ek v' = sv_ek v ->
  tvrel cmapS amap (Transitional.MVal vt tv) w ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set r tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) (Atom w vt))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Wpd Wa1 Wa2 Warg Wek Hv HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
have Harg : sv_arg w0 = true -> sv_arg v' = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
apply: (sync_regw Ev Ew Hle Wsg Wpd) => //.
-
  case Ecom: (is_r r R_COM).
  + rewrite (is_r_eq Ecom) in Hv *. exact: reg_synced_set Hv.
  + apply: reg_synced_set_other; last exact: (sy_com HS).
    move=> E. move: Ecom. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hau.
  case Ea1: (is_r r R_AUX1).
  + rewrite (is_r_eq Ea1) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a1 v = AU.
    { rewrite -(Wa1 Ea1).
      move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_set_other; last exact: (sy_a1u HS Ev Hav).
    move=> E. move: Ea1. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hau.
  case Ea2: (is_r r R_AUX2).
  + rewrite (is_r_eq Ea2) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a2 v = AU.
    { rewrite -(Wa2 Ea2).
      move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_set_other; last exact: (sy_a2u HS Ev Hav).
    move=> E. move: Ea2. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hasp Hcond.
  case Ea1: (is_r r R_AUX1).
  + rewrite (is_r_eq Ea1) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a1 v = ASp.
    { rewrite -(Wa1 Ea1).
      move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcond' : sv_ek v = true \/ sv_sig v <> [::].
    { move: Hcond. rewrite Eek Wek Esg Wsg. exact: id. }
    apply: reg_synced_set_other;
      last exact: (sy_a1sp HS Ev Hav Hcond').
    move=> E. move: Ea1. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hasp Hcond.
  case Ea2: (is_r r R_AUX2).
  + rewrite (is_r_eq Ea2) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a2 v = ASp.
    { rewrite -(Wa2 Ea2).
      move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcond' : sv_ek v = true \/ sv_sig v <> [::].
    { move: Hcond. rewrite Eek Wek Esg Wsg. exact: id. }
    apply: reg_synced_set_other;
      last exact: (sy_a2sp HS Ev Hav Hcond').
    move=> E. move: Ea2. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hw0.
  case Earg: (is_r r R_ARG).
  + rewrite (is_r_eq Earg) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_arg v = true by rewrite -(Warg Earg) (Harg Hw0).
    apply: reg_synced_set_other; last exact: (sy_arg HS Ev Hav).
    move=> E. move: Earg. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hpg Hcf.
  case Earg: (is_r r R_ARG).
  + rewrite (is_r_eq Earg) in Hv *. exact: reg_synced_set Hv.
  + have Hcf' : cargfree v = true.
    { move: Hcf. rewrite /cargfree Esg Wsg Epd Wpd. exact: id. }
    apply: reg_synced_set_other; last exact: (sy_argp HS Ev Hpg Hcf').
    move=> E. move: Earg. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
- exact: HS.
Qed.

(* [cell_synced] transport under a store: the written cell is synced iff the
   stored pair is; every other cell keeps its sync since the me write lands
   at a different flat address ([addr_sep_offs]/[addr_sep_blocks], [amap_ok]). *)

Lemma cell_synced_store (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom})
    (ptr : Pointer.t) (cellW : Transitional.tvalue * mem_tag)
    (mc' : @matom mt) (aptr : nat)
    (c : Component.id) (b : Block.id) (j : nat) :
  amap_ok PB amap tmem ->
  Transitional.Memory.store tmem ptr cellW = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some aptr ->
  ([&& c == Pointer.component ptr, b == Pointer.block ptr
     & j == BinInt.Z.to_nat (Pointer.offset ptr)] = true ->
     cellrel cmapS amap cellW mc') ->
  cell_synced amap tmem mmem c b j ->
  cell_synced amap tmem'
    (setm mmem
       (@word_of_nat (word_size mt)
          (aptr + BinInt.Z.to_nat (Pointer.offset ptr))) mc')
    c b j.
Proof.
move=> Haok Hst Haptr Hnew HS.
have [cm [chunk [chunk' [Hcm Hchunk Hoff Hupd Emem']]]] := store_shape Hst.
have Hofflt : BinInt.Z.to_nat (Pointer.offset ptr) < size chunk
  := list_upd_lt Hupd.
move=> cm2 blk2 cell a mc Hc2 Hb2 Hnth Ha Hmc.
case Etgt: [&& c == Pointer.component ptr, b == Pointer.block ptr
            & j == BinInt.Z.to_nat (Pointer.offset ptr)].
-
  have Hrel := Hnew Etgt.
  case/and3P: Etgt => /eqP Ec /eqP Eb /eqP Ej.
  subst c b j.
  have Ea2 : a = aptr by move: Ha; rewrite Haptr => -[].
  subst a.
  move: Hmc. rewrite setmE eqxx => -[<-].
  move: Hc2 Hb2 Hnth.
  rewrite Emem' setmE eqxx => -[<-] /=.
  rewrite setmE eqxx => -[<-].
  rewrite (list_upd_nth_error_same Hupd) => -[<-].
  exact: Hrel.
-
  have Hcell' : MDisc.cell_at tmem' c b j = Some cell.
  { by rewrite /MDisc.cell_at Hc2 Hb2. }
  have Hcell0 : MDisc.cell_at tmem c b j = Some cell.
  { by rewrite -(store_cell_other Hcm Hchunk Hupd Emem' Etgt). }
  move: Hcell0. rewrite /MDisc.cell_at.
  case Hc0: (getm tmem c) => [cm0|] //.
  case Hb0: (getm (Transitional.Memory.content cm0) b) => [blk0|] //.
  move=> Hnth0.
  have Hjlt : j < size blk0 := nth_error_size Hnth0.
  have Hsz0 : block_size tmem c b = Some (size blk0)
    by rewrite /block_size Hc0 /= Hb0.
  have HszP : block_size tmem (Pointer.component ptr) (Pointer.block ptr)
      = Some (size chunk)
    by rewrite /block_size Hcm /= Hchunk.
  have Hne : (@word_of_nat (word_size mt) (a + j))
             <> word_of_nat
                  (aptr + BinInt.Z.to_nat (Pointer.offset ptr)).
  { case Ecb: ((c == Pointer.component ptr) && (b == Pointer.block ptr)).
    - case/andP: Ecb => /eqP Ec /eqP Eb. subst c b.
      have Ea2 : a = aptr by move: Ha; rewrite Haptr => -[].
      subst a.
      have Ecm0 : cm0 = cm by move: Hc0; rewrite Hcm => -[].
      subst cm0.
      have Eblk : blk0 = chunk by move: Hb0; rewrite Hchunk => -[].
      subst blk0.
      have Hjne : j <> BinInt.Z.to_nat (Pointer.offset ptr).
      { move=> E. move: Etgt. by rewrite E !eqxx. }
      exact: (addr_sep_offs Haok Haptr HszP Hjlt Hofflt Hjne).
    - apply: (addr_sep_blocks Haok _ Ha Hsz0 Hjlt Haptr HszP Hofflt).
      move=> E. case: E => Ec Eb.
      move/negbT: Ecb. rewrite negb_and => /orP [] /eqP Hne0.
      + by case: (Hne0 Ec).
      + by case: (Hne0 Eb). }
  move: Hmc. rewrite setmE.
  case Ew: (@word_of_nat (word_size mt) (a + j)
            == word_of_nat (aptr + BinInt.Z.to_nat (Pointer.offset ptr))).
  { move/eqP: Ew => Ew. by case: (Hne Ew). }
  move=> Hmc.
  exact: (HS _ _ _ _ _ Hc0 Hb0 Hnth0 Ha Hmc).
Qed.

(* The per-opcode fleet: CONST. *)

Lemma sync_const (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (iv : imvalue) (r : register) (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrConst iv r) tg c ->
  tvrel cmapS amap (Transitional.MVal Other (imm_to_val iv)) w ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set r (imm_to_val iv) Other tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) (Atom w Other))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Hv HS.
have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w0 [Ew Hle]] := Hnx isT.
move: Evs => /=.
case Era: (is_r r R_RA) => //.
case Esp: (is_r r R_SP).
-
  case Eph: (sv_ph v) => // -[Evv]. subst v'.
  exact: (sync_regw_synced Ev Ew Hle (erefl _) (erefl _)
            (fun _ => erefl _) (fun _ => erefl _) (fun _ => erefl _)
            (erefl _) Hv HS).
-
  move=> -[Evv]. subst v'.
  have Wsg : sv_sig (warg_w r (wone r (cone iv)
               (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_sig v.
  { rewrite /warg_w /warg /wone /wtaint.
    by case: (is_r r R_AUX1); case: (is_r r R_AUX2);
       case: (is_r r R_ONE); case: (is_r r R_ARG). }
  have Wpd : sv_pend (warg_w r (wone r (cone iv)
               (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_pend v.
  { rewrite /warg_w /warg /wone /wtaint.
    by case: (is_r r R_AUX1); case: (is_r r R_AUX2);
       case: (is_r r R_ONE); case: (is_r r R_ARG). }
  have Wa1 : is_r r R_AUX1 = false ->
    sv_a1 (warg_w r (wone r (cone iv)
             (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_a1 v.
  { move=> E. rewrite /warg_w /warg /wone /wtaint E.
    by case: (is_r r R_AUX2); case: (is_r r R_ONE);
       case: (is_r r R_ARG). }
  have Wa2 : is_r r R_AUX2 = false ->
    sv_a2 (warg_w r (wone r (cone iv)
             (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_a2 v.
  { move=> E. rewrite /warg_w /warg /wone /wtaint E.
    by case: (is_r r R_AUX1); case: (is_r r R_ONE);
       case: (is_r r R_ARG). }
  have Warg : is_r r R_ARG = false ->
    sv_arg (warg_w r (wone r (cone iv)
              (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_arg v.
  { move=> E. rewrite /warg_w /warg /wone /wtaint E.
    by case: (is_r r R_AUX1); case: (is_r r R_AUX2);
       case: (is_r r R_ONE). }
  have Wek : sv_ek (warg_w r (wone r (cone iv)
               (wtaint r (ctaint (c, 1, Z0) iv) v))) = sv_ek v.
  { rewrite /warg_w /warg /wone /wtaint.
    by case: (is_r r R_AUX1); case: (is_r r R_AUX2);
       case: (is_r r R_ONE); case: (is_r r R_ARG). }
  exact: (sync_regw_synced Ev Ew Hle Wsg Wpd Wa1 Wa2 Warg Wek Hv HS).
Qed.

(* The push bump (Add R_SP R_ONE R_SP mid-macro): the pending slot becomes
   the frame top; R_SP carries no claim, the aux deadening preserves AU and
   refutes ASp. *)

Lemma sync_push (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tv : value) (vt : value_tag) (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w0 : sv) (k : class3) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w0 ->
  sv_le v' w0 ->
  sv_pend v = Some k ->
  sv_sig v' = rcons (sv_sig v) k ->
  sv_pend v' = None ->
  (sv_a1 v' = AU -> sv_a1 v = AU) ->
  (sv_a2 v' = AU -> sv_a2 v = AU) ->
  (sv_a1 v' = ASp -> False) ->
  (sv_a2 v' = ASp -> False) ->
  sv_arg v' = sv_arg v ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set R_SP tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat R_SP)) (Atom w vt))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Hpd Wsg Wpd Wa1u Wa2u Wa1s Wa2s Warg HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
have Harg : sv_arg w0 = true -> sv_arg v = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  rewrite -Warg. move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
- apply: reg_synced_set_other; last exact: (sy_com HS). by [].
- move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a1 v = AU.
  { apply: Wa1u. move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_set_other; last exact: (sy_a1u HS Ev Hav). by [].
- move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a2 v = AU.
  { apply: Wa2u. move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_set_other; last exact: (sy_a2u HS Ev Hav). by [].
- move=> ww. rewrite Ew => -[<-] Hasp _.
  exfalso. apply: Wa1s.
  move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq.
- move=> ww. rewrite Ew => -[<-] Hasp _.
  exfalso. apply: Wa2s.
  move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq.
- move=> ww. rewrite Ew => -[<-] Hw.
  apply: reg_synced_set_other; last exact: (sy_arg HS Ev (Harg Hw)).
  by [].
- move=> ww. rewrite Ew => -[<-] Hpg Hcf.
  have Hcf' : cargfree v = true.
  { move: Hcf. rewrite /cargfree Esg Wsg Epd Wpd Hpd has_rcons negb_or.
    move=> /andP [/andP [Hk1 Hsg1] _].
    apply/andP. split.
    - exact: Hsg1.
    - by case: (k) Hk1. }
  apply: reg_synced_set_other; last exact: (sy_argp HS Ev Hpg Hcf').
  by [].
- exact: (sy_mem HS).
- move=> ww b j k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg Wsg in Hk.
  move: Hk. rewrite nth_error_rcons.
  case Hlt: (j < size (sv_sig v)).
  + move=> Hk. exact: (sy_frame HS Ev Hb Hk Hs).
  + case Hje: (j == size (sv_sig v)) => // -[Ek1]. subst k1.
    move/eqP: Hje => Hje. subst j.
    exact: (sy_pend HS Ev Hb Hpd Hs).
- move=> ww b k1. rewrite Ew => -[<-] Hb.
  rewrite Epd Wpd. by [].
- exact: (sy_chain HS).
Qed.

(* The pop bump (Minus R_SP R_ONE R_SP): the frame top becomes the pending
   slot; [sv_sig v = rcons (sv_sig v') k] is the clean spelling of the
   checker's rev-split. *)

Lemma sync_pop (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tv : value) (vt : value_tag) (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w0 : sv) (k : class3) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w0 ->
  sv_le v' w0 ->
  sv_sig v = rcons (sv_sig v') k ->
  sv_pend v = None ->
  sv_pend v' = Some k ->
  (sv_a1 v' = AU -> sv_a1 v = AU) ->
  (sv_a2 v' = AU -> sv_a2 v = AU) ->
  (sv_a1 v' = ASp -> False) ->
  (sv_a2 v' = ASp -> False) ->
  sv_arg v' = sv_arg v ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set R_SP tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat R_SP)) (Atom w vt))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Hpd0 Wpd Wa1u Wa2u Wa1s Wa2s Warg HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
have Harg : sv_arg w0 = true -> sv_arg v = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  rewrite -Warg. move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
have Hsg_at : forall j k1, nth_error (sv_sig v') j = Some k1 ->
    nth_error (sv_sig v) j = Some k1.
{ move=> j k1 Hk.
  have Hjlt : j < size (sv_sig v') := nth_error_size Hk.
  by rewrite Wsg nth_error_rcons Hjlt. }
constructor.
- apply: reg_synced_set_other; last exact: (sy_com HS). by [].
- move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a1 v = AU.
  { apply: Wa1u. move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_set_other; last exact: (sy_a1u HS Ev Hav). by [].
- move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a2 v = AU.
  { apply: Wa2u. move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_set_other; last exact: (sy_a2u HS Ev Hav). by [].
- move=> ww. rewrite Ew => -[<-] Hasp _.
  exfalso. apply: Wa1s.
  move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq.
- move=> ww. rewrite Ew => -[<-] Hasp _.
  exfalso. apply: Wa2s.
  move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq.
- move=> ww. rewrite Ew => -[<-] Hw.
  apply: reg_synced_set_other; last exact: (sy_arg HS Ev (Harg Hw)).
  by [].
- move=> ww. rewrite Ew => -[<-] Hpg Hcf.
  have Hcf' : cargfree v = true.
  { move: Hcf. rewrite /cargfree Esg Epd Wpd Hpd0 Wsg has_rcons negb_or.
    move=> /andP [Hsg1 Hk1].
    rewrite andbT. apply/andP. split.
    - by case: (k) Hk1.
    - exact: Hsg1. }
  apply: reg_synced_set_other; last exact: (sy_argp HS Ev Hpg Hcf').
  by [].
- exact: (sy_mem HS).
- move=> ww b j k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg in Hk.
  exact: (sy_frame HS Ev Hb (Hsg_at _ _ Hk) Hs).
- move=> ww b k1. rewrite Ew Ec => -[<-] Hb.
  rewrite Epd Wpd => -[Ek1]. subst k1.
  rewrite Esg => Hs.
  have Hk : nth_error (sv_sig v) (size (sv_sig v')) = Some k.
  { by rewrite Wsg nth_error_rcons ltnn eqxx. }
  exact: (sy_frame HS Ev Hb Hk Hs).
- exact: (sy_chain HS).
Qed.

(* The per-opcode fleet: BINOP.  The vgeneric arm is the register fleet
   master; the Add/Minus R_SP bumps are [sync_push]/[sync_pop] (R_SP carries
   no claim, so the written pair needs no [tvrel]). *)

Lemma sync_binop_gen (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (r1 r2 r3 : register) (tv : value) (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w0 : sv) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w0 ->
  sv_le v' w0 ->
  vgeneric_binop v r1 r2 r3 = Some v' ->
  tvrel cmapS amap (Transitional.MVal Other tv) w ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set r3 tv Other tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r3)) (Atom w Other))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Hg Hv HS.
move: Hg. rewrite /vgeneric_binop.
case: (is_r r3 R_SP || is_r r3 R_RA) => //.
case: (sv_pend v) => [?|] //.
case: (t_eqb (rtaint v r1) AU && t_eqb (rtaint v r2) AU) => //.
move=> -[Evv]. subst v'.
have Wsg : sv_sig (warg_w r3 (wone r3 false (wtaint r3 AU v))) = sv_sig v.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r r3 R_AUX1); case: (is_r r3 R_AUX2);
     case: (is_r r3 R_ONE); case: (is_r r3 R_ARG). }
have Wpd : sv_pend (warg_w r3 (wone r3 false (wtaint r3 AU v)))
           = sv_pend v.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r r3 R_AUX1); case: (is_r r3 R_AUX2);
     case: (is_r r3 R_ONE); case: (is_r r3 R_ARG). }
have Wa1 : is_r r3 R_AUX1 = false ->
  sv_a1 (warg_w r3 (wone r3 false (wtaint r3 AU v))) = sv_a1 v.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r r3 R_AUX2); case: (is_r r3 R_ONE);
     case: (is_r r3 R_ARG). }
have Wa2 : is_r r3 R_AUX2 = false ->
  sv_a2 (warg_w r3 (wone r3 false (wtaint r3 AU v))) = sv_a2 v.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r r3 R_AUX1); case: (is_r r3 R_ONE);
     case: (is_r r3 R_ARG). }
have Warg : is_r r3 R_ARG = false ->
  sv_arg (warg_w r3 (wone r3 false (wtaint r3 AU v))) = sv_arg v.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r r3 R_AUX1); case: (is_r r3 R_AUX2);
     case: (is_r r3 R_ONE). }
have Wek : sv_ek (warg_w r3 (wone r3 false (wtaint r3 AU v))) = sv_ek v.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r r3 R_AUX1); case: (is_r r3 R_AUX2);
     case: (is_r r3 R_ONE); case: (is_r r3 R_ARG). }
exact: (sync_regw_synced Ev Ew Hle Wsg Wpd Wa1 Wa2 Warg Wek Hv HS).
Qed.

Lemma sync_binop (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (op : Values.binop) (r1 r2 r3 : register) (tv : value) (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrBinOp op r1 r2 r3) tg c ->
  tvrel cmapS amap (Transitional.MVal Other tv) w ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set r3 tv Other tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r3)) (Atom w Other))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Hv HS.
have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w0 [Ew Hle]] := Hnx isT.
move: Evs => /=.
case Eop: op => /=.
+
  case Eph: (sv_ph v) => //.
  case Etr: [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
              & sv_one v]; last first.
  { move=> Hg. exact: (sync_binop_gen Ev Ew Hle Hg Hv HS). }
  case Epd0: (sv_pend v) => [k|] //=; last by case: (sv_sc v).
  have Hsplit : forall Q : Prop,
      (sc_eqb (sv_sc v) SCpark = false ->
       v' = SV PBody (rcons (sv_sig v) k) None
              (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v)
              (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v)
              (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v) -> Q) ->
      (match sv_sc v with
       | SCpark => None
       | _ => Some (SV PBody (rcons (sv_sig v) k) None
                      (if t_eqb (sv_a1 v) ASp then ADead
                       else sv_a1 v)
                      (if t_eqb (sv_a2 v) ASp then ADead
                       else sv_a2 v)
                      (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
       end = Some v' -> Q).
  { move=> Q HQ.
    by case: (sv_sc v) HQ => HQ // -[E]; apply: HQ. }
  apply: Hsplit => Hnp Evv. subst v'.
  case/and4P: Etr => _ _ E3s _.
  have Er3 : r3 = R_SP := is_r_eq E3s.
  subst r3.
  have Wa1u : (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v) = AU ->
              sv_a1 v = AU.
  { by case: (t_eqb (sv_a1 v) ASp). }
  have Wa2u : (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v) = AU ->
              sv_a2 v = AU.
  { by case: (t_eqb (sv_a2 v) ASp). }
  have Wa1s : (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v) = ASp ->
              False.
  { case Ea: (t_eqb (sv_a1 v) ASp) => // E.
    by move: Ea; rewrite E t_eqb_refl. }
  have Wa2s : (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v) = ASp ->
              False.
  { case Ea: (t_eqb (sv_a2 v) ASp) => // E.
    by move: Ea; rewrite E t_eqb_refl. }
  apply: (sync_push tv Other w
            Ev Ew Hle Epd0 _ _ Wa1u Wa2u Wa1s Wa2s _ HS).
  - exact: erefl.
  - exact: erefl.
  - exact: erefl.
+
  case Eph: (sv_ph v) => //.
  case Etr: [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
              & sv_one v]; last first.
  { move=> Hg. exact: (sync_binop_gen Ev Ew Hle Hg Hv HS). }
  case Epd0: (sv_pend v) => [k0|]; first by case: (sv_sc v).
  case Erev: (rev (sv_sig v)) => [|k rest]; first by case: (sv_sc v).
  have Hsplit : forall Q : Prop,
      (sc_eqb (sv_sc v) SCpark = false ->
       v' = SV PBody (rev rest) (Some k)
              (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v)
              (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v)
              (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v) -> Q) ->
      (match sv_sc v with
       | SCpark => None
       | _ => Some (SV PBody (rev rest) (Some k)
                      (if t_eqb (sv_a1 v) ASp then ADead
                       else sv_a1 v)
                      (if t_eqb (sv_a2 v) ASp then ADead
                       else sv_a2 v)
                      (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
       end = Some v' -> Q).
  { move=> Q HQ.
    by case: (sv_sc v) HQ => HQ // -[E]; apply: HQ. }
  apply: Hsplit => Hnp Evv. subst v'.
  case/and4P: Etr => _ _ E3s _.
  have Er3 : r3 = R_SP := is_r_eq E3s.
  subst r3.
  have Esig : sv_sig v = rcons (rev rest) k.
  { by rewrite -(revK (sv_sig v)) Erev rev_cons. }
  have Wa1u : (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v) = AU ->
              sv_a1 v = AU.
  { by case: (t_eqb (sv_a1 v) ASp). }
  have Wa2u : (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v) = AU ->
              sv_a2 v = AU.
  { by case: (t_eqb (sv_a2 v) ASp). }
  have Wa1s : (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v) = ASp ->
              False.
  { case Ea: (t_eqb (sv_a1 v) ASp) => // E.
    by move: Ea; rewrite E t_eqb_refl. }
  have Wa2s : (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v) = ASp ->
              False.
  { case Ea: (t_eqb (sv_a2 v) ASp) => // E.
    by move: Ea; rewrite E t_eqb_refl. }
  apply: (sync_pop tv Other w
            Ev Ew Hle Esig Epd0 _ Wa1u Wa2u Wa1s Wa2s _ HS).
  - exact: erefl.
  - exact: erefl.
+
  case Eph: (sv_ph v) => // Hg.
  exact: (sync_binop_gen Ev Ew Hle Hg Hv HS).
+
  case Eph: (sv_ph v) => // Hg.
  exact: (sync_binop_gen Ev Ew Hle Hg Hv HS).
+
  case Eph: (sv_ph v) => // Hg.
  exact: (sync_binop_gen Ev Ew Hle Hg Hv HS).
Qed.

Lemma to_nat_neq (ra rb : register) : ra <> rb ->
  Intermediate.Register.to_nat ra <> Intermediate.Register.to_nat rb.
Proof.
move=> Hne E. apply: Hne.
apply: is_r_eq. by rewrite /is_r E PeanoNat.Nat.eqb_refl.
Qed.

(* Register-write masters generalized over a memory step: like
   [sync_regw]/[sync_regw_synced] but the caller supplies (a) a uniform
   [cell_synced] transport and (b) the successor pend column as a
   disjunction (the pop arms drop the pend slot). *)

Lemma sync_regw_store (amap amap' : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs tregs' : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w : sv) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w ->
  sv_le v' w ->
  sv_sig v' = sv_sig v ->
  (sv_pend v' = sv_pend v \/ sv_pend v' = None) ->
  reg_syncedS amap' tregs' mregs' R_COM ->
  (sv_a1 w = AU -> reg_syncedS amap' tregs' mregs' R_AUX1) ->
  (sv_a2 w = AU -> reg_syncedS amap' tregs' mregs' R_AUX2) ->
  (sv_a1 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap' tregs' mregs' R_AUX1) ->
  (sv_a2 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap' tregs' mregs' R_AUX2) ->
  (sv_arg w = true -> reg_syncedS amap' tregs' mregs' R_ARG) ->
  (parg_of chain = true -> cargfree w = true ->
     reg_syncedS amap' tregs' mregs' R_ARG) ->
  (forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap' tmem' mmem' c0 b0 j0) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap' tmem' tregs' mregs' mmem' (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Wpd SCOM SA1U SA2U SA1S SA2S SARG SARGP Hcells HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
rewrite Wsg in Esg.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
- exact: SCOM.
- move=> w0; rewrite Ew => -[<-]. exact: SA1U.
- move=> w0; rewrite Ew => -[<-]. exact: SA2U.
- move=> w0; rewrite Ew => -[<-]. exact: SA1S.
- move=> w0; rewrite Ew => -[<-]. exact: SA2S.
- move=> w0; rewrite Ew => -[<-]. exact: SARG.
- move=> w0; rewrite Ew => -[<-]. exact: SARGP.
- move=> c0 b0 j0 Hb0.
  exact: (Hcells _ _ _ (sy_mem HS Hb0)).
- move=> w0 b j k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg in Hk.
  exact: (Hcells _ _ _ (sy_frame HS Ev Hb Hk Hs)).
- move=> w0 b k. rewrite Ew Ec => -[<-] Hb Hk Hs.
  case: Wpd => Wpd; last first.
  { move: Hk. rewrite Epd Wpd. by []. }
  rewrite Epd Wpd in Hk. rewrite Esg in Hs.
  rewrite Esg.
  exact: (Hcells _ _ _ (sy_pend HS Ev Hb Hk Hs)).
- move=> i A j k HA Hk Hs.
  exact: (Hcells _ _ _ (sy_chain HS HA Hk Hs)).
Qed.

Lemma sync_regw_synced_store (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t) (r : register) (tv : value) (vt : value_tag)
    (w : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w0 : sv) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w0 ->
  sv_le v' w0 ->
  sv_sig v' = sv_sig v ->
  (sv_pend v' = sv_pend v \/
   (sv_pend v' = None /\ sv_pend v <> Some CArg)) ->
  (is_r r R_AUX1 = false -> sv_a1 v' = sv_a1 v) ->
  (is_r r R_AUX2 = false -> sv_a2 v' = sv_a2 v) ->
  (is_r r R_ARG = false -> sv_arg v' = sv_arg v) ->
  sv_ek v' = sv_ek v ->
  tvrel cmapS amap (Transitional.MVal vt tv) w ->
  (forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap tmem' mmem' c0 b0 j0) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) (Atom w vt))
    mmem' (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Wpd Wa1 Wa2 Warg Wek Hv Hcells HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
have Harg : sv_arg w0 = true -> sv_arg v' = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
have Wpd' : sv_pend v' = sv_pend v \/ sv_pend v' = None.
{ case: Wpd => [W|[W _]]; [by left | by right]. }
apply: (sync_regw_store Ev Ew Hle Wsg Wpd') => //.
-
  case Ecom: (is_r r R_COM).
  + rewrite (is_r_eq Ecom) in Hv *. exact: reg_synced_set Hv.
  + apply: reg_synced_set_other; last exact: (sy_com HS).
    move=> E. move: Ecom. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hau.
  case Ea1: (is_r r R_AUX1).
  + rewrite (is_r_eq Ea1) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a1 v = AU.
    { rewrite -(Wa1 Ea1).
      move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_set_other; last exact: (sy_a1u HS Ev Hav).
    move=> E. move: Ea1. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hau.
  case Ea2: (is_r r R_AUX2).
  + rewrite (is_r_eq Ea2) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a2 v = AU.
    { rewrite -(Wa2 Ea2).
      move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_set_other; last exact: (sy_a2u HS Ev Hav).
    move=> E. move: Ea2. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hasp Hcond.
  case Ea1: (is_r r R_AUX1).
  + rewrite (is_r_eq Ea1) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a1 v = ASp.
    { rewrite -(Wa1 Ea1).
      move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcond' : sv_ek v = true \/ sv_sig v <> [::].
    { move: Hcond. rewrite Eek Wek Esg Wsg. exact: id. }
    apply: reg_synced_set_other;
      last exact: (sy_a1sp HS Ev Hav Hcond').
    move=> E. move: Ea1. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hasp Hcond.
  case Ea2: (is_r r R_AUX2).
  + rewrite (is_r_eq Ea2) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_a2 v = ASp.
    { rewrite -(Wa2 Ea2).
      move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcond' : sv_ek v = true \/ sv_sig v <> [::].
    { move: Hcond. rewrite Eek Wek Esg Wsg. exact: id. }
    apply: reg_synced_set_other;
      last exact: (sy_a2sp HS Ev Hav Hcond').
    move=> E. move: Ea2. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hw0.
  case Earg: (is_r r R_ARG).
  + rewrite (is_r_eq Earg) in Hv *. exact: reg_synced_set Hv.
  + have Hav : sv_arg v = true by rewrite -(Warg Earg) (Harg Hw0).
    apply: reg_synced_set_other; last exact: (sy_arg HS Ev Hav).
    move=> E. move: Earg. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
-
  move=> Hpg Hcf.
  case Earg: (is_r r R_ARG).
  + rewrite (is_r_eq Earg) in Hv *. exact: reg_synced_set Hv.
  + have Hcf' : cargfree v = true.
    { move: Hcf. rewrite /cargfree Esg Wsg Epd.
      case: Wpd => [W|[W HpdC]].
      - rewrite W. exact: id.
      - rewrite W /=.
        move=> /andP [Hsg1 _].
        apply/andP. split.
        + exact: Hsg1.
        + case Epv: (sv_pend v) HpdC => [k0|] HpdC //.
          by case: k0 Epv HpdC. }
    apply: reg_synced_set_other; last exact: (sy_argp HS Ev Hpg Hcf').
    move=> E. move: Earg. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
- exact: Hcells.
- exact: HS.
Qed.

(* Load-side helpers: the T lookup decomposition and the write-back retag
   preserving [tvrel]/[cellrel]. *)

Lemma load_shape (mem : Transitional.Memory.t) (ptr : Pointer.t)
    (cell : Transitional.tvalue * mem_tag) :
  Transitional.Memory.load mem ptr = Some cell ->
  exists cm blk,
    [/\ getm mem (Pointer.component ptr) = Some cm,
        getm (Transitional.Memory.content cm) (Pointer.block ptr)
        = Some blk
      & List.nth_error blk (BinInt.Z.to_nat (Pointer.offset ptr))
        = Some cell].
Proof.
case: ptr => [[c b] o].
rewrite /Transitional.Memory.load /=.
case Hc: (getm mem c) => [cm|] //=.
rewrite /Transitional.Memory.load_b.
case Hb: (getm (Transitional.Memory.content cm) b) => [blk|] //.
case Ho: (BinInt.Z.leb 0 o) => // Hnth.
exists cm, blk.
split.
- exact: erefl.
- exact: Hb.
- exact: Hnth.
Qed.

Lemma tvrel_retag_s (amap : amap_t) (tval : Transitional.tvalue)
    (w : mword mt) :
  tvrel cmapS amap tval w ->
  tvrel cmapS amap
    {| Transitional.val := Transitional.val tval;
       Transitional.tvtag := moved_tag (Transitional.tvtag tval) |} w.
Proof.
move: tval => [vt v]. rewrite /tvrel /=.
by case: vt.
Qed.

Lemma tvrel_eta_s (amap : amap_t) (tv : Transitional.tvalue)
    (w : mword mt) :
  tvrel cmapS amap tv w ->
  tvrel cmapS amap
    (Transitional.MVal (Transitional.tvtag tv) (Transitional.val tv)) w.
Proof. by case: tv. Qed.

(* The per-opcode fleet: LOAD, user/scratch arms (address register not R_SP,
   plus the PPost scratch reload).  The loaded cell sits outside the frame
   blocks, so [sy_mem] makes it synced, the write-back retag keeps it synced,
   and the target register gets a synced pair — the fleet master applies. *)

Lemma sync_load_user (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t)
    (v : Transitional.tvalue * mem_tag)
    (wmc : mword mt) (mtg : mem_tag) (a : nat)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrLoad r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = false ->
  (Pointer.block ptr \in F (Pointer.component ptr)) = false ->
  Transitional.Memory.load tmem ptr = Some v ->
  Transitional.Memory.store tmem ptr
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
     {| vtag := moved_tag (Transitional.tvtag v.1);
        color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mmem (@word_of_nat (word_size mt)
               (a + BinInt.Z.to_nat (Pointer.offset ptr)))
    = Some (Atom wmc mtg) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2 (Transitional.val v.1)
       (Transitional.tvtag v.1) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom wmc (Transitional.tvtag v.1)))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                    color := Pointer.component ptr; entry := None;
                    is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Hbnf Hld Hst Ha Hmc HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w0 [Ew Hle]] := Hnx isT.
have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
have Hrelmc : cellrel cmapS amap v (Atom wmc mtg).
{ have Hcs : cell_synced amap tmem mmem (Pointer.component ptr)
      (Pointer.block ptr) (BinInt.Z.to_nat (Pointer.offset ptr)).
  { apply: (sy_mem HS). exact: Hbnf. }
  exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha Hmc). }
have Hrel' : cellrel cmapS amap
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
     {| vtag := moved_tag (Transitional.tvtag v.1);
        color := Pointer.component ptr; entry := None;
        is_code := false |})
    (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                 color := Pointer.component ptr; entry := None;
                 is_code := false |}).
{ case: Hrelmc => Hvmc Htmc Hvtmc.
  split.
  - exact: (tvrel_retag_s Hvmc).
  - exact: erefl.
  - exact: erefl. }
have Hcells : forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hc0.
  apply: (cell_synced_store Haok Hst Ha _ Hc0).
  move=> _. exact: Hrel'. }
have Hv2 : tvrel cmapS amap
    (Transitional.MVal (Transitional.tvtag v.1) (Transitional.val v.1))
    wmc.
{ case: Hrelmc => Hvmc _ _. exact: (tvrel_eta_s Hvmc). }
move: Evs => /=.
case Eph: (sv_ph v0) => //.
-
  rewrite E1sp.
  case Epd0: (sv_pend v0) => //.
  case Ert: (rtaint v0 r1) => //.
  +
    case Etr: [&& is_r r2 R_AUX1, sc_eqb (sv_sc v0) SCnone
              & cseq_eqb (sv_sig v0) [:: CSp]] => //.
    move=> -[Evv]. subst v'.
    case/and3P: Etr => E2a1 _ _.
    have Er2 : r2 = R_AUX1 := is_r_eq E2a1.
    subst r2.
    have Wpd : sv_pend (wtaint R_AUX1 ASp v0) = sv_pend v0.
    { exact: erefl. }
    have Wa1 : is_r R_AUX1 R_AUX1 = false ->
      sv_a1 (wtaint R_AUX1 ASp v0) = sv_a1 v0.
    { by []. }
    have Wa2 : is_r R_AUX1 R_AUX2 = false ->
      sv_a2 (wtaint R_AUX1 ASp v0) = sv_a2 v0.
    { move=> _. exact: erefl. }
    have Warg : is_r R_AUX1 R_ARG = false ->
      sv_arg (wtaint R_AUX1 ASp v0) = sv_arg v0.
    { move=> _. exact: erefl. }
    exact: (sync_regw_synced_store Ev Ew Hle (erefl _) (or_introl Wpd)
              Wa1 Wa2 Warg (erefl _) Hv2 Hcells HS).
  +
    case E2t: (is_r r2 R_SP || is_r r2 R_RA) => //.
    move=> -[Evv]. subst v'.
    have Wsg : sv_sig (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_sig v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wpd : sv_pend (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_pend v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wa1 : is_r r2 R_AUX1 = false ->
      sv_a1 (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_a1 v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX2); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Wa2 : is_r r2 R_AUX2 = false ->
      sv_a2 (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_a2 v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Warg : is_r r2 R_ARG = false ->
      sv_arg (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_arg v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE). }
    have Wek : sv_ek (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_ek v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    exact: (sync_regw_synced_store Ev Ew Hle Wsg (or_introl Wpd)
              Wa1 Wa2 Warg Wek Hv2 Hcells HS).
  +
    case E2t: (is_r r2 R_SP || is_r r2 R_RA) => //.
    move=> -[Evv]. subst v'.
    have Wsg : sv_sig (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_sig v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wpd : sv_pend (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_pend v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wa1 : is_r r2 R_AUX1 = false ->
      sv_a1 (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_a1 v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX2); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Wa2 : is_r r2 R_AUX2 = false ->
      sv_a2 (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_a2 v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Warg : is_r r2 R_ARG = false ->
      sv_arg (warg_w r2 (wone r2 false (wtaint r2 AU v0))) = sv_arg v0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE). }
    have Wek : sv_ek (warg_w r2 (wone r2 false (wtaint r2 AU v0)))
               = sv_ek v0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    exact: (sync_regw_synced_store Ev Ew Hle Wsg (or_introl Wpd)
              Wa1 Wa2 Warg Wek Hv2 Hcells HS).
-
  case Epd0: (sv_pend v0) => //.
  case Etr: [&& t_eqb (rtaint v0 r1) AScr, is_r r2 R_SP
            & ~~ nocra (sv_sig v0)] => //.
  move=> -[Evv]. subst v'.
  case/and3P: Etr => _ E2sp _.
  have Er2 : r2 = R_SP := is_r_eq E2sp.
  subst r2.
  have HpdC : sv_pend v0 <> Some CArg.
  { by rewrite Epd0. }
  apply: (sync_regw_synced_store Ev Ew Hle (erefl _)
            (or_intror (conj (erefl _) HpdC))
            _ _ _ (erefl _) Hv2 Hcells HS).
  + move=> _. exact: erefl.
  + move=> _. exact: erefl.
  + move=> _. exact: erefl.
Qed.

(* [cell_synced] transport for cells other than the written one, and the
   pc-preserving cells-only claims transport.  Together they let the
   frame-pop loads (whose loaded cell may be clobbed and carries no claim)
   move the memories first and the registers after. *)

Lemma cell_synced_store_other (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom})
    (ptr : Pointer.t) (cellW : Transitional.tvalue * mem_tag)
    (mc' : @matom mt) (aptr : nat)
    (c : Component.id) (b : Block.id) (j : nat) :
  amap_ok PB amap tmem ->
  Transitional.Memory.store tmem ptr cellW = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some aptr ->
  [&& c == Pointer.component ptr, b == Pointer.block ptr
    & j == BinInt.Z.to_nat (Pointer.offset ptr)] = false ->
  cell_synced amap tmem mmem c b j ->
  cell_synced amap tmem'
    (setm mmem
       (@word_of_nat (word_size mt)
          (aptr + BinInt.Z.to_nat (Pointer.offset ptr))) mc')
    c b j.
Proof.
move=> Haok Hst Haptr Hne HS.
apply: (cell_synced_store Haok Hst Haptr _ HS).
move=> E. exfalso. by rewrite E in Hne.
Qed.

Lemma cell_synced_store_new (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom})
    (ptr : Pointer.t) (cellW : Transitional.tvalue * mem_tag)
    (mc' : @matom mt) (aptr : nat) :
  Transitional.Memory.store tmem ptr cellW = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some aptr ->
  cellrel cmapS amap cellW mc' ->
  cell_synced amap tmem'
    (setm mmem
       (@word_of_nat (word_size mt)
          (aptr + BinInt.Z.to_nat (Pointer.offset ptr))) mc')
    (Pointer.component ptr) (Pointer.block ptr)
    (BinInt.Z.to_nat (Pointer.offset ptr)).
Proof.
move=> Hst Haptr Hrel.
have [cm [chunk [chunk' [Hcm Hchunk Hoff Hupd Emem']]]] := store_shape Hst.
move=> cm2 blk2 cell a mc Hc2 Hb2 Hnth Ha2 Hmc2.
have Ea : a = aptr by move: Ha2; rewrite Haptr => -[].
subst a.
move: Hmc2. rewrite setmE eqxx => -[<-].
move: Hc2 Hb2 Hnth.
rewrite Emem' setmE eqxx => -[<-] /=.
rewrite setmE eqxx => -[<-].
rewrite (list_upd_nth_error_same Hupd) => -[<-].
exact: Hrel.
Qed.

Lemma sync_claims_cells (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v : sv) :
  svat pc = Some v ->
  (forall c0 b0 j0, (b0 \in F c0) = false ->
     cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap tmem' mmem' c0 b0 j0) ->
  (forall b j0 k, cur = Some b -> nth_error (sv_sig v) j0 = Some k ->
     cell_synced amap tmem mmem (Pointer.component pc) b j0 ->
     cell_synced amap tmem' mmem' (Pointer.component pc) b j0) ->
  (forall b k, cur = Some b -> sv_pend v = Some k ->
     synced_slot (parg_of chain) k (size (sv_sig v)) = true ->
     cell_synced amap tmem mmem (Pointer.component pc) b
       (size (sv_sig v)) ->
     cell_synced amap tmem' mmem' (Pointer.component pc) b
       (size (sv_sig v))) ->
  (forall i A j0, nth_error chain i = Some A ->
     cell_synced amap tmem mmem (MDisc.a_comp A) (MDisc.a_blk A) j0 ->
     cell_synced amap tmem' mmem' (MDisc.a_comp A) (MDisc.a_blk A) j0) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem' tregs mregs mmem' pc cur chain F.
Proof.
move=> Ev Hm Hf Hp Hc HS.
constructor.
- exact: (sy_com HS).
- exact: (sy_a1u HS).
- exact: (sy_a2u HS).
- exact: (sy_a1sp HS).
- exact: (sy_a2sp HS).
- exact: (sy_arg HS).
- exact: (sy_argp HS).
- move=> c0 b0 j0 Hb0.
  exact: (Hm _ _ _ Hb0 (sy_mem HS Hb0)).
- move=> w0 b j k Ew0 Hb Hk Hs.
  have Evw : w0 = v by move: Ew0; rewrite Ev => -[].
  subst w0.
  exact: (Hf _ _ _ Hb Hk (sy_frame HS Ev Hb Hk Hs)).
- move=> w0 b k Ew0 Hb Hk Hs.
  have Evw : w0 = v by move: Ew0; rewrite Ev => -[].
  subst w0.
  exact: (Hp _ _ Hb Hk Hs (sy_pend HS Ev Hb Hk Hs)).
- move=> i A j k HA Hk Hs.
  exact: (Hc _ _ _ HA (sy_chain HS HA Hk Hs)).
Qed.

(* The per-opcode fleet: LOAD, frame-pop arms (address register IS R_SP; the
   pend slot returns to a register).  CU and the gated deep-CSp reloads read
   a CLAIMED pend cell (synced pair, fleet master applies); CRa/CArg/pos-0-CSp
   reloads read an UNCLAIMED cell whose target carries no successor claim, so
   the transport goes memories-first then registers. *)

Lemma sync_load_pop (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t)
    (v : Transitional.tvalue * mem_tag)
    (wmc : mword mt) (mtg : mem_tag) (a : nat) (bcur : Block.id)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrLoad r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = true ->
  svat pc = Some sv0 ->
  cur = Some bcur ->
  (bcur \in F (Pointer.component pc)) = true ->
  ptr = (Pointer.component pc, bcur,
         BinInt.Z.of_nat (size (sv_sig sv0))) ->
  (forall i A, nth_error chain i = Some A ->
     (MDisc.a_comp A == Pointer.component pc) &&
     (MDisc.a_blk A == bcur) = false) ->
  Transitional.Memory.load tmem ptr = Some v ->
  Transitional.Memory.store tmem ptr
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
     {| vtag := moved_tag (Transitional.tvtag v.1);
        color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mmem (@word_of_nat (word_size mt)
               (a + BinInt.Z.to_nat (Pointer.offset ptr)))
    = Some (Atom wmc mtg) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2 (Transitional.val v.1)
       (Transitional.tvtag v.1) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom wmc (Transitional.tvtag v.1)))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                    color := Pointer.component ptr; entry := None;
                    is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Ev0 Hcur Hbcur Eptr Hchdis Hld Hst Ha Hmc HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
have Ecptr : Pointer.component ptr = Pointer.component pc.
{ by rewrite Eptr. }
have Ebptr : Pointer.block ptr = bcur.
{ by rewrite Eptr. }
have Eoptr : BinInt.Z.to_nat (Pointer.offset ptr) = size (sv_sig sv0).
{ by rewrite Eptr /= Nat2Z.id. }
have Hne_mem : forall c0 b0 j0, (b0 \in F c0) = false ->
    [&& c0 == Pointer.component ptr, b0 == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> c0 b0 j0 Hb0.
  apply/negbTE/negP => /and3P [/eqP Ec0 /eqP Eb0 _].
  subst c0 b0.
  by rewrite Ebptr Ecptr Hbcur in Hb0. }
have Hne_frame : forall j0, j0 < size (sv_sig sv0) ->
    [&& Pointer.component pc == Pointer.component ptr,
        bcur == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> j0 Hj0.
  apply/negbTE/negP => /and3P [_ _ /eqP Ej0].
  move: Hj0. rewrite Ej0 Eoptr ltnn. by []. }
have Hne_chain : forall i A j0, nth_error chain i = Some A ->
    [&& MDisc.a_comp A == Pointer.component ptr,
        MDisc.a_blk A == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> i A j0 HA.
  apply/negbTE/negP => /and3P [/eqP EcA /eqP EbA _].
  have := Hchdis _ _ HA.
  by rewrite EcA EbA Ecptr Ebptr !eqxx. }
have HmemT : forall c0 b0 j0, (b0 \in F c0) = false ->
    cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hb0 Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_mem _ _ _ Hb0) Hc0). }
have HframeT : forall b j0 k, cur = Some b ->
    nth_error (sv_sig sv0) j0 = Some k ->
    cell_synced amap tmem mmem (Pointer.component pc) b j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      (Pointer.component pc) b j0.
{ move=> b j0 k Hb Hk Hc0.
  have Eb : b = bcur by move: Hb; rewrite Hcur => -[].
  subst b.
  have Hj0 : j0 < size (sv_sig sv0) := nth_error_size Hk.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_frame _ Hj0) Hc0). }
have HchainT : forall i A j0, nth_error chain i = Some A ->
    cell_synced amap tmem mmem (MDisc.a_comp A) (MDisc.a_blk A) j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      (MDisc.a_comp A) (MDisc.a_blk A) j0.
{ move=> i A j0 HA Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_chain _ _ j0 HA) Hc0). }
move: Evs => /=.
case Eph: (sv_ph sv0) => //.
-
  rewrite E1sp.
  case Epd0: (sv_pend sv0) => [k|] //.
  case: k Epd0 => Epd0.
  +
    case E2ra: (is_r r2 R_RA) => // -[Evv]. subst v'.
    have Er2 : r2 = R_RA := is_r_eq E2ra.
    subst r2.
    have HpendT : forall b k, cur = Some b -> sv_pend sv0 = Some k ->
        synced_slot (parg_of chain) k (size (sv_sig sv0)) = true ->
        cell_synced amap tmem mmem (Pointer.component pc) b
          (size (sv_sig sv0)) ->
        cell_synced amap tmem'
          (setm mmem (@word_of_nat (word_size mt)
                        (a + BinInt.Z.to_nat (Pointer.offset ptr)))
             (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                          color := Pointer.component ptr; entry := None;
                          is_code := false |}))
          (Pointer.component pc) b (size (sv_sig sv0)).
    { move=> b k Hb Hk Hs Hold. exfalso.
      move: Hk. rewrite Epd0 => -[Ek]. subst k.
      by move: Hs. }
    have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
    have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
    apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
    * apply: reg_synced_set_other; first by [].
      exact: (sy_com HS').
    * move=> Hau.
      have Hav : sv_a1 sv0 = AU.
      { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1u HS' Ev Hav).
    * move=> Hau.
      have Hav : sv_a2 sv0 = AU.
      { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2u HS' Ev Hav).
    * move=> Hasp Hcond.
      have Hav : sv_a1 sv0 = ASp.
      { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1sp HS' Ev Hav Hcondv).
    * move=> Hasp Hcond.
      have Hav : sv_a2 sv0 = ASp.
      { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2sp HS' Ev Hav Hcondv).
    * move=> Hw0arg.
      have Hargv : sv_arg sv0 = true.
      { move: Hle => /and5P [_ _ _ HA _].
        move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_arg HS' Ev Hargv).
    * move=> Hpg Hcf.
      have Hcf' : cargfree sv0 = true.
      { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
        move=> /andP [Hsg1 _]. by rewrite Hsg1. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_argp HS' Ev Hpg Hcf').
    * move=> c0 b0 j0 Hc0. exact: Hc0.
    * exact: HS'.
  +
    case E2t: (is_r r2 R_SP && cseq_eqb (sv_sig sv0) [::]).
    *
      move=> -[Evv]. subst v'.
      case/andP: E2t => E2sp Esgnil.
      have Er2 : r2 = R_SP := is_r_eq E2sp.
      subst r2.
      have Esg0 : sv_sig sv0 = [::].
      { by case: (sv_sig sv0) Esgnil. }
      have HpendT : forall b k, cur = Some b -> sv_pend sv0 = Some k ->
          synced_slot (parg_of chain) k (size (sv_sig sv0)) = true ->
          cell_synced amap tmem mmem (Pointer.component pc) b
            (size (sv_sig sv0)) ->
          cell_synced amap tmem'
            (setm mmem (@word_of_nat (word_size mt)
                          (a + BinInt.Z.to_nat (Pointer.offset ptr)))
               (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                            color := Pointer.component ptr; entry := None;
                            is_code := false |}))
            (Pointer.component pc) b (size (sv_sig sv0)).
      { move=> b k Hb Hk Hs Hold. exfalso.
        move: Hk. rewrite Epd0 => -[Ek]. subst k.
        move: Hs. rewrite Esg0. by []. }
      have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
      have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
      apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
      -- apply: reg_synced_set_other; first by [].
         exact: (sy_com HS').
      -- move=> Hau.
         have Hav : sv_a1 sv0 = AU.
         { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a1u HS' Ev Hav).
      -- move=> Hau.
         have Hav : sv_a2 sv0 = AU.
         { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a2u HS' Ev Hav).
      -- move=> Hasp Hcond.
         have Hav : sv_a1 sv0 = ASp.
         { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
         { move: Hcond. rewrite Eek' Esg'. exact: id. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a1sp HS' Ev Hav Hcondv).
      -- move=> Hasp Hcond.
         have Hav : sv_a2 sv0 = ASp.
         { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
         { move: Hcond. rewrite Eek' Esg'. exact: id. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a2sp HS' Ev Hav Hcondv).
      -- move=> Hw0arg.
         have Hargv : sv_arg sv0 = true.
         { move: Hle => /and5P [_ _ _ HA _].
           move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_arg HS' Ev Hargv).
      -- move=> Hpg Hcf.
         have Hcf' : cargfree sv0 = true.
         { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
           move=> /andP [Hsg1 _]. by rewrite Hsg1. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_argp HS' Ev Hpg Hcf').
      -- move=> c0 b0 j0 Hc0. exact: Hc0.
      -- exact: HS'.
    *
      case E2a1: (is_r r2 R_AUX1 && ~~ cseq_eqb (sv_sig sv0) [::])
        => // -[Evv]. subst v'.
      case/andP: E2a1 => E2a1 Hsgne.
      have Er2 : r2 = R_AUX1 := is_r_eq E2a1.
      subst r2.
      have Hpair : cellrel cmapS amap v (Atom wmc mtg).
      { have Hcs : cell_synced amap tmem mmem (Pointer.component pc)
            bcur (size (sv_sig sv0)).
        { apply: (sy_pend HS Ev Hcur Epd0).
          by case: (sv_sig sv0) Hsgne. }
        have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
        rewrite Ecptr in Hcm. rewrite Ebptr in Hblk.
        rewrite Eoptr in Hnth.
        have Ha' := Ha. rewrite Ecptr Ebptr in Ha'.
        have Hmc' := Hmc. rewrite Eoptr in Hmc'.
        exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha' Hmc'). }
      have Hrel' : cellrel cmapS amap
          ({| Transitional.val := Transitional.val v.1;
              Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
           {| vtag := moved_tag (Transitional.tvtag v.1);
              color := Pointer.component ptr; entry := None;
              is_code := false |})
          (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                       color := Pointer.component ptr; entry := None;
                       is_code := false |}).
      { case: Hpair => Hvmc Htmc Hvtmc.
        split.
        - exact: (tvrel_retag_s Hvmc).
        - exact: erefl.
        - exact: erefl. }
      have Hcells : forall c0 b0 j0,
          cell_synced amap tmem mmem c0 b0 j0 ->
          cell_synced amap tmem'
            (setm mmem (@word_of_nat (word_size mt)
                          (a + BinInt.Z.to_nat (Pointer.offset ptr)))
               (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                            color := Pointer.component ptr; entry := None;
                            is_code := false |}))
            c0 b0 j0.
      { move=> c0 b0 j0 Hc0.
        apply: (cell_synced_store Haok Hst Ha _ Hc0).
        move=> _. exact: Hrel'. }
      have Hv2 : tvrel cmapS amap
          (Transitional.MVal (Transitional.tvtag v.1)
             (Transitional.val v.1)) wmc.
      { case: Hpair => Hvmc _ _. exact: (tvrel_eta_s Hvmc). }
      have Wa1 : is_r R_AUX1 R_AUX1 = false ->
        sv_a1 (SV PBody (sv_sig sv0) None ASp (sv_a2 sv0) (sv_sc sv0)
                 (sv_one sv0) (sv_ek sv0) (sv_arg sv0)) = sv_a1 sv0.
      { by []. }
      have Wa2 : is_r R_AUX1 R_AUX2 = false ->
        sv_a2 (SV PBody (sv_sig sv0) None ASp (sv_a2 sv0) (sv_sc sv0)
                 (sv_one sv0) (sv_ek sv0) (sv_arg sv0)) = sv_a2 sv0.
      { move=> _. exact: erefl. }
      have Warg : is_r R_AUX1 R_ARG = false ->
        sv_arg (SV PBody (sv_sig sv0) None ASp (sv_a2 sv0) (sv_sc sv0)
                  (sv_one sv0) (sv_ek sv0) (sv_arg sv0)) = sv_arg sv0.
      { move=> _. exact: erefl. }
      have HpdC : sv_pend sv0 <> Some CArg.
      { by rewrite Epd0. }
      exact: (sync_regw_synced_store Ev Ew Hle (erefl _)
                (or_intror (conj (erefl _) HpdC)) Wa1 Wa2 Warg (erefl _)
                Hv2 Hcells HS).
  +
    case E2t: (is_r r2 R_SP || is_r r2 R_RA) => // -[Evv]. subst v'.
    have Hpair : cellrel cmapS amap v (Atom wmc mtg).
    { have Hcs : cell_synced amap tmem mmem (Pointer.component pc)
          bcur (size (sv_sig sv0)).
      { apply: (sy_pend HS Ev Hcur Epd0).
        exact: erefl. }
      have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
      rewrite Ecptr in Hcm. rewrite Ebptr in Hblk.
      rewrite Eoptr in Hnth.
      have Ha' := Ha. rewrite Ecptr Ebptr in Ha'.
      have Hmc' := Hmc. rewrite Eoptr in Hmc'.
      exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha' Hmc'). }
    have Hrel' : cellrel cmapS amap
        ({| Transitional.val := Transitional.val v.1;
            Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
         {| vtag := moved_tag (Transitional.tvtag v.1);
            color := Pointer.component ptr; entry := None;
            is_code := false |})
        (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                     color := Pointer.component ptr; entry := None;
                     is_code := false |}).
    { case: Hpair => Hvmc Htmc Hvtmc.
      split.
      - exact: (tvrel_retag_s Hvmc).
      - exact: erefl.
      - exact: erefl. }
    have Hcells : forall c0 b0 j0,
        cell_synced amap tmem mmem c0 b0 j0 ->
        cell_synced amap tmem'
          (setm mmem (@word_of_nat (word_size mt)
                        (a + BinInt.Z.to_nat (Pointer.offset ptr)))
             (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                          color := Pointer.component ptr; entry := None;
                          is_code := false |}))
          c0 b0 j0.
    { move=> c0 b0 j0 Hc0.
      apply: (cell_synced_store Haok Hst Ha _ Hc0).
      move=> _. exact: Hrel'. }
    have Hv2 : tvrel cmapS amap
        (Transitional.MVal (Transitional.tvtag v.1)
           (Transitional.val v.1)) wmc.
    { case: Hpair => Hvmc _ _. exact: (tvrel_eta_s Hvmc). }
    set inner := SV PBody (sv_sig sv0) None (sv_a1 sv0) (sv_a2 sv0)
                   (sv_sc sv0) (sv_one sv0) (sv_ek sv0) (sv_arg sv0).
    have Wsg : sv_sig (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
               = sv_sig sv0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wpd : sv_pend (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
               = None.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wa1 : is_r r2 R_AUX1 = false ->
      sv_a1 (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
      = sv_a1 sv0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX2); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Wa2 : is_r r2 R_AUX2 = false ->
      sv_a2 (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
      = sv_a2 sv0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_ONE);
         case: (is_r r2 R_ARG). }
    have Warg : is_r r2 R_ARG = false ->
      sv_arg (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
      = sv_arg sv0.
    { move=> E. rewrite /warg_w /warg /wone /wtaint E.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE). }
    have Wek : sv_ek (warg_w r2 (wone r2 false (wtaint r2 AU inner)))
               = sv_ek sv0.
    { rewrite /warg_w /warg /wone /wtaint.
      by case: (is_r r2 R_AUX1); case: (is_r r2 R_AUX2);
         case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have HpdC : sv_pend sv0 <> Some CArg.
    { by rewrite Epd0. }
    exact: (sync_regw_synced_store Ev Ew Hle Wsg
              (or_intror (conj Wpd HpdC)) Wa1 Wa2 Warg Wek Hv2
              Hcells HS).
  +
    case E2arg: (is_r r2 R_ARG) => // -[Evv]. subst v'.
    have Er2 : r2 = R_ARG := is_r_eq E2arg.
    subst r2.
    have HpendT : forall b k, cur = Some b -> sv_pend sv0 = Some k ->
        synced_slot (parg_of chain) k (size (sv_sig sv0)) = true ->
        cell_synced amap tmem mmem (Pointer.component pc) b
          (size (sv_sig sv0)) ->
        cell_synced amap tmem'
          (setm mmem (@word_of_nat (word_size mt)
                        (a + BinInt.Z.to_nat (Pointer.offset ptr)))
             (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                          color := Pointer.component ptr; entry := None;
                          is_code := false |}))
          (Pointer.component pc) b (size (sv_sig sv0)).
    {      move=> b k Hb Hk Hs Hold.
      move: Hk. rewrite Epd0 => -[Ek]. subst k.
      have Eb : b = bcur by move: Hb; rewrite Hcur => -[].
      subst b.
      have Hpair : cellrel cmapS amap v (Atom wmc mtg).
      { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
        rewrite Ecptr in Hcm. rewrite Ebptr in Hblk.
        rewrite Eoptr in Hnth.
        have Ha' := Ha. rewrite Ecptr Ebptr in Ha'.
        have Hmc' := Hmc. rewrite Eoptr in Hmc'.
        exact: (Hold _ _ _ _ _ Hcm Hblk Hnth Ha' Hmc'). }
      have Hrel' : cellrel cmapS amap
          ({| Transitional.val := Transitional.val v.1;
              Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
           {| vtag := moved_tag (Transitional.tvtag v.1);
              color := Pointer.component ptr; entry := None;
              is_code := false |})
          (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                       color := Pointer.component ptr; entry := None;
                       is_code := false |}).
      { case: Hpair => Hvmc Htmc Hvtmc.
        split.
        - exact: (tvrel_retag_s Hvmc).
        - exact: erefl.
        - exact: erefl. }
      have Hnew0 : cell_synced amap tmem'
          (setm mmem (@word_of_nat (word_size mt)
                        (a + BinInt.Z.to_nat (Pointer.offset ptr)))
             (Atom wmc {| vtag := moved_tag (Transitional.tvtag v.1);
                          color := Pointer.component ptr; entry := None;
                          is_code := false |}))
          (Pointer.component ptr) (Pointer.block ptr)
          (BinInt.Z.to_nat (Pointer.offset ptr)).
      { apply: cell_synced_store_new.
        - exact: Hst.
        - exact: Ha.
        - exact: Hrel'. }
      move: Hnew0. rewrite Ecptr Ebptr Eoptr. exact: id. }
    have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
    have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
    apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
    * apply: reg_synced_set_other; first by [].
      exact: (sy_com HS').
    * move=> Hau.
      have Hav : sv_a1 sv0 = AU.
      { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1u HS' Ev Hav).
    * move=> Hau.
      have Hav : sv_a2 sv0 = AU.
      { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2u HS' Ev Hav).
    * move=> Hasp Hcond.
      have Hav : sv_a1 sv0 = ASp.
      { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1sp HS' Ev Hav Hcondv).
    * move=> Hasp Hcond.
      have Hav : sv_a2 sv0 = ASp.
      { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2sp HS' Ev Hav Hcondv).
    * move=> Hw0arg. exfalso.
      move: Hle => /and5P [_ _ _ HA _].
      move: HA. by rewrite Hw0arg /o_le orbF.
    *
      move=> Hpg Hcf.
      have Hpair : cellrel cmapS amap v (Atom wmc mtg).
      { have Hcs : cell_synced amap tmem mmem (Pointer.component pc)
            bcur (size (sv_sig sv0)).
        { apply: (sy_pend HS Ev Hcur Epd0).
          rewrite /synced_slot. exact: Hpg. }
        have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
        rewrite Ecptr in Hcm. rewrite Ebptr in Hblk.
        rewrite Eoptr in Hnth.
        have Ha' := Ha. rewrite Ecptr Ebptr in Ha'.
        have Hmc' := Hmc. rewrite Eoptr in Hmc'.
        exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha' Hmc'). }
      case: Hpair => Hvmc _ _.
      apply: reg_synced_set.
      exact: (tvrel_eta_s Hvmc).
    * move=> c0 b0 j0 Hc0. exact: Hc0.
    * exact: HS'.
-
  case Epd1: (sv_pend sv0) => //.
  case Etr: [&& t_eqb (rtaint sv0 r1) AScr, is_r r2 R_SP
            & ~~ nocra (sv_sig sv0)] => //.
  case/and3P: Etr => Et _ _.
  move: Et. by rewrite /rtaint E1sp.
Qed.

(* a cell cannot be both synced-related and event-clobbed *)
Lemma cellrel_clob_clash (amap : amap_t)
    (tc : Transitional.tvalue * mem_tag) (mc : @matom mt) :
  cellrel cmapS amap tc mc -> clobcell tc mc -> False.
Proof.
move=> [_ Htg _] [[_ Hto Hti] _].
by rewrite Htg Hto in Hti.
Qed.

(* The clob mirror of [sync_load_pop]: the popped cell is event-clobbed (T
   Undef/Other vs me Invalidated), so me pops the Invalidated atom.  Only the
   UNCLAIMED arms survive (CRa, the position-0 teardown CSp, the dead-bit CArg
   restore); every claimed arm's [cellrel] clashes with the clob shape. *)

Lemma sync_load_pop_clob (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t)
    (v : Transitional.tvalue * mem_tag)
    (wmc : mword mt) (mtg : mem_tag) (a : nat) (bcur : Block.id)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrLoad r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = true ->
  svat pc = Some sv0 ->
  cur = Some bcur ->
  (bcur \in F (Pointer.component pc)) = true ->
  ptr = (Pointer.component pc, bcur,
         BinInt.Z.of_nat (size (sv_sig sv0))) ->
  (forall i A, nth_error chain i = Some A ->
     (MDisc.a_comp A == Pointer.component pc) &&
     (MDisc.a_blk A == bcur) = false) ->
  Transitional.Memory.load tmem ptr = Some v ->
  Transitional.Memory.store tmem ptr
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
     {| vtag := moved_tag (Transitional.tvtag v.1);
        color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mmem (@word_of_nat (word_size mt)
               (a + BinInt.Z.to_nat (Pointer.offset ptr)))
    = Some (Atom wmc mtg) ->
  clobcell v (Atom wmc mtg) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2 (Transitional.val v.1)
       (Transitional.tvtag v.1) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom wmc Invalidated))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom wmc {| vtag := Invalidated;
                    color := Pointer.component ptr; entry := None;
                    is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Ev0 Hcur Hbcur Eptr Hchdis Hld Hst Ha Hmc Hclob HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
have Ecptr : Pointer.component ptr = Pointer.component pc.
{ by rewrite Eptr. }
have Ebptr : Pointer.block ptr = bcur.
{ by rewrite Eptr. }
have Eoptr : BinInt.Z.to_nat (Pointer.offset ptr) = size (sv_sig sv0).
{ by rewrite Eptr /= Nat2Z.id. }
have Hclash : forall k, sv_pend sv0 = Some k ->
    synced_slot (parg_of chain) k (size (sv_sig sv0)) = true ->
    False.
{ move=> k Hk Hs.
  have Hcs : cell_synced amap tmem mmem (Pointer.component pc)
      bcur (size (sv_sig sv0)).
  { exact: (sy_pend HS Ev Hcur Hk Hs). }
  have Hpair : cellrel cmapS amap v (Atom wmc mtg).
  { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
    rewrite Ecptr in Hcm. rewrite Ebptr in Hblk.
    rewrite Eoptr in Hnth.
    have Ha' := Ha. rewrite Ecptr Ebptr in Ha'.
    have Hmc' := Hmc. rewrite Eoptr in Hmc'.
    exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha' Hmc'). }
  exact: (cellrel_clob_clash Hpair Hclob). }
have Hne_mem : forall c0 b0 j0, (b0 \in F c0) = false ->
    [&& c0 == Pointer.component ptr, b0 == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> c0 b0 j0 Hb0.
  apply/negbTE/negP => /and3P [/eqP Ec0 /eqP Eb0 _].
  subst c0 b0.
  by rewrite Ebptr Ecptr Hbcur in Hb0. }
have Hne_frame : forall j0, j0 < size (sv_sig sv0) ->
    [&& Pointer.component pc == Pointer.component ptr,
        bcur == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> j0 Hj0.
  apply/negbTE/negP => /and3P [_ _ /eqP Ej0].
  move: Hj0. rewrite Ej0 Eoptr ltnn. by []. }
have Hne_chain : forall i A j0, nth_error chain i = Some A ->
    [&& MDisc.a_comp A == Pointer.component ptr,
        MDisc.a_blk A == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> i A j0 HA.
  apply/negbTE/negP => /and3P [/eqP EcA /eqP EbA _].
  have := Hchdis _ _ HA.
  by rewrite EcA EbA Ecptr Ebptr !eqxx. }
have HmemT : forall c0 b0 j0, (b0 \in F c0) = false ->
    cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := Invalidated;
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hb0 Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_mem _ _ _ Hb0) Hc0). }
have HframeT : forall b j0 k, cur = Some b ->
    nth_error (sv_sig sv0) j0 = Some k ->
    cell_synced amap tmem mmem (Pointer.component pc) b j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := Invalidated;
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      (Pointer.component pc) b j0.
{ move=> b j0 k Hb Hk Hc0.
  have Eb : b = bcur by move: Hb; rewrite Hcur => -[].
  subst b.
  have Hj0 : j0 < size (sv_sig sv0) := nth_error_size Hk.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_frame _ Hj0) Hc0). }
have HchainT : forall i A j0, nth_error chain i = Some A ->
    cell_synced amap tmem mmem (MDisc.a_comp A) (MDisc.a_blk A) j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := Invalidated;
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      (MDisc.a_comp A) (MDisc.a_blk A) j0.
{ move=> i A j0 HA Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_chain _ _ j0 HA) Hc0). }
have HpendT : forall b k, cur = Some b -> sv_pend sv0 = Some k ->
    synced_slot (parg_of chain) k (size (sv_sig sv0)) = true ->
    cell_synced amap tmem mmem (Pointer.component pc) b
      (size (sv_sig sv0)) ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom wmc {| vtag := Invalidated;
                      color := Pointer.component ptr; entry := None;
                      is_code := false |}))
      (Pointer.component pc) b (size (sv_sig sv0)).
{ move=> b k Hb Hk Hs Hold. exfalso.
  exact: (Hclash _ Hk Hs). }
move: Evs => /=.
case Eph: (sv_ph sv0) => //.
-
  rewrite E1sp.
  case Epd0: (sv_pend sv0) => [k|] //.
  case: k Epd0 => Epd0.
  +
    case E2ra: (is_r r2 R_RA) => // -[Evv]. subst v'.
    have Er2 : r2 = R_RA := is_r_eq E2ra.
    subst r2.
    have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
    have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
    apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
    * apply: reg_synced_set_other; first by [].
      exact: (sy_com HS').
    * move=> Hau.
      have Hav : sv_a1 sv0 = AU.
      { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1u HS' Ev Hav).
    * move=> Hau.
      have Hav : sv_a2 sv0 = AU.
      { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2u HS' Ev Hav).
    * move=> Hasp Hcond.
      have Hav : sv_a1 sv0 = ASp.
      { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1sp HS' Ev Hav Hcondv).
    * move=> Hasp Hcond.
      have Hav : sv_a2 sv0 = ASp.
      { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2sp HS' Ev Hav Hcondv).
    * move=> Hw0arg.
      have Hargv : sv_arg sv0 = true.
      { move: Hle => /and5P [_ _ _ HA _].
        move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_arg HS' Ev Hargv).
    * move=> Hpg Hcf.
      have Hcf' : cargfree sv0 = true.
      { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
        move=> /andP [Hsg1 _]. by rewrite Hsg1. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_argp HS' Ev Hpg Hcf').
    * move=> c0 b0 j0 Hc0. exact: Hc0.
    * exact: HS'.
  +
    case E2t: (is_r r2 R_SP && cseq_eqb (sv_sig sv0) [::]).
    *
      move=> -[Evv]. subst v'.
      case/andP: E2t => E2sp Esgnil.
      have Er2 : r2 = R_SP := is_r_eq E2sp.
      subst r2.
      have Esg0 : sv_sig sv0 = [::].
      { by case: (sv_sig sv0) Esgnil. }
      have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
      have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
      apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
      -- apply: reg_synced_set_other; first by [].
         exact: (sy_com HS').
      -- move=> Hau.
         have Hav : sv_a1 sv0 = AU.
         { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a1u HS' Ev Hav).
      -- move=> Hau.
         have Hav : sv_a2 sv0 = AU.
         { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a2u HS' Ev Hav).
      -- move=> Hasp Hcond.
         have Hav : sv_a1 sv0 = ASp.
         { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
         { move: Hcond. rewrite Eek' Esg'. exact: id. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a1sp HS' Ev Hav Hcondv).
      -- move=> Hasp Hcond.
         have Hav : sv_a2 sv0 = ASp.
         { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
         { move: Hcond. rewrite Eek' Esg'. exact: id. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_a2sp HS' Ev Hav Hcondv).
      -- move=> Hw0arg.
         have Hargv : sv_arg sv0 = true.
         { move: Hle => /and5P [_ _ _ HA _].
           move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_arg HS' Ev Hargv).
      -- move=> Hpg Hcf.
         have Hcf' : cargfree sv0 = true.
         { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
           move=> /andP [Hsg1 _]. by rewrite Hsg1. }
         apply: reg_synced_set_other; first by [].
         exact: (sy_argp HS' Ev Hpg Hcf').
      -- move=> c0 b0 j0 Hc0. exact: Hc0.
      -- exact: HS'.
    *
      case E2a1: (is_r r2 R_AUX1 && ~~ cseq_eqb (sv_sig sv0) [::])
        => // -[Evv]. subst v'.
      case/andP: E2a1 => E2a1 Hsgne.
      exfalso.
      apply: (Hclash _ Epd0).
      rewrite /synced_slot.
      by case: (sv_sig sv0) Hsgne.
  +
    case E2t: (is_r r2 R_SP || is_r r2 R_RA) => // -[Evv]. subst v'.
    exfalso.
    apply: (Hclash _ Epd0).
    by [].
  +
    case E2arg: (is_r r2 R_ARG) => // -[Evv]. subst v'.
    have Er2 : r2 = R_ARG := is_r_eq E2arg.
    subst r2.
    have HS' := sync_claims_cells Ev HmemT HframeT HpendT HchainT HS.
    have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
    apply: (sync_regw_store Ev Ew Hle (erefl _) (or_intror (erefl _))).
    * apply: reg_synced_set_other; first by [].
      exact: (sy_com HS').
    * move=> Hau.
      have Hav : sv_a1 sv0 = AU.
      { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1u HS' Ev Hav).
    * move=> Hau.
      have Hav : sv_a2 sv0 = AU.
      { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2u HS' Ev Hav).
    * move=> Hasp Hcond.
      have Hav : sv_a1 sv0 = ASp.
      { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a1sp HS' Ev Hav Hcondv).
    * move=> Hasp Hcond.
      have Hav : sv_a2 sv0 = ASp.
      { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
      { move: Hcond. rewrite Eek' Esg'. exact: id. }
      apply: reg_synced_set_other; first by [].
      exact: (sy_a2sp HS' Ev Hav Hcondv).
    * move=> Hw0arg. exfalso.
      move: Hle => /and5P [_ _ _ HA _].
      move: HA. by rewrite Hw0arg /o_le orbF.
    *
      move=> Hpg Hcf. exfalso.
      apply: (Hclash _ Epd0).
      rewrite /synced_slot. exact: Hpg.
    * move=> c0 b0 j0 Hc0. exact: Hc0.
    * exact: HS'.
-
  case Epd1: (sv_pend sv0) => //.
  case Etr: [&& t_eqb (rtaint sv0 r1) AScr, is_r r2 R_SP
            & ~~ nocra (sv_sig sv0)] => //.
  case/and3P: Etr => Et _ _.
  move: Et. by rewrite /rtaint E1sp.
Qed.

(* Store-side helpers: the written cell's claim establishment (the push
   creates a fresh pend claim), and the source-register retag transports (T
   re-tags the stored register Invalidated-if-address; me mirrors with the
   same tag since the pair is synced). *)

Lemma reg_synced_retag1 (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (r2 : register) (w2 : mword mt) (ts2 vt : value_tag) :
  Transitional.tvtag (Transitional.Register.get r2 tregs) = vt ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2)) = Some (Atom w2 ts2) ->
  reg_syncedS amap tregs mregs r2 ->
  reg_syncedS amap
    (Transitional.Register.set r2
       (Transitional.val (Transitional.Register.get r2 tregs))
       (moved_tag vt) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom w2 (moved_tag vt)))
    r2.
Proof.
move=> Evt Hr2m [ra [Hra Hv Ht]].
have Era : ra = Atom w2 ts2 by move: Hra; rewrite Hr2m => -[].
subst ra.
exists (Atom w2 (moved_tag vt)).
rewrite tget_set_eq setmE eqxx.
split.
- exact: erefl.
- move: Hv Evt.
  case E0: (Transitional.Register.get r2 tregs) => [tg0 vv0] /=.
  move=> Hv Evt0.
  subst vt.
  case: tg0 E0 Ht Hv => [n| | |] E0 Ht Hv.
  + exact: I.
  + exact: Hv.
  + exact: Hv.
  + exact: I.
- exact: erefl.
Qed.

Lemma reg_synced_store_any (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (RX r2 : register) (w2 : mword mt) (ts2 vt : value_tag) :
  Transitional.tvtag (Transitional.Register.get r2 tregs) = vt ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2)) = Some (Atom w2 ts2) ->
  reg_syncedS amap tregs mregs RX ->
  reg_syncedS amap
    (Transitional.Register.set r2
       (Transitional.val (Transitional.Register.get r2 tregs))
       (moved_tag vt) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom w2 (moved_tag vt)))
    RX.
Proof.
move=> Evt Hr2m Hkeep.
case E2x: (is_r r2 RX).
- rewrite -(is_r_eq E2x).
  apply: (reg_synced_retag1 Evt Hr2m).
  rewrite (is_r_eq E2x). exact: Hkeep.
- apply: reg_synced_set_other; last exact: Hkeep.
  move=> E. move: E2x. by rewrite /is_r -E PeanoNat.Nat.eqb_refl.
Qed.

(* The per-opcode fleet: STORE, non-push arms (address register not R_SP: the
   scratch park/restore and the user/flag data stores).  The stored source is
   SYNCED (premise), so the written cell stays synced and the source retag
   preserves every register claim. *)

Lemma sync_store_user (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t) (vt : value_tag)
    (w2 : mword mt) (ts2 : value_tag) (a : nat)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrStore r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = false ->
  (Pointer.block ptr \in F (Pointer.component ptr)) = false ->
  Transitional.tvtag (Transitional.Register.get r2 tregs) = vt ->
  Transitional.Memory.store tmem ptr
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2)) = Some (Atom w2 ts2) ->
  reg_syncedS amap tregs mregs r2 ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2
       (Transitional.val (Transitional.Register.get r2 tregs))
       (moved_tag vt) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom w2 (moved_tag vt)))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                   entry := None; is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Hbnf Evt Hst Ha Hr2m Hsrc HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w0 [Ew Hle]] := Hnx isT.
have HrelW : cellrel cmapS amap
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := Pointer.component ptr; entry := None;
        is_code := false |})
    (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                entry := None; is_code := false |}).
{ case: Hsrc => [ra [Hra Hv Ht]].
  have Era : ra = Atom w2 ts2 by move: Hra; rewrite Hr2m => -[].
  subst ra.
  split.
  - exact: Hv.
  - exact: erefl.
  - rewrite /= Evt. exact: erefl. }
have Hcells : forall c0 b0 j0,
    cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                     entry := None; is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hc0.
  apply: (cell_synced_store Haok Hst Ha _ Hc0).
  move=> _. exact: HrelW. }
have [[Eph0 Esg0 Epd0f Eek0] [Ht10 Ht20 Hsc0 Hon0]] := sv_le_fields Hle.
have Hrows : forall v1 : sv,
    v' = v1 ->
    sv_sig v1 = sv_sig v0 ->
    sv_pend v1 = sv_pend v0 ->
    sv_a1 v1 = sv_a1 v0 ->
    sv_a2 v1 = sv_a2 v0 ->
    sv_ek v1 = sv_ek v0 ->
    sv_arg v1 = sv_arg v0 ->
    sync_claims amap tmem'
      (Transitional.Register.set r2
         (Transitional.val (Transitional.Register.get r2 tregs))
         (moved_tag vt) tregs)
      (setm mregs (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat r2))
         (Atom w2 (moved_tag vt)))
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                     entry := None; is_code := false |}))
      (Pointer.inc pc) cur chain F.
{ move=> v1 Ev1 Wsg Wpd Wa1 Wa2 Wek Warg.
  subst v1.
  have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
  apply: (sync_regw_store Ev Ew Hle Wsg (or_introl Wpd)).
  - apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_com HS).
  - move=> Hau.
    have Hav : sv_a1 v0 = AU.
    { rewrite -Wa1. move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_a1u HS Ev Hav).
  - move=> Hau.
    have Hav : sv_a2 v0 = AU.
    { rewrite -Wa2. move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_a2u HS Ev Hav).
  - move=> Hasp Hcond.
    have Hav : sv_a1 v0 = ASp.
    { rewrite -Wa1. move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcondv : sv_ek v0 = true \/ sv_sig v0 <> [::].
    { move: Hcond. rewrite Eek' Wek Esg' Wsg. exact: id. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_a1sp HS Ev Hav Hcondv).
  - move=> Hasp Hcond.
    have Hav : sv_a2 v0 = ASp.
    { rewrite -Wa2. move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcondv : sv_ek v0 = true \/ sv_sig v0 <> [::].
    { move: Hcond. rewrite Eek' Wek Esg' Wsg. exact: id. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_a2sp HS Ev Hav Hcondv).
  - move=> Hw0arg.
    have Hargv : sv_arg v0 = true.
    { rewrite -Warg.
      move: Hle => /and5P [_ _ _ HA _].
      move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_arg HS Ev Hargv).
  - move=> Hpg Hcf.
    have Hcf' : cargfree v0 = true.
    { move: Hcf. rewrite /cargfree Esg' Wsg Epd' Wpd. exact: id. }
    apply: (reg_synced_store_any Evt Hr2m).
    exact: (sy_argp HS Ev Hpg Hcf').
  - exact: Hcells.
  - exact: HS. }
move: Evs => /=.
case Eph: (sv_ph v0) => //.
case Epd0: (sv_pend v0) => //.
rewrite E1sp.
case Ert: (rtaint v0 r1) => //.
-
  case E2sp: (is_r r2 R_SP).
  + move=> -[Evv].
    apply: (Hrows _ (esym Evv)) => //.
  + case Erst: (t_eqb (rtaint v0 r2) ASp
                && cseq_eqb (sv_sig v0) [:: CSp]) => //.
    move=> -[Evv].
    apply: (Hrows _ (esym Evv)) => //.
-
  case Ert2: (t_eqb (rtaint v0 r2) AU) => //.
  move=> -[Evv].
  apply: (Hrows _ (esym Evv)) => //.
-
  case Ert2: (t_eqb (rtaint v0 r2) AU) => //.
  move=> -[Evv].
  apply: (Hrows _ (esym Evv)) => //.
Qed.

(* The push master: like [sync_regw_store] but the successor creates a pend
   claim (sv_pend v' = Some k); the caller establishes the freshly-written
   cell's sync (via [cell_synced_store_new]). *)

Lemma sync_regw_store_push (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs tregs' : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v v' w : sv) (k : class3) :
  svat pc = Some v ->
  svat (Pointer.inc pc) = Some w ->
  sv_le v' w ->
  sv_sig v' = sv_sig v ->
  sv_pend v' = Some k ->
  reg_syncedS amap tregs' mregs' R_COM ->
  (sv_a1 w = AU -> reg_syncedS amap tregs' mregs' R_AUX1) ->
  (sv_a2 w = AU -> reg_syncedS amap tregs' mregs' R_AUX2) ->
  (sv_a1 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap tregs' mregs' R_AUX1) ->
  (sv_a2 w = ASp -> sv_ek w = true \/ sv_sig w <> [::] ->
     reg_syncedS amap tregs' mregs' R_AUX2) ->
  (sv_arg w = true -> reg_syncedS amap tregs' mregs' R_ARG) ->
  (parg_of chain = true -> cargfree w = true ->
     reg_syncedS amap tregs' mregs' R_ARG) ->
  (forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap tmem' mmem' c0 b0 j0) ->
  (forall b, cur = Some b ->
     synced_slot (parg_of chain) k (size (sv_sig v)) = true ->
     cell_synced amap tmem' mmem' (Pointer.component pc) b
       (size (sv_sig v))) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem' tregs' mregs' mmem' (Pointer.inc pc) cur chain F.
Proof.
move=> Ev Ew Hle Wsg Wpd SCOM SA1U SA2U SA1S SA2S SARG SARGP Hcells
       Hpnew HS.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
rewrite Wsg in Esg.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
- exact: SCOM.
- move=> w0; rewrite Ew => -[<-]. exact: SA1U.
- move=> w0; rewrite Ew => -[<-]. exact: SA2U.
- move=> w0; rewrite Ew => -[<-]. exact: SA1S.
- move=> w0; rewrite Ew => -[<-]. exact: SA2S.
- move=> w0; rewrite Ew => -[<-]. exact: SARG.
- move=> w0; rewrite Ew => -[<-]. exact: SARGP.
- move=> c0 b0 j0 Hb0.
  exact: (Hcells _ _ _ (sy_mem HS Hb0)).
- move=> w0 b j k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg in Hk.
  exact: (Hcells _ _ _ (sy_frame HS Ev Hb Hk Hs)).
- move=> w0 b k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  move: Hk. rewrite Epd Wpd => -[Ek1]. subst k1.
  move: Hs. rewrite Esg => Hs.
  exact: (Hpnew _ Hb Hs).
- move=> i A j k1 HA Hk Hs.
  exact: (Hcells _ _ _ (sy_chain HS HA Hk Hs)).
Qed.

(* The per-opcode fleet: STORE, push arm (address register IS R_SP: the frame
   push).  The stored source is SYNCED (premise); the fresh pend cell's claim
   is established outright, the deadened source aux drops its claim, everything
   else transports. *)

Lemma sync_store_push (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t) (vt : value_tag)
    (w2 : mword mt) (ts2 : value_tag) (a : nat) (bcur : Block.id)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrStore r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = true ->
  svat pc = Some sv0 ->
  cur = Some bcur ->
  ptr = (Pointer.component pc, bcur,
         BinInt.Z.of_nat (size (sv_sig sv0))) ->
  Transitional.tvtag (Transitional.Register.get r2 tregs) = vt ->
  Transitional.Memory.store tmem ptr
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2)) = Some (Atom w2 ts2) ->
  reg_syncedS amap tregs mregs r2 ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2
       (Transitional.val (Transitional.Register.get r2 tregs))
       (moved_tag vt) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom w2 (moved_tag vt)))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                   entry := None; is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Ev0 Hcur Eptr Evt Hst Ha Hr2m Hsrc HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
have Ecptr : Pointer.component ptr = Pointer.component pc.
{ by rewrite Eptr. }
have Ebptr : Pointer.block ptr = bcur.
{ by rewrite Eptr. }
have Eoptr : BinInt.Z.to_nat (Pointer.offset ptr) = size (sv_sig sv0).
{ by rewrite Eptr /= Nat2Z.id. }
have HrelW : cellrel cmapS amap
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := Pointer.component ptr; entry := None;
        is_code := false |})
    (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                entry := None; is_code := false |}).
{ case: Hsrc => [ra [Hra Hv Ht]].
  have Era : ra = Atom w2 ts2 by move: Hra; rewrite Hr2m => -[].
  subst ra.
  split.
  - exact: Hv.
  - exact: erefl.
  - rewrite /= Evt. exact: erefl. }
have Hcells : forall c0 b0 j0,
    cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                     entry := None; is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hc0.
  apply: (cell_synced_store Haok Hst Ha _ Hc0).
  move=> _. exact: HrelW. }
have Hpnew : forall b, cur = Some b ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                     entry := None; is_code := false |}))
      (Pointer.component pc) b (size (sv_sig sv0)).
{ move=> b Hb.
  have Eb : b = bcur by move: Hb; rewrite Hcur => -[].
  subst b.
  have Hnew0 : cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := vt; color := Pointer.component ptr;
                     entry := None; is_code := false |}))
      (Pointer.component ptr) (Pointer.block ptr)
      (BinInt.Z.to_nat (Pointer.offset ptr)).
  { apply: cell_synced_store_new.
    - exact: Hst.
    - exact: Ha.
    - exact: HrelW. }
  move: Hnew0. rewrite Ecptr Ebptr Eoptr. exact: id. }
move: Evs => /=.
case Eph: (sv_ph sv0) => //.
case Epd0: (sv_pend sv0) => //.
rewrite E1sp.
case Epk: (pushclass sv0 r2) => [k|] // -[Evv]. subst v'.
have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
apply: (sync_regw_store_push Ev Ew Hle (erefl _) (erefl _)).
- apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_com HS).
- move=> Hau.
  have Hav : (if is_r r2 R_AUX1 then ADead else sv_a1 sv0) = AU.
  { move: Ht1. rewrite Hau /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  move: Hav.
  case E2a1: (is_r r2 R_AUX1) => // Hav.
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_a1u HS Ev Hav).
- move=> Hau.
  have Hav : (if is_r r2 R_AUX2 then ADead else sv_a2 sv0) = AU.
  { move: Ht2. rewrite Hau /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - have E2a2 : is_r r2 R_AUX2 = false.
      { by rewrite (is_r_eq E2a1). }
      rewrite E2a2. exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  move: Hav.
  case E2a2: (is_r r2 R_AUX2) => // Hav.
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_a2u HS Ev Hav).
- move=> Hasp Hcond.
  have Hav : (if is_r r2 R_AUX1 then ADead else sv_a1 sv0) = ASp.
  { move: Ht1. rewrite Hasp /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { move: Hcond. rewrite Eek' Esg'. exact: id. }
  move: Hav.
  case E2a1: (is_r r2 R_AUX1) => // Hav.
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_a1sp HS Ev Hav Hcondv).
- move=> Hasp Hcond.
  have Hav : (if is_r r2 R_AUX2 then ADead else sv_a2 sv0) = ASp.
  { move: Ht2. rewrite Hasp /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - have E2a2 : is_r r2 R_AUX2 = false.
      { by rewrite (is_r_eq E2a1). }
      rewrite E2a2. exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { move: Hcond. rewrite Eek' Esg'. exact: id. }
  move: Hav.
  case E2a2: (is_r r2 R_AUX2) => // Hav.
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_a2sp HS Ev Hav Hcondv).
- move=> Hw0arg.
  have Hargv : sv_arg sv0 = true.
  { move: Hle => /and5P [_ _ _ HA _].
    move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_arg HS Ev Hargv).
- move=> Hpg Hcf.
  have Hcf' : cargfree sv0 = true.
  { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
    by case: (k); rewrite ?andbF ?andbT. }
  apply: (reg_synced_store_any Evt Hr2m).
  exact: (sy_argp HS Ev Hpg Hcf').
- exact: Hcells.
- move=> b Hb _. exact: (Hpnew _ Hb).
- exact: HS.
Qed.

(* The clob mirror of [sync_store_push]: the pushed source is event-clobbed
   (T Undef/Other vs me Invalidated) — by the checker gates this can only hit
   a DEAD slot (CRa; the position-0 CSp park; a dead-kept-bit CArg), so the
   written cell carries no claim and every register row transports around it. *)

Lemma sync_store_push_clob (amap : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (ptr : Pointer.t) (vt : value_tag)
    (w2 : mword mt) (a : nat) (bcur : Block.id)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrStore r1 r2) tg c ->
  amap_ok PB amap tmem ->
  is_r r1 R_SP = true ->
  svat pc = Some sv0 ->
  cur = Some bcur ->
  (bcur \in F (Pointer.component pc)) = true ->
  ptr = (Pointer.component pc, bcur,
         BinInt.Z.of_nat (size (sv_sig sv0))) ->
  (forall i A, nth_error chain i = Some A ->
     (MDisc.a_comp A == Pointer.component pc) &&
     (MDisc.a_blk A == bcur) = false) ->
  [\/ r2 = R_RA,
      r2 = R_AUX1 /\ sv_sig sv0 = [::]
    | r2 = R_ARG /\ parg_of chain = false] ->
  vt = Other ->
  Transitional.Register.get r2 tregs = Transitional.tUndef ->
  Transitional.Memory.store tmem ptr
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := Pointer.component ptr; entry := None;
        is_code := false |}) = Some tmem' ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = Some a ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2))
    = Some (Atom w2 Invalidated) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem'
    (Transitional.Register.set r2
       (Transitional.val (Transitional.Register.get r2 tregs))
       (moved_tag vt) tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r2))
       (Atom w2 Invalidated))
    (setm mmem (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
       (Atom w2 {| vtag := Invalidated;
                   color := Pointer.component ptr; entry := None;
                   is_code := false |}))
    (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Haok E1sp Ev0 Hcur Hbcur Eptr Hchdis Hclass Evto Hu2 Hst
       Ha Hr2m HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
have Ecptr : Pointer.component ptr = Pointer.component pc.
{ by rewrite Eptr. }
have Ebptr : Pointer.block ptr = bcur.
{ by rewrite Eptr. }
have Eoptr : BinInt.Z.to_nat (Pointer.offset ptr) = size (sv_sig sv0).
{ by rewrite Eptr /= Nat2Z.id. }
have Hclash : reg_syncedS amap tregs mregs r2 -> False.
{ move=> [ra [Hra _ Hta]].
  move: Hra; rewrite Hr2m => -[Era]. subst ra.
  move: Hta. rewrite /= Hu2. by []. }
have Hne_mem : forall c0 b0 j0, (b0 \in F c0) = false ->
    [&& c0 == Pointer.component ptr, b0 == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> c0 b0 j0 Hb0.
  apply/negbTE/negP => /and3P [/eqP Ec0 /eqP Eb0 _].
  subst c0 b0.
  by rewrite Ebptr Ecptr Hbcur in Hb0. }
have Hne_frame : forall j0, j0 < size (sv_sig sv0) ->
    [&& Pointer.component pc == Pointer.component ptr,
        bcur == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> j0 Hj0.
  apply/negbTE/negP => /and3P [_ _ /eqP Ej0].
  move: Hj0. rewrite Ej0 Eoptr ltnn. by []. }
have Hne_chain : forall i A j0, nth_error chain i = Some A ->
    [&& MDisc.a_comp A == Pointer.component ptr,
        MDisc.a_blk A == Pointer.block ptr
      & j0 == BinInt.Z.to_nat (Pointer.offset ptr)] = false.
{ move=> i A j0 HA.
  apply/negbTE/negP => /and3P [/eqP EcA /eqP EbA _].
  have := Hchdis _ _ HA.
  by rewrite EcA EbA Ecptr Ebptr !eqxx. }
have HmemT : forall c0 b0 j0, (b0 \in F c0) = false ->
    cell_synced amap tmem mmem c0 b0 j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := Invalidated;
                     color := Pointer.component ptr; entry := None;
                     is_code := false |}))
      c0 b0 j0.
{ move=> c0 b0 j0 Hb0 Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_mem _ _ _ Hb0) Hc0). }
have HframeT : forall b j0, cur = Some b -> j0 < size (sv_sig sv0) ->
    cell_synced amap tmem mmem (Pointer.component pc) b j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := Invalidated;
                     color := Pointer.component ptr; entry := None;
                     is_code := false |}))
      (Pointer.component pc) b j0.
{ move=> b j0 Hb Hj0 Hc0.
  have Eb : b = bcur by move: Hb; rewrite Hcur => -[].
  subst b.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_frame _ Hj0) Hc0). }
have HchainT : forall i A j0, nth_error chain i = Some A ->
    cell_synced amap tmem mmem (MDisc.a_comp A) (MDisc.a_blk A) j0 ->
    cell_synced amap tmem'
      (setm mmem (@word_of_nat (word_size mt)
                    (a + BinInt.Z.to_nat (Pointer.offset ptr)))
         (Atom w2 {| vtag := Invalidated;
                     color := Pointer.component ptr; entry := None;
                     is_code := false |}))
      (MDisc.a_comp A) (MDisc.a_blk A) j0.
{ move=> i A j0 HA Hc0.
  exact: (cell_synced_store_other Haok Hst Ha (Hne_chain _ _ j0 HA) Hc0). }
move: Evs => /=.
case Eph: (sv_ph sv0) => //.
case Epd0: (sv_pend sv0) => //.
rewrite E1sp.
case Epk: (pushclass sv0 r2) => [k|] // -[Evv]. subst v'.
have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
have Hlt32 : forall r0 : register, Intermediate.Register.to_nat r0 < 32
  by case.
have Hdead : synced_slot (parg_of chain) k (size (sv_sig sv0)) = false.
{ case: Hclass Epk => [Er2|[Er2 Esg0]|[Er2 Hpgf]]; subst r2;
    rewrite /pushclass /=.
  - case Enc: (_ && _) => // -[Ek]. subst k. by [].
  - case Ecsp: (_ && _).
    + move=> -[Ek]. subst k.
      by rewrite /synced_slot Esg0.
    + case Eau: (rtaint sv0 R_AUX1) => // -[Ek]. subst k.
      exfalso. apply: Hclash.
      have Hav : sv_a1 sv0 = AU.
      { move: Eau. rewrite /rtaint /=. by []. }
      exact: (sy_a1u HS Ev Hav).
  - case Earg: (sv_arg sv0).
    + move=> -[Ek]. subst k.
      exfalso. apply: Hclash.
      exact: (sy_arg HS Ev Earg).
    + case Enca: (nocarg (sv_sig sv0)) => // -[Ek]. subst k.
      by rewrite /synced_slot Hpgf. }
constructor.
-
  apply: reg_synced_set_other; last exact: (sy_com HS).
  case: Hclass => [Er2|[Er2 _]|[Er2 _]]; subst r2; by [].
-
  move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : (if is_r r2 R_AUX1 then ADead else sv_a1 sv0) = AU.
  { move: Ht1. rewrite Hau /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  move: Hav.
  case E2a1: (is_r r2 R_AUX1) => // Hav.
  apply: reg_synced_set_other; last exact: (sy_a1u HS Ev Hav).
  move=> E. move: E2a1. by rewrite /is_r E PeanoNat.Nat.eqb_refl.
-
  move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : (if is_r r2 R_AUX2 then ADead else sv_a2 sv0) = AU.
  { move: Ht2. rewrite Hau /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - have E2a2 : is_r r2 R_AUX2 = false.
      { by rewrite (is_r_eq E2a1). }
      rewrite E2a2. exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  move: Hav.
  case E2a2: (is_r r2 R_AUX2) => // Hav.
  apply: reg_synced_set_other; last exact: (sy_a2u HS Ev Hav).
  move=> E. move: E2a2. by rewrite /is_r E PeanoNat.Nat.eqb_refl.
-
  move=> ww. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : (if is_r r2 R_AUX1 then ADead else sv_a1 sv0) = ASp.
  { move: Ht1. rewrite Hasp /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { move: Hcond. rewrite Eek' Esg'. exact: id. }
  move: Hav.
  case E2a1: (is_r r2 R_AUX1) => // Hav.
  apply: reg_synced_set_other;
    last exact: (sy_a1sp HS Ev Hav Hcondv).
  move=> E. move: E2a1. by rewrite /is_r E PeanoNat.Nat.eqb_refl.
-
  move=> ww. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : (if is_r r2 R_AUX2 then ADead else sv_a2 sv0) = ASp.
  { move: Ht2. rewrite Hasp /t_le orbF /dead_src /wtaint.
    case E2a1: (is_r r2 R_AUX1).
    - have E2a2 : is_r r2 R_AUX2 = false.
      { by rewrite (is_r_eq E2a1). }
      rewrite E2a2. exact: t_eqb_eq.
    - case E2a2: (is_r r2 R_AUX2); exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { move: Hcond. rewrite Eek' Esg'. exact: id. }
  move: Hav.
  case E2a2: (is_r r2 R_AUX2) => // Hav.
  apply: reg_synced_set_other;
    last exact: (sy_a2sp HS Ev Hav Hcondv).
  move=> E. move: E2a2. by rewrite /is_r E PeanoNat.Nat.eqb_refl.
-
  move=> ww. rewrite Ew => -[<-] Hw0arg.
  have Hargv : sv_arg sv0 = true.
  { move: Hle => /and5P [_ _ _ HA _].
    move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
  have Hne2 : Intermediate.Register.to_nat R_ARG
              <> Intermediate.Register.to_nat r2.
  { case: Hclass => [Er2|[Er2 _]|[Er2 _]]; subst r2.
    - by [].
    - by [].
    - exfalso. apply: Hclash. exact: (sy_arg HS Ev Hargv). }
  apply: reg_synced_set_other; last exact: (sy_arg HS Ev Hargv).
  exact: Hne2.
-
  move=> ww. rewrite Ew => -[<-] Hpg Hcf.
  have Hcf' : cargfree sv0 = true.
  { move: Hcf. rewrite /cargfree Esg' Epd' /= Epd0 /=.
    by case: (k); rewrite ?andbF ?andbT. }
  have Hne2 : Intermediate.Register.to_nat R_ARG
              <> Intermediate.Register.to_nat r2.
  { case: Hclass => [Er2|[Er2 _]|[Er2 Hpgf]]; subst r2.
    - by [].
    - by [].
    - exfalso. move: Hpg. by rewrite Hpgf. }
  apply: reg_synced_set_other;
    last exact: (sy_argp HS Ev Hpg Hcf').
  exact: Hne2.
-
  move=> c0 b0 j0 Hb0.
  exact: (HmemT _ _ _ Hb0 (sy_mem HS Hb0)).
-
  move=> ww b j k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  rewrite Esg' in Hk.
  have Hj0 : j < size (sv_sig sv0) := nth_error_size Hk.
  exact: (HframeT _ _ Hb Hj0 (sy_frame HS Ev Hb Hk Hs)).
-
  move=> ww b k1. rewrite Ew Ec => -[<-] Hb Hk Hs.
  move: Hk. rewrite Epd' => -[Ek1]. subst k1.
  exfalso.
  move: Hs. rewrite Esg' Hdead. by [].
-
  move=> i A j k1 HA Hk Hs.
  exact: (HchainT _ _ _ HA (sy_chain HS HA Hk Hs)).
Qed.

(* The per-opcode fleet: ALLOC.  The only step where the address map extends
   (the fresh block gets mapped): stated over an abstract [amap'] with a
   register-monotonicity premise and the uniform cell transport (which also
   establishes the fresh block's sy_mem claim).  The me register file is
   abstract too: the syscall stub writes only [rptr] among the user registers. *)

Lemma reg_synced_alloc_new (amap' : amap_t)
    (tregs : Transitional.Register.t)
    (mregs' : {fmap reg mt -> @ratom mt})
    (rptr : register) (ptr : Pointer.t) (wret : mword mt) :
  getm mregs' (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat rptr))
    = Some (Atom wret Other) ->
  tvrel cmapS amap' (Transitional.MVal Other (Ptr ptr)) wret ->
  reg_syncedS amap'
    (Transitional.Register.set rptr (Ptr ptr) Other tregs) mregs' rptr.
Proof.
move=> Hget Hv.
exists (Atom wret Other).
rewrite tget_set_eq.
split.
- exact: Hget.
- exact: Hv.
- exact: erefl.
Qed.

Lemma reg_synced_alloc_other (amap' : amap_t)
    (tregs : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (rptr RX : register) (vp : value) (vt : value_tag) :
  is_r rptr RX = false ->
  (forall r : register, r <> rptr ->
     getm mregs' (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r))
     = getm mregs (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat r))) ->
  reg_syncedS amap' tregs mregs RX ->
  reg_syncedS amap'
    (Transitional.Register.set rptr vp vt tregs) mregs' RX.
Proof.
move=> Hne Hpres [ra [Hra Hv Ht]].
have HneP : RX <> rptr.
{ move=> E. move: Hne. by rewrite E /is_r PeanoNat.Nat.eqb_refl. }
exists ra.
rewrite (tget_set_neq _ _ _ HneP) (Hpres _ HneP).
split.
- exact: Hra.
- exact: Hv.
- exact: Ht.
Qed.

Lemma sync_alloc_heap (amap amap' : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (rptr rsize : register) (ptr : Pointer.t) (wret : mword mt)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrAlloc rptr rsize) tg c ->
  svat pc = Some sv0 ->
  sv_ph sv0 = PBody ->
  (forall r : register, r <> rptr ->
     getm mregs' (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r))
     = getm mregs (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat r))) ->
  getm mregs' (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat rptr))
    = Some (Atom wret Other) ->
  tvrel cmapS amap' (Transitional.MVal Other (Ptr ptr)) wret ->
  (forall r : register, reg_syncedS amap tregs mregs r ->
     reg_syncedS amap' tregs mregs r) ->
  (forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap' tmem' mmem' c0 b0 j0) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap' tmem'
    (Transitional.Register.set rptr (Ptr ptr) Other tregs)
    mregs' mmem' (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Ev0 Eph Hpres Hget Hvret Hmono Hcells HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
move: Evs => /=.
rewrite Eph.
case Egate: ([|| is_r rptr R_SP, is_r rsize R_SP | is_r rptr R_RA])
  => //.
case Epd0: (sv_pend sv0) => //.
case Eau: (t_eqb (rtaint sv0 rsize) AU) => // -[Evv]. subst v'.
have Wsg : sv_sig (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
           = sv_sig sv0.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r rptr R_AUX1); case: (is_r rptr R_AUX2);
     case: (is_r rptr R_ONE); case: (is_r rptr R_ARG). }
have Wpd : sv_pend (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
           = sv_pend sv0.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r rptr R_AUX1); case: (is_r rptr R_AUX2);
     case: (is_r rptr R_ONE); case: (is_r rptr R_ARG). }
have Wa1 : is_r rptr R_AUX1 = false ->
  sv_a1 (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
  = sv_a1 sv0.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r rptr R_AUX2); case: (is_r rptr R_ONE);
     case: (is_r rptr R_ARG). }
have Wa2 : is_r rptr R_AUX2 = false ->
  sv_a2 (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
  = sv_a2 sv0.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r rptr R_AUX1); case: (is_r rptr R_ONE);
     case: (is_r rptr R_ARG). }
have Warg : is_r rptr R_ARG = false ->
  sv_arg (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
  = sv_arg sv0.
{ move=> E. rewrite /warg_w /warg /wone /wtaint E.
  by case: (is_r rptr R_AUX1); case: (is_r rptr R_AUX2);
     case: (is_r rptr R_ONE). }
have Wek : sv_ek (warg_w rptr (wone rptr false (wtaint rptr AU sv0)))
           = sv_ek sv0.
{ rewrite /warg_w /warg /wone /wtaint.
  by case: (is_r rptr R_AUX1); case: (is_r rptr R_AUX2);
     case: (is_r rptr R_ONE); case: (is_r rptr R_ARG). }
have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
have Harg : sv_arg w0 = true ->
  sv_arg (warg_w rptr (wone rptr false (wtaint rptr AU sv0))) = true.
{ move: Hle => /and5P [_ _ _ HA _] Hw.
  move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
apply: (sync_regw_store Ev Ew Hle Wsg (or_introl Wpd)).
-
  case Ex: (is_r rptr R_COM).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_com HS)).
-
  move=> Hau.
  case Ex: (is_r rptr R_AUX1).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hav : sv_a1 sv0 = AU.
    { rewrite -(Wa1 Ex).
      move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_a1u HS Ev Hav)).
-
  move=> Hau.
  case Ex: (is_r rptr R_AUX2).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hav : sv_a2 sv0 = AU.
    { rewrite -(Wa2 Ex).
      move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_a2u HS Ev Hav)).
-
  move=> Hasp Hcond.
  case Ex: (is_r rptr R_AUX1).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hav : sv_a1 sv0 = ASp.
    { rewrite -(Wa1 Ex).
      move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
    { move: Hcond. rewrite Eek' Wek Esg' Wsg. exact: id. }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_a1sp HS Ev Hav Hcondv)).
-
  move=> Hasp Hcond.
  case Ex: (is_r rptr R_AUX2).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hav : sv_a2 sv0 = ASp.
    { rewrite -(Wa2 Ex).
      move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
    have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
    { move: Hcond. rewrite Eek' Wek Esg' Wsg. exact: id. }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_a2sp HS Ev Hav Hcondv)).
-
  move=> Hw0arg.
  case Ex: (is_r rptr R_ARG).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hargv : sv_arg sv0 = true.
    { rewrite -(Warg Ex). exact: (Harg Hw0arg). }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_arg HS Ev Hargv)).
-
  move=> Hpg Hcf.
  case Ex: (is_r rptr R_ARG).
  + rewrite -(is_r_eq Ex).
    apply: reg_synced_alloc_new.
    * exact: Hget.
    * exact: Hvret.
  + have Hcf' : cargfree sv0 = true.
    { move: Hcf. rewrite /cargfree Esg' Wsg Epd' Wpd. exact: id. }
    apply: reg_synced_alloc_other.
    * exact: Ex.
    * exact: Hpres.
    * exact: (Hmono _ (sy_argp HS Ev Hpg Hcf')).
- exact: Hcells.
- exact: HS.
Qed.

Lemma sync_alloc_frame (amap amap' : amap_t)
    (tmem tmem' : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem mmem' : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (rptr rsize : register) (ptr : Pointer.t) (bnew : Block.id)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F F' : Component.id -> seq Block.id) (sv0 : sv) :
  Transitional.executing cde pc (TrAlloc rptr rsize) tg c ->
  svat pc = Some sv0 ->
  sv_ph sv0 = PProlB ->
  sv_sig sv0 = [::] ->
  sv_pend sv0 = None ->
  (forall c0, F' c0 = if Nat.eqb c0 (Pointer.component pc)
                      then bnew :: F c0 else F c0) ->
  (forall r : register, r <> rptr ->
     getm mregs' (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r))
     = getm mregs (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat r))) ->
  (forall r : register, reg_syncedS amap tregs mregs r ->
     reg_syncedS amap' tregs mregs r) ->
  (forall c0 b0 j0, cell_synced amap tmem mmem c0 b0 j0 ->
     cell_synced amap' tmem' mmem' c0 b0 j0) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap' tmem'
    (Transitional.Register.set rptr (Ptr ptr) Other tregs)
    mregs' mmem' (Pointer.inc pc) (Some bnew) chain F'.
Proof.
move=> Hex Ev0 Eph Hsg0 Hpd0 HF' Hpres Hmono Hcells HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Evv0 : v0 = sv0 by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
move: Evs => /=.
rewrite Eph.
case Etr: (is_r rptr R_SP && is_r rsize R_SP) => //.
case/andP: Etr => E1sp E2sp.
have Er1 : rptr = R_SP := is_r_eq E1sp.
subst rptr.
have Hsplit : forall Q : Prop,
    (sc_eqb (sv_sc sv0) SCpark = false ->
     v' = SV PBody [::] None (sv_a1 sv0) (sv_a2 sv0) (sv_sc sv0)
            (sv_one sv0) (sv_ek sv0) (sv_arg sv0) -> Q) ->
    (match sv_sc sv0 with
     | SCpark => None
     | _ => Some (SV PBody [::] None (sv_a1 sv0) (sv_a2 sv0)
                    (sv_sc sv0) (sv_one sv0) (sv_ek sv0) (sv_arg sv0))
     end = Some v' -> Q).
{ move=> Q HQ.
  by case: (sv_sc sv0) HQ => HQ // -[E]; apply: HQ. }
apply: Hsplit => Hnp Evv. subst v'.
have [[Eph' Esg' Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
-
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_com HS)).
-
  move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a1 sv0 = AU.
  { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_a1u HS Ev Hav)).
-
  move=> ww. rewrite Ew => -[<-] Hau.
  have Hav : sv_a2 sv0 = AU.
  { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_a2u HS Ev Hav)).
-
  move=> ww. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : sv_a1 sv0 = ASp.
  { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { left.
    move: Hcond. rewrite Eek' Esg' /=.
    case=> [Hek|Hnil].
    - exact: Hek.
    - by case: Hnil. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_a1sp HS Ev Hav Hcondv)).
-
  move=> ww. rewrite Ew => -[<-] Hasp Hcond.
  have Hav : sv_a2 sv0 = ASp.
  { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
  have Hcondv : sv_ek sv0 = true \/ sv_sig sv0 <> [::].
  { left.
    move: Hcond. rewrite Eek' Esg' /=.
    case=> [Hek|Hnil].
    - exact: Hek.
    - by case: Hnil. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_a2sp HS Ev Hav Hcondv)).
-
  move=> ww. rewrite Ew => -[<-] Hw0arg.
  have Hargv : sv_arg sv0 = true.
  { move: Hle => /and5P [_ _ _ HA _].
    move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_arg HS Ev Hargv)).
-
  move=> ww. rewrite Ew => -[<-] Hpg Hcf.
  have Hcf' : cargfree sv0 = true.
  { by rewrite /cargfree Hsg0 Hpd0. }
  apply: reg_synced_alloc_other.
  + by [].
  + exact: Hpres.
  + exact: (Hmono _ (sy_argp HS Ev Hpg Hcf')).
-
  move=> c0 b0 j0 Hb0.
  have Hb0F : (b0 \in F c0) = false.
  { move: Hb0. rewrite HF'.
    case: (Nat.eqb c0 (Pointer.component pc)).
    - rewrite in_cons => /negbT.
      rewrite negb_or => /andP [_ /negbTE Hb0']. exact: Hb0'.
    - exact: id. }
  exact: (Hcells _ _ _ (sy_mem HS Hb0F)).
-
  move=> ww b j k. rewrite Ew => -[<-] _.
  rewrite Esg' /=.
  by case: j.
-
  move=> ww b k. rewrite Ew => -[<-] _.
  rewrite Epd' /=.
  by [].
-
  move=> i A j k HA Hk Hs.
  exact: (Hcells _ _ _ (sy_chain HS HA Hk Hs)).
Qed.

(* The per-opcode fleet: internal JAL.  The target label carries the literal
   [sv0_one] column (jal_target), so every keyed register claim at the target
   is dead; the current frame's claims move onto the freshly pushed chain
   entry (whose [asv] is the resume column, sig-equal to the jal site's);
   memory untouched.  R_RA is written on both sides but carries no claim. *)

Lemma sync_jal (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc pc' : Pointer.t) (tg : mem_tag) (c : Component.id) (l : label)
    (ra_me : @ratom mt) (b : Block.id) (cs : value)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrJalNat l) tg c ->
  Transitional.find_label_in_comp cde c l = Some pc' ->
  cur = Some b ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set R_RA (Ptr (Pointer.inc pc))
       InternalJump tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat R_RA)) ra_me)
    mmem pc'
    None
    ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
        MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |} :: chain)
    F.
Proof.
move=> Hex Hfl Hcur HS.
have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w [Ew Hle]] := Hnx isT.
have [Ecpc' EvT] := jal_target HMM Huniq Hex Ev Hfl.
move: Evs => /=.
case Eph: (sv_ph v) => //.
case Epd0: (sv_pend v) => //.
case Eg0: (sv_one v && ~~ nocra (sv_sig v)) => // -[Evv]. subst v'.
have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
constructor.
- apply: reg_synced_set_other; first by [].
  exact: (sy_com HS).
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
-
  move=> ww. rewrite EvT => -[<-] Hpg _.
  have Hargv : sv_arg v = true.
  { move: Hpg. rewrite /parg_of /MDisc.asv /= Ew /= => Hw.
    move: Hle => /and5P [_ _ _ HA _].
    move: HA. rewrite Hw /o_le orbF. exact: Bool.eqb_prop. }
  apply: reg_synced_set_other; first by [].
  exact: (sy_arg HS Ev Hargv).
- exact: (sy_mem HS).
- move=> ww b0 j k _ Hb. by [].
- move=> ww b0 k _ Hb. by [].
- move=> i A0 j k HA0 Hk Hs.
  case: i HA0 Hs => [|i] HA0 Hs.
  + move: HA0 => /= -[EA0]. subst A0.
    move: Hk Hs. rewrite /MDisc.asv /= Ew /= Esg => Hk.
    rewrite parg_at_cons0 => Hs.
    exact: (sy_frame HS Ev Hcur Hk Hs).
  + move: HA0 => /= HA0.
    exact: (sy_chain HS HA0 Hk Hs).
Qed.

(* The per-opcode fleet: internal JUMP (the TrJump return to a JalNat resume).
   No register or memory changes on either side; the head chain act pops — its
   sy_chain claims become the resumed frame's sy_frame claims; the resume
   column's aux claims are dead (premises from dinv's per-act record), and the
   kept arg claim comes from the interim R_ARG premise. *)

Lemma sync_jump (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc pc' : Pointer.t) (tg : mem_tag) (c : Component.id) (r : register)
    (A : MDisc.act) (chain' : seq MDisc.act)
    (cur : option Block.id)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrJump r) tg c ->
  pc' = MDisc.a_ret A ->
  Pointer.component (MDisc.a_ret A) = MDisc.a_comp A ->
  sv_a1 (asv A) = ADead ->
  sv_a2 (asv A) = ADead ->
  sv_pend (asv A) = None ->
  (sv_arg (asv A) = true -> reg_syncedS amap tregs mregs R_ARG) ->
  (parg_of chain' = true -> cargfree (asv A) = true ->
     reg_syncedS amap tregs mregs R_ARG) ->
  sync_claims amap tmem tregs mregs mmem pc cur (A :: chain') F ->
  sync_claims amap tmem tregs mregs mmem pc'
    (Some (MDisc.a_blk A)) chain' F.
Proof.
move=> Hex Epc' HcA Ha1A Ha2A HpdA Hargres Hargp' HS.
constructor.
- exact: (sy_com HS).
- move=> w0 Ew0 Hau. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha1A. rewrite EA Hau. by [].
- move=> w0 Ew0 Hau. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha2A. rewrite EA Hau. by [].
- move=> w0 Ew0 Hasp _. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha1A. rewrite EA Hasp. by [].
- move=> w0 Ew0 Hasp _. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha2A. rewrite EA Hasp. by [].
- move=> w0 Ew0 Hw0.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  apply: Hargres. by rewrite EA.
- move=> w0 Ew0 Hpg Hcf.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  apply: (Hargp' Hpg). by rewrite EA.
- exact: (sy_mem HS).
- move=> w0 b j k Ew0 Hb Hk Hs.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  have Eb : b = MDisc.a_blk A by move: Hb => -[].
  subst b.
  rewrite Epc' HcA.
  have HkA : nth_error (sv_sig (asv A)) j = Some k.
  { by rewrite EA. }
  have Hnth : nth_error (A :: chain') 0 = Some A.
  { exact: erefl. }
  rewrite -(parg_at_cons0 A chain') in Hs.
  exact: (sy_chain HS Hnth HkA Hs).
- move=> w0 b k Ew0 Hb Hk. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: HpdA. rewrite EA Hk. by [].
- move=> i A0 j k HA0 Hk Hs.
  have Hnth' : nth_error (A :: chain') i.+1 = Some A0.
  { exact: HA0. }
  exact: (sy_chain HS Hnth' Hk Hs).
Qed.

(* The per-opcode fleet: the CROSS events.  Both machines invalidate the
   register file (T writes tUndef, me re-tags Invalidated), so the me register
   file is abstract and the only register premise is the post-state R_COM sync.
   CALL pushes the caller's window act (target = literal [sv0], all keyed
   claims dead); RETURN pops the window act (its resume column's aux/arg claims
   are dead — premises from the act record). *)

Lemma sync_call (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc pc' : Pointer.t) (tg : mem_tag) (c c' : Component.id)
    (pid : Procedure.id) (n : nat) (b : Block.id) (cs : value)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrJalProc (c', pid)) tg c ->
  Transitional.find_plabel_in_code cde c' pid = Some pc' ->
  cur = Some b ->
  reg_syncedS amap
    (Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n)
       (Transitional.Register.invalidate tregs))
    mregs' R_COM ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n)
       (Transitional.Register.invalidate tregs))
    mregs' mmem pc'
    None
    ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
        MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |} :: chain)
    F.
Proof.
move=> Hex Hfl Hcur Hcom' HS.
have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have [w [Ew Hle]] := Hnx isT.
have [Ecpc' EvT] := plabel_target HMM Hfl.
move: Evs => /=.
case Eph: (sv_ph v) => //.
case Epd0: (sv_pend v) => //.
case Esc0: (sv_sc v) => //.
case Eg6: (if sv_ek v then nth1carg (sv_sig v) else true) => //.
move=> -[Evv]. subst v'.
have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc' Hon]] := sv_le_fields Hle.
constructor.
- exact: Hcom'.
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
- move=> ww. rewrite EvT => -[<-]. by [].
-
  move=> ww. rewrite EvT => -[<-] Hpg _. exfalso.
  move: Hpg. rewrite /parg_of /MDisc.asv /= Ew /= => Hw.
  move: Hle => /and5P [_ _ _ HA _].
  move: HA. rewrite Hw /o_le orbF => /Bool.eqb_prop. by [].
- exact: (sy_mem HS).
- move=> ww b0 j k _ Hb. by [].
- move=> ww b0 k _ Hb. by [].
- move=> i A0 j k HA0 Hk Hs.
  case: i HA0 Hs => [|i] HA0 Hs.
  + move: HA0 => /= -[EA0]. subst A0.
    move: Hk Hs. rewrite /MDisc.asv /= Ew /= Esg => Hk.
    rewrite parg_at_cons0 => Hs.
    exact: (sy_frame HS Ev Hcur Hk Hs).
  + move: HA0 => /= HA0.
    exact: (sy_chain HS HA0 Hk Hs).
Qed.

Lemma sync_jumpret (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (mregs mregs' : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc pc' : Pointer.t) (tg : mem_tag) (c : Component.id) (r : register)
    (A : MDisc.act) (chain' : seq MDisc.act)
    (cur : option Block.id)
    (F : Component.id -> seq Block.id) :
  Transitional.executing cde pc (TrJump r) tg c ->
  pc' = MDisc.a_ret A ->
  Pointer.component (MDisc.a_ret A) = MDisc.a_comp A ->
  sv_a1 (asv A) = ADead ->
  sv_a2 (asv A) = ADead ->
  sv_pend (asv A) = None ->
  sv_arg (asv A) = false ->
  (parg_of chain' = true -> cargfree (asv A) = false) ->
  reg_syncedS amap (TS.invalidate_ret tregs) mregs' R_COM ->
  sync_claims amap tmem tregs mregs mmem pc cur (A :: chain') F ->
  sync_claims amap tmem (TS.invalidate_ret tregs) mregs' mmem pc'
    (Some (MDisc.a_blk A)) chain' F.
Proof.
move=> Hex Epc' HcA Ha1A Ha2A HpdA HargA HcfA Hcom' HS.
constructor.
- exact: Hcom'.
- move=> w0 Ew0 Hau. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha1A. rewrite EA Hau. by [].
- move=> w0 Ew0 Hau. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha2A. rewrite EA Hau. by [].
- move=> w0 Ew0 Hasp _. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha1A. rewrite EA Hasp. by [].
- move=> w0 Ew0 Hasp _. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: Ha2A. rewrite EA Hasp. by [].
- move=> w0 Ew0 Hw0. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: HargA. rewrite EA Hw0. by [].
- move=> w0 Ew0 Hpg Hcf. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: (HcfA Hpg). rewrite EA Hcf. by [].
- exact: (sy_mem HS).
- move=> w0 b j k Ew0 Hb Hk Hs.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  have Eb : b = MDisc.a_blk A by move: Hb => -[].
  subst b.
  rewrite Epc' HcA.
  have HkA : nth_error (sv_sig (asv A)) j = Some k.
  { by rewrite EA. }
  have Hnth : nth_error (A :: chain') 0 = Some A.
  { exact: erefl. }
  rewrite -(parg_at_cons0 A chain') in Hs.
  exact: (sy_chain HS Hnth HkA Hs).
- move=> w0 b k Ew0 Hb Hk. exfalso.
  have EA : asv A = w0.
  { by rewrite /MDisc.asv -Epc' Ew0. }
  move: HpdA. rewrite EA Hk. by [].
- move=> i A0 j k HA0 Hk Hs.
  have Hnth' : nth_error (A :: chain') i.+1 = Some A0.
  { exact: HA0. }
  exact: (sy_chain HS Hnth' Hk Hs).
Qed.

(* The per-opcode fleet: MOV.  T does two chained writes (copy to r2 with the
   travelling tag, then r1 retagged Invalidated-if-address); the me term is
   stated r1-outer.  [reg_synced_mov_any] absorbs the row split (copy target /
   retagged source / untouched). *)

Lemma reg_synced_mov_copy (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (r1 r2 : register) (w1 : mword mt) (ts1 : value_tag)
    (vo : value) (topt : value_tag) (rao : @ratom mt) :
  Intermediate.Register.to_nat r2 <> Intermediate.Register.to_nat r1 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r1)) = Some (Atom w1 ts1) ->
  reg_syncedS amap tregs mregs r1 ->
  reg_syncedS amap
    (Transitional.Register.set r1 vo topt
       (Transitional.Register.set r2
          (Transitional.val (Transitional.Register.get r1 tregs))
          (Transitional.tvtag (Transitional.Register.get r1 tregs)) tregs))
    (setm (setm mregs
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2)) (Atom w1 ts1))
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r1)) rao)
    r2.
Proof.
move=> Hne Hr1m [ra [Hra Hv Ht]].
have Era : ra = Atom w1 ts1 by move: Hra; rewrite Hr1m => -[].
subst ra.
exists (Atom w1 ts1).
have Hlt : forall r : register, Intermediate.Register.to_nat r < 32 by case.
have Hr21 : r2 <> r1.
{ move=> E. apply: Hne. by rewrite E. }
rewrite (tget_set_neq _ _ _ Hr21) tget_set_eq.
rewrite setmE (won_eqE (small_lt_reg (Hlt r2)) (small_lt_reg (Hlt r1))).
have -> : (Intermediate.Register.to_nat r2
           == Intermediate.Register.to_nat r1) = false.
{ by apply/eqP. }
rewrite setmE eqxx.
move: Hv Ht.
case E1: (Transitional.Register.get r1 tregs) => [vt1 vv1] /=.
move=> Hv Ht.
split.
- exact: erefl.
- exact: Hv.
- exact: Ht.
Qed.

Lemma reg_synced_mov_retag (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (r1 r2 : register) (w1 : mword mt) (ts1 : value_tag)
    (v2 : value) (t2 : value_tag) (ra2 : @ratom mt) :
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r1)) = Some (Atom w1 ts1) ->
  reg_syncedS amap tregs mregs r1 ->
  reg_syncedS amap
    (Transitional.Register.set r1
       (Transitional.val (Transitional.Register.get r1 tregs))
       (moved_tag (Transitional.tvtag (Transitional.Register.get r1 tregs)))
       (Transitional.Register.set r2 v2 t2 tregs))
    (setm (setm mregs
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2)) ra2)
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r1))
       (Atom w1 (moved_tag ts1)))
    r1.
Proof.
move=> Hr1m [ra [Hra Hv Ht]].
have Era : ra = Atom w1 ts1 by move: Hra; rewrite Hr1m => -[].
subst ra.
exists (Atom w1 (moved_tag ts1)).
rewrite tget_set_eq setmE eqxx.
move: Hv Ht.
case E1: (Transitional.Register.get r1 tregs) => [vt1 vv1] /=.
move=> Hv Ht.
rewrite Ht.
split.
- exact: erefl.
- move: Hv. rewrite /tvrel /=. by case: (vt1).
- exact: erefl.
Qed.

Lemma reg_synced_mov_any (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (RX r1 r2 : register) (w1 : mword mt) (ts1 : value_tag) :
  r1 <> r2 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r1)) = Some (Atom w1 ts1) ->
  (is_r r2 RX = true -> reg_syncedS amap tregs mregs r1) ->
  (is_r r2 RX = false -> reg_syncedS amap tregs mregs RX) ->
  reg_syncedS amap
    (Transitional.Register.set r1
       (Transitional.val (Transitional.Register.get r1 tregs))
       (moved_tag (Transitional.tvtag (Transitional.Register.get r1 tregs)))
       (Transitional.Register.set r2
          (Transitional.val (Transitional.Register.get r1 tregs))
          (Transitional.tvtag (Transitional.Register.get r1 tregs)) tregs))
    (setm (setm mregs
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2)) (Atom w1 ts1))
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r1))
       (Atom w1 (moved_tag ts1)))
    RX.
Proof.
move=> Hr12 Hr1m Hcopy Hkeep.
have Hr21 : r2 <> r1.
{ move=> E. apply: Hr12. by rewrite E. }
case E2x: (is_r r2 RX).
- rewrite -(is_r_eq E2x).
  apply: reg_synced_mov_copy.
  + exact: to_nat_neq Hr21.
  + exact: Hr1m.
  + exact: (Hcopy E2x).
- case E1x: (is_r r1 RX).
  + rewrite -(is_r_eq E1x).
    apply: reg_synced_mov_retag.
    * exact: Hr1m.
    * rewrite (is_r_eq E1x). exact: (Hkeep E2x).
  + apply: reg_synced_set_other.
    { move=> E. move: E1x. by rewrite /is_r -E PeanoNat.Nat.eqb_refl. }
    apply: reg_synced_set_other.
    { move=> E. move: E2x. by rewrite /is_r -E PeanoNat.Nat.eqb_refl. }
    exact: (Hkeep E2x).
Qed.

Lemma sync_mov (amap : amap_t) (tmem : Transitional.Memory.t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt})
    (mmem : {fmap mword mt -> matom})
    (pc : Pointer.t) (tg : mem_tag) (c : Component.id)
    (r1 r2 : register) (w1 : mword mt) (ts1 : value_tag)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (v : sv) :
  Transitional.executing cde pc (TrMov r1 r2) tg c ->
  svat pc = Some v ->
  r1 <> r2 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r1)) = Some (Atom w1 ts1) ->
  (sv_one v = true -> reg_syncedS amap tregs mregs R_ONE) ->
  (sv_ph v = PProlA -> sv_ek v = true \/ sv_sig v <> [::] ->
     reg_syncedS amap tregs mregs R_SP) ->
  sync_claims amap tmem tregs mregs mmem pc cur chain F ->
  sync_claims amap tmem
    (Transitional.Register.set r1
       (Transitional.val (Transitional.Register.get r1 tregs))
       (moved_tag (Transitional.tvtag (Transitional.Register.get r1 tregs)))
       (Transitional.Register.set r2
          (Transitional.val (Transitional.Register.get r1 tregs))
          (Transitional.tvtag (Transitional.Register.get r1 tregs)) tregs))
    (setm (setm mregs
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2)) (Atom w1 ts1))
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r1))
       (Atom w1 (moved_tag ts1)))
    mmem (Pointer.inc pc) cur chain F.
Proof.
move=> Hex Ev0 Hr12 Hr1m Hone Hsp HS.
have [v0 [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
have Ev0v : v0 = v by move: Ev; rewrite Ev0 => -[].
subst v0.
have [w0 [Ew Hle]] := Hnx isT.
move: Evs => /=.
case Et2: (is_r r2 R_SP || is_r r2 R_RA) => //.
move/negbT/norP: Et2 => [/negbTE E2sp /negbTE E2ra].
case E1sp: (is_r r1 R_SP).
+
  case Eph: (sv_ph v) => //.
  case E2a1: (is_r r2 R_AUX1) => // -[Evv]. subst v'.
  have Er1 : r1 = R_SP := is_r_eq E1sp.
  have Er2 : r2 = R_AUX1 := is_r_eq E2a1.
  subst r1 r2.
  have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
  apply: (sync_regw Ev Ew Hle (erefl _) (erefl _)).
  -
    apply: reg_synced_mov_any.
    * exact: Hr12.
    * exact: Hr1m.
    * by [].
    * move=> _. exact: (sy_com HS).
  -
    move=> Hau. by move: Ht1; rewrite Hau.
  -
    move=> Hau. by move: Ht2; rewrite Hau.
  -
    move=> Hasp Hcond.
    have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
    { move: Hcond. rewrite Eek' Esg. exact: id. }
    apply: reg_synced_mov_any.
    * exact: Hr12.
    * exact: Hr1m.
    * move=> _. exact: (Hsp Eph Hcondv).
    * by [].
  -
    move=> Hasp _. by move: Ht2; rewrite Hasp.
  -
    move=> Hw0arg.
    have Hargv : sv_arg v = true.
    { move: Hle => /and5P [_ _ _ HA _].
      move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
    apply: reg_synced_mov_any.
    * exact: Hr12.
    * exact: Hr1m.
    * by [].
    * move=> _. exact: (sy_arg HS Ev Hargv).
  -
    move=> Hpg Hcf.
    have Hcf' : cargfree v = true.
    { move: Hcf. rewrite /cargfree Esg Epd'. exact: id. }
    apply: reg_synced_mov_any.
    * exact: Hr12.
    * exact: Hr1m.
    * by [].
    * move=> _. exact: (sy_argp HS Ev Hpg Hcf').
  - exact: HS.
+
  case Edead: (t_eqb (rtaint v r1) ADead) => //.
  case Earg: (is_r r1 R_ARG && ~~ sv_arg v) => //.
  have Hsync1 : rtaint v r1 = AU -> reg_syncedS amap tregs mregs r1.
  { rewrite /rtaint E1sp.
    case Era1: (is_r r1 R_RA) => //.
    case Ea11: (is_r r1 R_AUX1).
    - move=> Hau. rewrite (is_r_eq Ea11). exact: (sy_a1u HS Ev Hau).
    - case Ea21: (is_r r1 R_AUX2).
      + move=> Hau. rewrite (is_r_eq Ea21). exact: (sy_a2u HS Ev Hau).
      + case Eone1: (is_r r1 R_ONE).
        * case Eonev: (sv_one v) => // _.
          rewrite (is_r_eq Eone1). exact: (Hone Eonev).
        * case Ecom1: (is_r r1 R_COM).
          -- move=> _. rewrite (is_r_eq Ecom1). exact: (sy_com HS).
          -- move=> _.
             have Er1 : r1 = R_ARG.
             { by case: (r1) E1sp Era1 Ea11 Ea21 Eone1 Ecom1. }
             have Hargv : sv_arg v = true.
             { move: Earg. rewrite Er1 /=.
               by case: (sv_arg v). }
             rewrite Er1. exact: (sy_arg HS Ev Hargv). }
  have Hsync1sp : rtaint v r1 = ASp ->
      sv_ek v = true \/ sv_sig v <> [::] ->
      reg_syncedS amap tregs mregs r1.
  { rewrite /rtaint E1sp.
    case Era1: (is_r r1 R_RA) => //.
    case Ea11: (is_r r1 R_AUX1).
    - move=> Hasp Hcnd. rewrite (is_r_eq Ea11).
      exact: (sy_a1sp HS Ev Hasp Hcnd).
    - case Ea21: (is_r r1 R_AUX2).
      + move=> Hasp Hcnd. rewrite (is_r_eq Ea21).
        exact: (sy_a2sp HS Ev Hasp Hcnd).
      + case Eone1: (is_r r1 R_ONE).
        * by case: (sv_one v).
        * case Earg1: (is_r r1 R_ARG); last by [].
          by case: (sv_arg v). }
  case Eaux: (is_r r2 R_AUX1 || is_r r2 R_AUX2).
  -
    move=> -[Evv]. subst v'.
    case/orP: Eaux => [E2a1|E2a2].
    *
      have Er2 : r2 = R_AUX1 := is_r_eq E2a1.
      subst r2.
      have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
      apply: (sync_regw Ev Ew Hle (erefl _) (erefl _)).
      --
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_com HS).
      --
         move=> Hau.
         have Hsrc : rtaint v r1 = AU.
         { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ move=> _. exact: (Hsync1 Hsrc).
         ++ by [].
      --
         move=> Hau.
         have Hav : sv_a2 v = AU.
         { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_a2u HS Ev Hav).
      --
         move=> Hasp Hcond.
         have Hsrc : rtaint v r1 = ASp.
         { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
         { move: Hcond. rewrite Eek' Esg. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ move=> _. exact: (Hsync1sp Hsrc Hcondv).
         ++ by [].
      --
         move=> Hasp Hcond.
         have Hav : sv_a2 v = ASp.
         { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
         { move: Hcond. rewrite Eek' Esg. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_a2sp HS Ev Hav Hcondv).
      --
         move=> Hw0arg.
         have Hargv : sv_arg v = true.
         { move: Hle => /and5P [_ _ _ HA _].
           move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_arg HS Ev Hargv).
      --
         move=> Hpg Hcf.
         have Hcf' : cargfree v = true.
         { move: Hcf. rewrite /cargfree Esg Epd'. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_argp HS Ev Hpg Hcf').
      -- exact: HS.
    *
      have Er2 : r2 = R_AUX2 := is_r_eq E2a2.
      subst r2.
      have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
      apply: (sync_regw Ev Ew Hle (erefl _) (erefl _)).
      --
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_com HS).
      --
         move=> Hau.
         have Hav : sv_a1 v = AU.
         { move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_a1u HS Ev Hav).
      --
         move=> Hau.
         have Hsrc : rtaint v r1 = AU.
         { move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ move=> _. exact: (Hsync1 Hsrc).
         ++ by [].
      --
         move=> Hasp Hcond.
         have Hav : sv_a1 v = ASp.
         { move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
         { move: Hcond. rewrite Eek' Esg. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_a1sp HS Ev Hav Hcondv).
      --
         move=> Hasp Hcond.
         have Hsrc : rtaint v r1 = ASp.
         { move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
         have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
         { move: Hcond. rewrite Eek' Esg. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ move=> _. exact: (Hsync1sp Hsrc Hcondv).
         ++ by [].
      --
         move=> Hw0arg.
         have Hargv : sv_arg v = true.
         { move: Hle => /and5P [_ _ _ HA _].
           move: HA. rewrite Hw0arg /o_le orbF. exact: Bool.eqb_prop. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_arg HS Ev Hargv).
      --
         move=> Hpg Hcf.
         have Hcf' : cargfree v = true.
         { move: Hcf. rewrite /cargfree Esg Epd'. exact: id. }
         apply: reg_synced_mov_any.
         ++ exact: Hr12.
         ++ exact: Hr1m.
         ++ by [].
         ++ move=> _. exact: (sy_argp HS Ev Hpg Hcf').
      -- exact: HS.
  -
    case Eau: (t_eqb (rtaint v r1) AU) => // -[Evv]. subst v'.
    have Hsrc0 : rtaint v r1 = AU := t_eqb_eq Eau.
    have HSY1 := Hsync1 Hsrc0.
    move/negbT/norP: Eaux => [/negbTE E2a1 /negbTE E2a2].
    have Wsg : sv_sig (warg_w r2 (wone r2 false v)) = sv_sig v.
    { rewrite /warg_w /warg /wone.
      by case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wpd : sv_pend (warg_w r2 (wone r2 false v)) = sv_pend v.
    { rewrite /warg_w /warg /wone.
      by case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wa1 : sv_a1 (warg_w r2 (wone r2 false v)) = sv_a1 v.
    { rewrite /warg_w /warg /wone.
      by case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wa2 : sv_a2 (warg_w r2 (wone r2 false v)) = sv_a2 v.
    { rewrite /warg_w /warg /wone.
      by case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have Wek : sv_ek (warg_w r2 (wone r2 false v)) = sv_ek v.
    { rewrite /warg_w /warg /wone.
      by case: (is_r r2 R_ONE); case: (is_r r2 R_ARG). }
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    apply: (sync_regw Ev Ew Hle Wsg Wpd).
    *
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- move=> _. exact: HSY1.
      -- move=> _. exact: (sy_com HS).
    *
      move=> Hau.
      have Hav : sv_a1 v = AU.
      { rewrite -Wa1. move: Ht1. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- by rewrite E2a1.
      -- move=> _. exact: (sy_a1u HS Ev Hav).
    *
      move=> Hau.
      have Hav : sv_a2 v = AU.
      { rewrite -Wa2. move: Ht2. rewrite Hau /t_le orbF. exact: t_eqb_eq. }
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- by rewrite E2a2.
      -- move=> _. exact: (sy_a2u HS Ev Hav).
    *
      move=> Hasp Hcond.
      have Hav : sv_a1 v = ASp.
      { rewrite -Wa1. move: Ht1. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
      { move: Hcond. rewrite Eek' Wek Esg Wsg. exact: id. }
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- by rewrite E2a1.
      -- move=> _. exact: (sy_a1sp HS Ev Hav Hcondv).
    *
      move=> Hasp Hcond.
      have Hav : sv_a2 v = ASp.
      { rewrite -Wa2. move: Ht2. rewrite Hasp /t_le orbF. exact: t_eqb_eq. }
      have Hcondv : sv_ek v = true \/ sv_sig v <> [::].
      { move: Hcond. rewrite Eek' Wek Esg Wsg. exact: id. }
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- by rewrite E2a2.
      -- move=> _. exact: (sy_a2sp HS Ev Hav Hcondv).
    *
      move=> Hw0arg.
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- move=> _. exact: HSY1.
      -- move=> E2arg.
         have Hargv : sv_arg v = true.
         { move: Hle => /and5P [_ _ _ HA _].
           move: HA. rewrite Hw0arg /o_le orbF.
           rewrite /warg_w /warg /wone E2arg.
           by case: (is_r r2 R_ONE); exact: Bool.eqb_prop. }
         exact: (sy_arg HS Ev Hargv).
    *
      move=> Hpg Hcf.
      apply: reg_synced_mov_any.
      -- exact: Hr12.
      -- exact: Hr1m.
      -- move=> _. exact: HSY1.
      -- move=> _.
         have Hcf' : cargfree v = true.
         { move: Hcf. rewrite /cargfree Esg Wsg Epd' Wpd. exact: id. }
         exact: (sy_argp HS Ev Hpg Hcf').
    * exact: HS.
Qed.

(* The carried relational invariant: the discipline ([MDisc.dinv]) and the
   sync claims share one ghost pack (cur/chain/F/cs) — the per-case threading
   consumes [dinv_step_X] and [sync_X] on the same witnesses and repacks. *)

Definition mm_dsync (amap : amap_t) (ts : TS.state)
    (ms : @Symbolic.state mt lrc_tags unit) : Prop :=
  let '(tmem, tregs, pc, pct) := ts in
  exists cur chain F cs,
    MDisc.dinv cde MM cur chain F cs tmem tregs pc pct /\
    sync_claims amap tmem tregs (Symbolic.regs ms) (Symbolic.mem ms)
      pc cur chain F.

End SyncDef.

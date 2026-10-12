(** * T2M per-step dispatch and star simulation.  [t2me_step_sim] turns
    one [TS.step] into a [plus] of me steps preserving [match_st] and the
    heap occupancy invariant, dispatching on the T instruction to the
    per-opcode diagrams (MStep.v / MAlloc.v). *)

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype order ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import S2T.TSem.
Require Import S2T.TSim.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.
Require Import MicroPolicies.Recomposition.BufferShape.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require Import T2M.MStep.
Require Import T2M.MAlloc.
Require Import T2M.MHeap.
Require T2M.MDefs.
Require Import T2M.MSig.
Require T2M.MDisc.
Require T2M.MDiscStepA.
Require T2M.MDiscStepA2.
Require T2M.MDiscStepB.
Require T2M.MDiscStepC.
Require T2M.MDiscStepD.
Require Import T2M.MSync.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section StarSim.

Variable NC : nat.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Local Notation cdeW :=
  (Transitional.intermediate_to_transitional_gen PI
     (Intermediate.program_link pra prb)).
Local Notation codeW :=
  (compiler_code L P C PB PI pra ++ compiler_code L P C PB PI prb).
Local Notation pc0 := (size (initial_memory (mt := mt) PB)).
Local Notation match_statesW := (match_states L P C pra prb PB PI).
Local Notation match_stW := (match_st L P C pra prb PB PI).
Local Notation mregs_relW := (mregs_rel L P C pra prb PB PI).
Local Notation reg_syncedW := (reg_synced L P C pra prb PB PI).
Local Notation mstep := (RSCDefs.prog_step_me NC).

(* ---- the checker context (discharged at assembly, like the other
   standing hypotheses) ---- *)
Variable MM : Component.id -> seq sv.
Hypothesis HMM : forall c S,
  getm cdeW c = Some S -> comp_ok (c, 1, Z0) S (MM c).
Hypothesis Hcst : forall pc iv r tg c p,
  Transitional.executing cdeW pc (TrConst iv r) tg c ->
  iv = IPtr p ->
  p = (c, 0, Z0) \/
  ((p = (c, 1, Z0) \/ p = (c, 1, BinInt.Z.one)) /\
   (r = R_AUX1 \/ r = R_AUX2)).
Hypothesis HuniqL : forall (c : Component.id) (S : TS.tcode) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  getm cdeW c = Some S ->
  nth_error S m = Some (TrLabel (inl l), t1) ->
  nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.

Local Notation mm_dsyncW := (mm_dsync L P C pra prb PB PI MM cdeW).

(* ---- the standing side conditions (as in MStep/MAlloc) ---- *)
Hypothesis Hbound : pc0 + size codeW < 2 ^ word_size mt.
Hypothesis HPB :
  PB = Intermediate.prog_buffers (Intermediate.program_link pra prb).
Hypothesis Hwfa : Intermediate.well_formed_program pra.
Hypothesis Hwfb : Intermediate.well_formed_program prb.
Hypothesis Hlinkable :
  linkable (Intermediate.prog_interface pra) (Intermediate.prog_interface prb).
Hypothesis Hsmall :
  size (linearize_bufs PB) + size codeW < Merged.alloc_label.
Hypothesis HNCws : NC <= word_size mt.
Hypothesis HNCal : Merged.alloc_label < 2 ^ (word_size mt - NC).
Hypothesis HNCeq : NC = MDefs.NC.
Hypothesis Himm_a : MDefs.imm_fits pra.
Hypothesis Himm_b : MDefs.imm_fits prb.

(* ---- the label/procedure statics (as in MStep) ---- *)
Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Huniq_a : forall cid l0 Cprocs0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.
Hypothesis Huniq_b : forall cid l0 Cprocs0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.

(* ---- the statics this file consumes ---- *)

Hypothesis Hself : forall tpc r1 r2 tg c,
  Transitional.executing cdeW tpc (TrMov r1 r2) tg c -> r1 <> r2.

Hypothesis Hjra : forall tpc r tg c,
  Transitional.executing cdeW tpc (TrJump r) tg c -> r = R_RA.

Hypothesis Hbf : forall tpc r l tg c pc',
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' ->
  BinInt.Z.le (Pointer.offset tpc) (Pointer.offset pc').

Hypothesis HlL_bnz : forall tpc r l tg c pc',
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' -> l < L.
Hypothesis HlL_jal : forall tpc l tg c pc',
  Transitional.executing cdeW tpc (TrJalNat l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' -> l < L.

Hypothesis HpP : forall tpc c' pid tg c pc',
  Transitional.executing cdeW tpc (TrJalProc (c', pid)) tg c ->
  Transitional.find_plabel_in_code cdeW c' pid = Some pc' -> pid < P.

Hypothesis Hsucc_jal : forall tpc l tg c,
  Transitional.executing cdeW tpc (TrJalNat l) tg c ->
  exists i3 tg3, Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c.
Hypothesis Hsucc_call : forall tpc pl tg c,
  Transitional.executing cdeW tpc (TrJalProc pl) tg c ->
  exists i3 tg3, Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c.

Hypothesis Hc1s : forall tpc i tg c,
  Transitional.executing cdeW tpc i tg c ->
  1 + Pointer.component tpc < 2 ^ NC.

(* ================================================================== *)
(* 1. Deriving [reg_synced] — refuting the clobbered disjunct.        *)
(* ================================================================== *)

(* any fact contradicting [get r tregs = tUndef] flips [mregs_rel]'s
   disjunction to the strong branch *)
Lemma mregs_rel_synced (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) :
  mregs_relW amap tregs mregs ->
  Transitional.Register.get r tregs <> Transitional.tUndef ->
  reg_syncedW amap tregs mregs r.
Proof.
move=> Hrel Hne.
case: (Hrel r) => [//|[ra [_ Hu _]]].
by rewrite Hu in Hne.
Qed.

(* the common refuters *)
Lemma get_int_synced (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (z : Z) :
  mregs_relW amap tregs mregs ->
  Transitional.val (Transitional.Register.get r tregs) = Int z ->
  reg_syncedW amap tregs mregs r.
Proof.
move=> Hrel Hv.
apply: mregs_rel_synced Hrel _ => E.
by rewrite E in Hv.
Qed.

Lemma get_ptr_synced (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (p : Pointer.t) :
  mregs_relW amap tregs mregs ->
  Transitional.val (Transitional.Register.get r tregs) = Ptr p ->
  reg_syncedW amap tregs mregs r.
Proof.
move=> Hrel Hv.
apply: mregs_rel_synced Hrel _ => E.
by rewrite E in Hv.
Qed.

Lemma get_tag_synced (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (vt : value_tag) :
  mregs_relW amap tregs mregs ->
  Transitional.tvtag (Transitional.Register.get r tregs) = vt ->
  vt <> Other ->
  reg_syncedW amap tregs mregs r.
Proof.
move=> Hrel Ht Hne.
apply: mregs_rel_synced Hrel _ => E.
by rewrite E /= in Ht; rewrite -Ht in Hne.
Qed.

(* the [rtaint]-row map: every register the checker taints [AU] at a
   [dinv]+[sync_claims] state has its me image in the synced branch.
   The only reader of the [rtaint] shape. *)
Lemma rtaint_AU_synced (amap : amap_t)
    (mem : Transitional.Memory.t) (regs : Transitional.Register.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (pc : Pointer.t) (pct : Transitional.pc_tag)
    (cur : option Block.id) (chain : seq MDisc.act)
    (F : Component.id -> seq Block.id) (cs : value) (v0 : sv) :
  MDisc.dinv cdeW MM cur chain F cs mem regs pc pct ->
  sync_claims L P C pra prb PB PI MM amap mem regs
    (Symbolic.regs ms) (Symbolic.mem ms) pc cur chain F ->
  mregs_relW amap regs (Symbolic.regs ms) ->
  MDisc.svat MM pc = Some v0 ->
  forall r, rtaint v0 r = AU -> reg_syncedW amap regs (Symbolic.regs ms) r.
Proof.
move=> HI HS Hregs Ev r.
rewrite /rtaint.
case Espq: (is_r r R_SP) => //.
case Eraq: (is_r r R_RA) => //.
case Ea1q: (is_r r R_AUX1).
- move=> Ea1.
  have -> : r = R_AUX1 := MDisc.is_r_eq Ea1q.
  exact: (sy_a1u HS Ev Ea1).
- case Ea2q: (is_r r R_AUX2).
  + move=> Ea2.
    have -> : r = R_AUX2 := MDisc.is_r_eq Ea2q.
    exact: (sy_a2u HS Ev Ea2).
  + case Eoneq: (is_r r R_ONE).
    * case Eone: (sv_one v0) => // _.
      have -> : r = R_ONE := MDisc.is_r_eq Eoneq.
      apply: (get_int_synced Hregs).
      exact: (MDisc.di_one HI Ev Eone).
    * case Eargq: (is_r r R_ARG).
      -- case Earg: (sv_arg v0) => // _.
         have -> : r = R_ARG := MDisc.is_r_eq Eargq.
         exact: (sy_arg HS Ev Earg).
      -- move=> _.
         have -> : r = R_COM.
         { by move: Espq Eraq Ea1q Ea2q Eoneq Eargq; case: (r). }
         exact: (sy_com HS).
Qed.

(* ================================================================== *)
(* 2. The heap occupancy invariant.                                   *)
(* ================================================================== *)

(* the me bump allocator's high-water mark stays within the region
   start plus the T-side footprint — what [sim_alloc]'s capacity
   premise ([Hfitcap]) consumes, maintained along the star *)
Definition heap_inv (tmem : Transitional.Memory.t)
    (mmem : {fmap mword mt -> matom}) : Prop :=
  forall cid cm,
    tmem cid = Some cm ->
    1 + cid < 2 ^ NC ->
    (\val (maxaddr NC mmem cid) : nat)
    <= (1 + cid) * 2 ^ (word_size mt - NC) + MDefs.heap_used cm.

Lemma maxaddr_domm (mmem mmem' : {fmap mword mt -> matom}) (c0 : nat) :
  domm mmem' = domm mmem ->
  maxaddr NC mmem' c0 = maxaddr NC mmem c0.
Proof.
by rewrite /maxaddr => ->.
Qed.

(* silent me steps + unchanged T memory *)
Lemma heap_inv_pres (tmem : Transitional.Memory.t)
    (mmem mmem' : {fmap mword mt -> matom}) :
  domm mmem' = domm mmem ->
  heap_inv tmem mmem -> heap_inv tmem mmem'.
Proof.
move=> Hd Hh cid cm Hcm Hb.
rewrite (maxaddr_domm _ Hd).
exact: (Hh _ _ Hcm Hb).
Qed.

(* T stores keep the footprint; me stores keep the domain *)
Lemma heap_inv_store (tmem tmem' : Transitional.Memory.t)
    (ptr : Pointer.t) (v : Transitional.tvalue * mem_tag)
    (mmem mmem' : {fmap mword mt -> matom}) :
  Transitional.Memory.store tmem ptr v = Some tmem' ->
  domm mmem' = domm mmem ->
  heap_inv tmem mmem -> heap_inv tmem' mmem'.
Proof.
rewrite /Transitional.Memory.store.
case Hc0: (tmem (Pointer.component ptr)) => [cm0|] //=.
case Hsb: (Transitional.Memory.store_b cm0 (Pointer.block ptr)
             (Pointer.offset ptr) v) => [cmn|] //=.
move=> [<-] Hd Hh cid cm Hcm Hb.
move: Hcm Hb; rewrite setmE.
case: (altP (cid =P Pointer.component ptr)) => [->|Hne] Hcm Hb.
- case: Hcm => <-.
  rewrite (maxaddr_domm _ Hd) (heap_used_store_b Hsb).
  exact: (Hh _ _ Hc0 Hb).
- rewrite (maxaddr_domm _ Hd).
  exact: (Hh _ _ Hcm Hb).
Qed.

(* six silent me steps make a [plus] *)
Lemma star1 (a b c : @Symbolic.state mt lrc_tags unit) :
  step_me (NC := NC) a b None ->
  star mstep tt b E0 c -> star mstep tt a E0 c.
Proof.
move=> HS HT.
have HS' : mstep tt a E0 b := HS.
apply: star_step; [exact: HS' | exact: HT | by []].
Qed.

Lemma plus6 (s1 s2 s3 s4 s5 s6 s7 : @Symbolic.state mt lrc_tags unit) :
  step_me (NC := NC) s1 s2 None ->
  step_me (NC := NC) s2 s3 None ->
  step_me (NC := NC) s3 s4 None ->
  step_me (NC := NC) s4 s5 None ->
  step_me (NC := NC) s5 s6 None ->
  step_me (NC := NC) s6 s7 None ->
  plus mstep tt s1 E0 s7.
Proof.
move=> H1 H2 H3 H4 H5 H6.
have H1' : mstep tt s1 E0 s2 := H1.
apply: plus_left; [exact: H1' | | by []].
apply: star1 H2 _. apply: star1 H3 _. apply: star1 H4 _.
apply: star1 H5 _. apply: star1 H6 _.
exact: star_refl.
Qed.

(* an upper bound for the high-water mark: bound the default and every
   in-region key *)
Lemma maxaddr_ub (m : {fmap mword mt -> matom}) (c0 B : nat) :
  ((\val (LRC.component_memory_prefix (NC := NC)
            (ssrint.Posz (1 + c0)) : mword mt) : nat) <= B) ->
  (forall w : mword mt, w \in domm m ->
     pfilterC NC c0 w -> (\val w : nat) <= B) ->
  (\val (maxaddr NC m c0) : nat) <= B.
Proof.
move=> Hdflt Hmem.
rewrite maxaddrE.
case E: (filter (pfilterC NC c0) (domm m)) => [|x s] //=.
have Hin : last x s \in filter (pfilterC NC c0) (domm m).
{ rewrite E.
  have -> : last x s = last x (x :: s) by [].
  have -> : last x (x :: s) = last x s by [].
  exact: (mem_last x s). }
move: Hin; rewrite mem_filter => /andP[Hp Hd].
exact: Hmem Hd Hp.
Qed.

(* ================================================================== *)
(* 2b. The BINOP arithmetic bridge (pointer shapes).                  *)
(* ================================================================== *)

(* adding a related integer to a flat address, in words *)
Lemma won_addw_wrepr (m m' : nat) (nz : Z) (w2 : mword mt) :
  wrepr nz w2 ->
  Z.of_nat m' = BinInt.Z.add (Z.of_nat m) nz ->
  addw (@word_of_nat (word_size mt) m) w2
  = @word_of_nat (word_size mt) m'.
Proof.
move=> H2 Em.
have [k2 E2] := wrepr_val Hbound Hsmall H2.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hw2 : n2 < 2 ^ word_size mt by rewrite /n2; exact: ltn_ord.
have Hval : (\val (addw (@word_of_nat (word_size mt) m) w2) : nat)
            = ((\val (@word_of_nat (word_size mt) m) : nat) + n2)
              %% 2 ^ word_size mt
  := valw_addw (@word_of_nat (word_size mt) m) w2.
have Em1 : (\val (@word_of_nat (word_size mt) m) : nat)
           = m %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m.
have Em2 : (\val (@word_of_nat (word_size mt) m') : nat)
           = m' %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m'.
have Hmid : (m + n2) %% 2 ^ word_size mt = m' %% 2 ^ word_size mt.
{ rewrite !E32. by lia. }
apply: (@word_nat_inj (word_size mt)).
exact: (eq_trans Hval
         (eq_trans (congr1 (fun x => (x + n2) %% 2 ^ word_size mt) Em1)
            (eq_trans (modnDml m n2 (2 ^ word_size mt))
               (eq_trans Hmid (esym Em2))))).
Qed.

(* subtracting a related integer from a flat address *)
Lemma won_subw_wrepr (m m' : nat) (nz : Z) (w2 : mword mt) :
  wrepr nz w2 ->
  Z.of_nat m' = BinInt.Z.sub (Z.of_nat m) nz ->
  subw (@word_of_nat (word_size mt) m) w2
  = @word_of_nat (word_size mt) m'.
Proof.
move=> H2 Em.
have [k2 E2] := wrepr_val Hbound Hsmall H2.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hw2 : n2 < 2 ^ word_size mt by rewrite /n2; exact: ltn_ord.
have Hval : (\val (subw (@word_of_nat (word_size mt) m) w2) : nat)
            = ((\val (@word_of_nat (word_size mt) m) : nat)
               + (\val (oppw w2) : nat)) %% 2 ^ word_size mt
  := valw_addw (@word_of_nat (word_size mt) m) (oppw w2).
have Eop : (\val (oppw w2) : nat)
           = (2 ^ word_size mt - n2) %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) (2 ^ word_size mt - n2).
have Em1 : (\val (@word_of_nat (word_size mt) m) : nat)
           = m %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m.
have Em2 : (\val (@word_of_nat (word_size mt) m') : nat)
           = m' %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m'.
have Hmid : (m + (2 ^ word_size mt - n2)) %% 2 ^ word_size mt
            = m' %% 2 ^ word_size mt.
{ rewrite !E32. rewrite !E32 in Hw2. by lia. }
apply: (@word_nat_inj (word_size mt)).
exact: (eq_trans Hval
         (eq_trans
            (congr1 (fun x => ((\val (@word_of_nat (word_size mt) m)
                                : nat) + x) %% 2 ^ word_size mt) Eop)
            (eq_trans (modnDmr _ _ _)
               (eq_trans
                  (congr1 (fun x => (x + (2 ^ word_size mt - n2))
                                    %% 2 ^ word_size mt) Em1)
                  (eq_trans (modnDml _ _ _)
                     (eq_trans Hmid (esym Em2))))))).
Qed.

(* the flat difference of two same-block addresses decodes to the
   offset difference *)
Lemma won_subw_won (m1 m2 : nat) (z : Z) :
  m1 <= 2 ^ word_size mt ->
  m2 <= 2 ^ word_size mt ->
  MDefs.int_fits z ->
  BinInt.Z.sub (Z.of_nat m1) (Z.of_nat m2) = z ->
  wrepr z (subw (@word_of_nat (word_size mt) m1)
             (@word_of_nat (word_size mt) m2)).
Proof.
move=> Hm1 Hm2 Hf Em.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set v := nat_of_ord (word.ord_of_word
           (subw (@word_of_nat (word_size mt) m1)
              (@word_of_nat (word_size mt) m2))).
have Hv : v < 2 ^ word_size mt by rewrite /v; exact: ltn_ord.
have Hval : (\val (subw (@word_of_nat (word_size mt) m1)
                     (@word_of_nat (word_size mt) m2)) : nat)
            = ((\val (@word_of_nat (word_size mt) m1) : nat)
               + (\val (oppw (@word_of_nat (word_size mt) m2)) : nat))
              %% 2 ^ word_size mt
  := valw_addw (@word_of_nat (word_size mt) m1)
       (oppw (@word_of_nat (word_size mt) m2)).
have Eop : (\val (oppw (@word_of_nat (word_size mt) m2)) : nat)
           = (2 ^ word_size mt
              - (\val (@word_of_nat (word_size mt) m2) : nat))
             %% 2 ^ word_size mt
  := @valw_as_word (word_size mt)
       (2 ^ word_size mt - \val (@word_of_nat (word_size mt) m2)).
have Em1 : (\val (@word_of_nat (word_size mt) m1) : nat)
           = m1 %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m1.
have Em2 : (\val (@word_of_nat (word_size mt) m2) : nat)
           = m2 %% 2 ^ word_size mt
  := @valw_as_word (word_size mt) m2.
have Ev : v = (m1 + (2 ^ word_size mt
                     - m2 %% 2 ^ word_size mt)) %% 2 ^ word_size mt.
{ rewrite /v.
  exact: (eq_trans Hval
           (eq_trans
              (congr1 (fun x => ((\val (@word_of_nat (word_size mt) m1)
                                  : nat) + x) %% 2 ^ word_size mt)
                 (eq_trans Eop
                    (congr1 (fun x => (2 ^ word_size mt - x)
                                      %% 2 ^ word_size mt) Em2)))
              (eq_trans (modnDmr _ _ _)
                 (eq_trans
                    (congr1 (fun x => (x + (2 ^ word_size mt
                        - m2 %% 2 ^ word_size mt)) %% 2 ^ word_size mt)
                       Em1)
                    (modnDml _ _ _))))). }
case: (Hf) => Hzlo Hzhi.
rewrite !E32 in Hv Ev Hm1 Hm2.
have [E0|E1] : Z.of_nat v = z
               \/ Z.of_nat v = BinInt.Z.add z (4294967296 : Z)
  by lia.
- apply: (wrepr_congr Hbound Hsmall (k := (0 : Z)) Hf).
  rewrite -/v. by lia.
- apply: (wrepr_congr Hbound Hsmall (k := (1 : Z)) Hf).
  rewrite -/v. by lia.
Qed.

(* flat same-block equality decodes to offset equality *)
Lemma wrepr_eq_flat (a o1 o2 : nat) :
  a + o1 < 2 ^ word_size mt ->
  a + o2 < 2 ^ word_size mt ->
  wrepr (Util.Z.of_bool (o1 == o2))
        (word.as_word (((@word_of_nat (word_size mt) (a + o1)
                         == @word_of_nat (word_size mt) (a + o2))) : nat)).
Proof.
move=> H1 H2.
rewrite won_eqE // eqn_add2l.
case E: (o1 == o2) => /=.
- have Hfit1 : MDefs.int_fits 1 by split; lia.
  have := wrepr_encode_int Hfit1.
  by [].
- have Hfit0 : MDefs.int_fits 0 by split; lia.
  have := wrepr_encode_int Hfit0.
  by [].
Qed.

(* flat same-block comparison decodes to offset comparison: signed word
   comparison agrees with [Leq] on the WHOLE [int_fits] window (the me
   [LEQ] is signed via [int_of_word]) *)
Lemma wrepr_lequw (z1 z2 : Z) (w1 w2 : mword mt) :
  MDefs.int_fits z1 -> MDefs.int_fits z2 ->
  wrepr z1 w1 -> wrepr z2 w2 ->
  wrepr (Util.Z.of_bool (BinInt.Z.leb z1 z2))
        (word.as_word
           (((word.int_of_word w1 <= word.int_of_word w2)%O) : nat)).
Proof.
move=> Hf1 Hf2 H1 H2.
have [k1 E1] := wrepr_val Hbound Hsmall H1.
have [k2 E2] := wrepr_val Hbound Hsmall H2.
have Hb31 : Z.of_nat (2 ^ 31) = (2147483648 : Z) by rewrite expn_Zpow31.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n1 := nat_of_ord (word.ord_of_word w1) in E1 *.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hw1 : n1 < 2 ^ word_size mt by rewrite /n1; exact: ltn_ord.
have Hw2 : n2 < 2 ^ word_size mt by rewrite /n2; exact: ltn_ord.
case: (Hf1) => Hlo1 Hhi1. case: (Hf2) => Hlo2 Hhi2.
rewrite E32 in Hw1 Hw2.
have Hk1 : k1 = BinNums.Z0 \/ k1 = BinNums.Zpos BinNums.xH by lia.
have Hk2 : k2 = BinNums.Z0 \/ k2 = BinNums.Zpos BinNums.xH by lia.
have E31 : 2 ^ (word_size mt).-1 = 2 ^ 31 := erefl _.
have Eleq : ((word.int_of_word w1 <= word.int_of_word w2)%O)
            = BinInt.Z.leb z1 z2.
{ rewrite /word.int_of_word E31 -/n1 -/n2.
  case: ifP => T1; case: ifP => T2;
  case Eb: (BinInt.Z.leb z1 z2);
  try (move/BinInt.Z.leb_le: Eb => Eb; apply/idP; by lia);
  move/BinInt.Z.leb_gt: Eb => Eb; apply/negbTE/negP => Hle; by lia. }
rewrite Eleq.
case Eb: (BinInt.Z.leb z1 z2) => /=.
- have Hfit1 : MDefs.int_fits 1 by split; lia.
  have := wrepr_encode_int Hfit1.
  by [].
- have Hfit0 : MDefs.int_fits 0 by split; lia.
  have := wrepr_encode_int Hfit0.
  by [].
Qed.

Lemma get_value_val (r : register) (tregs : Transitional.Register.t) :
  Transitional.Register.get_value r tregs
  = Transitional.val (Transitional.Register.get r tregs).
Proof.
rewrite /Transitional.Register.get_value /Transitional.Register.get.
by case: (getm _ _).
Qed.

(* an indexed CArg contradicts CArg-freeness (mirror of
   [MDisc.nth_error_hasCRa]) *)
Lemma nth_error_hasCArg (sg : seq class3) (j : nat) :
  nth_error sg j = Some CArg -> has (fun k => c3_eqb k CArg) sg.
Proof.
elim: sg j => [|x sg IH] [|j] //=.
- by move=> [->]; rewrite c3_eqb_refl.
- move=> H. by rewrite (IH _ H) orbT.
Qed.

(* the cell-claim transport across a T allocation: fresh cells are
   trivially synced (T Undef vs me 0, both def-tagged); old cells
   convert through the extension shape *)
Lemma cell_synced_alloc_trans (amap : amap_t) (base : nat)
    (tmem tmem' : Transitional.Memory.t)
    (mmem BB : {fmap mword mt -> matom})
    (c : Component.id) (n : nat) (ptr : Pointer.t) :
  Transitional.Memory.alloc tmem c n = Some (tmem', ptr) ->
  minj PB (cmapW L P C pra prb PB PI) amap tmem mmem ->
  addr_of amap (Pointer.component ptr) (Pointer.block ptr) = None ->
  (forall o, o < n ->
     getm (unionm mmem BB) (@word_of_nat (word_size mt) (base + o))
     = Some (Atom (word.as_word 0 : mword mt) (def_mem_tag c false))) ->
  forall c0 b0 j0,
    cell_synced L P C pra prb PB PI amap tmem mmem c0 b0 j0 ->
    cell_synced L P C pra prb PB PI
      (amap_upd amap (Pointer.component ptr) (Pointer.block ptr) base)
      tmem' (unionm mmem BB) c0 b0 j0.
Proof.
move=> Hal Hmj Hfr Hocells c0 b0 j0 Hold cm2 blk2 cell a2 mc2
       Hcm2 Hblk2 Hnth2 Ha2 Hmc2.
have [cmA [HcmA [EptrA EmemA]]] := MDisc.alloc_shape Hal.
have Ecp : Pointer.component ptr = c by rewrite EptrA.
have Ebp : Pointer.block ptr = Transitional.Memory.nextblock cmA
  by rewrite EptrA.
case: (altP ((c0, b0) =P (Pointer.component ptr, Pointer.block ptr)))
  => [Ecb|Hne].
-
  case: Ecb => Ec0 Eb0. subst c0 b0.
  have Ea2b : a2 = base.
  { move: Ha2. rewrite addr_of_upd_same. by move=> [<-]. }
  subst a2.
  move: Hcm2. rewrite EmemA Ecp setmE eqxx => -[Ecm2]. subst cm2.
  move: Hblk2. rewrite /= Ebp setmE eqxx => -[Eblk2]. subst blk2.
  have Ecell : cell = (Transitional.tUndef, def_mem_tag c false)
    := MDisc.nth_error_repeat_inv Hnth2.
  subst cell.
  have Hj0 : j0 < n.
  { have := nth_error_size Hnth2.
    by rewrite size_repeat. }
  move: Hmc2. rewrite (Hocells _ Hj0) => -[<-].
  split.
  + rewrite /tvrel /=. exact: VRUndef.
  + exact: erefl.
  + exact: erefl.
-
  have Ha2' : addr_of amap c0 b0 = Some a2.
  { move: Ha2. rewrite addr_of_upd_other; first by [].
    by apply/eqP. }
  move: Hcm2. rewrite EmemA setmE.
  case Ec0c: (c0 == c) => Hcm2.
  +
    move/eqP: Ec0c => Ec0c. subst c0.
    case: Hcm2 => Ecm2. subst cm2.
    move: Hblk2. rewrite /= setmE.
    have Ebne : (b0 == Transitional.Memory.nextblock cmA) = false.
    { case Eb: (b0 == _) => //.
      move/eqP: Eb => Eb. subst b0.
      move: Hne. by rewrite Ecp Ebp eqxx. }
    rewrite Ebne => Hblk2.
    have [mcO [HmcO _]] := mj_cell Hmj HcmA Hblk2 Hnth2 Ha2'.
    move: Hmc2. rewrite unionmE HmcO => -[Emc2]. subst mc2.
    exact: (@cellrel_upd _ _ _ _ base _ _ Hfr
              (Hold _ _ _ _ _ HcmA Hblk2 Hnth2 Ha2' HmcO)).
  +
    have [mcO [HmcO _]] := mj_cell Hmj Hcm2 Hblk2 Hnth2 Ha2'.
    move: Hmc2. rewrite unionmE HmcO => -[Emc2]. subst mc2.
    exact: (@cellrel_upd _ _ _ _ base _ _ Hfr
              (Hold _ _ _ _ _ Hcm2 Hblk2 Hnth2 Ha2' HmcO)).
Qed.

(* ================================================================== *)
(* 3. The per-step dispatch.                                          *)
(* ================================================================== *)

Theorem t2me_step_sim (ts ts' : TS.state) (tr : Events.trace)
    (amap : amap_t) (ms : @Symbolic.state mt lrc_tags unit) :
  TS.step cdeW ts tr ts' ->
  match_stW amap ts ms ->
  MDefs.state_fits ts ->
  (tr = E0 -> MDefs.state_fits ts') ->
  MDefs.binop_ok cdeW ts ->
  heap_inv (let '(tmem, _, _, _) := ts in tmem) (Symbolic.mem ms) ->
  mm_dsyncW amap ts ms ->
  exists amap' ms',
    plus mstep tt ms tr ms' /\
    match_stW amap' ts' ms' /\
    heap_inv (let '(tmem, _, _, _) := ts' in tmem) (Symbolic.mem ms') /\
    mm_dsyncW amap' ts' ms'.
Proof using All.
move=> Hstep.
case: Hstep.
-
  move=> mem regs pc tg c pct Hex Hcp /= Hm _ _ _ Hh Hdsy.
  have [ms' [Hs Hm' Hdm Hrgs Hmm]] := sim_nop NC Hbound Hsmall Hm Hex Hcp.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA.dinv_step_nop HMM Hex Hcp HI).
    * rewrite Hrgs Hmm.
      have [v [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      move: Evs => /= -[Evv]. subst v'.
      have [w [Ew Hle]] := Hnx isT.
      have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
      { by case: (pc) => [[c0 b0] o0]. }
      exact: (sync_pcmove Ec Ev Ew Hle HS).
-
  move=> mem regs pc tg c pct l Hex Hcp /= Hm _ _ _ Hh Hdsy.
  have [ms' [Hs Hm' Hdm Hrgs Hmm]] := sim_label NC Hbound Hsmall Hm Hex Hcp.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA.dinv_step_label HMM Hex Hcp HI).
    * rewrite Hrgs Hmm.
      have [v [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      move: Evs => /= -[Evv]. subst v'.
      have [w [Ew Hle]] := Hnx isT.
      have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
      { by case: (pc) => [[c0 b0] o0]. }
      exact: (sync_pcmove Ec Ev Ew Hle HS).
-
  move=> mem regs pc tg c pct r v Hex Hcp /= Hm _ _ _ Hh Hdsy.
  have [ms' [w [Hs Hm' Hdm Hv [Hrgs Hmm]]]] := sim_const NC Hbound HPB Hwfa Hsmall Himm_a Himm_b Hm Hex Hcp.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA.dinv_step_const HMM Hcst Hex Hcp HI).
    * rewrite Hrgs Hmm.
      exact: (sync_const HMM Hex Hv HS).
-
  move=> mem regs pc tg c pct r1 r2 Hex Hcp /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs _ _ _ _.
  have [ms' [w1 [ts1 [Hs Hm' Hdm Hlk [Hrgs Hmm]]]]] :=
    sim_mov NC Hbound Hsmall (Hself Hex) Hm Hex Hcp.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA2.dinv_step_mov HMM Hex Hcp HI).
    * rewrite Hrgs Hmm.
      have Hr12 := Hself Hex.
      have [v [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      have Honed : sv_one v = true ->
          reg_syncedW amap regs (Symbolic.regs ms) R_ONE.
      { move=> Hov.
        apply: (get_int_synced Hregs).
        exact: (MDisc.di_one HI Ev Hov). }
      have Hspd : sv_ph v = PProlA ->
          sv_ek v = true \/ sv_sig v <> [::] ->
          reg_syncedW amap regs (Symbolic.regs ms) R_SP.
      { move=> Ephv Hcond.
        have [_ [Hsig _]] := MDisc.di_prol HI Ev (or_introl Ephv).
        have Hekv : sv_ek v = true.
        { case: Hcond => [//|]. by rewrite Hsig. }
        have Hsp0 := MDisc.di_spprol HI Ev Ephv.
        have Hchain := MDisc.di_ek HI Ev Hekv.
        move: Hsp0 Hchain.
        case Ech: (chain) => [|A0 rest] //= Hsp0 Hnw0.
        rewrite Hnw0 in Hsp0.
        apply: (get_ptr_synced Hregs).
        exact: Hsp0. }
      rewrite setmC; last exact: (regkey_neq Hr12).
      exact: (sync_mov HMM Hex Ev Hr12 Hlk Honed Hspd HS).
-
  move=> mem regs pc tg c pct r1 r2 r3 op Hex Hcp Ht1 Ht2 /= Hm Hf Hf' Hbo Hh Hdsy.
  case: (Hm) => _ _ Hregs Hmem _ _ _.
  case: (Hdsy) => cur0 [chain0 [F0 [cs0 [HI0 HS0]]]].
  have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
  have Hsyngen := rtaint_AU_synced HI0 HS0 Hregs Ev.
  have [Hsync1 Hsync2] : reg_syncedW amap regs (Symbolic.regs ms) r1
                      /\ reg_syncedW amap regs (Symbolic.regs ms) r2.
  { have Hgen : forall w, vgeneric_binop v0 r1 r2 r3 = Some w ->
        reg_syncedW amap regs (Symbolic.regs ms) r1
        /\ reg_syncedW amap regs (Symbolic.regs ms) r2.
    { move=> w. rewrite /vgeneric_binop.
      case: (is_r r3 R_SP || is_r r3 R_RA) => //.
      case: (sv_pend v0) => //.
      case Egate: (t_eqb (rtaint v0 r1) AU && t_eqb (rtaint v0 r2) AU)
        => // _.
      case/andP: Egate => /t_eqb_eq Eau1 /t_eqb_eq Eau2.
      split.
      - exact: (Hsyngen _ Eau1).
      - exact: (Hsyngen _ Eau2). }
    have Hspone : is_r r1 R_SP = true -> is_r r2 R_ONE = true ->
        sv_one v0 = true -> sv_ph v0 = PBody ->
        reg_syncedW amap regs (Symbolic.regs ms) r1
        /\ reg_syncedW amap regs (Symbolic.regs ms) r2.
    { move=> E1 E2 Eone EphB.
      have Hnp1 : sv_ph v0 <> PProlA by rewrite EphB.
      have Hnp2 : sv_ph v0 <> PProlB by rewrite EphB.
      have [bcur [Hcur HbF]] := MDisc.di_body HI0 Ev Hnp1 Hnp2.
      have Hspv := MDisc.di_sp HI0 Ev EphB Hcur.
      rewrite (MDisc.is_r_eq E1) (MDisc.is_r_eq E2).
      split.
      - apply: (get_ptr_synced Hregs). exact: Hspv.
      - apply: (get_int_synced Hregs).
        exact: (MDisc.di_one HI0 Ev Eone). }
    clear Hex Hf' Hnx.
    move: Evs => /=.
    case: op => /=.
    -
      case EphB: (sv_ph v0) => //.
      case Egd: ([&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
                   & sv_one v0]).
      + case/and4P: Egd => E1 E2 E3 Eone.
        move=> _. exact: (Hspone E1 E2 Eone EphB).
      + move=> HG. exact: (Hgen _ HG).
    -
      case EphB: (sv_ph v0) => //.
      case Egd: ([&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
                   & sv_one v0]).
      + case/and4P: Egd => E1 E2 E3 Eone.
        move=> _. exact: (Hspone E1 E2 Eone EphB).
      + move=> HG. exact: (Hgen _ HG).
    -
      case EphB: (sv_ph v0) => // HG. exact: (Hgen _ HG).
    -
      case EphB: (sv_ph v0) => // HG. exact: (Hgen _ HG).
    -
      case EphB: (sv_ph v0) => // HG. exact: (Hgen _ HG). }
  clear Hsyngen Evs Hnx Ev v' v0 HI0 HS0 cs0 F0 chain0 cur0.
  have Hbo' := Hbo _ _ _ _ _ _ Hex.
  case: (Hf) => Hfregs _ _.
  have Hfit1 : MDefs.value_fits mem
                 (Transitional.val (Transitional.Register.get r1 regs)).
  { have := Hfregs r1. by rewrite get_value_val. }
  have Hfit2 : MDefs.value_fits mem
                 (Transitional.val (Transitional.Register.get r2 regs)).
  { have := Hfregs r2. by rewrite get_value_val. }
  have Hfres : MDefs.value_fits mem
                 (eval_binop op
                    (Transitional.val (Transitional.Register.get r1 regs))
                    (Transitional.val (Transitional.Register.get r2 regs))).
  { case: (Hf' (erefl _)) => Hfregs' _ _.
    have := Hfregs' r3.
    by rewrite /Transitional.Register.get_value /Transitional.Register.set
       setmE eqxx. }
  have Harith : forall w1 w2,
      vrel amap (Transitional.val (Transitional.Register.get r1 regs)) w1 ->
      vrel amap (Transitional.val (Transitional.Register.get r2 regs)) w2 ->
      vrel amap
        (eval_binop op
           (Transitional.val (Transitional.Register.get r1 regs))
           (Transitional.val (Transitional.Register.get r2 regs)))
        (binop_denote (binop_trans op) w1 w2).
  { move=> w1 w2 Hv1 Hv2.
    move: Hbo' Hfit1 Hfit2 Hfres Hv1 Hv2.
    case: op {Hex Hcp Ht1 Ht2 Hf'} => /=;
    case Ev1: (Transitional.val (Transitional.Register.get r1 regs))
      => [z1|p1|];
    case Ev2: (Transitional.val (Transitional.Register.get r2 regs))
      => [z2|p2|] //=;
    move=> Hbo' Hfit1 Hfit2 Hfres Hv1 Hv2; try exact: VRUndef.
    -
      apply: VRInt.
      apply: (wrepr_addw Hbound Hsmall Hfres).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv1).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv2).
    -
      case: p2 Ev2 Hv2 Hfit2 Hfres => [[c2 b2] o2] Ev2 Hv2 Hfit2 Hfres.
      have [a [Ha Hoff2 Ew2]] := vrel_ptr_inv Hbound HPB Hsmall Hv2.
      move: Ha Hoff2 Ew2 => /= Ha Hoff2 Ew2.
      have Hw1 := vrel_int_inv Hbound HPB Hsmall Hv1.
      case: Hfres => /= Hoffres _.
      apply: (@VRPtr _ _ _ _ _ a).
      + exact: Ha.
      + exact: Hoffres.
      + rewrite Ew2 addwC.
        apply: (won_addw_wrepr Hw1). by lia.
    -
      case: p1 Ev1 Hv1 Hfit1 Hfres => [[c1 b1] o1] Ev1 Hv1 Hfit1 Hfres.
      have [a [Ha Hoff1 Ew1]] := vrel_ptr_inv Hbound HPB Hsmall Hv1.
      move: Ha Hoff1 Ew1 => /= Ha Hoff1 Ew1.
      have Hw2 := vrel_int_inv Hbound HPB Hsmall Hv2.
      case: Hfres => /= Hoffres _.
      apply: (@VRPtr _ _ _ _ _ a).
      + exact: Ha.
      + exact: Hoffres.
      + rewrite Ew1.
        apply: (won_addw_wrepr Hw2). by lia.
    -
      apply: VRInt.
      apply: (wrepr_subw Hbound Hsmall Hfres).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv1).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv2).
    -
      case: p1 Ev1 Hv1 Hfit1 Hfres => [[c1 b1] o1] Ev1 Hv1 Hfit1 Hfres.
      have [a [Ha Hoff1 Ew1]] := vrel_ptr_inv Hbound HPB Hsmall Hv1.
      move: Ha Hoff1 Ew1 => /= Ha Hoff1 Ew1.
      have Hw2 := vrel_int_inv Hbound HPB Hsmall Hv2.
      case: Hfres => /= Hoffres _.
      apply: (@VRPtr _ _ _ _ _ a).
      + exact: Ha.
      + exact: Hoffres.
      + rewrite Ew1.
        apply: (won_subw_wrepr Hw2). by lia.
    -
      case: p1 Ev1 Hv1 Hfit1 Hfres => [[c1 b1] o1] Ev1 Hv1 Hfit1 Hfres.
      case: p2 Ev2 Hv2 Hfit2 Hfres => [[c2 b2] o2] Ev2 Hv2 Hfit2 Hfres.
      case: ifP Hfres => [Hcb|_] Hfres; last exact: VRUndef.
      move: Hcb => /andP[/PeanoNat.Nat.eqb_spec Ec /PeanoNat.Nat.eqb_spec Eb].
      subst c2 b2.
      have [a1 [Ha1 Hoff1 Ew1]] := vrel_ptr_inv Hbound HPB Hsmall Hv1.
      have [a2 [Ha2 Hoff2 Ew2]] := vrel_ptr_inv Hbound HPB Hsmall Hv2.
      move: Ha1 Hoff1 Ew1 Ha2 Hoff2 Ew2 => /= Ha1 Hoff1 Ew1 Ha2 Hoff2 Ew2.
      have Ea : a2 = a1.
      { move: Ha2. rewrite Ha1. by case. }
      subst a2.
      case: (Hfit1) => /= _ [cm [blk [Hcm [Hblk Hsz1]]]].
      case: (Hfit2) => /= _ [cm' [blk' [Hcm' [Hblk' Hsz2]]]].
      move: Hcm'; rewrite Hcm => -[?]; subst cm'.
      move: Hblk'; rewrite Hblk => -[?]; subst blk'.
      have Hbs : block_size mem c1 b1 = Some (size blk).
      { by rewrite /block_size Hcm Hblk. }
      have Hab := aok_bound (mj_amap Hmem) Ha1 Hbs.
      apply: VRInt.
      rewrite Ew1 Ew2.
      apply: won_subw_won.
      + by lia.
      + by lia.
      + exact: Hfres.
      + by lia.
    -
      apply: VRInt.
      apply: (wrepr_mulw Hbound Hsmall Hfres).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv1).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv2).
    -
      apply: VRInt.
      apply: (wrepr_eqw Hbound Hsmall Hfit1 Hfit2).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv1).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv2).
    -
      case: p1 Ev1 Hv1 Hfit1 Hbo' Hfres
        => [[c1 b1] o1] Ev1 Hv1 Hfit1 Hbo' Hfres.
      case: p2 Ev2 Hv2 Hfit2 Hbo' Hfres
        => [[c2 b2] o2] Ev2 Hv2 Hfit2 Hbo' Hfres.
      case: Hbo' => /= Ec Eb [cm [blk [Hcm [Hblk Hs1 Hs2]]]].
      subst c2 b2.
      have [a1 [Ha1 Hoff1 Ew1]] := vrel_ptr_inv Hbound HPB Hsmall Hv1.
      have [a2 [Ha2 Hoff2 Ew2]] := vrel_ptr_inv Hbound HPB Hsmall Hv2.
      move: Ha1 Hoff1 Ew1 Ha2 Hoff2 Ew2 => /= Ha1 Hoff1 Ew1 Ha2 Hoff2 Ew2.
      have Ea : a2 = a1.
      { move: Ha2. rewrite Ha1. by case. }
      subst a2.
      have Hbs : block_size mem c1 b1 = Some (size blk).
      { by rewrite /block_size Hcm Hblk. }
      have Hab := aok_bound (mj_amap Hmem) Ha1 Hbs.
      rewrite /Pointer.eq /= !PeanoNat.Nat.eqb_refl /=.
      have Ebb : BinInt.Z.eqb o1 o2
                 = (BinInt.Z.to_nat o1 == BinInt.Z.to_nat o2).
      { case E1: (BinInt.Z.eqb o1 o2); case E2: (_ == _) => //.
        - move/BinInt.Z.eqb_eq: E1 => E1. move/eqP: E2 => E2. by lia.
        - move/BinInt.Z.eqb_neq: E1 => E1. move/eqP: E2 => E2. by lia. }
      rewrite Ebb Ew1 Ew2.
      apply: VRInt.
      apply: wrepr_eq_flat; by lia.
    -
      apply: VRInt.
      apply: (wrepr_lequw Hfit1 Hfit2).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv1).
      + exact: (vrel_int_inv Hbound HPB Hsmall Hv2).
    (* Leq-Ptr-Ptr is fit-excluded ([binop_ok] arm = False) and is
       closed by the case chain itself *) }
  have [ms' [w [Hs Hm' Hdm Hv [Hrgs Hmm]]]] :=
    sim_binop NC Hbound Hsmall Hm Hsync1 Hsync2 Hex Hcp Ht1 Ht2 Harith.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepB.dinv_step_binop HMM Hex Hcp Ht1 Ht2 HI).
    * rewrite Hrgs Hmm.
      exact: (sync_binop HMM Hex Hv HS).
-
  move=> mem mem' regs pc tg c pct r1 r2 ptr v Hex Hcp Ht1 Hv1 Hcomp
         Hld Hst /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs Hmem _ _ _.
  have Hsync1 := get_ptr_synced Hregs Hv1.
  have [ms' [a1 [wmc [mtg [Hs Hm' Hdm [Ha Hmc] Harm]]]]] :=
    sim_load NC Hbound HPB Hsmall Hm Hsync1 Hex Hcp Ht1 Hv1 Hcomp Hld Hst.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_store Hst Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepC.dinv_step_load HMM Hex Hcp Ht1 Hv1 Hcomp Hld
                Hst HI).
    * have Haok := mj_amap Hmem.
      have Ecc : Pointer.component pc = c.
      { by case: Hex => C_code [E _]. }
      have Ecp : Pointer.component ptr = Pointer.component pc.
      { by rewrite Hcomp Ecc. }
      rewrite -Hcomp in Hst.
      have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      move: Evs => /=.
      case Eph: (sv_ph v0) => //.
      --
         case E1sp: (is_r r1 R_SP).
         ++
            move=> _.
            have Hnp1 : sv_ph v0 <> PProlA by rewrite Eph.
            have Hnp2 : sv_ph v0 <> PProlB by rewrite Eph.
            have [bcur [Hcur HbF]] := MDisc.di_body HI Ev Hnp1 Hnp2.
            have Hsp := MDisc.di_sp HI Ev Eph Hcur.
            have Er1 : r1 = R_SP := MDisc.is_r_eq E1sp.
            have Eptr : ptr = (Pointer.component pc, bcur,
                               BinInt.Z.of_nat (size (sv_sig v0))).
            { move: Hv1. rewrite Er1 Hsp. by move=> [->]. }
            have Hchdis : forall i A, nth_error chain i = Some A ->
                (MDisc.a_comp A == Pointer.component pc) &&
                (MDisc.a_blk A == bcur) = false.
            { move=> i A HA.
              apply/negbTE/negP => /andP [/eqP EcA /eqP EbA].
              exact: (MDisc.di_dist HI HA Hcur EcA EbA). }
            case: Harm => [[Hpair [Hrgs' Hmm']]|[Hclob [Hrgs' Hmm']]].
            ** rewrite Hrgs' Hmm' -Ecp.
               exact: (sync_load_pop HMM Hex Haok E1sp Ev Hcur HbF
                         Eptr Hchdis Hld Hst Ha Hmc HS).
            ** rewrite Hrgs' Hmm' -Ecp.
               exact: (sync_load_pop_clob HMM Hex Haok E1sp Ev Hcur
                         HbF Eptr Hchdis Hld Hst Ha Hmc Hclob HS).
         ++
            case Epd0: (sv_pend v0) => //.
            case Etr1: (rtaint v0 r1) => //.
            **
               move=> _.
               have E1ra : is_r r1 R_RA = false.
               { by move: Etr1; rewrite /rtaint E1sp;
                    case: (is_r r1 R_RA). }
               have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
               rewrite Etr1 /= in Hrc.
               have Eptru : ptr = (Pointer.component pc, 1, Z0).
               { move: Hv1. rewrite Hrc. by move=> [->]. }
               have [F0 F1] := MDisc.di_f01 HI (Pointer.component pc).
               have Hbnf : (Pointer.block ptr
                            \in F (Pointer.component ptr)) = false.
               { rewrite Eptru. exact: F1. }
               case: Harm => [[Hpair [Hrgs' Hmm']]
                             |[Hclob [Hrgs' Hmm']]]; last first.
               { exfalso.
                 have Hcs : cell_synced L P C pra prb PB PI amap mem (Symbolic.mem ms)
                     (Pointer.component ptr) (Pointer.block ptr)
                     (BinInt.Z.to_nat (Pointer.offset ptr)).
                 { exact: (sy_mem HS Hbnf). }
                 have Hpair2 : cellrel (cmapW L P C pra prb PB PI) amap v (Atom wmc mtg).
                 { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
                   exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha Hmc). }
                 exact: (cellrel_clob_clash Hpair2 Hclob). }
               rewrite Hrgs' Hmm' -Ecp.
               exact: (sync_load_user HMM Hex Haok E1sp Hbnf Hld Hst
                         Ha Hmc HS).
            **
               move=> _.
               have E1ra : is_r r1 R_RA = false.
               { by move: Etr1; rewrite /rtaint E1sp;
                    case: (is_r r1 R_RA). }
               have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
               rewrite Etr1 /= in Hrc.
               have Eptru : ptr = (Pointer.component pc, 1, BinInt.Z.one).
               { move: Hv1. rewrite Hrc. by move=> [->]. }
               have [F0 F1] := MDisc.di_f01 HI (Pointer.component pc).
               have Hbnf : (Pointer.block ptr
                            \in F (Pointer.component ptr)) = false.
               { rewrite Eptru. exact: F1. }
               case: Harm => [[Hpair [Hrgs' Hmm']]
                             |[Hclob [Hrgs' Hmm']]]; last first.
               { exfalso.
                 have Hcs : cell_synced L P C pra prb PB PI amap mem (Symbolic.mem ms)
                     (Pointer.component ptr) (Pointer.block ptr)
                     (BinInt.Z.to_nat (Pointer.offset ptr)).
                 { exact: (sy_mem HS Hbnf). }
                 have Hpair2 : cellrel (cmapW L P C pra prb PB PI) amap v (Atom wmc mtg).
                 { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
                   exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha Hmc). }
                 exact: (cellrel_clob_clash Hpair2 Hclob). }
               rewrite Hrgs' Hmm' -Ecp.
               exact: (sync_load_user HMM Hex Haok E1sp Hbnf Hld Hst
                         Ha Hmc HS).
            **
               move=> _.
               have E1ra : is_r r1 R_RA = false.
               { by move: Etr1; rewrite /rtaint E1sp;
                    case: (is_r r1 R_RA). }
               have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
               rewrite Etr1 /= in Hrc.
               have [HbFp Hb1p Hvb] := Hrc ptr Hv1.
               case: Harm => [[Hpair [Hrgs' Hmm']]
                             |[Hclob [Hrgs' Hmm']]]; last first.
               { exfalso.
                 have Hcs : cell_synced L P C pra prb PB PI amap mem (Symbolic.mem ms)
                     (Pointer.component ptr) (Pointer.block ptr)
                     (BinInt.Z.to_nat (Pointer.offset ptr)).
                 { exact: (sy_mem HS HbFp). }
                 have Hpair2 : cellrel (cmapW L P C pra prb PB PI) amap v (Atom wmc mtg).
                 { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
                   exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha Hmc). }
                 exact: (cellrel_clob_clash Hpair2 Hclob). }
               rewrite Hrgs' Hmm' -Ecp.
               exact: (sync_load_user HMM Hex Haok E1sp HbFp Hld Hst
                         Ha Hmc HS).
      --
         case Epd0: (sv_pend v0) => //.
         case Eg: ([&& t_eqb (rtaint v0 r1) AScr, is_r r2 R_SP
                   & ~~ nocra (sv_sig v0)]) => // _.
         case/and3P: Eg => /t_eqb_eq Etr1 E2sp Hnc.
         have E1sp : is_r r1 R_SP = false.
         { case E: (is_r r1 R_SP) => //.
           move: Etr1. by rewrite /rtaint E. }
         have E1ra : is_r r1 R_RA = false.
         { case E: (is_r r1 R_RA) => //.
           move: Etr1. by rewrite /rtaint E1sp E. }
         have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
         rewrite Etr1 /= in Hrc.
         have Eptru : ptr = (Pointer.component pc, 1, Z0).
         { move: Hv1. rewrite Hrc. by move=> [->]. }
         have [F0 F1] := MDisc.di_f01 HI (Pointer.component pc).
         have Hbnf : (Pointer.block ptr
                      \in F (Pointer.component ptr)) = false.
         { rewrite Eptru. exact: F1. }
         case: Harm => [[Hpair [Hrgs' Hmm']]
                       |[Hclob [Hrgs' Hmm']]]; last first.
         { exfalso.
           have Hcs : cell_synced L P C pra prb PB PI amap mem (Symbolic.mem ms)
               (Pointer.component ptr) (Pointer.block ptr)
               (BinInt.Z.to_nat (Pointer.offset ptr)).
           { exact: (sy_mem HS Hbnf). }
           have Hpair2 : cellrel (cmapW L P C pra prb PB PI) amap v (Atom wmc mtg).
           { have [cm [blk [Hcm Hblk Hnth]]] := load_shape Hld.
             exact: (Hcs _ _ _ _ _ Hcm Hblk Hnth Ha Hmc). }
           exact: (cellrel_clob_clash Hpair2 Hclob). }
         rewrite Hrgs' Hmm' -Ecp.
         exact: (sync_load_user HMM Hex Haok E1sp Hbnf Hld Hst
                   Ha Hmc HS).
-
  move=> mem mem' regs pc tg c pct ptr r1 r2 vt Hex Hcp Ht1 Hv1 Hcomp
         Hgt Hst /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs Hmem _ _ _.
  have Hsync1 := get_ptr_synced Hregs Hv1.
  have [ms' [a1 [w2 [ts2 [Hs Hm' Hdm [Ha Hr2m] [[Hrgs' Hmm'] Harm2]]]]]] :=
    sim_store NC Hbound HPB Hsmall Hm Hsync1 Hex Hcp Ht1 Hv1
      Hcomp Hgt Hst.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_store Hst Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepC.dinv_step_store HMM Hex Hcp Ht1 Hv1 Hcomp Hgt
                Hst HI).
    * have Haok := mj_amap Hmem.
      have Ecc : Pointer.component pc = c.
      { by case: Hex => C_code [E _]. }
      have Ecp : Pointer.component ptr = Pointer.component pc.
      { by rewrite Hcomp Ecc. }
      have Evt : Transitional.tvtag (Transitional.Register.get r2 regs)
                 = vt.
      { move: Hgt.
        rewrite /Transitional.Register.get_tag /Transitional.Register.get.
        by case: (getm regs _) => [tv|] // [<-]. }
      rewrite -Hcomp in Hst.
      case: Harm2 => [Ets2|[Ets2c Evto Hu2]].
      {
      rewrite {}Ets2 in Hr2m Hrgs' Hmm'.
      have Hsync2 : reg_syncedW amap regs (Symbolic.regs ms) r2.
      { case: (Hregs r2) => [//|[ra [Hra Hu Hta]]].
        exfalso.
        move: Hra; rewrite Hr2m => -[Era]. subst ra.
        move: Evt. rewrite Hu /= => Evt2.
        move: Hta. rewrite /= -Evt2. by []. }
      have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      move: Evs => /=.
      case Eph: (sv_ph v0) => //.
      case Epd0: (sv_pend v0) => //.
      case E1sp: (is_r r1 R_SP).
      --
         move=> _.
         have Hnp1 : sv_ph v0 <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v0 <> PProlB by rewrite Eph.
         have [bcur [Hcur HbF]] := MDisc.di_body HI Ev Hnp1 Hnp2.
         have Hsp := MDisc.di_sp HI Ev Eph Hcur.
         have Er1 : r1 = R_SP := MDisc.is_r_eq E1sp.
         have Eptr : ptr = (Pointer.component pc, bcur,
                            BinInt.Z.of_nat (size (sv_sig v0))).
         { move: Hv1. rewrite Er1 Hsp. by move=> [->]. }
         rewrite Hrgs' Hmm' -Ecp.
         exact: (sync_store_push HMM Hex Haok E1sp Ev Hcur Eptr Evt
                   Hst Ha Hr2m Hsync2 HS).
      --
         case Etr1: (rtaint v0 r1) => //.
         ++
            move=> _.
            have E1ra : is_r r1 R_RA = false.
            { by move: Etr1; rewrite /rtaint E1sp;
                 case: (is_r r1 R_RA). }
            have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
            rewrite Etr1 /= in Hrc.
            have Eptru : ptr = (Pointer.component pc, 1, Z0).
            { move: Hv1. rewrite Hrc. by move=> [->]. }
            have [F0 F1] := MDisc.di_f01 HI (Pointer.component pc).
            have Hbnf : (Pointer.block ptr
                         \in F (Pointer.component ptr)) = false.
            { rewrite Eptru. exact: F1. }
            rewrite Hrgs' Hmm' -Ecp.
            exact: (sync_store_user HMM Hex Haok E1sp Hbnf Evt Hst Ha
                      Hr2m Hsync2 HS).
         ++
            move=> _.
            have E1ra : is_r r1 R_RA = false.
            { by move: Etr1; rewrite /rtaint E1sp;
                 case: (is_r r1 R_RA). }
            have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
            rewrite Etr1 /= in Hrc.
            have Eptru : ptr = (Pointer.component pc, 1, BinInt.Z.one).
            { move: Hv1. rewrite Hrc. by move=> [->]. }
            have [F0 F1] := MDisc.di_f01 HI (Pointer.component pc).
            have Hbnf : (Pointer.block ptr
                         \in F (Pointer.component ptr)) = false.
            { rewrite Eptru. exact: F1. }
            rewrite Hrgs' Hmm' -Ecp.
            exact: (sync_store_user HMM Hex Haok E1sp Hbnf Evt Hst Ha
                      Hr2m Hsync2 HS).
         ++
            move=> _.
            have E1ra : is_r r1 R_RA = false.
            { by move: Etr1; rewrite /rtaint E1sp;
                 case: (is_r r1 R_RA). }
            have Hrc := MDisc.rtaint_claim HI Ev E1sp E1ra.
            rewrite Etr1 /= in Hrc.
            have [HbFp Hb1p Hvb] := Hrc ptr Hv1.
            rewrite Hrgs' Hmm' -Ecp.
            exact: (sync_store_user HMM Hex Haok E1sp HbFp Evt Hst Ha
                      Hr2m Hsync2 HS). }
      have Hclash2 : reg_syncedW amap regs (Symbolic.regs ms) r2 -> False.
      { move=> [ra [Hra _ Hta]].
        move: Hra; rewrite Hr2m => -[Era]. subst ra.
        move: Hta. rewrite /= Hu2 Ets2c. by []. }
      have Hr2m' : getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat r2))
        = Some (Atom w2 Invalidated).
      { by rewrite Hr2m Ets2c. }
      have Hrgs'' : Symbolic.regs ms'
          = setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r2))
              (Atom w2 Invalidated).
      { by rewrite Hrgs' Ets2c. }
      have Hmm'' : Symbolic.mem ms'
          = setm (Symbolic.mem ms)
              (@word_of_nat (word_size mt)
                 (a1 + BinInt.Z.to_nat (Pointer.offset ptr)))
              (Atom w2 (MTag Invalidated (Pointer.component pc) None
                          false)).
      { by rewrite Hmm' Ets2c. }
      have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      have HrefAU : rtaint v0 r2 = AU -> False.
      { move=> Hau. exact: (Hclash2 (rtaint_AU_synced HI HS Hregs Ev Hau)). }
      move: Evs => /=.
      case Eph: (sv_ph v0) => //.
      case Epd0: (sv_pend v0) => //.
      case E1sp: (is_r r1 R_SP).
      {
        case Epk: (pushclass v0 r2) => [k|] // _.
        have Hnp1 : sv_ph v0 <> PProlA by rewrite Eph.
        have Hnp2 : sv_ph v0 <> PProlB by rewrite Eph.
        have [bcur [Hcur HbF]] := MDisc.di_body HI Ev Hnp1 Hnp2.
        have Hsp := MDisc.di_sp HI Ev Eph Hcur.
        have Er1 : r1 = R_SP := MDisc.is_r_eq E1sp.
        have Eptr : ptr = (Pointer.component pc, bcur,
                           BinInt.Z.of_nat (size (sv_sig v0))).
        { move: Hv1. rewrite Er1 Hsp. by move=> [->]. }
        have Hchdis : forall i A, nth_error chain i = Some A ->
            (MDisc.a_comp A == Pointer.component pc) &&
            (MDisc.a_blk A == bcur) = false.
        { move=> i A HA.
          apply/negbTE/negP => /andP [/eqP EcA /eqP EbA].
          exact: (MDisc.di_dist HI HA Hcur EcA EbA). }
        have Hclass : [\/ r2 = R_RA,
            r2 = R_AUX1 /\ sv_sig v0 = [::]
          | r2 = R_ARG /\ parg_of MM chain = false].
        { move: Epk. rewrite /pushclass.
          case E2ra: (is_r r2 R_RA).
          - move=> _. apply: Or31. exact: MDisc.is_r_eq E2ra.
          - case E2sp: (is_r r2 R_SP) => //.
            case Ecsp: ([&& _, _ & _]).
            + move=> _.
              case/and3P: Ecsp => Eaux1 /t_eqb_eq Easp /orP Esg01.
              have Er2 : r2 = R_AUX1 := MDisc.is_r_eq Eaux1.
              subst r2.
              case: Esg01 => /cseq_eqb_eq E3.
              * apply: Or32. by split.
              * exfalso. apply: Hclash2.
                apply: (sy_a1sp HS Ev Easp).
                right. by rewrite E3.
            + case E2arg: (is_r r2 R_ARG).
              * have Er2 : r2 = R_ARG := MDisc.is_r_eq E2arg.
                subst r2.
                case Earg: (sv_arg v0).
                -- move=> _.
                   exfalso. apply: Hclash2.
                   exact: (sy_arg HS Ev Earg).
                -- case Enca: (nocarg (sv_sig v0)) => // _.
                   case Epg: (parg_of MM chain).
                   ++ exfalso. apply: Hclash2.
                      apply: (sy_argp HS Ev Epg).
                      rewrite /cargfree Epd0 /=.
                      move: Enca. rewrite /nocarg => Enca.
                      by rewrite Enca.
                   ++ apply: Or33. by split.
              * case Eau2: (rtaint v0 r2) => //. }
        rewrite Hrgs'' Hmm'' -Ecp.
        exact: (sync_store_push_clob HMM Hex Haok E1sp Ev Hcur HbF
                  Eptr Hchdis Hclass Evto Hu2 Hst Ha Hr2m' HS). }
      case Etr1: (rtaint v0 r1) => //.
      {
        case E2spx: (is_r r2 R_SP).
        - move=> _.
          have Hnp1 : sv_ph v0 <> PProlA by rewrite Eph.
          have Hnp2 : sv_ph v0 <> PProlB by rewrite Eph.
          have [bcur [Hcur HbF]] := MDisc.di_body HI Ev Hnp1 Hnp2.
          have Hspv := MDisc.di_sp HI Ev Eph Hcur.
          have Er2 : r2 = R_SP := MDisc.is_r_eq E2spx.
          subst r2.
          move: Hspv. rewrite Hu2. by [].
        - case Erst: (_ && _) => // _.
          case/andP: Erst => /t_eqb_eq Er2t /cseq_eqb_eq Esg1.
          exfalso.
          move: Er2t. rewrite /rtaint E2spx.
          case E2rax: (is_r r2 R_RA) => //.
          case E2a1x: (is_r r2 R_AUX1).
          + move=> Ea1.
            have Er2 : r2 = R_AUX1 := MDisc.is_r_eq E2a1x. subst r2.
            apply: Hclash2.
            apply: (sy_a1sp HS Ev Ea1).
            right. by rewrite Esg1.
          + case E2a2x: (is_r r2 R_AUX2).
            * move=> Ea2.
              have Er2 : r2 = R_AUX2 := MDisc.is_r_eq E2a2x. subst r2.
              apply: Hclash2.
              apply: (sy_a2sp HS Ev Ea2).
              right. by rewrite Esg1.
            * case E2onex: (is_r r2 R_ONE).
              -- by case: (sv_one v0).
              -- case E2argx: (is_r r2 R_ARG).
                 ++ by case: (sv_arg v0).
                 ++ by []. }
      {
        case Eau2: (t_eqb (rtaint v0 r2) AU) => // _.
        exfalso. exact: (HrefAU (t_eqb_eq Eau2)). }
      {
        case Eau2: (t_eqb (rtaint v0 r2) AU) => // _.
        exfalso. exact: (HrefAU (t_eqb_eq Eau2)). }
-
  move=> mem regs pc tg c pct pc' l Hex Hfind Hcpj /= Hm _ _ _ Hh Hdsy.
  have [i3 [tg3 Hex3]] := Hsucc_jal Hex.
  have [ms' [ra_me [Hs Hm' Hdm Hrgs Hmm]]] :=
    sim_jal NC Hbound HPB Hwfa Hwfb Hlinkable Hsmall Hlab_a Hlab_b
      Hcomp_a Hcomp_b Huniq_a Huniq_b Hm Hex Hfind Hcpj Hex3 (HlL_jal Hex Hfind).
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    have [b [cvnew [Hcur HI']]] :=
      MDiscStepC.dinv_step_jal HMM HuniqL Hex Hfind Hcpj HI.
    exists None,
      ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
          MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |} :: chain),
      F, cvnew.
    split.
    * exact: HI'.
    * rewrite Hrgs Hmm.
      apply: sync_jal.
      -- exact: HMM.
      -- exact: HuniqL.
      -- exact: Hex.
      -- exact: Hfind.
      -- exact: Hcur.
      -- exact: HS.
-
  move=> mem regs pc tg c pct pc' r Hex Hget Hcomp Hcpj /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs _ _ _ _.
  have Hsync : reg_syncedW amap regs (Symbolic.regs ms) r.
  { apply: mregs_rel_synced Hregs _ => E.
    by rewrite E in Hget. }
  have [ms' [Hs Hm' Hdm Hrgs Hmm]] :=
    sim_jump NC Hbound HPB Hsmall Hm Hsync Hex Hget Hcomp Hcpj.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    have [A [chain' [Echain Hnw Epc' HI']]] :=
      MDiscStepC.dinv_step_jump HMM Hex Hget Hcomp Hcpj HI.
    exists (Some (MDisc.a_blk A)), chain', F, (MDisc.a_scr A).
    split.
    * exact: HI'.
    * rewrite Hrgs Hmm.
      rewrite Echain in HS.
      have HAh : nth_error chain 0 = Some A by rewrite Echain.
      have [W1 W2 W3 W4 W5] := MDisc.di_chain HI HAh.
      case: W5 => Ecomp Hnocra Hek5 Hpin.
      case: W2 => [[Hor Hpd Ha1 Ha2 Hsc1] Hone1].
      have [v [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      move: Evs => /=.
      case Eph: (sv_ph v) => //.
      case Epd0: (sv_pend v) => //.
      case Eg0: ([&& sv_one v, cseq_eqb (sv_sig v) [::]
                 & sv_ek v || match sv_sc v with
                              | SCrest | SCnone => true
                              | _ => false
                              end]) => // _.
      case/and3P: Eg0 => Eon /cseq_eqb_eq Esg0 _.
      have Hcf : cargfree v = true.
      { by rewrite /cargfree Esg0 Epd0. }
      apply: sync_jump.
      -- exact: Hex.
      -- exact: Epc'.
      -- exact: (esym Ecomp).
      -- exact: Ha1.
      -- exact: Ha2.
      -- exact: Hpd.
      -- move=> Harg.
         exact: (sy_argp HS Ev Harg Hcf).
      -- move=> Hpg Hcf'.
         exfalso.
         case Hek: (sv_ek (MDisc.asv MM A)).
         ++ have [_ _ R4 _] := MDisc.di_chain2 HI HAh.
            have HB := R4 Hek.
            have Hnn := Hnocra Hnw.
            have H1 := MDisc.bodycarg_nocra Hnn HB.
            move: Hcf'. rewrite /cargfree (nth_error_hasCArg H1).
            by [].
         ++ have [_ R3 _ _] := MDisc.di_chain2 HI HAh.
            have Hhead := R3 Hek.
            move: Hhead Hpg. rewrite Echain /= drop0.
            case Ech': (chain') => [|B rest] //= Hwin Hpg.
            have HBn : nth_error chain 1 = Some B.
            { by rewrite Echain Ech'. }
            have [R1 _ _ _] := MDisc.di_chain2 HI HBn.
            have Hph : sv_ph (MDisc.asv MM B) = PPost.
            { move: Hwin. rewrite /MDisc.in_window.
              by case: (sv_ph (MDisc.asv MM B)). }
            have Harg0 := R1 Hph.
            by rewrite Harg0 in Hpg.
      -- exact: HS.
-
  move=> mem regs pc tg c pct pc' r rcomval Hex Hv Hcomp Hpct Hrcom
         Hcpj /= Hm _ _ _ Hh Hdsy.
  have Er := Hjra Hex. subst r.
  have [Ec _ _] := executing_props Hex. subst c.
  case: (Hm) => _ _ Hregs _ _ _ _.
  case Etag: (Transitional.tvtag
                (Transitional.Register.get R_RA regs)) Hpct => [n| | |] //=.
  move=> Hpct.
  have Epct : pct = Transitional.Level n.+1 by case: Hpct.
  subst pct.
  have Hget : Transitional.Register.get R_RA regs
              = Transitional.MVal (Ret n) (Ptr pc').
  { move: Etag Hv.
    case: (Transitional.Register.get R_RA regs) => tg0 v0 /= -> ->.
    by []. }
  have HsyncRA : reg_syncedW amap regs (Symbolic.regs ms) R_RA.
  { apply: mregs_rel_synced Hregs _ => E. by rewrite E in Hget. }
  have HsyncCOM := get_int_synced Hregs Hrcom.
  have Hother : Transitional.tvtag (Transitional.Register.get R_COM regs)
                = Other.
  { case: (Hdsy) => cur0 [chain0 [F0 [cs0 [HI0 _]]]].
    have HCOM : R_COM <> R_RA. { move=> E. discriminate E. }
    exact: (MDisc.di_rtag HI0 HCOM). }
  have [ms' [Hs Hm' Hdm Hmm]] :=
    sim_ret NC Hbound HPB Hwfa Hwfb Hlinkable Hsmall Hm HsyncRA HsyncCOM
      Hex Hget Hcomp (erefl _) Hother Hrcom Hcpj.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    have Hpct2 : Some (Transitional.Level n.+1)
                 = Transitional.value_to_pc_tag
                     (Transitional.tvtag
                        (Transitional.Register.get R_RA regs)).
    { by rewrite Etag. }
    have [A [chain' [Echain Hwin Epc' HI']]] :=
      MDiscStepC.dinv_step_jumpret HMM Hex Hv Hcomp Hpct2 Hrcom Hcpj HI.
    exists (Some (MDisc.a_blk A)), chain', F, (MDisc.a_scr A).
    split.
    * exact: HI'.
    * rewrite Hmm.
      rewrite Echain in HS.
      have HAh : nth_error chain 0 = Some A by rewrite Echain.
      have [W1 W2 W3 W4 W5] := MDisc.di_chain HI HAh.
      case: W5 => Ecomp Hnocra Hek5 Hpin.
      case: W2 => [[Hor Hpd Ha1 Ha2 Hsc1] Hone1].
      have Hph : sv_ph (MDisc.asv MM A) = PPost.
      { move: Hwin. rewrite /MDisc.in_window.
        by case: (sv_ph (MDisc.asv MM A)). }
      have [R1 _ _ R4A] := MDisc.di_chain2 HI HAh.
      have HargA := R1 Hph.
      have Hcom' : reg_syncedW amap (TS.invalidate_ret regs)
                     (Symbolic.regs ms') R_COM.
      { case: (Hm') => _ _ Hregs' _ _ _ _.
        apply: mregs_rel_synced Hregs' _.
        have HCR : R_COM <> R_RA by [].
        rewrite /TS.invalidate_ret (MDisc.tget_set_neq _ _ _ HCR)
                MDisc.tget_invalidate_com.
        move=> E.
        have := f_equal Transitional.val E.
        rewrite Hrcom /=.
        by []. }
      apply: sync_jumpret.
      -- exact: Hex.
      -- exact: Epc'.
      -- exact: (esym Ecomp).
      -- exact: Ha1.
      -- exact: Ha2.
      -- exact: Hpd.
      -- exact: HargA.
      -- move=> Hpg.
         case Hek: (sv_ek (MDisc.asv MM A)).
         ++ have H1 := R4A Hwin Hek.
            by rewrite /cargfree (nth_error_hasCArg H1).
         ++ exfalso.
            have [_ R3 _ _] := MDisc.di_chain2 HI HAh.
            have Hhead := R3 Hek.
            move: Hhead Hpg. rewrite Echain /= drop0.
            case Ech': (chain') => [|B rest] //= Hwin2 Hpg.
            have HBn : nth_error chain 1 = Some B.
            { by rewrite Echain Ech'. }
            have [R1B _ _ _] := MDisc.di_chain2 HI HBn.
            have HphB : sv_ph (MDisc.asv MM B) = PPost.
            { move: Hwin2. rewrite /MDisc.in_window.
              by case: (sv_ph (MDisc.asv MM B)). }
            have Harg0 := R1B HphB.
            by rewrite Harg0 in Hpg.
      -- exact: Hcom'.
      -- exact: HS.
-
  move=> mem regs pc tg c pct pc' r l v Hex Hcp Ht Hv Hnz Hfind
         Hcpj /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs _ _ _ _.
  have Hsync := get_int_synced Hregs Hv.
  have [ms' [Hs Hm' Hdm Hrgs Hmm]] :=
    sim_bnzNZ NC Hbound HPB Hwfa Hwfb Hlinkable Hsmall Hlab_a Hlab_b
      Hcomp_a Hcomp_b Huniq_a Huniq_b Hm Hsync Hex Ht Hv Hnz Hfind Hcpj
      (Hbf Hex Hfind) (HlL_bnz Hex Hfind).
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA2.dinv_step_bnznz HMM HuniqL Hex Hcp Ht Hv Hnz
                Hfind Hcpj HI).
    * rewrite Hrgs Hmm.
      have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      have Evv : v' = v0.
      { move: Evs => /=.
        by case: (sv_ph v0) => //; case: (sv_pend v0) => // -[]. }
      subst v'.
      have [Ec' [w [Ew Hle]]] := MDisc.bnz_target HMM HuniqL Hex Ev Hfind.
      have Ecc : Pointer.component pc = c.
      { by case: Hex => C_code [E _]. }
      rewrite -Ecc in Ec'.
      exact: (sync_pcmove Ec' Ev Ew Hle HS).
-
  move=> mem regs pc tg c pct r l Hex Hcp Ht Hv /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs _ _ _ _.
  have Hsync := get_int_synced Hregs Hv.
  have [ms' [Hs Hm' Hdm Hrgs Hmm]] :=
    sim_bnzZ NC Hbound HPB Hsmall Hm Hsync Hex Hcp Ht Hv.
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    exists cur, chain, F, cs. split.
    * exact: (MDiscStepA2.dinv_step_bnzz HMM Hex Hcp Ht Hv HI).
    * rewrite Hrgs Hmm.
      have [v0 [v' [Ev Evs Hnx]]] := MDisc.exec_sv HMM Hex.
      have Evv : v' = v0.
      { move: Evs => /=.
        by case: (sv_ph v0) => //; case: (sv_pend v0) => // -[]. }
      subst v'.
      have [w [Ew Hle]] := Hnx isT.
      have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
      { by case: (pc) => [[c0 b0] o0]. }
      exact: (sync_pcmove Ec Ev Ew Hle HS).
-
  move=> mem mem' regs pc tg c pct rsize rptr zsz ptr Hex Hcp Ht Hv Hpos
         Hal /= Hm Hf Hf' _ Hh Hdsy.
  case: (Hm) => _ _ Hregs Hmem _ _ _.
  have [Ec _ _] := executing_props Hex. subst c.
  have Hsyncr := get_int_synced Hregs Hv.
  have Hc1 := Hc1s Hex.
  move: (Hal); rewrite /Transitional.Memory.alloc.
  case Hcm: (mem (Pointer.component pc)) => [cm|] //=.
  move=> [Etm Etp].
  have Hfresh : Transitional.Memory.content cm
                  (Transitional.Memory.nextblock cm) = None.
  { case E: (Transitional.Memory.content cm
               (Transitional.Memory.nextblock cm)) => [blk|] //.
    have Hlt := aok_next (mj_amap Hmem) Hcm E.
    by rewrite ltnn in Hlt. }
  set CHUNK := List.repeat (Transitional.tUndef,
                  def_mem_tag (Pointer.component pc) false)
                 (BinInt.Z.to_nat zsz).
  have Ehu := @heap_used_fresh cm (Transitional.Memory.nextblock cm)
                CHUNK Hfresh.
  have Hcm' : mem' (Pointer.component pc)
              = Some {| Transitional.Memory.content :=
                          setm (Transitional.Memory.content cm)
                            (Transitional.Memory.nextblock cm) CHUNK;
                        Transitional.Memory.nextblock :=
                          1 + Transitional.Memory.nextblock cm |}.
  { by rewrite -Etm setmE eqxx. }
  have Hbud : (BinInt.Z.to_nat zsz).+1 + MDefs.heap_used cm
              < MDefs.heap_capacity.
  { case: (Hf' (erefl _)) => _ _ Hbudget.
    have HB := Hbudget _ _ Hcm'.
    rewrite Ehu /CHUNK size_repeat in HB.
    exact: HB. }
  have Hfitlen : BinInt.Z.to_nat zsz + 1 <= 2 ^ (word_size mt - NC).
  { move: Hbud. rewrite /MDefs.heap_capacity -HNCeq => Hbud'. by lia. }
  have Hh' : heap_inv mem (Symbolic.mem ms) := Hh.
  have Hused := Hh' _ _ Hcm Hc1.
  have Hre := region_end_le Hbound Hsmall HNCws HNCal Hc1.
  have E2 : (2 + Pointer.component pc) * 2 ^ (word_size mt - NC)
            = (1 + Pointer.component pc) * 2 ^ (word_size mt - NC)
              + 2 ^ (word_size mt - NC).
  { have -> : 2 + Pointer.component pc
              = (1 + Pointer.component pc) + 1 by lia.
    by rewrite mulnDl mul1n. }
  have Hnw : (\val (maxaddr NC (Symbolic.mem ms)
                      (Pointer.component pc)) : nat)
             + (BinInt.Z.to_nat zsz + 1) < 2 ^ word_size mt.
  { move: Hbud. rewrite /MDefs.heap_capacity -HNCeq => Hbud'. by lia. }
  have Hval := val_addw_small Hbound Hsmall HNCws HNCal Hnw.
  have Hlo : (1 + Pointer.component pc) * 2 ^ (word_size mt - NC)
             <= \val (maxaddr NC (Symbolic.mem ms) (Pointer.component pc))
    := maxaddr_lo Hbound Hsmall HNCws HNCal (Symbolic.mem ms) Hc1.
  have Hfitcap : pfilterC NC (Pointer.component pc)
                   (word.addw (maxaddr NC (Symbolic.mem ms)
                                 (Pointer.component pc))
                      (word.as_word
                         (ssrint.Posz (BinInt.Z.to_nat zsz + 1)))).
  { rewrite /pfilterC (@pfilter_val NC L P C pra prb PB PI
        Hbound Hsmall HNCws HNCal _ _ Hc1).
    apply/andP; split; rewrite Hval.
    - by lia.
    - move: Hbud. rewrite /MDefs.heap_capacity -HNCeq => Hbud'. by lia. }
  have Hpos' : (BinInt.Z.lt BinNums.Z0 zsz) by lia.
  have [amap' [ms1 [ms2 [ms3 [ms4 [ms5 [ms' [HS1 [HS2 [HS3 [HS4 [HS5
    [HS6 [Hm' [Hfoot [Hpres [Hrptr Hshape]]]]]]]]]]]]]]]]] :=
    sim_alloc (NC := NC) Hbound HPB Hsmall HNCws HNCal Hm Hsyncr Hex Hcp
      Ht Hv Hpos' Hal Hc1 Hfitlen Hfitcap.
  exists amap', ms'. split; [|split; [|split]].
  + exact: plus6 HS1 HS2 HS3 HS4 HS5 HS6.
  + exact: Hm'.
  +
    move=> cid cm2 Hcm2 Hb2.
    rewrite Hfoot.
    move: Hcm2; rewrite -Etm setmE.
    case: (altP (cid =P Pointer.component pc)) => [->|Hne] Hcm2.
    *
      case: Hcm2 => <-.
      rewrite Ehu /CHUNK size_repeat.
      have Epv : (\val (LRC.component_memory_prefix (NC := NC)
                   (ssrint.Posz (1 + Pointer.component pc)) : mword mt) : nat)
                 = (1 + Pointer.component pc) * 2 ^ (word_size mt - NC)
        := prefix_val HNCws Hc1.
      apply: maxaddr_ub.
      { rewrite Epv. by lia. }
      move=> w Hw Hp.
      move: Hw; rewrite domm_union in_fsetU => /orP[Hw|Hw].
      { have Hle : Ord.leq w
            (last (LRC.component_memory_prefix (NC := NC)
                     (ssrint.Posz (1 + Pointer.component pc)))
               (filter (pfilterC NC (Pointer.component pc))
                  (domm (Symbolic.mem ms))))
          := domm_filter_last_max
               (LRC.component_memory_prefix (NC := NC)
                  (ssrint.Posz (1 + Pointer.component pc))) Hw Hp.
        rewrite -maxaddrE word_leq_val in Hle.
        by lia. }
      move: Hw; rewrite domm_mkfmap /unzip1 /mkseq -!map_comp
        => /mapP[o Ho /= ->].
      move: Ho; rewrite mem_iota add0n => /andP[_ Ho].
      have Hnwo : (\val (maxaddr NC (Symbolic.mem ms)
                    (Pointer.component pc)) : nat)
                  + (o + 1) < 2 ^ word_size mt by lia.
      rewrite (val_addw_small Hbound Hsmall HNCws HNCal Hnwo).
      by lia.
    *
      have Epv : (\val (LRC.component_memory_prefix (NC := NC)
                   (ssrint.Posz (1 + cid)) : mword mt) : nat)
                 = (1 + cid) * 2 ^ (word_size mt - NC)
        := prefix_val HNCws Hb2.
      have Hother := Hh' _ _ Hcm2 Hb2.
      apply: maxaddr_ub.
      { rewrite Epv. by lia. }
      move=> w Hw Hp.
      move: Hw; rewrite domm_union in_fsetU => /orP[Hw|Hw].
      { have Hle : Ord.leq w
            (last (LRC.component_memory_prefix (NC := NC)
                     (ssrint.Posz (1 + cid)))
               (filter (pfilterC NC cid) (domm (Symbolic.mem ms))))
          := domm_filter_last_max
               (LRC.component_memory_prefix (NC := NC)
                  (ssrint.Posz (1 + cid))) Hw Hp.
        rewrite -maxaddrE word_leq_val in Hle.
        by lia. }
      exfalso.
      move: Hw; rewrite domm_mkfmap /unzip1 /mkseq -!map_comp
        => /mapP[o Ho /= Ew].
      move: Ho; rewrite mem_iota add0n => /andP[_ Ho].
      have Hnwo : (\val (maxaddr NC (Symbolic.mem ms)
                    (Pointer.component pc)) : nat)
                  + (o + 1) < 2 ^ word_size mt by lia.
      move: Hp; rewrite Ew /pfilterC
        (@pfilter_val NC L P C pra prb PB PI
           Hbound Hsmall HNCws HNCal _ _ Hb2)
        (val_addw_small Hbound Hsmall HNCws HNCal Hnwo)
        => /andP[Hp1 Hp2].
      have Hmul : forall a b : nat,
          a <= b ->
          a * 2 ^ (word_size mt - NC) <= b * 2 ^ (word_size mt - NC).
      { move=> a b Hab. by rewrite leq_mul2r Hab orbT. }
      have Hcap : (BinInt.Z.to_nat zsz).+1 + MDefs.heap_used cm
                  < 2 ^ (word_size mt - NC)
        by move: Hbud; rewrite /MDefs.heap_capacity -HNCeq.
      move/eqP: Hne => Hne.
      case: (ltngtP cid (Pointer.component pc)) => [Hlt|Hgt|//].
      { have HM' : (2 + cid) * 2 ^ (word_size mt - NC)
                   <= (1 + Pointer.component pc)
                      * 2 ^ (word_size mt - NC).
        { apply: Hmul. by lia. }
        by lia. }
      have HM' : (2 + Pointer.component pc)
                 * 2 ^ (word_size mt - NC)
                 <= (1 + cid) * 2 ^ (word_size mt - NC).
      { apply: Hmul. by lia. }
      by lia.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    case: Hshape => base [Eam Hfr Hocells].
    case: Hrptr => wret [Hget Hvret].
    have Hmono : forall r0 : register,
        reg_syncedW amap regs (Symbolic.regs ms) r0 ->
        reg_syncedW amap' regs (Symbolic.regs ms) r0.
    { move=> r0 [ra [Hra Hvv Htt]].
      exists ra. split=> //.
      rewrite Eam.
      apply: tvrel_upd; last exact: Hvv.
      exact: Hfr. }
    have Hcells : forall c0 b0 j0,
        cell_synced L P C pra prb PB PI amap mem
          (Symbolic.mem ms) c0 b0 j0 ->
        cell_synced L P C pra prb PB PI amap' mem'
          (Symbolic.mem ms') c0 b0 j0.
    { rewrite Eam Hfoot.
      apply: cell_synced_alloc_trans.
      - exact: Hal.
      - exact: Hmem.
      - exact: Hfr.
      - move=> o Ho. rewrite -Hfoot. exact: (Hocells o Ho). }
    have := MDiscStepD.dinv_step_alloc HMM Hex Hcp Ht Hv Hpos Hal HI.
    case=> [[[v0 [Ev0 Eph0]] HI']
           |[cmD [HcmD EptrD [v0 [Ev0 Eph0]] HI']]].
    *
      exists cur, chain, F, cs. split.
      -- exact: HI'.
      -- exact: (sync_alloc_heap HMM Hex Ev0 Eph0 Hpres Hget Hvret
                   Hmono Hcells HS).
    *
      exists (Some (Transitional.Memory.nextblock cmD)), chain,
        (fun c0 => if Nat.eqb c0 (Pointer.component pc)
                   then Transitional.Memory.nextblock cmD :: F c0
                   else F c0), cs.
      split.
      -- exact: HI'.
      -- have [Hcur0 [Hsg0 Hpd0]] := MDisc.di_prol HI Ev0 (or_intror Eph0).
         apply: sync_alloc_frame.
         ++ exact: HMM.
         ++ exact: Hex.
         ++ exact: Ev0.
         ++ exact: Eph0.
         ++ exact: Hsg0.
         ++ exact: Hpd0.
         ++ move=> c0. by [].
         ++ exact: Hpres.
         ++ exact: Hmono.
         ++ exact: Hcells.
         ++ exact: HS.
-
  move=> mem regs pc tg c pct pc' i tni c' pid call_arg n Hex Hfind Hex'
         Hne Hcpc Hpct Hrcom /= Hm _ _ _ Hh Hdsy.
  case: (Hm) => _ _ Hregs _ _ _ _.
  have HsyncCOM := get_int_synced Hregs Hrcom.
  have Hother : Transitional.tvtag (Transitional.Register.get R_COM regs)
                = Other.
  { case: (Hdsy) => cur0 [chain0 [F0 [cs0 [HI0 _]]]].
    have HCOM : R_COM <> R_RA. { move=> E. discriminate E. }
    exact: (MDisc.di_rtag HI0 HCOM). }
  have [i3 [tg3 Hex3]] := Hsucc_call Hex.
  have [ms' [Hs Hm' Hdm Hmm]] :=
    sim_call NC Hbound HPB Hwfa Hwfb Hlinkable Hsmall Hlab_a Hlab_b
      Hcomp_a Hcomp_b Hproc_a Hproc_b Hm HsyncCOM Hex Hfind Hex' Hne Hcpc
      Hpct Hother Hrcom Hex3 (HpP Hex Hfind).
  exists amap, ms'. split; [|split; [|split]].
  + by apply: plus_one.
  + exact: Hm'.
  + exact: heap_inv_pres Hdm Hh.
  + case: Hdsy => cur [chain [F [cs [HI HS]]]].
    have [b [cvnew [Hcur HI']]] :=
      MDiscStepC.dinv_step_call HMM Hex Hfind Hex' Hne Hcpc Hpct
        Hrcom HI.
    exists None,
      ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
          MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |} :: chain),
      F, cvnew.
    split.
    * exact: HI'.
    * case: (Hm') => _ _ Hregs' _ _ _ _.
      have Hcom' : reg_syncedW amap
          (Transitional.Register.set R_RA (Ptr (Pointer.inc pc))
             (Ret n) (Transitional.Register.invalidate regs))
          (Symbolic.regs ms') R_COM.
      { apply: mregs_rel_synced Hregs' _.
        have HCR : R_COM <> R_RA by [].
        rewrite (MDisc.tget_set_neq _ _ _ HCR) MDisc.tget_invalidate_com.
        move=> E.
        have := f_equal Transitional.val E.
        rewrite Hrcom /=.
        by []. }
      rewrite Hmm.
      apply: sync_call.
      -- exact: HMM.
      -- exact: Hex.
      -- exact: Hfind.
      -- exact: Hcur.
      -- exact: Hcom'.
      -- exact: HS.
Qed.

(* ================================================================== *)
(* 4. The star-level simulation.                                      *)
(* ================================================================== *)

Theorem t2me_star_sim (s0 : TS.state) (tr : Events.trace) (s : TS.state) :
  star TS.step cdeW s0 tr s ->
  forall (amap : amap_t) (ms : @Symbolic.state mt lrc_tags unit),
  match_stW amap s0 ms ->
  heap_inv (let '(tm, _, _, _) := s0 in tm) (Symbolic.mem ms) ->
  mm_dsyncW amap s0 ms ->
  (forall s1 tr1 tr2,
      star TS.step cdeW s0 tr1 s1 -> tr = Eapp tr1 tr2 ->
      [/\ MDefs.state_fits s1 & MDefs.binop_ok cdeW s1]) ->
  exists (amap' : amap_t)
         (ms' : @Symbolic.state mt lrc_tags unit),
    star mstep tt ms tr ms' /\
    match_stW amap' s ms' /\
    heap_inv (let '(tm, _, _, _) := s in tm) (Symbolic.mem ms') /\
    mm_dsyncW amap' s ms'.
Proof using All.
move=> Hstar.
elim: Hstar => [s1|s1 t1 s2 t2 s3 t Hstep Hst IH Et] amap ms Hm Hh Hdsy
  Hfits.
- exists amap, ms.
  split; [exact: star_refl | by []].
- have [F0 B0] := Hfits s1 E0 t (star_refl _ _ _) (erefl _).
  have Hst1 : star TS.step cdeW s1 t1 s2.
  { apply: star_step; [exact: Hstep | exact: star_refl | by rewrite E0_right]. }
  have [Fm Bm] := Hfits s2 t1 t2 Hst1 Et.
  have [amap1 [ms1 [Hplus [Hm1 [Hh1 Hdsy1]]]]] :=
    t2me_step_sim Hstep Hm F0 (fun _ => Fm) B0 Hh Hdsy.
  have Hfits' : forall s4 tr1 tr2,
      star TS.step cdeW s2 tr1 s4 -> t2 = Eapp tr1 tr2 ->
      [/\ MDefs.state_fits s4 & MDefs.binop_ok cdeW s4].
  { move=> s4 tr1 tr2 Hst4 Et2.
    apply: (Hfits s4 (Eapp t1 tr1) tr2).
    - apply: star_step; [exact: Hstep | exact: Hst4 | by []].
    - rewrite Et Et2. by rewrite Eapp_assoc. }
  have [amap' [ms' [Hstar' [Hm' [Hh' Hdsy']]]]] :=
    IH amap1 ms1 Hm1 Hh1 Hdsy1 Hfits'.
  exists amap', ms'. split; [|split] => //.
  rewrite Et.
  exact: (star_trans (plus_star Hplus) Hstar' (erefl _)).
Qed.

(* ================================================================== *)
(* 5. The behavior-level transport.                                   *)
(* ================================================================== *)

Local Notation tpW := (Intermediate.program_link pra prb).

(* T steps emit at most one event *)
Lemma t_single (s1 : TS.state) (t : Events.trace) (s2 : TS.state) :
  TS.step cdeW s1 t s2 -> (length t <= 1)%coq_nat.
Proof.
by case=> *; simpl; lia.
Qed.

(* a me memory with no key at or above the first heap region satisfies
   the occupancy invariant outright *)
Lemma heap_inv_init (tmem0 : Transitional.Memory.t)
    (mmem0 : {fmap mword mt -> matom}) :
  (forall w : mword mt,
      2 ^ (word_size mt - NC) <= (\val w : nat) -> mmem0 w = None) ->
  heap_inv tmem0 mmem0.
Proof.
move=> Hnone cid cm Hcm Hb.
apply: maxaddr_ub.
- have Epv : (\val (LRC.component_memory_prefix (NC := NC)
               (ssrint.Posz (1 + cid)) : mword mt) : nat)
             = (1 + cid) * 2 ^ (word_size mt - NC)
    := prefix_val HNCws Hb.
  rewrite Epv. by lia.
- move=> w Hw Hp.
  exfalso.
  move: Hp; rewrite /pfilterC
    (@pfilter_val NC L P C pra prb PB PI
       Hbound Hsmall HNCws HNCal _ _ Hb) => /andP[Hp1 _].
  have Hge : 2 ^ (word_size mt - NC) <= (\val w : nat).
  { have : 2 ^ (word_size mt - NC)
           <= (1 + cid) * 2 ^ (word_size mt - NC) by rewrite leq_pmull.
    by lia. }
  move: Hw; rewrite mem_domm (Hnone _ Hge). by [].
Qed.

Theorem t2me_fwd_prefix (W : Definitions.program)
    (m : finpref_behavior) :
  let ms0 := Merged.initial_state (Definitions.code W)
               (Definitions.prog_buffers W)
               (Definitions.prog_interface W) in
  (forall ts0, TSim.t_initial_base cdeW tpW ts0 ->
     match_stW (amap0 PB) ts0 ms0 /\
     heap_inv (let '(tm, _, _, _) := ts0 in tm) (Symbolic.mem ms0) /\
     mm_dsyncW (amap0 PB) ts0 ms0) ->
  does_prefix (TSim.t_sem cdeW tpW) m ->
  not_wrong_finpref m ->
  MDefs.run_fits cdeW tpW (finpref_trace m) ->
  does_prefix (RSCDefs.me_sem NC W) m.
Proof.
move=> ms0 Hbridge Hdp Hnw Hrf.
case: Hdp => b [Hpb Hpref].
case: Hpb Hpref => [s0 beh Hinit Hsb|Hnoinit] Hpref; last first.
-
  case: m Hrf Hnw Hpref => [t| |t] //= Hrf _ Hpref; last first.
  +
    case: Hpref => b2 Eb2.
    case: b2 Eb2 => //= t2 [Et2].
    move: Et2 => /esym/List.app_eq_nil [-> _].
    have [b' Hb'] := @program_behaves_exists (RSCDefs.me_sem NC W).
    exists b'. split; first exact: Hb'.
    exists b'. by rewrite behavior_app_E0.
-
  case: Hinit => s00 [Hbase Hstar0].
  have [Hm0 [Hh0 Hdsy0]] := Hbridge _ Hbase.
  case: m Hrf Hnw Hpref => [t| |t] //= Hrf _ Hpref.
  +
    case: beh Hsb Hpref => //= t2 Hsb Et2.
    rewrite -{}Et2 in Hsb.
    have [sF [HstarF HfinF]] : exists sF,
        star TS.step cdeW s0 t sF /\ TSim.t_final cdeW sF.
    { inversion Hsb; subst. by exists s'; split. }
    have Hstar : star TS.step cdeW s00 t sF.
    { apply: (star_trans Hstar0 HstarF). by []. }
    have Hfits : forall s1 tr1 tr2,
        star TS.step cdeW s00 tr1 s1 -> t = Eapp tr1 tr2 ->
        [/\ MDefs.state_fits s1 & MDefs.binop_ok cdeW s1].
    { move=> s1 tr1 tr2 Hst1 Et.
      apply: (Hrf _ _ _ Hbase Hst1).
      exists tr2. by rewrite Et. }
    have [amap' [ms' [Hstar' [Hm' _]]]] :=
      t2me_star_sim Hstar Hm0 Hh0 Hdsy0 Hfits.
    case: HfinF => tg [c Hex].
    case: sF Hex Hm' {Hsb Hstar HstarF} => [[[tmem' tregs'] tpc'] tpct']
      /= Hex Hm'.
    have Hfinal : RSCDefs.final_halt_code ms'
      := sim_halt Hbound Hm' Hex.
    exists (Terminates t). split.
    * apply: program_runs; last first.
      { apply: state_terminates; [exact: Hstar' | exact: Hfinal]. }
      by [].
    * by [].
  +
    case: Hpref => b2 Eb2. subst beh.
    have Hsingle : single_events (TSim.t_sem cdeW tpW).
    { move=> s1' t' s2' Hst. exact: t_single Hst. }
    have [s1 [Hstar1 _]] : exists s1,
        star TS.step cdeW s0 t s1 /\
        state_behaves (TSim.t_sem cdeW tpW) s1 b2.
    { have Hinv := state_behaves_app_inv Hsingle.
      have [s2 [HS HB]] := Hinv _ _ _ Hsb.
      by exists s2; split. }
    have Hstar : star TS.step cdeW s00 t s1.
    { apply: (star_trans Hstar0 Hstar1). by []. }
    have Hfits : forall s2 tr1 tr2,
        star TS.step cdeW s00 tr1 s2 -> t = Eapp tr1 tr2 ->
        [/\ MDefs.state_fits s2 & MDefs.binop_ok cdeW s2].
    { move=> s2 tr1 tr2 Hst1 Et.
      apply: (Hrf _ _ _ Hbase Hst1).
      exists tr2. by rewrite Et. }
    have [amap' [ms' [Hstar' [Hm' _]]]] :=
      t2me_star_sim Hstar Hm0 Hh0 Hdsy0 Hfits.
    have [b'' Hb''] := @state_behaves_exists (RSCDefs.me_sem NC W) ms'.
    exists (behavior_app t b''). split.
    * apply: program_runs; last first.
      { apply: state_behaves_app; [exact: Hstar' | exact: Hb'']. }
      by [].
    * by exists b''.
Qed.

End StarSim.

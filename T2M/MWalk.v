(** * T2M — the backward walk.

    [t2me_walk]: a T run transported along the observed me prefix — either
    stays within the prefix (full transport), or is decomposed exactly at
    the prefix boundary with the pending event-step recorded. *)

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
Require Import MicroPolicies.Recomposition.Definitions.
Require Import S2T.TSem.
Require Import S2T.TSim.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require Import T2M.MStep.
Require Import T2M.MAlloc.
Require Import T2M.MHeap.
Require Import T2M.MStar.
Require Import T2M.MSig.
Require T2M.MDisc.
Require Import T2M.MSync.
Require Import T2M.MFlip.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section Walk.

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

(* ---- the standing side conditions ---- *)
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

(* ---- the label/procedure statics ---- *)
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

(* ---- the code-shape statics this file consumes ---- *)

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


Local Notation tpW := (Intermediate.program_link pra prb).
Local Notation heap_invW := (heap_inv NC).

(* the closed dispatch, saturated with the section context *)
Local Notation step_sim :=
  (t2me_step_sim HMM Hcst HuniqL Hbound HPB Hwfa Hwfb Hlinkable Hsmall HNCws HNCal
     HNCeq Himm_a Himm_b Hlab_a Hlab_b Hcomp_a Hcomp_b Huniq_a Huniq_b
     Hproc_a Hproc_b Hself Hjra Hbf HlL_bnz HlL_jal HpP Hsucc_jal
     Hsucc_call Hc1s).

(* an arbitrary program pins the me determinacy instance; the step
   relation [prog_step_me NC] does not depend on it *)
Variable Wdet : program.
Let DETme : determinate (me_sem NC Wdet) := det_me_sem NC Wdet.

(* T steps carry at most one event *)
Lemma tr_shape (s1 : TS.state) (tr : Events.trace) (s2 : TS.state) :
  TS.step cdeW s1 tr s2 -> tr = E0 \/ exists e, tr = [:: e].
Proof.
case=> *; try by left.
- by right; eexists.
- by right; eexists.
Qed.

Theorem t2me_walk (t : Events.trace)
    (ms0 ms_m : @Symbolic.state mt lrc_tags unit)
    (ts_base : TS.state) :
  TSim.t_initial_base cdeW tpW ts_base ->
  MDefs.run_fits cdeW tpW t ->
  star (RSCDefs.prog_step_me NC) tt ms0 t ms_m ->
  forall (u : Events.trace) (tsA ts1 : TS.state),
  star TS.step cdeW tsA u ts1 ->
  forall (tdone : Events.trace) (amapA : amap_t)
         (msA : @Symbolic.state mt lrc_tags unit),
  star TS.step cdeW ts_base tdone tsA ->
  match_stW amapA tsA msA ->
  heap_invW (let '(tm, _, _, _) := tsA in tm) (Symbolic.mem msA) ->
  mm_dsyncW amapA tsA msA ->
  star (RSCDefs.prog_step_me NC) tt ms0 tdone msA ->
  (exists trem, t = Eapp tdone trem) ->
  (exists trem' amap1 ms1,
     [/\ t = Eapp (Eapp tdone u) trem',
         star (RSCDefs.prog_step_me NC) tt ms0 (Eapp tdone u) ms1,
         match_stW amap1 ts1 ms1,
         heap_invW (let '(tm, _, _, _) := ts1 in tm) (Symbolic.mem ms1)
       & mm_dsyncW amap1 ts1 ms1])
  \/ (exists tpref e urest ts_t ts_next amap1 ms1,
     [/\ u = Eapp tpref (e :: urest),
         t = Eapp tdone tpref,
         star TS.step cdeW tsA tpref ts_t,
         TS.step cdeW ts_t [:: e] ts_next
       & [/\ match_stW amap1 ts_t ms1,
             star (RSCDefs.prog_step_me NC) tt ms0 t ms1,
             heap_invW (let '(tm, _, _, _) := ts_t in tm)
               (Symbolic.mem ms1)
           & mm_dsyncW amap1 ts_t ms1]]).
Proof.
move=> Hbase Hrf Hmrun u tsA ts1 HstarT.
elim: HstarT => [tsX|tsX tr tsB u' ts1' u0 Hstep Hrest IH Eu0]
  tdone amapA msA Hroot Hm Hh Hdsy Hme [trem Erem].
-
  left. exists trem, amapA, msA.
  split=> //.
  + by rewrite E0_right.
  + by rewrite E0_right.
-
  subst u0.
  have [F0 B0] := Hrf ts_base tdone tsX Hbase Hroot
                          (ex_intro _ trem Erem).
  have Hone : star TS.step cdeW tsX tr tsB.
  { apply: star_step; [exact: Hstep | exact: star_refl | by rewrite E0_right]. }
  have HrootB : star TS.step cdeW ts_base (Eapp tdone tr) tsB.
  { apply: star_trans; [exact: Hroot | exact: Hone | by []]. }
  have Hpost : tr = E0 -> MDefs.state_fits tsB.
  { move=> Etr.
    have HrootB' : star TS.step cdeW ts_base tdone tsB.
    { by rewrite -(E0_right tdone) -Etr. }
    have [FB _] := Hrf ts_base tdone tsB Hbase HrootB'
                         (ex_intro _ trem Erem).
    exact: FB. }
  have [amapB [msB [Hplus [HmB [HhB HdsyB]]]]] :=
    step_sim Hstep Hm F0 Hpost B0 Hh Hdsy.
  have HmeB : star (RSCDefs.prog_step_me NC) tt ms0 (Eapp tdone tr) msB.
  { apply: star_trans; [exact: Hme | exact: (plus_star Hplus) | by []]. }
  have Hcmp := star_run_compare DETme HmeB Hmrun.
  case: Hcmp => [[t2 [Et2 Hcont]]|[u2 [Eu2 Hpast]]].
  +
    case: (IH (Eapp tdone tr) amapB msB HrootB HmB HhB HdsyB HmeB
            (ex_intro _ t2 Et2)) => [HA|HB].
    * left.
      case: HA => [trem' [amap1 [ms1 [HA1 HA2 HA3 HA4 HA5]]]].
      exists trem', amap1, ms1.
      split=> //.
      -- by rewrite -Eapp_assoc.
      -- by rewrite -Eapp_assoc.
    * right.
      case: HB
        => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
             [HB1 HB2 HB3 HB4 HB5]]]]]]]].
      exists (Eapp tr tpref), e, urest, ts_t, ts_next, amap1, ms1.
      split=> //.
      -- by rewrite HB1 Eapp_assoc.
      -- by rewrite HB2 -Eapp_assoc.
      -- apply: star_trans; [exact: Hone | exact: HB3 | by []].
  +
    have Etr2 : tr = Eapp trem u2.
    { move: Eu2. rewrite Erem Eapp_assoc.
      exact: List.app_inv_head. }
    case: (tr_shape Hstep) => [Etr|[e Etr]];
      move: Etr2; subst tr; move=> Etr2.
    *
      have [E1 E2] : trem = E0 /\ u2 = E0.
      { by move: Etr2 => /esym /List.app_eq_nil. }
      subst trem u2.
      have Erem0 : t = Eapp (Eapp tdone E0) E0.
      { by rewrite !E0_right Erem E0_right. }
      case: (IH (Eapp tdone E0) amapB msB HrootB HmB HhB HdsyB HmeB
              (ex_intro _ E0 Erem0)) => [HA|HB].
      -- left.
        case: HA => [trem' [amap1 [ms1 [HA1 HA2 HA3 HA4 HA5]]]].
        exists trem', amap1, ms1.
        split=> //.
        ++ by rewrite -Eapp_assoc.
        ++ by rewrite -Eapp_assoc.
      -- right.
        case: HB
          => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
               [HB1 HB2 HB3 HB4 HB5]]]]]]]].
        exists (Eapp E0 tpref), e, urest, ts_t, ts_next, amap1, ms1.
        split=> //.
        ++ by rewrite HB2 Eapp_assoc.
        ++ apply: star_trans; [exact: Hone | exact: HB3 | by []].
    *
      case: trem Etr2 Erem => [|e' trem'] /= Etr2 Erem.
      --
        right.
        exists E0, e, u', tsX, tsB, amapA, msA.
        split=> //.
        ++ exact: star_refl.
        ++ split=> //.
           by rewrite Erem E0_right.
      --
        case: Etr2 => Ee Enil.
        have [E1 E2] : trem' = E0 /\ u2 = E0.
        { by move: Enil => /esym /List.app_eq_nil. }
        subst e' trem' u2.
        have Erem1 : t = Eapp (Eapp tdone [:: e]) E0.
        { by rewrite E0_right Erem. }
        case: (IH (Eapp tdone [:: e]) amapB msB HrootB HmB HhB HdsyB HmeB
                (ex_intro _ E0 Erem1)) => [HA|HB].
        ++ left.
           case: HA => [trem2 [amap1 [ms1 [HA1 HA2 HA3 HA4 HA5]]]].
           exists trem2, amap1, ms1.
           split=> //.
           ** by rewrite HA1 (Eapp_assoc tdone [:: e] u').
           ** by move: HA2; rewrite Eapp_assoc.
        ++ right.
           case: HB
             => [tpref [e2 [urest [ts_t [ts_next [amap1 [ms1
                  [HB1 HB2 HB3 HB4 HB5]]]]]]]].
           exists (Eapp [:: e] tpref), e2, urest, ts_t, ts_next,
             amap1, ms1.
           split=> //.
           ** by rewrite HB1.
           ** by rewrite HB2 Eapp_assoc.
           ** apply: star_trans; [exact: Hone | exact: HB3 | by []].
Qed.

(* every silent T chain pumps at least as many silent me steps *)
Lemma t2me_silent_pump (t : Events.trace) (ts_base : TS.state) :
  TSim.t_initial_base cdeW tpW ts_base ->
  MDefs.run_fits cdeW tpW t ->
  forall (n : nat) (tsA ts1 : TS.state),
  starN TS.step cdeW n tsA E0 ts1 ->
  forall (tdone : Events.trace) (amapA : amap_t)
         (msA : @Symbolic.state mt lrc_tags unit),
  star TS.step cdeW ts_base tdone tsA ->
  match_stW amapA tsA msA ->
  heap_invW (let '(tm, _, _, _) := tsA in tm) (Symbolic.mem msA) ->
  mm_dsyncW amapA tsA msA ->
  (exists trem, t = Eapp tdone trem) ->
  exists (p : nat) (msB : @Symbolic.state mt lrc_tags unit),
    (n <= p)%coq_nat /\ starN mstep tt p msA E0 msB.
Proof.
move=> Hbase Hrf n.
elim: n => [|n IH] tsA ts1 HsN tdone amapA msA Hroot Hm Hh Hdsy Hrem.
- exists 0%nat, msA. split=> //. exact: starN_refl.
- inversion HsN.
  have [E1 E2] := Eapp_E0_inv _ _ (esym H2).
  rewrite E1 in H0. rewrite E2 in H1.
  case: Hrem => trem Erem.
  have [F0 B0] := Hrf ts_base tdone tsA Hbase Hroot
                          (ex_intro _ trem Erem).
  have HrootB : star TS.step cdeW ts_base tdone s'.
  { rewrite -(E0_right tdone).
    apply: star_trans; [exact: Hroot | | by []].
    apply: star_step; [exact: H0 | exact: star_refl | by []]. }
  have Hpost : E0 = E0 -> MDefs.state_fits s'.
  { move=> _.
    have [FB _] := Hrf ts_base tdone s' Hbase HrootB
                         (ex_intro _ trem Erem).
    exact: FB. }
  have [amapB [msB [Hplus [HmB [HhB HdsyB]]]]] :=
    step_sim H0 Hm F0 Hpost B0 Hh Hdsy.
  inversion Hplus.
  have [E3 E4] := Eapp_E0_inv _ _ (esym H8).
  rewrite E3 in H6. rewrite E4 in H7.
  have [q HqN] := star_to_starN (L := RSCDefs.me_sem NC Wdet) H7.
  have [p [msC [Hnp HpN]]] :=
    IH s' ts1 H1 tdone amapB msB HrootB HmB HhB HdsyB
      (ex_intro _ trem Erem).
  exists ((q.+1) + p)%coq_nat, msC. split; first by lia.
  apply: (starN_silent_trans (L := RSCDefs.me_sem NC Wdet) (n := q.+1) (m := p)); last exact: HpN.
  apply: starN_step; [exact: H6 | exact: HqN | by []].
Qed.

(* ================================================================== *)
(* The contradiction kernels for the flip.                            *)
(* ================================================================== *)

(* two same-trace me runs from one state are silently linked *)
Lemma same_trace_silent_link (tm : Events.trace)
    (msO msA msB : @Symbolic.state mt lrc_tags unit) :
  star mstep tt msO tm msA -> star mstep tt msO tm msB ->
  star mstep tt msA E0 msB \/ star mstep tt msB E0 msA.
Proof.
move=> HA HB.
case: (star_run_compare DETme HA HB) => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
- left.
  have Et : E0 = t2.
  { move: Et2. rewrite -{1}(E0_right tm). exact: List.app_inv_head. }
  by rewrite -Et in HS.
- right.
  have Eu : E0 = u2.
  { move: Eu2. rewrite -{1}(E0_right tm). exact: List.app_inv_head. }
  by rewrite -Eu in HS.
Qed.

(* a stuck state admits only the reflexive run *)
Lemma nostep_star_refl (msX msY : @Symbolic.state mt lrc_tags unit)
    (tr : Events.trace) :
  (forall t' s', ~ mstep tt msX t' s') ->
  star mstep tt msX tr msY -> tr = E0 /\ msY = msX.
Proof.
move=> Hns Hst.
inversion Hst; subst; first by [].
by case: (Hns _ _ H).
Qed.

(* an me run about to emit an event passes a silently-stuck state *)
Lemma me_first_event_stuck (e : Events.event) (rest : Events.trace)
    (msA msB : @Symbolic.state mt lrc_tags unit) :
  star mstep tt msA (e :: rest) msB ->
  exists msx,
    star mstep tt msA E0 msx /\ (forall s', ~ mstep tt msx E0 s').
Proof.
move=> Hst.
have Hse : single_events (RSCDefs.me_sem NC Wdet) := sd_traces DETme.
have Hst' : star mstep tt msA (Eapp [:: e] rest) msB := Hst.
have [smid [H1 _]] := star_app_inv Hse [:: e] rest Hst'.
have Hlen : (Datatypes.length [:: e] = 1)%nat by [].
have [msx [msy [Hsil [Hstep _]]]] :=
  star_non_E0_split (RSCDefs.me_sem NC Wdet) H1 Hlen.
exists msx. split=> // s' Hs'.
exact: (event_no_silent DETme Hstep Hs').
Qed.

(* reaching a stuck state yields a silently-stuck state on the way *)
Lemma stuck_target (t2 : Events.trace)
    (ms1 s_m : @Symbolic.state mt lrc_tags unit) :
  star mstep tt ms1 t2 s_m ->
  (forall t' s', ~ mstep tt s_m t' s') ->
  exists msx,
    star mstep tt ms1 E0 msx /\ (forall s', ~ mstep tt msx E0 s').
Proof.
case: t2 => [|ev rest] Hst Hns.
- by exists s_m; split.
- exact: me_first_event_stuck Hst.
Qed.

(* the pending-event kernel: a matched T event step at the exhausted
   prefix boundary contradicts a stuck end of the me run *)
Lemma boundary_event_dead (tm : Events.trace)
    (ts_base ts_t ts_next : TS.state) (e : Events.event)
    (amap1 : amap_t)
    (ms00 ms1 s_m : @Symbolic.state mt lrc_tags unit) :
  TSim.t_initial_base cdeW tpW ts_base ->
  MDefs.run_fits cdeW tpW tm ->
  star TS.step cdeW ts_base tm ts_t ->
  TS.step cdeW ts_t [:: e] ts_next ->
  match_stW amap1 ts_t ms1 ->
  heap_invW (let '(tmm, _, _, _) := ts_t in tmm) (Symbolic.mem ms1) ->
  mm_dsyncW amap1 ts_t ms1 ->
  star mstep tt ms00 tm ms1 ->
  star mstep tt ms00 tm s_m ->
  (forall t' s', ~ mstep tt s_m t' s') ->
  False.
Proof.
move=> Hbase Hrf Hroot Hstep Hm Hh Hdsy Hms1 Hsm Hns.
have [F0 B0] := Hrf ts_base tm ts_t Hbase Hroot
                        (ex_intro _ E0 (esym (E0_right tm))).
have Hpost : [:: e] = E0 -> MDefs.state_fits ts_next.
{ move=> Ee. by inversion Ee. }
have [amapE [msE [Hplus _]]] :=
  step_sim Hstep Hm F0 Hpost B0 Hh Hdsy.
have HplusS := plus_star Hplus.
case: (same_trace_silent_link Hms1 Hsm) => Hlink; last first.
-
  have [_ E2] := nostep_star_refl Hns Hlink.
  rewrite E2 in HplusS.
  inversion HplusS.
  by case: (Hns _ _ H).
-
  case: (star_run_compare DETme HplusS Hlink)
    => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
  + by inversion Et2.
  + inversion HS; subst.
    * by move: Eu2; rewrite E0_right.
    * by case: (Hns _ _ H).
Qed.

(* the divergence kernel: silent T divergence at a matched state
   contradicts a silently-stuck state on the me path *)
Lemma silent_div_dead (t : Events.trace) (ts_base ts1 : TS.state)
    (tdone : Events.trace) (amap1 : amap_t)
    (ms1 msx : @Symbolic.state mt lrc_tags unit) :
  TSim.t_initial_base cdeW tpW ts_base ->
  MDefs.run_fits cdeW tpW t ->
  star TS.step cdeW ts_base tdone ts1 ->
  match_stW amap1 ts1 ms1 ->
  heap_invW (let '(tmm, _, _, _) := ts1 in tmm) (Symbolic.mem ms1) ->
  mm_dsyncW amap1 ts1 ms1 ->
  (exists trem, t = Eapp tdone trem) ->
  forever_silent TS.step cdeW ts1 ->
  star mstep tt ms1 E0 msx ->
  (forall s', ~ mstep tt msx E0 s') ->
  False.
Proof.
move=> Hbase Hrf Hroot Hm Hh Hdsy Hrem Hfs Hlink Hstuck.
have [n0 HsN0] := star_to_starN (L := RSCDefs.me_sem NC Wdet) Hlink.
have [tsZ [HtN _]] :=
  forever_silent_starN (L := TSim.t_sem cdeW tpW) Hfs (n0.+1).
have [p [msB [Hple HpN]]] :=
  t2me_silent_pump Hbase Hrf HtN Hroot Hm Hh Hdsy Hrem.
have Hbound' := silent_starN_bound DETme HsN0 Hstuck HpN.
by lia.
Qed.

(* ================================================================== *)
(* The base-rooted walk (tdone = E0), as consumed by the assembly.    *)
(* ================================================================== *)

Corollary t2me_walk0 (t : Events.trace)
    (ms0 ms_m : @Symbolic.state mt lrc_tags unit)
    (ts_base : TS.state) (u : Events.trace) (ts1 : TS.state) :
  TSim.t_initial_base cdeW tpW ts_base ->
  MDefs.run_fits cdeW tpW t ->
  star mstep tt ms0 t ms_m ->
  star TS.step cdeW ts_base u ts1 ->
  match_stW (amap0 PB) ts_base ms0 ->
  heap_invW (let '(tm, _, _, _) := ts_base in tm) (Symbolic.mem ms0) ->
  mm_dsyncW (amap0 PB) ts_base ms0 ->
  (exists trem' amap1 ms1,
     [/\ t = Eapp u trem',
         star mstep tt ms0 u ms1,
         match_stW amap1 ts1 ms1,
         heap_invW (let '(tm, _, _, _) := ts1 in tm) (Symbolic.mem ms1)
       & mm_dsyncW amap1 ts1 ms1])
  \/ (exists tpref e urest ts_t ts_next amap1 ms1,
     [/\ u = Eapp tpref (e :: urest),
         t = tpref,
         star TS.step cdeW ts_base tpref ts_t,
         TS.step cdeW ts_t [:: e] ts_next
       & [/\ match_stW amap1 ts_t ms1,
             star mstep tt ms0 t ms1,
             heap_invW (let '(tm, _, _, _) := ts_t in tm)
               (Symbolic.mem ms1)
           & mm_dsyncW amap1 ts_t ms1]]).
Proof.
move=> Hbase Hrf Hmrun Hstar Hm0 Hh0 Hdsy0.
have Hrefl_t : star TS.step cdeW ts_base E0 ts_base := star_refl _ _ _.
have Hrefl_m : star mstep tt ms0 E0 ms0 := star_refl _ _ _.
case: (t2me_walk Hbase Hrf Hmrun Hstar Hrefl_t Hm0 Hh0 Hdsy0 Hrefl_m
         (ex_intro _ t (erefl _))) => [HA|HB].
- left.
  case: HA => [trem' [amap1 [ms1 [E1 E2 E3 E4 E5]]]].
  by exists trem', amap1, ms1; split.
- right.
  case: HB
    => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
         [E1 E2 E3 E4 E5]]]]]]]].
  by exists tpref, e, urest, ts_t, ts_next, amap1, ms1; split.
Qed.

(* ================================================================== *)
(* The backward flip: an observed me prefix is matched by a T          *)
(* behaviour that prefixes or improves it.                             *)
(* ================================================================== *)

Theorem t2me_bwd_prefix_for (m : finpref_behavior)
    (bT : program_behavior) :
  let msI := Merged.initial_state (Definitions.code Wdet)
               (Definitions.prog_buffers Wdet)
               (Definitions.prog_interface Wdet) in
  (forall ts0, TSim.t_initial_base cdeW tpW ts0 ->
     match_stW (amap0 PB) ts0 msI /\
     heap_invW (let '(tm, _, _, _) := ts0 in tm) (Symbolic.mem msI) /\
     mm_dsyncW (amap0 PB) ts0 msI) ->
  does_prefix (RSCDefs.me_sem NC Wdet) m ->
  MDefs.run_fits cdeW tpW (finpref_trace m) ->
  program_behaves (TSim.t_sem cdeW tpW) bT ->
  CompCertExtensions.prefix m bT \/ behavior_improves_finpref bT m.
Proof.
move=> msI Hbridge Hdp Hrf HbT.
have Hdp' : does_prefix' (RSCDefs.me_sem NC Wdet) m
  := proj1 (does_prefix_equiv DETme m) Hdp.
case: bT / HbT => [s0T bTx HinitT Hsb|Hnoinit_T]; last first.
-
  right. exists E0. split=> //.
  by case: m {Hdp Hdp' Hrf} => t'; exists t'.
-
  case: HinitT => s00 [HbaseT Hstar0].
  have [Hm0 [Hh0 Hdsy0]] := Hbridge _ HbaseT.
  move: Hrf.
  case: m / Hdp' {Hdp}
    => [s_i s_m t_m Hinit Hstar_m
       |s_i s_m t_m Hinit Hstar_m Hns0 Hnf
       |s_i s_m t_m Hinit Hstar_m Hfin
       |Hnoinit|Hnoinit] Hrf;
    try by case: (Hnoinit _ (erefl _)).
  +
    have Ei : s_i = msI := Hinit. subst s_i.
    have Hrf' : MDefs.run_fits cdeW tpW t_m := Hrf.
    case: bTx / Hsb
      => [tT sF HstarF HfinF|tT sT1 HstarT Hfs|Tinf Hfr
         |tT sT1 HstarT HnsT HnfT].
    *
      case: sF HstarF HfinF => [[[tmF trF] tpF] ttF] HstarF HfinF.
      have HstarR : star TS.step cdeW s00 tT (tmF, trF, tpF, ttF).
      { apply: star_trans; [exact: Hstar0 | exact: HstarF | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: HfinF => tg [c Hex].
         have Hfm : RSCDefs.final_halt_code ms1 := sim_halt Hbound EA3 Hex.
         have Hns1 : forall t' s', ~ mstep tt ms1 t' s'
           := sd_final_nostep DETme _ Hfm.
         case: (star_run_compare DETme EA2 Hstar_m)
           => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
         ++ have [Et20 _] := nostep_star_refl Hns1 HS.
            left. exists (Terminates E0).
            by rewrite /= Et2 Et20 !E0_right.
         ++ left. exists (Terminates u2).
            by rewrite /= Eu2.
      -- case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         left. exists (Terminates (e :: urest)).
         by rewrite /= EB1 EB2.
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: trem' EA1 => [|ev rest] EA1.
         ++ left. exists (Diverges E0).
            by rewrite /= EA1 !E0_right.
         ++ exfalso.
            case: (star_run_compare DETme EA2 Hstar_m)
              => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
            ** have Et2' : t2 = ev :: rest.
               { move: (eq_trans (esym Et2) EA1).
                 exact: List.app_inv_head. }
               rewrite Et2' in HS.
               have [msx [Hsil Hstuck]] := me_first_event_stuck HS.
               exact: (silent_div_dead HbaseT Hrf' HstarR EA3 EA4 EA5
                        (ex_intro _ (ev :: rest) EA1) Hfs Hsil Hstuck).
            ** have S1 : size tT = (size t_m + size u2)%N.
               { by rewrite Eu2 size_cat. }
               have S2 : size t_m = (size tT + (size rest).+1)%N.
               { by rewrite EA1 size_cat. }
               by lia.
      -- case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         left. exists (Diverges (e :: urest)).
         by rewrite /= EB1 EB2.
    *
      have [t' [sR [HstarR' Hlen [T' ET']]]] :=
        reactive_star_events (L := TSim.t_sem cdeW tpW) Hfr
          ((size t_m).+1).
      have HstarR : star TS.step cdeW s00 t' sR.
      { apply: star_trans; [exact: Hstar0 | exact: HstarR' | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 _ _ _]]]].
         have := f_equal size EA1.
         rewrite size_cat. by lia.
      -- case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         left. exists (Reacts ((e :: urest) *** T')).
         by rewrite /= ET' EB1 EB2 Eappinf_assoc.
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         right. exists tT.
         split; [exact: (erefl _) | by exists trem'].
      -- case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         left. exists (Goes_wrong (e :: urest)).
         by rewrite /= EB1 EB2.
  +
    have Ei : s_i = msI := Hinit. subst s_i.
    have Hrf' : MDefs.run_fits cdeW tpW t_m := Hrf.
    have Hnsm : forall t' s', ~ mstep tt s_m t' s' := Hns0.
    case: bTx / Hsb
      => [tT sF HstarF HfinF|tT sT1 HstarT Hfs|Tinf Hfr
         |tT sT1 HstarT HnsT HnfT].
    *
      case: sF HstarF HfinF => [[[tmF trF] tpF] ttF] HstarF HfinF.
      have HstarR : star TS.step cdeW s00 tT (tmF, trF, tpF, ttF).
      { apply: star_trans; [exact: Hstar0 | exact: HstarF | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: HfinF => tg [c Hex].
         have Hfm : RSCDefs.final_halt_code ms1 := sim_halt Hbound EA3 Hex.
         have Hns1 : forall t' s', ~ mstep tt ms1 t' s'
           := sd_final_nostep DETme _ Hfm.
         case: (star_run_compare DETme EA2 Hstar_m)
           => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
         ++ have [_ E2] := nostep_star_refl Hns1 HS.
            apply: Hnf. rewrite E2. exact: Hfm.
         ++ have [_ E2] := nostep_star_refl Hnsm HS.
            apply: Hnf. rewrite -E2. exact: Hfm.
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: (star_run_compare DETme EA2 Hstar_m)
           => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
         ++ have [msx [Hsil Hstuck]] := stuck_target HS Hnsm.
            exact: (silent_div_dead HbaseT Hrf' HstarR EA3 EA4 EA5
                     (ex_intro _ trem' EA1) Hfs Hsil Hstuck).
         ++ have [_ E2] := nostep_star_refl Hnsm HS.
            have Hst1 : forall s', ~ mstep tt ms1 E0 s'.
            { move=> s'. rewrite E2. exact: Hnsm. }
            exact: (silent_div_dead HbaseT Hrf' HstarR EA3 EA4 EA5
                     (ex_intro _ trem' EA1) Hfs (star_refl _ _ _) Hst1).
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have [t' [sR [HstarR' Hlen [T' ET']]]] :=
        reactive_star_events (L := TSim.t_sem cdeW tpW) Hfr
          ((size t_m).+1).
      have HstarR : star TS.step cdeW s00 t' sR.
      { apply: star_trans; [exact: Hstar0 | exact: HstarR' | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 _ _ _]]]].
         have := f_equal size EA1.
         rewrite size_cat. by lia.
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         right. exists tT.
         split; [exact: (erefl _) | by exists trem'].
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
  +
    have Ei : s_i = msI := Hinit. subst s_i.
    have Hrf' : MDefs.run_fits cdeW tpW t_m := Hrf.
    have Hnsm : forall t' s', ~ mstep tt s_m t' s'
      := sd_final_nostep DETme _ Hfin.
    case: bTx / Hsb
      => [tT sF HstarF HfinF|tT sT1 HstarT Hfs|Tinf Hfr
         |tT sT1 HstarT HnsT HnfT].
    *
      case: sF HstarF HfinF => [[[tmF trF] tpF] ttF] HstarF HfinF.
      have HstarR : star TS.step cdeW s00 tT (tmF, trF, tpF, ttF).
      { apply: star_trans; [exact: Hstar0 | exact: HstarF | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: HfinF => tg [c Hex].
         have Hfm : RSCDefs.final_halt_code ms1 := sim_halt Hbound EA3 Hex.
         have Hns1 : forall t' s', ~ mstep tt ms1 t' s'
           := sd_final_nostep DETme _ Hfm.
         left.
         case: (star_run_compare DETme EA2 Hstar_m)
           => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
         ++ have [Et20 _] := nostep_star_refl Hns1 HS.
            by rewrite /= Et2 Et20 E0_right.
         ++ have [Eu20 _] := nostep_star_refl Hnsm HS.
            by rewrite /= Eu2 Eu20 E0_right.
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         case: (star_run_compare DETme EA2 Hstar_m)
           => [[t2 [Et2 HS]]|[u2 [Eu2 HS]]].
         ++ have [msx [Hsil Hstuck]] := stuck_target HS Hnsm.
            exact: (silent_div_dead HbaseT Hrf' HstarR EA3 EA4 EA5
                     (ex_intro _ trem' EA1) Hfs Hsil Hstuck).
         ++ have [_ E2] := nostep_star_refl Hnsm HS.
            have Hst1 : forall s', ~ mstep tt ms1 E0 s'.
            { move=> s'. rewrite E2. exact: Hnsm. }
            exact: (silent_div_dead HbaseT Hrf' HstarR EA3 EA4 EA5
                     (ex_intro _ trem' EA1) Hfs (star_refl _ _ _) Hst1).
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have [t' [sR [HstarR' Hlen [T' ET']]]] :=
        reactive_star_events (L := TSim.t_sem cdeW tpW) Hfr
          ((size t_m).+1).
      have HstarR : star TS.step cdeW s00 t' sR.
      { apply: star_trans; [exact: Hstar0 | exact: HstarR' | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- exfalso.
         case: HA => [trem' [amap1 [ms1 [EA1 _ _ _]]]].
         have := f_equal size EA1.
         rewrite size_cat. by lia.
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
    *
      have HstarR : star TS.step cdeW s00 tT sT1.
      { apply: star_trans; [exact: Hstar0 | exact: HstarT | by []]. }
      case: (t2me_walk0 HbaseT Hrf' Hstar_m HstarR Hm0 Hh0 Hdsy0) => [HA|HB].
      -- case: HA => [trem' [amap1 [ms1 [EA1 EA2 EA3 EA4 EA5]]]].
         right. exists tT.
         split; [exact: (erefl _) | by exists trem'].
      -- exfalso.
         case: HB
           => [tpref [e [urest [ts_t [ts_next [amap1 [ms1
                [EB1 EB2 EB3 EB4 [EB5 EB6 EB7 EB8]]]]]]]]].
         have Hroot : star TS.step cdeW s00 t_m ts_t by rewrite EB2.
         exact: (boundary_event_dead HbaseT Hrf' Hroot EB4 EB5 EB7 EB8
                  EB6 Hstar_m Hnsm).
Qed.

(* the existential form *)
Corollary t2me_bwd_prefix (m : finpref_behavior) :
  let msI := Merged.initial_state (Definitions.code Wdet)
               (Definitions.prog_buffers Wdet)
               (Definitions.prog_interface Wdet) in
  (forall ts0, TSim.t_initial_base cdeW tpW ts0 ->
     match_stW (amap0 PB) ts0 msI /\
     heap_invW (let '(tm, _, _, _) := ts0 in tm) (Symbolic.mem msI) /\
     mm_dsyncW (amap0 PB) ts0 msI) ->
  does_prefix (RSCDefs.me_sem NC Wdet) m ->
  MDefs.run_fits cdeW tpW (finpref_trace m) ->
  exists beh,
    program_behaves (TSim.t_sem cdeW tpW) beh /\
    (CompCertExtensions.prefix m beh \/
     behavior_improves_finpref beh m).
Proof.
move=> msI Hbridge Hdp Hrf.
have [bT HbT] := @program_behaves_exists (TSim.t_sem cdeW tpW).
exists bT. split; first exact: HbT.
exact: (t2me_bwd_prefix_for Hbridge Hdp Hrf HbT).
Qed.

End Walk.
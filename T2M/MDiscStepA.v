(** * T2M — [disc_inv]-preservation lemmas for the Nop, Label and
    Const cases of [TS.step]. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import T2M.MSig.
Require T2M.MDefs.
Require Import T2M.MDisc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section DiscStepA.

Variable cde : Transitional.code.
Variable MM : Component.id -> seq sv.
Hypothesis HMM : forall c S,
  getm cde c = Some S -> comp_ok (c, 1, 0%Z) S (MM c).
Hypothesis Hcst : forall pc iv r tg c p,
  Transitional.executing cde pc (TrConst iv r) tg c ->
  iv = IPtr p ->
  p = (c, 0, 0%Z) \/
  ((p = (c, 1, 0%Z) \/ p = (c, 1, 1%Z)) /\ (r = R_AUX1 \/ r = R_AUX2)).
Hypothesis Huniq : forall (c : Component.id) (S : TS.tcode) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  getm cde c = Some S ->
  nth_error S m = Some (TrLabel (inl l), t1) ->
  nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.

Local Notation svat := (MDisc.svat MM).
Local Notation asv := (MDisc.asv MM).
Local Notation in_window := (MDisc.in_window MM).
Local Notation sp_of := (MDisc.sp_of MM).
Local Notation topc := (MDisc.topc).
Local Notation topw := (MDisc.topw MM).
Local Notation carry0 := (MDisc.carry0 MM).
Local Notation scrpin := (MDisc.scrpin MM).
Local Notation cap := (MDisc.cap MM).
Local Notation dinv := (MDisc.dinv cde MM).
Local Notation disc_inv := (MDisc.disc_inv cde MM).

Lemma dinv_step_nop :
  forall mem regs pc tg c pct cur chain F cs,
    Transitional.executing cde pc TrNop tg c ->
    Transitional.check_pc cde pc tg ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem regs (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct cur chain F cs Hex Hpc HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  move: Evs => /= [Evv]. subst v'.
  have [w [Ew Hle]] := Hnx isT.
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  exact: (dinv_pcmove HI Ec Ev Ew Hle).
Qed.

Lemma dinv_step_label :
  forall mem regs pc tg c pct l cur chain F cs,
    Transitional.executing cde pc (TrLabel l) tg c ->
    Transitional.check_pc cde pc tg ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem regs (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct l cur chain F cs Hex Hpc HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  move: Evs => /= [Evv]. subst v'.
  have [w [Ew Hle]] := Hnx isT.
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  exact: (dinv_pcmove HI Ec Ev Ew Hle).
Qed.

Lemma dinv_step_const :
  forall mem regs pc tg c pct r iv cur chain F cs,
    Transitional.executing cde pc (TrConst iv r) tg c ->
    Transitional.check_pc cde pc tg ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs
      mem (Transitional.Register.set r (imm_to_val iv) Other regs)
      (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct r iv cur chain F cs Hex Hpc HI.
  have Hex' := Hex.
  have Ecc : Pointer.component pc = c.
  { by case: Hex' => C_code [E _]. }
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  move: Evs => /=.
  case Era: (is_r r R_RA) => //.
  have Hra' : R_RA <> r := is_r_neq' Era.
  case Esp: (is_r r R_SP).
  +
    have HrSP : r = R_SP := is_r_eq Esp.
    case Eph: (sv_ph v) => // -[Evv]. subst v'.
    have [[Eph' Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    subst r.
    have HA1 : R_AUX1 <> R_SP by [].
    have HA2 : R_AUX2 <> R_SP by [].
    have HO1 : R_ONE <> R_SP by [].
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 R_SP).
      -- have -> : r0 = R_SP := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      rewrite (tget_set_neq _ _ _ H2).
      exact: (di_rval HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      rewrite (tget_set_neq _ _ _ HA1).
      apply: (aux_claim_le Eph' Esg Epd Ht1).
      move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      rewrite (tget_set_neq _ _ _ HA2).
      apply: (aux_claim_le Eph' Esg Epd Ht2).
      move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      rewrite (tget_set_neq _ _ _ HO1).
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' Esg Epd => HP.
      exact: (di_prol HI Ev HP).
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph Ec => HP1 HP2.
      by case: (HP2 (erefl _)).
    * move=> w0 b; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> w0 b; rewrite Ew => -[<-]. rewrite Esg Ec => Hb.
      exact: (di_frame HI Ev Hb).
    * move=> w0 b k; rewrite Ew => -[<-]. rewrite Esg Epd Ec => Hb Hk.
      exact: (di_pend HI Ev Hb Hk).
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Eph Esg Epd => HP HPd HK.
      have HRA : R_RA <> R_SP by [].
      rewrite (tget_set_neq _ _ _ HRA).
      apply: (di_ra HI Ev).
      -- by rewrite Eph.
      -- exact: HPd.
      -- exact: HK.
    * exact: (di_mem HI).
    * exact: (di_scrtag HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      case: (sv_sc v) HD => HD /=.
      -- exact: HD.
      -- by rewrite Eph' Eph.
      -- exact: HD.
      -- by [].
    * move=> w0 b; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> c0 A. rewrite Ec => Hc0 HA.
      exact: (di_scrfor HI Hc0 HA).
    * exact: (di_chain HI).
    * move=> i A b0 HA Hb0. rewrite Ec => HcA.
      exact: (di_dist HI HA Hb0 HcA).
    * exact: (di_dist2 HI).
    * exact: (di_fbound HI).
    * exact: (di_f01 HI).
    * exact: (di_nb2 HI).
    * exact: (di_dom HI).
    * exact: (di_level HI).
    * exact: (di_flag HI).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ek HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * move=> i X HX Hnw.
      case: (di_nwshadow HI HX Hnw)
        => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
      { right. exists j, W. by split. }
      left. split; last exact: HPre.
      by rewrite Ec.
    * move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
    * move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
      exact: (di_scr0 HI Hc0 Hg0 Htw).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      rewrite (pend_sig_eq Esg Epd).
      apply: (di_bodycarg HI Ev).
      move: Hekw. by rewrite Eek'.
    * exact: (di_chain2 HI).
  +
    move=> -[Evv]. subst v'.
    have [W1ph W1sg W1pd W1sc W1on]
      := wtaint_fields r (ctaint (c, 1, 0%Z) iv) v.
    have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
      := wone_fields r (cone iv) (wtaint r (ctaint (c, 1, 0%Z) iv) v).
    have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
      := warg_w_fields r
           (wone r (cone iv) (wtaint r (ctaint (c, 1, 0%Z) iv) v)).
    have [[Eph Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    rewrite G1 W2ph W1ph in Eph. rewrite G2 W2sg W1sg in Esg.
    rewrite G3 W2pd W1pd in Epd. rewrite G4 W2sc W1sc in Hsc.
    rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
    rewrite G7 in Hon. rewrite G8 in Eek'.
    have Hg00 : goodu mem F (Ptr (c, 0, 0%Z)).
    { move=> p0 [<-].
      have [F0 _] := di_f01 HI c.
      have [C_code [_ [Eg _]]] := Hex.
      have [cm Hcm] := di_dom HI Eg.
      have Hnb := di_nb2 HI Hcm.
      split=> //.
      exists cm. split=> //=. exact: ltnW Hnb. }
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 r).
      -- have -> : r0 = r := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      case E0: (is_r r0 r).
      -- have Er0 : r0 = r := is_r_eq E0. subst r0.
         rewrite tget_set_eq /=.
         case Eiv: iv => [i|p].
         ++ by move=> p0.
         ++ have [Ep0|[[Ep1|Ep1] Haux]] := Hcst Hex Eiv.
            ** subst p. exact: Hg00.
            ** by case: Haux => Er; subst r;
                 [case: (H3 (erefl _))|case: (H4 (erefl _))].
            ** by case: Haux => Er; subst r;
                 [case: (H3 (erefl _))|case: (H4 (erefl _))].
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rval HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E1: (is_r r R_AUX1).
      -- have Er : r = R_AUX1 := is_r_eq E1. subst r.
         rewrite tget_set_eq /=.
         have Ea1 : sv_a1 (wtaint R_AUX1 (ctaint (c, 1, 0%Z) iv) v)
                    = ctaint (c, 1, 0%Z) iv by [].
         move: Ht1. rewrite Ea1 /t_le.
         case/orP => [/t_eqb_eq Ew1|/t_eqb_eq Ew1]; last first.
         { by rewrite /aux_claim Ew1. }
         rewrite /aux_claim -Ew1.
         case Eiv: iv => [i|p] /=.
         ++ by move=> p0.
         ++ case Es1: (ptr_eqb p (c, 1, 0%Z)) => /=.
            ** by rewrite (ptr_eqb_eq Es1).
            ** case Es2: (ptr_eqb p (Pointer.add (c, 1, 0%Z) 1)) => /=.
               --- by rewrite (ptr_eqb_eq Es2).
               --- have [Ep0|[[Ep1|Ep1] _]] := Hcst Hex Eiv.
                   +++ subst p. exact: Hg00.
                   +++ subst p. by rewrite ptr_eqb_refl in Es1.
                   +++ subst p. exfalso. move: Es2.
                       by rewrite /ptr_eqb /= !PeanoNat.Nat.eqb_refl.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E1)).
         have Ea1 : sv_a1 (wtaint r (ctaint (c, 1, 0%Z) iv) v)
                    = sv_a1 v.
         { rewrite /wtaint E1. by case: (is_r r R_AUX2). }
         move: Ht1. rewrite Ea1 => Ht1.
         apply: (aux_claim_le Eph Esg Epd Ht1).
         move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E2: (is_r r R_AUX2).
      -- have Er : r = R_AUX2 := is_r_eq E2. subst r.
         rewrite tget_set_eq /=.
         have Ea2 : sv_a2 (wtaint R_AUX2 (ctaint (c, 1, 0%Z) iv) v)
                    = ctaint (c, 1, 0%Z) iv by [].
         move: Ht2. rewrite Ea2 /t_le.
         case/orP => [/t_eqb_eq Ew2|/t_eqb_eq Ew2]; last first.
         { by rewrite /aux_claim Ew2. }
         rewrite /aux_claim -Ew2.
         case Eiv: iv => [i|p] /=.
         ++ by move=> p0.
         ++ case Es1: (ptr_eqb p (c, 1, 0%Z)) => /=.
            ** by rewrite (ptr_eqb_eq Es1).
            ** case Es2: (ptr_eqb p (Pointer.add (c, 1, 0%Z) 1)) => /=.
               --- by rewrite (ptr_eqb_eq Es2).
               --- have [Ep0|[[Ep1|Ep1] _]] := Hcst Hex Eiv.
                   +++ subst p. exact: Hg00.
                   +++ subst p. by rewrite ptr_eqb_refl in Es1.
                   +++ subst p. exfalso. move: Es2.
                       by rewrite /ptr_eqb /= !PeanoNat.Nat.eqb_refl.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E2)).
         have Ea2 : sv_a2 (wtaint r (ctaint (c, 1, 0%Z) iv) v)
                    = sv_a2 v.
         { rewrite /wtaint E2.
           by case: (is_r r R_AUX1). }
         move: Ht2. rewrite Ea2 => Ht2.
         apply: (aux_claim_le Eph Esg Epd Ht2).
         move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      have Hone' : sv_one (wone r (cone iv)
                     (wtaint r (ctaint (c, 1, 0%Z) iv) v)) = true
        := o_le_true Hon Hon1.
      case E0: (is_r r R_ONE).
      -- have Er : r = R_ONE := is_r_eq E0. subst r.
         rewrite tget_set_eq /=.
         move: Hone'. rewrite /wone /= => Hone'.
         case Eiv: iv Hone' => [z|p] //= Hone'.
         by move/Z.eqb_eq: Hone' => ->.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E0)).
         apply: (di_one HI Ev).
         move: Hone'. by rewrite /wone E0 W1on.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP.
      exact: (di_prol HI Ev HP).
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
      rewrite (tget_set_neq _ _ _ (is_r_neq' Esp)).
      exact: (di_spprol HI Ev HP).
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph Ec => HP1 HP2.
      exact: (di_body HI Ev HP1 HP2).
    * move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
      rewrite (tget_set_neq _ _ _ (is_r_neq' Esp)).
      exact: (di_sp HI Ev HP Hb).
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
      rewrite (tget_set_neq _ _ _ (is_r_neq' Esp)).
      exact: (di_sptear HI Ev HP).
    * move=> w0 b; rewrite Ew => -[<-]. rewrite Esg Ec => Hb.
      exact: (di_frame HI Ev Hb).
    * move=> w0 b k; rewrite Ew => -[<-]. rewrite Esg Epd Ec => Hb Hk.
      exact: (di_pend HI Ev Hb Hk).
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP HPd HK.
      rewrite (tget_set_neq _ _ _ Hra').
      exact: (di_ra HI Ev HP HPd HK).
    * exact: (di_mem HI).
    * exact: (di_scrtag HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ (is_r_neq' Esp)).
      exact: (scr_claim_le Eph Hsc (di_scr HI Ev)).
    * move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
      exact: (di_post HI Ev HP Hb).
    * move=> c0 A. rewrite Ec => Hc0 HA.
      exact: (di_scrfor HI Hc0 HA).
    * exact: (di_chain HI).
    * move=> i A b0 HA Hb0. rewrite Ec => HcA.
      exact: (di_dist HI HA Hb0 HcA).
    * exact: (di_dist2 HI).
    * exact: (di_fbound HI).
    * exact: (di_f01 HI).
    * exact: (di_nb2 HI).
    * exact: (di_dom HI).
    * exact: (di_level HI).
    * exact: (di_flag HI).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ek HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * move=> i X HX Hnw.
      case: (di_nwshadow HI HX Hnw)
        => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
      { right. exists j, W. by split. }
      left. split; last exact: HPre.
      by rewrite Ec.
    * move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
    * move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
      exact: (di_scr0 HI Hc0 Hg0 Htw).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      rewrite (pend_sig_eq Esg Epd).
      apply: (di_bodycarg HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * exact: (di_chain2 HI).
Qed.

End DiscStepA.

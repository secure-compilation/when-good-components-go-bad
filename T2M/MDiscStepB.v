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

Section DiscStepB.

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

Lemma dinv_step_binop :
  forall mem regs pc tg c pct r1 r2 r3 op cur chain F cs,
    Transitional.executing cde pc (TrBinOp op r1 r2 r3) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    tvtag (Transitional.Register.get r2 regs) = Other ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem
       (Transitional.Register.set r3
         (eval_binop op (Transitional.val (Transitional.Register.get r1 regs))
                        (Transitional.val (Transitional.Register.get r2 regs)))
         Other regs)
       (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct r1 r2 r3 op cur chain F cs Hex Hpc Htg1 Htg2
         HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  move: Evs => /=.
  case Eop: op => /=.
  +
    case Eph: (sv_ph v) => //.
    case Etr: [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
                & sv_one v]; last first.
    { move=> Hg. exact: (dinv_binop_gen Values.Add HI Ev Ew Hle Hg). }
    case Epd0: (sv_pend v) => [k|] //=; last by case: (sv_sc v).
    have Hsplit : forall P : Prop,
        (sc_eqb (sv_sc v) SCpark = false ->
         v' = SV PBody (rcons (sv_sig v) k) None
                (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v)
                (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v)
                (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v) -> P) ->
        (match sv_sc v with
         | SCpark => None
         | _ => Some (SV PBody (rcons (sv_sig v) k) None
                        (if t_eqb (sv_a1 v) ASp then ADead
                         else sv_a1 v)
                        (if t_eqb (sv_a2 v) ASp then ADead
                         else sv_a2 v)
                        (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
         end = Some v' -> P).
    { move=> P HP.
      by case: (sv_sc v) HP => HP // -[E]; apply: HP. }
    apply: Hsplit => Hnp Evv. subst v'.
    case/and4P: Etr => E1s E2o E3s Eone.
    have Er1 : r1 = R_SP := is_r_eq E1s.
    have Er2 : r2 = R_ONE := is_r_eq E2o.
    have Er3 : r3 = R_SP := is_r_eq E3s.
    subst r1 r2 r3.
    have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
    have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
    have [b [Hcur HbF]] := di_body HI Ev Hnp1 Hnp2.
    have Ecc : Pointer.component pc = c.
    { by case: Hex => C_code [E _]. }
    have Hsp := di_sp HI Ev Eph Hcur.
    have Hone1 := di_one HI Ev Eone.
    have Ec : Pointer.component (Pointer.inc pc)
              = Pointer.component pc.
    { by case: (pc) => [[c0 b0] o0]. }
    rewrite Hsp Hone1 /=.
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
    have Hpend := di_pend HI Ev Hcur Epd0.
    have HA1sp : R_AUX1 <> R_SP by [].
    have HA2sp : R_AUX2 <> R_SP by [].
    have HO1sp : R_ONE <> R_SP by [].
    have HRAsp : R_RA <> R_SP by [].
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 R_SP).
      -- have -> : r0 = R_SP := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      rewrite (tget_set_neq _ _ _ H2).
      exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA1sp).
      move: Ht1.
      case Ea1v: (t_eqb (sv_a1 v) ASp) => Ht1.
      -- move: Ht1. rewrite /t_le.
         case/orP => /t_eqb_eq E1w.
         ++ by rewrite /aux_claim -E1w.
         ++ by rewrite /aux_claim E1w.
      -- move: Ht1. rewrite /t_le.
         case/orP => /t_eqb_eq E1w; last first.
         { by rewrite /aux_claim E1w. }
         rewrite -E1w.
         apply: (aux_claim_nsp (v := v)).
         { move=> E. by rewrite E in Ea1v. }
         move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA2sp).
      move: Ht2.
      case Ea2v: (t_eqb (sv_a2 v) ASp) => Ht2.
      -- move: Ht2. rewrite /t_le.
         case/orP => /t_eqb_eq E2w.
         ++ by rewrite /aux_claim -E2w.
         ++ by rewrite /aux_claim E2w.
      -- move: Ht2. rewrite /t_le.
         case/orP => /t_eqb_eq E2w; last first.
         { by rewrite /aux_claim E2w. }
         rewrite -E2w.
         apply: (aux_claim_nsp (v := v)).
         { move=> E. by rewrite E in Ea2v. }
         move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      rewrite (tget_set_neq _ _ _ HO1sp).
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
      by exists b.
    * move=> w0 b0; rewrite Ew => -[<-] _.
      rewrite Hcur => -[<-].
      rewrite tget_set_eq /= Ec Esg /= size_rcons.
      by rewrite Nat2Z.inj_succ Z.add_1_r.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b0; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Esg Ec => j k0.
      rewrite nth_error_rcons.
      case Hj: (j < size (sv_sig v)).
      -- move=> Hk0.
         have HF := di_frame HI Ev Hcur.
         exact: (HF j k0 Hk0).
      -- case Ej: (j == size (sv_sig v)) => // -[Ek0]. subst k0.
         move/eqP: Ej => Ej. subst j.
         have [cv [tg0 [Hcell Hrow]]] := Hpend.
         exists cv, tg0. by split.
    * move=> w0 b0 k0; rewrite Ew => -[<-]. by rewrite Epd'.
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Esg Epd' => HP HPd HK.
      case Ek: (c3_eqb k CRa).
      -- move/c3_eqb_eq: Ek => Ek. subst k.
         case: (HK (size (sv_sig v))).
         by rewrite nth_error_rcons ltnn eqxx.
      -- rewrite (tget_set_neq _ _ _ HRAsp).
         apply: (di_ra HI Ev).
         ++ by rewrite Eph.
         ++ rewrite Epd0 => -[E].
            by rewrite E c3_eqb_refl in Ek.
         ++ move=> j E. apply: (HK j).
            by rewrite nth_error_rcons (nth_error_size E).
    * exact: (di_mem HI).
    * exact: (di_scrtag HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      by case: (sv_sc v) HD Hnp => HD Hnp0 //=.
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
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
      by rewrite -Eek'.
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
      by rewrite -Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      rewrite (pend_sig_none Epd') Esg -(pend_sig_some Epd0).
      apply: (di_bodycarg HI Ev).
      by rewrite -Eek'.
    * exact: (di_chain2 HI).
  +
    case Eph: (sv_ph v) => //.
    case Etr: [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
                & sv_one v]; last first.
    { move=> Hg. exact: (dinv_binop_gen Values.Minus HI Ev Ew Hle Hg). }
    case Epd0: (sv_pend v) => [k0|]; first by case: (sv_sc v).
    case Erev: (rev (sv_sig v)) => [|k rest]; first by case: (sv_sc v).
    have Hsplit : forall P : Prop,
        (sc_eqb (sv_sc v) SCpark = false ->
         v' = SV PBody (rev rest) (Some k)
                (if t_eqb (sv_a1 v) ASp then ADead else sv_a1 v)
                (if t_eqb (sv_a2 v) ASp then ADead else sv_a2 v)
                (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v) -> P) ->
        (match sv_sc v with
         | SCpark => None
         | _ => Some (SV PBody (rev rest) (Some k)
                        (if t_eqb (sv_a1 v) ASp then ADead
                         else sv_a1 v)
                        (if t_eqb (sv_a2 v) ASp then ADead
                         else sv_a2 v)
                        (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
         end = Some v' -> P).
    { move=> P HP.
      by case: (sv_sc v) HP => HP // -[E]; apply: HP. }
    apply: Hsplit => Hnp Evv. subst v'.
    case/and4P: Etr => E1s E2o E3s Eone.
    have Er1 : r1 = R_SP := is_r_eq E1s.
    have Er2 : r2 = R_ONE := is_r_eq E2o.
    have Er3 : r3 = R_SP := is_r_eq E3s.
    subst r1 r2 r3.
    have Esig : sv_sig v = rcons (rev rest) k.
    { by rewrite -(revK (sv_sig v)) Erev rev_cons. }
    have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
    have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
    have [b [Hcur HbF]] := di_body HI Ev Hnp1 Hnp2.
    have Ecc : Pointer.component pc = c.
    { by case: Hex => C_code [E _]. }
    have Hsp := di_sp HI Ev Eph Hcur.
    have Hone1 := di_one HI Ev Eone.
    have Ec : Pointer.component (Pointer.inc pc)
              = Pointer.component pc.
    { by case: (pc) => [[c0 b0] o0]. }
    rewrite Hsp Hone1 /=.
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
    have HA1sp : R_AUX1 <> R_SP by [].
    have HA2sp : R_AUX2 <> R_SP by [].
    have HO1sp : R_ONE <> R_SP by [].
    have HRAsp : R_RA <> R_SP by [].
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 R_SP).
      -- have -> : r0 = R_SP := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      rewrite (tget_set_neq _ _ _ H2).
      exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA1sp).
      case Ea1v: (t_eqb (sv_a1 v) ASp).
      -- move: Ht1. rewrite Ea1v /t_le.
         case/orP => /t_eqb_eq E1w.
         ++ by rewrite /aux_claim -E1w.
         ++ by rewrite /aux_claim E1w.
      -- move: Ht1. rewrite Ea1v /t_le.
         case/orP => /t_eqb_eq E1w; last first.
         { by rewrite /aux_claim E1w. }
         rewrite -E1w.
         apply: (aux_claim_nsp (v := v)).
         { move=> E. by rewrite E in Ea1v. }
         move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA2sp).
      case Ea2v: (t_eqb (sv_a2 v) ASp).
      -- move: Ht2. rewrite Ea2v /t_le.
         case/orP => /t_eqb_eq E2w.
         ++ by rewrite /aux_claim -E2w.
         ++ by rewrite /aux_claim E2w.
      -- move: Ht2. rewrite Ea2v /t_le.
         case/orP => /t_eqb_eq E2w; last first.
         { by rewrite /aux_claim E2w. }
         rewrite -E2w.
         apply: (aux_claim_nsp (v := v)).
         { move=> E. by rewrite E in Ea2v. }
         move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      rewrite (tget_set_neq _ _ _ HO1sp).
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
      by exists b.
    * move=> w0 b0; rewrite Ew => -[<-] _.
      rewrite Hcur => -[<-].
      rewrite tget_set_eq /= Ec Esg.
      rewrite Esig size_rcons.
      have -> : (Z.of_nat (size (rev rest)).+1 - 1)%Z
                = Z.of_nat (size (rev rest)) by lia.
      by [].
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b0; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Esg Ec => j k1 Hk1.
      have HF := di_frame HI Ev Hcur.
      have Hjlt : j < size (rev rest) := nth_error_size Hk1.
      have Hk1' : nth_error (sv_sig v) j = Some k1.
      { by rewrite Esig nth_error_rcons Hjlt. }
      exact: (HF j k1 Hk1').
    * move=> w0 b0 k1; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Epd' => -[<-].
      rewrite Esg Ec.
      have HF := di_frame HI Ev Hcur.
      have Hk : nth_error (sv_sig v) (size (rev rest)) = Some k.
      { by rewrite Esig nth_error_rcons ltnn eqxx. }
      have [cv [tg0 [Hcell Hrow]]] := HF (size (rev rest)) k Hk.
      exists cv, tg0. by split.
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Esg Epd' => HP HPd HK.
      rewrite (tget_set_neq _ _ _ HRAsp).
      apply: (di_ra HI Ev).
      -- by rewrite Eph.
      -- by rewrite Epd0.
      -- move=> j E.
         move: E. rewrite Esig nth_error_rcons.
         case Hj: (j < size (rev rest)); first by apply: (HK j).
         case Ej: (j == size (rev rest)).
         ++ move=> -[E']. by apply: HPd; rewrite E'.
         ++ by [].
    * exact: (di_mem HI).
    * exact: (di_scrtag HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      by case: (sv_sc v) HD Hnp => HD Hnp0 //=.
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
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
      by rewrite -Eek'.
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
      by rewrite -Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      rewrite (pend_sig_some Epd') Esg -Esig -(pend_sig_none Epd0).
      apply: (di_bodycarg HI Ev).
      by rewrite -Eek'.
    * exact: (di_chain2 HI).
  +
    case Eph: (sv_ph v) => // Hg.
    exact: (dinv_binop_gen Values.Mul HI Ev Ew Hle Hg).
  +
    case Eph: (sv_ph v) => // Hg.
    exact: (dinv_binop_gen Values.Eq HI Ev Ew Hle Hg).
  +
    case Eph: (sv_ph v) => // Hg.
    exact: (dinv_binop_gen Values.Leq HI Ev Ew Hle Hg).
Qed.

End DiscStepB.

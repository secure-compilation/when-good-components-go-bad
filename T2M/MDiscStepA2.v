(** * T2M — [disc_inv]-preservation lemmas for the Mov and Bnz
    cases of [TS.step]. *)

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

Section DiscStepA2.

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

Lemma dinv_step_mov :
  forall mem regs pc tg c pct r1 r2 cur chain F cs,
    Transitional.executing cde pc (TrMov r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem
       (Transitional.Register.set r1
         (Transitional.val (Transitional.Register.get r1 regs))
         (moved_tag (tvtag (Transitional.Register.get r1 regs)))
         (Transitional.Register.set r2
            (Transitional.val (Transitional.Register.get r1 regs))
            (tvtag (Transitional.Register.get r1 regs)) regs))
       (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct r1 r2 cur chain F cs Hex Hpc HI.
  have Hex' := Hex.
  have Ecc : Pointer.component pc = c.
  { by case: Hex' => C_code [E _]. }
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  move: Evs => /=.
  case E2s: (is_r r2 R_SP) => //=.
  case E2r: (is_r r2 R_RA) => //=.
  case Esp1: (is_r r1 R_SP).
  +
    case Eph: (sv_ph v) => //.
    case E21: (is_r r2 R_AUX1) => // -[Evv]. subst v'.
    have Er1 : r1 = R_SP := is_r_eq Esp1.
    have Er2 : r2 = R_AUX1 := is_r_eq E21.
    subst r1 r2.
    have [[Eph' Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd Ht1 Ht2 Hsc Hon.
    have [Hcur [Hsig Hpend]] := di_prol HI Ev (or_introl Eph).
    have Hsp0 : Transitional.val (Transitional.Register.get R_SP regs)
                = carry0 chain := di_spprol HI Ev Eph.
    have Etv : tvtag (Transitional.Register.get R_SP regs) = Other.
    { by apply: (di_rtag HI). }
    rewrite Etv /=.
    constructor.
    * move=> r0 Hr0.
      rewrite get_write2.
      by case: (is_r r0 R_SP || is_r r0 R_AUX1) => //=;
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      rewrite get_write2.
      case E0: (is_r r0 R_SP || is_r r0 R_AUX1) => /=.
      -- case/orP: E0 => E0.
         ++ by case: (H2 (is_r_eq E0)).
         ++ by case: (H3 (is_r_eq E0)).
      -- exact: (di_rval HI).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite get_write2 orbT /=.
      move: Ht1. rewrite /t_le.
      case/orP => [/t_eqb_eq Ew1|/t_eqb_eq Ew1]; last first.
      { by rewrite /aux_claim Ew1. }
      rewrite /aux_claim -Ew1 Eph'.
      exact: Hsp0.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      move: Ht2. rewrite /t_le.
      case/orP => /t_eqb_eq Ew2.
      -- by rewrite /aux_claim -Ew2.
      -- by rewrite /aux_claim Ew2.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      rewrite get_write2 /=.
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-] _.
      by rewrite Esg Epd Hsig Hpend Hcur.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP1 HP2.
      by case: (HP2 (erefl _)).
    * move=> w0 b; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b; rewrite Ew => -[<-]. by rewrite Hcur.
    * move=> w0 b k; rewrite Ew => -[<-]. by rewrite Hcur.
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Esg Epd => HP HPd HK.
      rewrite get_write2.
      have -> : is_r R_RA R_SP || is_r R_RA R_AUX1 = false by [].
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
      -- by rewrite Eph'.
      -- exact: HD.
      -- by [].
    * move=> w0 b; rewrite Ew => -[<-]. by rewrite Eph'.
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
  +
    case Edead: (t_eqb (rtaint v r1) ADead) => //.
    case Earg: (is_r r1 R_ARG && ~~ sv_arg v) => //.
    have E1r : is_r r1 R_RA = false.
    { case E: (is_r r1 R_RA) => //.
      move: Edead. by rewrite (is_r_eq E) /rtaint /=. }
    have Hclaim := rtaint_claim HI Ev Esp1 E1r.
    have Etv : tvtag (Transitional.Register.get r1 regs) = Other.
    { apply: (di_rtag HI). exact: is_r_neq E1r. }
    rewrite Etv /=.
    case E2a: (is_r r2 R_AUX1 || is_r r2 R_AUX2).
    *
      move=> -[Evv]. subst v'.
      case/orP: E2a => E2x; rewrite (is_r_eq E2x) in Hle *.
      --
         have [[Eph Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         have [Wph Wsg Wpd Wsc Won]
           := wtaint_fields R_AUX1 (rtaint v r1) v.
         rewrite Wph in Eph. rewrite Wsg in Esg. rewrite Wpd in Epd.
         rewrite Wsc in Hsc.
         apply: (dinv_regw HI Ev Ew Hle Wph Wsg Wpd Wsc
                   (wtaint_ek _ _ _)).
         ++ move=> Hon1.
            have EO : Transitional.val (Transitional.Register.get
                        R_ONE (Transitional.Register.set r1
                          (Transitional.val
                             (Transitional.Register.get r1 regs))
                          Other
                          (Transitional.Register.set R_AUX1
                             (Transitional.val
                                (Transitional.Register.get r1 regs))
                             Other regs)))
                      = Transitional.val
                          (Transitional.Register.get R_ONE regs).
            { rewrite get_write2.
              case E: (is_r R_ONE r1) => /=.
              - by rewrite -(is_r_eq E).
              - by []. }
            rewrite EO.
            apply: (di_one HI Ev).
            move: Hon1. by rewrite Won.
         ++ rewrite get_write2.
            have -> : is_r R_RA r1 || is_r R_RA R_AUX1 = false.
            { rewrite {2}/is_r /= orbF.
              case E: (is_r R_RA r1) => //.
              by rewrite -(is_r_eq E) in E1r. }
            by [].
         ++ rewrite get_write2.
            have -> : is_r R_SP r1 || is_r R_SP R_AUX1 = false.
            { rewrite {2}/is_r /= orbF.
              case E: (is_r R_SP r1) => //.
              by rewrite -(is_r_eq E) in Esp1. }
            by [].
         ++ move=> r0 Hr0. rewrite get_write2.
            by case: (is_r r0 r1 || is_r r0 R_AUX1) => //=;
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4. rewrite get_write2.
            case E0: (is_r r0 r1 || is_r r0 R_AUX1) => /=.
            ** case/orP: E0 => E0; last by case: (H3 (is_r_eq E0)).
               rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
               exact: (di_rval HI H1 H2 H3 H4).
            ** exact: (di_rval HI H1 H2 H3 H4).
         ++ rewrite get_write2 orbT /=.
            have Ea1 : sv_a1 (wtaint R_AUX1 (rtaint v r1) v)
                       = rtaint v r1 by [].
            move: Ht1. rewrite Ea1 => Ht1.
            apply: (aux_claim_le Eph Esg Epd Ht1).
            exact: Hclaim.
         ++ have EA2 : Transitional.val (Transitional.Register.get
                         R_AUX2 (Transitional.Register.set r1
                           (Transitional.val
                              (Transitional.Register.get r1 regs))
                           Other
                           (Transitional.Register.set R_AUX1
                              (Transitional.val
                                 (Transitional.Register.get r1 regs))
                              Other regs)))
                       = Transitional.val
                           (Transitional.Register.get R_AUX2 regs).
            { rewrite get_write2.
              case E: (is_r R_AUX2 r1) => /=.
              - by rewrite -(is_r_eq E).
              - by []. }
            rewrite EA2.
            have Ea2 : sv_a2 (wtaint R_AUX1 (rtaint v r1) v)
                       = sv_a2 v by [].
            move: Ht2. rewrite Ea2 => Ht2.
            apply: (aux_claim_le Eph Esg Epd Ht2).
            exact: (di_a2 HI Ev).
      --
         have [[Eph Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         have [Wph Wsg Wpd Wsc Won]
           := wtaint_fields R_AUX2 (rtaint v r1) v.
         rewrite Wph in Eph. rewrite Wsg in Esg. rewrite Wpd in Epd.
         rewrite Wsc in Hsc.
         apply: (dinv_regw HI Ev Ew Hle Wph Wsg Wpd Wsc
                   (wtaint_ek _ _ _)).
         ++ move=> Hon1.
            have EO : Transitional.val (Transitional.Register.get
                        R_ONE (Transitional.Register.set r1
                          (Transitional.val
                             (Transitional.Register.get r1 regs))
                          Other
                          (Transitional.Register.set R_AUX2
                             (Transitional.val
                                (Transitional.Register.get r1 regs))
                             Other regs)))
                      = Transitional.val
                          (Transitional.Register.get R_ONE regs).
            { rewrite get_write2.
              case E: (is_r R_ONE r1) => /=.
              - by rewrite -(is_r_eq E).
              - by []. }
            rewrite EO.
            apply: (di_one HI Ev).
            move: Hon1. by rewrite Won.
         ++ rewrite get_write2.
            have -> : is_r R_RA r1 || is_r R_RA R_AUX2 = false.
            { rewrite {2}/is_r /= orbF.
              case E: (is_r R_RA r1) => //.
              by rewrite -(is_r_eq E) in E1r. }
            by [].
         ++ rewrite get_write2.
            have -> : is_r R_SP r1 || is_r R_SP R_AUX2 = false.
            { rewrite {2}/is_r /= orbF.
              case E: (is_r R_SP r1) => //.
              by rewrite -(is_r_eq E) in Esp1. }
            by [].
         ++ move=> r0 Hr0. rewrite get_write2.
            by case: (is_r r0 r1 || is_r r0 R_AUX2) => //=;
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4. rewrite get_write2.
            case E0: (is_r r0 r1 || is_r r0 R_AUX2) => /=.
            ** case/orP: E0 => E0; last by case: (H4 (is_r_eq E0)).
               rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
               exact: (di_rval HI H1 H2 H3 H4).
            ** exact: (di_rval HI H1 H2 H3 H4).
         ++ have EA1 : Transitional.val (Transitional.Register.get
                         R_AUX1 (Transitional.Register.set r1
                           (Transitional.val
                              (Transitional.Register.get r1 regs))
                           Other
                           (Transitional.Register.set R_AUX2
                              (Transitional.val
                                 (Transitional.Register.get r1 regs))
                              Other regs)))
                       = Transitional.val
                           (Transitional.Register.get R_AUX1 regs).
            { rewrite get_write2.
              case E: (is_r R_AUX1 r1) => /=.
              - by rewrite -(is_r_eq E).
              - by []. }
            rewrite EA1.
            have Ea1 : sv_a1 (wtaint R_AUX2 (rtaint v r1) v)
                       = sv_a1 v by [].
            move: Ht1. rewrite Ea1 => Ht1.
            apply: (aux_claim_le Eph Esg Epd Ht1).
            exact: (di_a1 HI Ev).
         ++ rewrite get_write2 orbT /=.
            have Ea2 : sv_a2 (wtaint R_AUX2 (rtaint v r1) v)
                       = rtaint v r1 by [].
            move: Ht2. rewrite Ea2 => Ht2.
            apply: (aux_claim_le Eph Esg Epd Ht2).
            exact: Hclaim.
    *
      case Eau: (t_eqb (rtaint v r1) AU) => // -[Evv]. subst v'.
      have [[Vph Vsg Vpd] [Vsc Va1 Va2]] := wone_fields r2 false v.
      have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
        := warg_w_fields r2 (wone r2 false v).
      have [[Eph Esg Epd Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
      rewrite G1 Vph in Eph. rewrite G2 Vsg in Esg.
      rewrite G3 Vpd in Epd. rewrite G4 Vsc in Hsc.
      rewrite G5 Va1 in Ht1. rewrite G6 Va2 in Ht2.
      rewrite G7 in Hon. rewrite G8 in Eek'.
      move/negbT: E2a. rewrite negb_or => /andP [E2a1 E2a2].
      have Hgood : goodu mem F
        (Transitional.val (Transitional.Register.get r1 regs)).
      { move: Hclaim. by rewrite (t_eqb_eq Eau). }
      apply: (dinv_regw HI Ev Ew Hle (etrans G1 Vph) (etrans G2 Vsg)
                (etrans G3 Vpd) (etrans G4 Vsc)
                (etrans G8 (wone_ek _ _ _))).
      -- move=> Hon1.
         move: Hon1. rewrite G7 /wone.
         case E1o: (is_r r2 R_ONE) => //= Hon1.
         have E1o' : is_r R_ONE r2 = false.
         { apply: is_r_false => E.
           by case: (is_r_neq E1o (esym E)). }
         have EO : Transitional.val (Transitional.Register.get
                     R_ONE (Transitional.Register.set r1
                       (Transitional.val
                          (Transitional.Register.get r1 regs))
                       Other
                       (Transitional.Register.set r2
                          (Transitional.val
                             (Transitional.Register.get r1 regs))
                          Other regs)))
                   = Transitional.val
                       (Transitional.Register.get R_ONE regs).
         { rewrite get_write2 E1o' orbF.
           case E: (is_r R_ONE r1) => /=.
           - by rewrite -(is_r_eq E).
           - by []. }
         rewrite EO.
         exact: (di_one HI Ev Hon1).
      -- rewrite get_write2.
         have -> : is_r R_RA r1 || is_r R_RA r2 = false.
         { case E: (is_r R_RA r1) => /=.
           - by rewrite -(is_r_eq E) in E1r.
           - case E': (is_r R_RA r2) => //.
             by rewrite -(is_r_eq E') in E2r. }
         by [].
      -- rewrite get_write2.
         have -> : is_r R_SP r1 || is_r R_SP r2 = false.
         { case E: (is_r R_SP r1) => /=.
           - by rewrite -(is_r_eq E) in Esp1.
           - case E': (is_r R_SP r2) => //.
             by rewrite -(is_r_eq E') in E2s. }
         by [].
      -- move=> r0 Hr0. rewrite get_write2.
         by case: (is_r r0 r1 || is_r r0 r2) => //=;
            exact: (di_rtag HI).
      -- move=> r0 H1 H2 H3 H4. rewrite get_write2.
         by case: (is_r r0 r1 || is_r r0 r2) => //=;
            exact: (di_rval HI H1 H2 H3 H4).
      -- have EA1 : Transitional.val (Transitional.Register.get
                      R_AUX1 (Transitional.Register.set r1
                        (Transitional.val
                           (Transitional.Register.get r1 regs))
                        Other
                        (Transitional.Register.set r2
                           (Transitional.val
                              (Transitional.Register.get r1 regs))
                           Other regs)))
                    = Transitional.val
                        (Transitional.Register.get R_AUX1 regs).
         { rewrite get_write2.
           have -> : is_r R_AUX1 r2 = false.
           { case E: (is_r R_AUX1 r2) => //.
             by rewrite -(is_r_eq E) in E2a1. }
           rewrite orbF.
           case E: (is_r R_AUX1 r1) => /=.
           - by rewrite -(is_r_eq E).
           - by []. }
         rewrite EA1.
         apply: (aux_claim_le Eph Esg Epd Ht1).
         exact: (di_a1 HI Ev).
      -- have EA2 : Transitional.val (Transitional.Register.get
                      R_AUX2 (Transitional.Register.set r1
                        (Transitional.val
                           (Transitional.Register.get r1 regs))
                        Other
                        (Transitional.Register.set r2
                           (Transitional.val
                              (Transitional.Register.get r1 regs))
                           Other regs)))
                    = Transitional.val
                        (Transitional.Register.get R_AUX2 regs).
         { rewrite get_write2.
           have -> : is_r R_AUX2 r2 = false.
           { case E: (is_r R_AUX2 r2) => //.
             by rewrite -(is_r_eq E) in E2a2. }
           rewrite orbF.
           case E: (is_r R_AUX2 r1) => /=.
           - by rewrite -(is_r_eq E).
           - by []. }
         rewrite EA2.
         apply: (aux_claim_le Eph Esg Epd Ht2).
         exact: (di_a2 HI Ev).
Qed.

Lemma dinv_step_bnznz :
  forall mem regs pc tg c pct pc' r l vz cur chain F cs,
    Transitional.executing cde pc (TrBnz r l) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r regs) = Other ->
    Transitional.val (Transitional.Register.get r regs) = Int vz ->
    (vz <> 0)%Z ->
    Transitional.find_label_in_comp cde c l = Some pc' ->
    Transitional.check_pc_jump cde tg pc' c ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem regs pc' pct.
Proof.
  move=> mem regs pc tg c pct pc' r l vz cur chain F cs
         Hex Hpc Htag Hval Hnz Hfl Hcj HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have Evv : v' = v.
  { move: Evs => /=.
    by case: (sv_ph v) => //; case: (sv_pend v) => // -[]. }
  subst v'.
  have [Ec' [w [Ew Hle]]] := bnz_target HMM Huniq Hex Ev Hfl.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  rewrite -Ecc in Ec'.
  exact: (dinv_pcmove HI Ec' Ev Ew Hle).
Qed.

Lemma dinv_step_bnzz :
  forall mem regs pc tg c pct r l cur chain F cs,
    Transitional.executing cde pc (TrBnz r l) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r regs) = Other ->
    Transitional.val (Transitional.Register.get r regs) = Int 0 ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem regs (Pointer.inc pc) pct.
Proof.
  move=> mem regs pc tg c pct r l cur chain F cs Hex Hpc Htag Hval HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have Evv : v' = v.
  { move: Evs => /=.
    by case: (sv_ph v) => //; case: (sv_pend v) => // -[]. }
  subst v'.
  have [w [Ew Hle]] := Hnx isT.
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  exact: (dinv_pcmove HI Ec Ev Ew Hle).
Qed.

End DiscStepA2.

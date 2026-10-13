(** * T2M — [disc_inv]-preservation lemmas for the Store, Load, Jal,
    Jump, JumpRet and Call cases of [TS.step]. *)

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

Section DiscStepC.

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

Lemma dinv_step_store :
  forall mem mem' regs pc tg c pct ptr r1 r2 vt cur chain F cs,
    Transitional.executing cde pc (TrStore r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Register.get_tag r2 regs = Some vt ->
    Transitional.Memory.store mem ptr
      (Transitional.Register.get r2 regs,
       {| vtag := vt; color := c; entry := None; is_code := false |})
      = Some mem' ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem'
       (Transitional.Register.set r2
         (Transitional.val (Transitional.Register.get r2 regs))
         (moved_tag vt) regs)
       (Pointer.inc pc) pct.
Proof.
  move=> mem mem' regs pc tg c pct ptr r1 r2 vt cur chain F cs
         Hex Hpc Htg1 Hval1 Hcptr Hgt2 Hstore HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have [cm [chunk [chunk' [Hcm Hchunk Hoff Hupd Emem']]]]
    := store_shape Hstore.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  have Evt : vt = tvtag (Transitional.Register.get r2 regs).
  { move: Hgt2.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm regs _) => [tv|] // [<-]. }
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  case Epd0: (sv_pend v) => [k0|] //.
  case E1sp: (is_r r1 R_SP).
  +
    case Epk: (pushclass v r2) => [k|] // -[Evv]. subst v'.
    have Er1 : r1 = R_SP := is_r_eq E1sp.
    subst r1.
    have Hpk : [\/ [/\ k = CRa, r2 = R_RA, nocra (sv_sig v)
                     & if sv_ek v
                       then nth_error (sv_sig v) 1 = Some CArg
                       else sv_sig v = [:: CSp; CSp]],
                  [/\ k = CSp, r2 = R_AUX1, sv_a1 v = ASp
                    & sv_sig v = [::] \/ sv_sig v = [:: CSp]],
                  [/\ k = CU, is_r r2 R_RA = false,
                      is_r r2 R_SP = false & rtaint v r2 = AU]
                | [/\ k = CArg, r2 = R_ARG & nocarg (sv_sig v)]].
    { move: Epk. rewrite /pushclass.
      case E2ra: (is_r r2 R_RA).
      - case Enc: (_ && _) => // -[<-].
        case/andP: Enc => Enc Egt.
        apply: Or41. split=> //.
        + exact: is_r_eq E2ra.
        + case: (sv_ek v) Egt => Egt.
          * exact: opt_eqb_eq Egt.
          * exact: cseq_eqb_eq Egt.
      - case E2sp: (is_r r2 R_SP) => //.
        case Ecsp: ([&& _, _ & _]).
        + move=> -[<-].
          case/and3P: Ecsp => Eaux1 /t_eqb_eq Easp /orP Esg01.
          apply: Or42.
          split=> //; first exact: is_r_eq Eaux1.
          by case: Esg01 => /cseq_eqb_eq E3; [left|right].
        + case E2arg: (is_r r2 R_ARG).
          * have Er2 : r2 = R_ARG := is_r_eq E2arg. subst r2.
            case Earg: (sv_arg v).
            -- move=> -[<-].
               apply: Or43. split=> //.
               by rewrite /rtaint /= Earg.
            -- case Enca: (nocarg (sv_sig v)) => // -[<-].
               apply: Or44. by split.
          * case Eau2: (rtaint v r2) => // -[<-].
            apply: Or43. by split=> //. }
    have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
    have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
    have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
    have Hsp := di_sp HI Ev Eph Hcur.
    have Eptr : ptr
      = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
    { move: Hval1. rewrite Hsp. by move=> [->]. }
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
    have Hr2nsp : R_SP <> r2.
    { case: Hpk => [[_ -> _ _]|[_ -> _ _]|[_ _ E _]|[_ -> _]] //.
      exact: (is_r_neq' E). }
    have Hb1 : (1 == Pointer.block ptr) = false.
    { rewrite Eptr /=.
      case E: (1 == b) => //.
      move/eqP: E => E.
      have [F0 F1] := di_f01 HI (Pointer.component pc).
      rewrite -E in HbF1.
      by rewrite HbF1 in F1. }
    have Hupmem : forall x, goodu mem F x -> goodu mem' F x
      := fun x => store_goodu Hcm Emem' (F := F) (x := x).
    have Hupscr : forall c0 x, scr_val mem c0 x -> scr_val mem' c0 x.
    { move=> c0 x.
      apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
      by rewrite Hb1 andbF. }
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 r2).
      -- have E0' : r0 = r2 := is_r_eq E0.
         rewrite E0' in Hr0 *.
         rewrite tget_set_eq /=.
         have -> : vt = Other.
         { rewrite Evt. exact: (di_rtag HI Hr0). }
         by [].
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      case E0: (is_r r0 r2).
      -- rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
         rewrite tget_set_eq /=.
         apply: Hupmem.
         exact: (di_rval HI H1 H2 H3 H4).
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         apply: Hupmem.
         exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E21: (is_r r2 R_AUX1).
      -- have Ea1 : sv_a1 (dead_src r2 v) = ADead.
         { by rewrite /dead_src /wtaint E21. }
         move: Ht1. rewrite Ea1 /t_le.
         case/orP => /t_eqb_eq E1w.
         ++ by rewrite /aux_claim -E1w.
         ++ by rewrite /aux_claim E1w.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E21)).
         have Ea1 : sv_a1 (dead_src r2 v) = sv_a1 v.
         { rewrite /dead_src /wtaint E21.
           by case: (is_r r2 R_AUX2). }
         move: Ht1. rewrite Ea1 /t_le.
         case/orP => /t_eqb_eq E1w; last first.
         { by rewrite /aux_claim E1w. }
         rewrite -E1w.
         have Ephw2 : sv_ph w = sv_ph v by rewrite Eph' Eph.
         apply: (aux_claim_le_nopd Ephw2 Esg (t_le_refl _)).
         apply: (store_aux_claim Hcm Emem').
         move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E22: (is_r r2 R_AUX2).
      -- have Ea2 : sv_a2 (dead_src r2 v) = ADead.
         { rewrite /dead_src /wtaint E22.
           by case E21: (is_r r2 R_AUX1);
              rewrite //= (is_r_eq E21) in E22. }
         move: Ht2. rewrite Ea2 /t_le.
         case/orP => /t_eqb_eq E2w.
         ++ by rewrite /aux_claim -E2w.
         ++ by rewrite /aux_claim E2w.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E22)).
         have Ea2 : sv_a2 (dead_src r2 v) = sv_a2 v.
         { rewrite /dead_src /wtaint E22.
           by case: (is_r r2 R_AUX1). }
         move: Ht2. rewrite Ea2 /t_le.
         case/orP => /t_eqb_eq E2w; last first.
         { by rewrite /aux_claim E2w. }
         rewrite -E2w.
         have Ephw2 : sv_ph w = sv_ph v by rewrite Eph' Eph.
         apply: (aux_claim_le_nopd Ephw2 Esg (t_le_refl _)).
         apply: (store_aux_claim Hcm Emem').
         move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      have EO : Transitional.val
                  (Transitional.Register.get R_ONE
                     (Transitional.Register.set r2
                        (Transitional.val
                           (Transitional.Register.get r2 regs))
                        (moved_tag vt)
                        regs))
                = Transitional.val
                    (Transitional.Register.get R_ONE regs).
      { case E0: (is_r R_ONE r2).
        - by rewrite -(is_r_eq E0) tget_set_eq.
        - by rewrite (tget_set_neq _ _ _ (is_r_neq E0)). }
      rewrite EO.
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
      by exists b.
    * move=> w0 b0; rewrite Ew => -[<-] _.
      rewrite Hcur => -[<-].
      rewrite (tget_set_neq _ _ _ Hr2nsp).
      rewrite Esg Ec.
      exact: Hsp.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b0; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Esg Ec => j k1 Hk1.
      have HF := di_frame HI Ev Hcur.
      have [cv [tg0 [Hcell Hrow]]] := HF j k1 Hk1.
      exists cv, tg0.
      have Hjlt : j < size (sv_sig v) := nth_error_size Hk1.
      have Hne3 : [&& Pointer.component pc == Pointer.component ptr,
                     b == Pointer.block ptr
                   & j == Z.to_nat (Pointer.offset ptr)] = false.
      { rewrite Eptr /= !eqxx /= Nat2Z.id.
        by rewrite (ltn_eqF Hjlt). }
      rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
      split=> //.
      case: k1 {Hk1} Hrow => //= -[T1 T2]; split=> //;
      exact: (Hupmem _ T2).
    * move=> w0 b0 k1; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Epd' => -[<-].
      rewrite Esg Ec.
      have Hcs := store_cell_same Hupd Emem'.
      move: Hcs. rewrite Eptr /= Nat2Z.id => Hcs.
      exists (Transitional.Register.get r2 regs),
             {| vtag := vt; color := c; entry := None;
                is_code := false |}.
      split; first exact: Hcs.
      case: Hpk => [[Ek Er2 Hnc _]|[Ek Er2 Ea1v Esig01]
                   |[Ek E2ra E2sp Eau2]|[Ek Er2 Enca]].
      -- subst k r2.
         have HK : forall j', nth_error (sv_sig v) j' <> Some CRa.
         { move=> j' E.
           move: Hnc. by rewrite /nocra (nth_error_hasCRa E). }
         apply: (di_ra HI Ev) => //.
         ++ by rewrite Eph.
         ++ by rewrite Epd0.
      -- subst k r2.
         split.
         ++ apply: (di_rtag HI). by [].
         ++ case: Esig01 => Esig0.
            ** rewrite Esig0 /=.
               move: (di_a1 HI Ev).
               by rewrite Ea1v /aux_claim Eph Esig0.
            ** rewrite Esig0 /=.
               move: (di_a1 HI Ev).
               by rewrite Ea1v /aux_claim Eph Esig0.
      -- subst k.
         split.
         ++ by apply: (di_rtag HI); exact: (is_r_neq E2ra).
         ++ apply: Hupmem.
            have := rtaint_claim HI Ev E2sp E2ra.
            by rewrite Eau2.
      -- subst k r2.
         split.
         ++ apply: (di_rtag HI). by [].
         ++ apply: Hupmem.
            apply: (di_rval HI); by [].
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Esg Epd' => HP HPd HK.
      case: Hpk => [[Ek Er2 _ _]|[Ek Er2 _ _]|[Ek E2ra _ _]|[Ek Er2 _]].
      -- subst k. by case: (HPd (erefl _)).
      -- subst k r2.
         have HRA1 : R_RA <> R_AUX1 by [].
         rewrite (tget_set_neq _ _ _ HRA1).
         apply: (di_ra HI Ev) => //.
         ++ by rewrite Eph.
         ++ by rewrite Epd0.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E2ra)).
         apply: (di_ra HI Ev) => //.
         ++ by rewrite Eph.
         ++ by rewrite Epd0.
      -- subst k r2.
         have HRAG : R_RA <> R_ARG by [].
         rewrite (tget_set_neq _ _ _ HRAG).
         apply: (di_ra HI Ev) => //.
         ++ by rewrite Eph.
         ++ by rewrite Epd0.
    * move=> c0 b0 j cv tg0 Hcell HbF.
      case Etgt: ([&& c0 == Pointer.component ptr,
                     b0 == Pointer.block ptr
                   & j == Z.to_nat (Pointer.offset ptr)]).
      -- case/and3P: Etgt => /eqP E1 /eqP E2 _.
         subst c0 b0.
         move: HbF. rewrite Eptr /=.
         by rewrite HbF1.
      -- rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt) in Hcell.
         have [T1 T2] := di_mem HI Hcell HbF.
         split=> // Hb1'.
         exact: (Hupmem _ (T2 Hb1')).
    * move=> c0 cm0 Hcm0.
      have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
      { move: Hcm0. rewrite Emem' setmE.
        case E: (c0 == Pointer.component ptr) => H.
        - move/eqP: E => E. subst c0. by exists cm.
        - by exists cm0. }
      have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm1.
      exists cv, tg0. split=> //.
      have Hne3 : [&& c0 == Pointer.component ptr,
                     1 == Pointer.block ptr
                   & 0 == Z.to_nat (Pointer.offset ptr)] = false.
      { by rewrite Hb1 andbF. }
      by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      case: (sv_sc v) HD => HD /=.
      -- exact: Hupscr HD.
      -- rewrite Eph' => _.
         rewrite (tget_set_neq _ _ _ Hr2nsp).
         exact: Hupscr (HD Eph).
      -- exact: Hupscr HD.
      -- by [].
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> c0 A. rewrite Ec => Hc0 HA.
      have [W1 W2] := di_scrfor HI Hc0 HA.
      split=> //.
      exact: Hupscr W2.
    * move=> i A HA.
      have [W1 W2 W3 W4 W5] := di_chain HI HA.
      split=> //.
      apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
      rewrite Eptr /=.
      case EcA: (a_comp A == Pointer.component pc) => //=.
      move/eqP: EcA => EcA.
      have Hne := di_dist HI HA Hcur EcA.
      case Eb: (a_blk A == b) => //.
      move/eqP: Eb => Eb. by case: (Hne Eb).
    * move=> i A b0 HA Hb0. rewrite Ec => HcA.
      exact: (di_dist HI HA Hb0 HcA).
    * exact: (di_dist2 HI).
    * move=> c0 b0 HbF.
      have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
      case Ec0: (c0 == Pointer.component ptr).
      -- move/eqP: Ec0 => Ec0. subst c0.
         eexists. split; first by rewrite Emem' setmE eqxx.
         move=> /=.
         have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
         by subst cm0.
      -- exists cm0. split=> //.
         rewrite (store_getm_other Emem') //.
         by move=> E; rewrite E eqxx in Ec0.
    * exact: (di_f01 HI).
    * move=> c0 cm0.
      apply: (store_nb2 Hcm Emem').
      exact: (di_nb2 HI).
    * move=> c0 S Hs.
      apply: (store_dom Emem').
      exact: (di_dom HI Hs).
    * exact: (di_level HI).
    * move=> c0 cm0 Hcm0.
      have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
      { move: Hcm0. rewrite Emem' setmE.
        case E: (c0 == Pointer.component ptr) => H.
        - move/eqP: E => E. subst c0. by exists cm.
        - by exists cm0. }
      have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm1.
      exists cv, tg0.
      have Hne3 : [&& c0 == Pointer.component ptr,
                     1 == Pointer.block ptr
                   & 1 == Z.to_nat (Pointer.offset ptr)] = false.
      { by rewrite Hb1 /= andbF. }
      rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
      split=> //. split=> //.
      exact: (Hupmem _ Hgd).
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
      apply: Hupscr.
      exact: (di_scr0 HI Hc0 Hg0 Htw).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      have Hek : sv_ek v = true.
      { move: Hekw. by rewrite Eek'. }
      rewrite (pend_sig_some Epd') Esg.
      have HB : bodycarg (sv_sig v).
      { rewrite -(pend_sig_none Epd0). exact: (di_bodycarg HI Ev Hek). }
      case: Hpk => [[Ekk _ _ Hgate]|[Ekk _ _ _]|[Ekk _ _ _]|[Ekk _ _]].
      -- subst k. apply: (bodycarg_rcons_ra _ HB).
         move: Hgate. by rewrite Hek.
      -- subst k. exact: (@bodycarg_rcons_u (sv_sig v) CSp (erefl _) HB).
      -- subst k. exact: (@bodycarg_rcons_u (sv_sig v) CU (erefl _) HB).
      -- subst k. exact: (@bodycarg_rcons_u (sv_sig v) CArg (erefl _) HB).
    * exact: (di_chain2 HI).
  +
    case Etr1: (rtaint v r1) => //.
    *
      have E1ra : is_r r1 R_RA = false.
      { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
      have Hp1 : Transitional.val (Transitional.Register.get r1 regs)
                 = Ptr (Pointer.component pc, 1, 0%Z).
      { have Hrc := rtaint_claim HI Ev E1sp E1ra.
        by rewrite Etr1 in Hrc. }
      have Eptr : ptr = (Pointer.component pc, 1, 0%Z).
      { move: Hval1. rewrite Hp1. by move=> [->]. }
      have Ecp : Pointer.component ptr = Pointer.component pc
        by rewrite Eptr.
      have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
      have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
      have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
      have Hsp := di_sp HI Ev Eph Hcur.
      have [F0 F1] := di_f01 HI (Pointer.component pc).
      have Hupmem : forall x, goodu mem F x -> goodu mem' F x
        := fun x => store_goodu Hcm Emem' (F := F) (x := x).
      have Hupscr_o : forall c0 x, (c0 == Pointer.component pc) = false ->
          scr_val mem c0 x -> scr_val mem' c0 x.
      { move=> c0 x Hne.
        apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
        by rewrite Ecp Hne. }
      have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg carry
          cscr rcap,
          b1 \in F c1 ->
          frame_ok F mem c1 b1 sg carry cscr rcap ->
          frame_ok F mem' c1 b1 sg carry cscr rcap.
      { move=> c1 b1 sg carry cscr rcap Hb1'.
        apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
        rewrite Eptr /=.
        case E: (c1 == Pointer.component pc) => //=.
        case Eb: (b1 == 1) => //.
        move/eqP: Eb => Eb. subst b1.
        move/eqP: E => E. subst c1.
        by rewrite F1 in Hb1'. }
      case E2sp: (is_r r2 R_SP).
      --
         move=> -[Evv]. subst v'.
         have Er2 : r2 = R_SP := is_r_eq E2sp.
         subst r2.
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
           => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
         have Epdw : sv_pend w = sv_pend v by rewrite Epd' Epd0.
         have Evt0 : vt = Other.
         { rewrite Evt. by apply: (di_rtag HI). }
         have Eia : (moved_tag vt) = Other
           by rewrite Evt0.
         rewrite Eia.
         have Hcs := store_cell_same Hupd Emem'.
         move: Hcs. rewrite Eptr /= => Hcs.
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 R_SP).
            ** by rewrite (is_r_eq E0) tget_set_eq.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            rewrite (tget_set_neq _ _ _ H2).
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA1sp : R_AUX1 <> R_SP by [].
            rewrite (tget_set_neq _ _ _ HA1sp).
            apply: (aux_claim_le Ephw Esg Epdw Ht1).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA2sp : R_AUX2 <> R_SP by [].
            rewrite (tget_set_neq _ _ _ HA2sp).
            apply: (aux_claim_le Ephw Esg Epdw Ht2).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            have HOsp : R_ONE <> R_SP by [].
            rewrite (tget_set_neq _ _ _ HOsp).
            apply: (di_one HI Ev).
            exact: o_le_true Hon Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            rewrite tget_set_eq /= Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec.
            exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd'.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            have HRAsp : R_RA <> R_SP by [].
            rewrite (tget_set_neq _ _ _ HRAsp).
            apply: (di_ra HI Ev) => //.
            ** by rewrite Eph.
            ** by rewrite Epd0.
         ++ move=> c0 b0 j cv tg0 Hcell HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1 /eqP T2 /eqP T3.
               subst c0 b0 j.
               have Hcs2 := store_cell_same Hupd Emem'.
               rewrite Hcs2 in Hcell.
               move: Hcell => -[<- _].
               split.
               --- by apply: (di_rtag HI).
               --- move=> Hb1'. case: Hb1'. by rewrite Eptr.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell.
               have [T1 T2] := di_mem HI Hcell HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2 Hb1')).
         ++ move=> c0 cm0 Hcm0.
            case Ec0: (c0 == Pointer.component pc).
            ** move/eqP: Ec0 => Ec0. subst c0.
               exists (Transitional.Register.get R_SP regs),
                      {| vtag := vt; color := c; entry := None;
                         is_code := false |}.
               split; first exact: Hcs.
               by apply: (di_rtag HI).
            ** have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm1.
               exists cv, tg0. split=> //.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 0 == Z.to_nat (Pointer.offset ptr)] = false.
               { by rewrite Ecp Ec0. }
               by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw => _.
            rewrite tget_set_eq /=.
            exists (Transitional.Register.get R_SP regs),
                   {| vtag := vt; color := c; entry := None;
                      is_code := false |}.
            by split.
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            apply: (Hupscr_o _ _ _ W2).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            exact: (Hupfr _ _ _ _ _ _ W3 W4).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm1.
            exists cv, tg0.
            have E31 : (1 == Z.to_nat (Pointer.offset ptr)) = false
              by rewrite Eptr.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite E31 !andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: (Hupscr_o _ _ _ (di_scr0 HI Hc0 Hg0 Htw)).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            have Hek : sv_ek v = true.
            { move: Hekw. by rewrite Eek'. }
            rewrite (pend_sig_none Epd') Esg -(pend_sig_none Epd0).
            exact: (di_bodycarg HI Ev Hek).
         ++ exact: (di_chain2 HI).
      --
         case Erst: (t_eqb (rtaint v r2) ASp
                     && cseq_eqb (sv_sig v) [:: CSp]) => // -[Evv].
         subst v'.
         case/andP: Erst => /t_eqb_eq Er2t /cseq_eqb_eq Esg1.
         have E2ra : is_r r2 R_RA = false.
         { by move: Er2t; rewrite /rtaint E2sp; case: (is_r r2 R_RA). }
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
           => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
         have Epdw : sv_pend w = sv_pend v by rewrite Epd' Epd0.
         have Evt0 : vt = Other.
         { rewrite Evt. apply: (di_rtag HI). exact: (is_r_neq E2ra). }
         have Eia : (moved_tag vt) = Other
           by rewrite Evt0.
         rewrite Eia.
         have Hv2 : Transitional.val (Transitional.Register.get r2 regs)
                    = cs.
         { have Hrc2 := rtaint_claim HI Ev E2sp E2ra.
           rewrite Er2t in Hrc2.
           move: Hrc2. by rewrite /aux_claim Eph Esg1. }
         have Hcs' := store_cell_same Hupd Emem'.
         move: Hcs'. rewrite Eptr /= => Hcs'.
         have Hx : forall r0, r0 <> r2 ->
             Transitional.Register.get r0
               (Transitional.Register.set r2
                  (Transitional.val (Transitional.Register.get r2 regs))
                  Other regs)
             = Transitional.Register.get r0 regs.
         { move=> r0 E0. by rewrite (tget_set_neq _ _ _ E0). }
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 r2).
            ** by rewrite (is_r_eq E0) tget_set_eq.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            case E0: (is_r r0 r2).
            ** rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
               rewrite tget_set_eq /=.
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have Hx1 : Transitional.val
                (Transitional.Register.get R_AUX1
                   (Transitional.Register.set r2
                      (Transitional.val
                         (Transitional.Register.get r2 regs))
                      Other regs))
              = Transitional.val
                  (Transitional.Register.get R_AUX1 regs).
            { case E21: (is_r r2 R_AUX1).
              - by rewrite (is_r_eq E21) tget_set_eq.
              - by rewrite (tget_set_neq _ _ _ (is_r_neq' E21)). }
            rewrite Hx1.
            apply: (aux_claim_le Ephw Esg Epdw Ht1).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have Hx2 : Transitional.val
                (Transitional.Register.get R_AUX2
                   (Transitional.Register.set r2
                      (Transitional.val
                         (Transitional.Register.get r2 regs))
                      Other regs))
              = Transitional.val
                  (Transitional.Register.get R_AUX2 regs).
            { case E22: (is_r r2 R_AUX2).
              - by rewrite (is_r_eq E22) tget_set_eq.
              - by rewrite (tget_set_neq _ _ _ (is_r_neq' E22)). }
            rewrite Hx2.
            apply: (aux_claim_le Ephw Esg Epdw Ht2).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            have Hx1 : Transitional.val
                (Transitional.Register.get R_ONE
                   (Transitional.Register.set r2
                      (Transitional.val
                         (Transitional.Register.get r2 regs))
                      Other regs))
              = Transitional.val
                  (Transitional.Register.get R_ONE regs).
            { case E0: (is_r R_ONE r2).
              - by rewrite -(is_r_eq E0) tget_set_eq.
              - by rewrite (tget_set_neq _ _ _ (is_r_neq E0)). }
            rewrite Hx1.
            apply: (di_one HI Ev).
            exact: o_le_true Hon Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            rewrite (Hx _ (is_r_neq' E2sp)) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec.
            exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd'.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            rewrite (Hx _ (is_r_neq' E2ra)).
            apply: (di_ra HI Ev) => //.
            ** by rewrite Eph.
            ** by rewrite Epd0.
         ++ move=> c0 b0 j cv tg0 Hcell HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1 /eqP T2 /eqP T3.
               subst c0 b0 j.
               have Hcs2 := store_cell_same Hupd Emem'.
               rewrite Hcs2 in Hcell.
               move: Hcell => -[<- _].
               split.
               --- apply: (di_rtag HI). exact: (is_r_neq E2ra).
               --- move=> Hb1'. case: Hb1'. by rewrite Eptr.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell.
               have [T1 T2] := di_mem HI Hcell HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2 Hb1')).
         ++ move=> c0 cm0 Hcm0.
            case Ec0: (c0 == Pointer.component pc).
            ** move/eqP: Ec0 => Ec0. subst c0.
               exists (Transitional.Register.get r2 regs),
                      {| vtag := vt; color := c; entry := None;
                         is_code := false |}.
               split; first exact: Hcs'.
               apply: (di_rtag HI). exact: (is_r_neq E2ra).
            ** have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm1.
               exists cv, tg0. split=> //.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 0 == Z.to_nat (Pointer.offset ptr)] = false.
               { by rewrite Ecp Ec0. }
               by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            exists (Transitional.Register.get r2 regs),
                   {| vtag := vt; color := c; entry := None;
                      is_code := false |}.
            by split.
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            apply: (Hupscr_o _ _ _ W2).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            exact: (Hupfr _ _ _ _ _ _ W3 W4).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm1.
            exists cv, tg0.
            have E31 : (1 == Z.to_nat (Pointer.offset ptr)) = false
              by rewrite Eptr.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite E31 !andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: (Hupscr_o _ _ _ (di_scr0 HI Hc0 Hg0 Htw)).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            have Hek : sv_ek v = true.
            { move: Hekw. by rewrite Eek'. }
            rewrite (pend_sig_none Epd') Esg -(pend_sig_none Epd0).
            exact: (di_bodycarg HI Ev Hek).
         ++ exact: (di_chain2 HI).
    *
      case Eau2: (t_eqb (rtaint v r2) AU) => // -[Evv].
      subst v'.
      have Er2t : rtaint v r2 = AU := t_eqb_eq Eau2.
      have E1ra : is_r r1 R_RA = false.
      { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
      have Hp1 : Transitional.val (Transitional.Register.get r1 regs)
                 = Ptr (Pointer.component pc, 1, 1%Z).
      { have Hrc := rtaint_claim HI Ev E1sp E1ra.
        by rewrite Etr1 in Hrc. }
      have Eptr : ptr = (Pointer.component pc, 1, 1%Z).
      { move: Hval1. rewrite Hp1. by move=> [->]. }
      have Ecp : Pointer.component ptr = Pointer.component pc
        by rewrite Eptr.
      have E2sp : is_r r2 R_SP = false.
      { by move: Er2t; rewrite /rtaint; case: (is_r r2 R_SP). }
      have E2ra : is_r r2 R_RA = false.
      { by move: Er2t; rewrite /rtaint E2sp; case: (is_r r2 R_RA). }
      have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
      have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
      have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
      have Hsp := di_sp HI Ev Eph Hcur.
      have [F0 F1] := di_f01 HI (Pointer.component pc).
      have Hupmem : forall x, goodu mem F x -> goodu mem' F x
        := fun x => store_goodu Hcm Emem' (F := F) (x := x).
      have E3 : (0 == Z.to_nat (Pointer.offset ptr)) = false
        by rewrite Eptr.
      have Hupscr : forall c0 x, scr_val mem c0 x -> scr_val mem' c0 x.
      { move=> c0 x [cv [tg0 [Hcell Hv]]].
        exists cv, tg0. split=> //.
        have Hne3 : [&& c0 == Pointer.component ptr,
                       1 == Pointer.block ptr
                     & 0 == Z.to_nat (Pointer.offset ptr)] = false.
        { by rewrite E3 !andbF. }
        by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3). }
      have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg carry
          cscr rcap,
          b1 \in F c1 ->
          frame_ok F mem c1 b1 sg carry cscr rcap ->
          frame_ok F mem' c1 b1 sg carry cscr rcap.
      { move=> c1 b1 sg carry cscr rcap Hb1'.
        apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
        rewrite Eptr /=.
        case E: (c1 == Pointer.component pc) => //=.
        case Eb: (b1 == 1) => //.
        move/eqP: Eb => Eb. subst b1.
        move/eqP: E => E. subst c1.
        by rewrite F1 in Hb1'. }
      have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
      have Evt0 : vt = Other.
      { rewrite Evt. apply: (di_rtag HI). exact: (is_r_neq E2ra). }
      have Eia : (moved_tag vt) = Other
        by rewrite Evt0.
      rewrite Eia.
      have Hx : forall r0, r0 <> r2 ->
          Transitional.Register.get r0
            (Transitional.Register.set r2
               (Transitional.val (Transitional.Register.get r2 regs))
               Other regs)
          = Transitional.Register.get r0 regs.
      { move=> r0 E0. by rewrite (tget_set_neq _ _ _ E0). }
      constructor.
      -- move=> r0 Hr0.
         case E0: (is_r r0 r2).
         ++ by rewrite (is_r_eq E0) tget_set_eq.
         ++ rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
            exact: (di_rtag HI).
      -- move=> r0 H1 H2 H3 H4.
         case E0: (is_r r0 r2).
         ++ rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
            rewrite tget_set_eq /=.
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have Hx1 : Transitional.val
             (Transitional.Register.get R_AUX1
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_AUX1 regs).
         { case E21: (is_r r2 R_AUX1).
           - by rewrite (is_r_eq E21) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq' E21)). }
         rewrite Hx1.
         apply: (aux_claim_le Eph' Esg Epd' Ht1).
         apply: (store_aux_claim Hcm Emem').
         exact: (di_a1 HI Ev).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have Hx2 : Transitional.val
             (Transitional.Register.get R_AUX2
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_AUX2 regs).
         { case E22: (is_r r2 R_AUX2).
           - by rewrite (is_r_eq E22) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq' E22)). }
         rewrite Hx2.
         apply: (aux_claim_le Eph' Esg Epd' Ht2).
         apply: (store_aux_claim Hcm Emem').
         exact: (di_a2 HI Ev).
      -- move=> w0; rewrite Ew => -[<-] Hon1.
         have Hx1 : Transitional.val
             (Transitional.Register.get R_ONE
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_ONE regs).
         { case E0: (is_r R_ONE r2).
           - by rewrite -(is_r_eq E0) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq E0)). }
         rewrite Hx1.
         apply: (di_one HI Ev).
         exact: o_le_true Hon Hon1.
      -- move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
         by case: HP.
      -- move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
         by exists b.
      -- move=> w0 b0; rewrite Ew => -[<-] _.
         rewrite Hcur => -[<-].
         rewrite (Hx _ (is_r_neq' E2sp)) Esg Ec.
         exact: Hsp.
      -- move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> w0 b0; rewrite Ew => -[<-].
         rewrite Hcur => -[<-].
         rewrite Esg Ec.
         exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
      -- move=> w0 b0 k1; rewrite Ew => -[<-] _.
         by rewrite Epd' Epd0.
      -- move=> w0; rewrite Ew => -[<-].
         rewrite Eph' Esg Epd' => HP HPd HK.
         rewrite (Hx _ (is_r_neq' E2ra)).
         exact: (di_ra HI Ev HP HPd HK).
      -- move=> c0 b0 j cv tg0 Hcell HbF.
         case Etgt: ([&& c0 == Pointer.component ptr,
                        b0 == Pointer.block ptr
                      & j == Z.to_nat (Pointer.offset ptr)]).
         ++ case/and3P: Etgt => /eqP T1 /eqP T2 /eqP T3.
            subst c0 b0 j.
            have Hcs2 := store_cell_same Hupd Emem'.
            rewrite Hcs2 in Hcell.
            move: Hcell => -[<- _].
            split.
            ** apply: (di_rtag HI). exact: (is_r_neq E2ra).
            ** move=> Hb1'. case: Hb1'. by rewrite Eptr.
         ++ rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
              in Hcell.
            have [T1 T2] := di_mem HI Hcell HbF.
            split=> // Hb1'.
            exact: (Hupmem _ (T2 Hb1')).
      -- move=> c0 cm0 Hcm0.
         have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
         { move: Hcm0. rewrite Emem' setmE.
           case E: (c0 == Pointer.component ptr) => H.
           - move/eqP: E => E. subst c0. by exists cm.
           - by exists cm0. }
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm1.
         exists cv, tg0. split=> //.
         have Hne3 : [&& c0 == Pointer.component ptr,
                        1 == Pointer.block ptr
                      & 0 == Z.to_nat (Pointer.offset ptr)] = false.
         { by rewrite E3 !andbF. }
         by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have HD := di_scr HI Ev.
         move: Hsc. rewrite /sc_le.
         case/orP => /sc_eqb_eq Escw; last first.
         { by rewrite Escw. }
         rewrite -Escw.
         case: (sv_sc v) HD => HD /=.
         ++ exact: Hupscr HD.
         ++ rewrite Eph' => HPB.
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp)).
            exact: Hupscr (HD HPB).
         ++ exact: Hupscr HD.
         ++ by [].
      -- move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> c0 A. rewrite Ec => Hc0 HA.
         have [W1 W2] := di_scrfor HI Hc0 HA.
         split=> //.
         exact: (Hupscr _ _ W2).
      -- move=> i A HA.
         have [W1 W2 W3 W4 W5] := di_chain HI HA.
         split=> //.
         exact: (Hupfr _ _ _ _ _ _ W3 W4).
      -- move=> i A b0 HA Hb0. rewrite Ec => HcA.
         exact: (di_dist HI HA Hb0 HcA).
      -- exact: (di_dist2 HI).
      -- move=> c0 b0 HbF.
         have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
         case Ec0: (c0 == Pointer.component ptr).
         ++ move/eqP: Ec0 => Ec0. subst c0.
            eexists. split; first by rewrite Emem' setmE eqxx.
            move=> /=.
            have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
            by subst cm0.
         ++ exists cm0. split=> //.
            rewrite (store_getm_other Emem') //.
            by move=> E; rewrite E eqxx in Ec0.
      -- exact: (di_f01 HI).
      -- move=> c0 cm0.
         apply: (store_nb2 Hcm Emem').
         exact: (di_nb2 HI).
      -- move=> c0 S Hs.
         apply: (store_dom Emem').
         exact: (di_dom HI Hs).
      -- exact: (di_level HI).
      -- move=> c0 cm0 Hcm0.
         case Ec0: (c0 == Pointer.component pc).
         ++ move/eqP: Ec0 => Ec0. subst c0.
            have Hcs2 := store_cell_same Hupd Emem'.
            move: Hcs2. rewrite Eptr /= => Hcs2.
            exists (Transitional.Register.get r2 regs),
                   {| vtag := vt; color := c; entry := None;
                      is_code := false |}.
            split; first exact: Hcs2.
            split.
            ** apply: (di_rtag HI). exact: (is_r_neq E2ra).
            ** apply: Hupmem.
               have Hrc2 := rtaint_claim HI Ev E2sp E2ra.
               by rewrite Er2t in Hrc2.
         ++ have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm1.
            exists cv, tg0.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Ecp Ec0. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd).
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         apply: (di_ek HI Ev).
         rewrite ?wone_ek ?wtaint_ek in Eek'.
         move: Hekw. by rewrite Eek'.
      -- move=> i X HX Hnw.
         case: (di_nwshadow HI HX Hnw)
           => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
         { right. exists j, W. by split. }
         left. split; last exact: HPre.
         by rewrite Ec.
      -- move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
      -- move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
         apply: Hupscr.
         exact: (di_scr0 HI Hc0 Hg0 Htw).
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         apply: (di_ekwin HI Ev).
         move: Hekw. by rewrite Eek'.
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         rewrite (pend_sig_eq Esg Epd').
         apply: (di_bodycarg HI Ev).
         move: Hekw. by rewrite Eek'.
      -- exact: (di_chain2 HI).
    *
      case Eau2: (t_eqb (rtaint v r2) AU) => // -[Evv].
      subst v'.
      have Er2t : rtaint v r2 = AU := t_eqb_eq Eau2.
      have E1ra : is_r r1 R_RA = false.
      { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
      have Hgd : goodu mem F (Ptr ptr).
      { have Hrc := rtaint_claim HI Ev E1sp E1ra.
        rewrite Etr1 Hval1 in Hrc.
        exact: Hrc. }
      have [HbFp Hb1p Hvb] := Hgd ptr (erefl _).
      have Hb1e : (1 == Pointer.block ptr) = false.
      { case E: (1 == Pointer.block ptr) => //.
        move/eqP: E => E. case: Hb1p. by rewrite -E. }
      have E2sp : is_r r2 R_SP = false.
      { by move: Er2t; rewrite /rtaint; case: (is_r r2 R_SP). }
      have E2ra : is_r r2 R_RA = false.
      { by move: Er2t; rewrite /rtaint E2sp; case: (is_r r2 R_RA). }
      have Hg2 : goodu mem F
          (Transitional.val (Transitional.Register.get r2 regs)).
      { have Hrc2 := rtaint_claim HI Ev E2sp E2ra.
        by rewrite Er2t in Hrc2. }
      have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
      have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
      have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
      have Hsp := di_sp HI Ev Eph Hcur.
      have Hupmem : forall x, goodu mem F x -> goodu mem' F x
        := fun x => store_goodu Hcm Emem' (F := F) (x := x).
      have Hupscr : forall c0 x, scr_val mem c0 x -> scr_val mem' c0 x.
      { move=> c0 x.
        apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
        by rewrite Hb1e andbF. }
      have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg carry
          cscr rcap,
          b1 \in F c1 ->
          frame_ok F mem c1 b1 sg carry cscr rcap ->
          frame_ok F mem' c1 b1 sg carry cscr rcap.
      { move=> c1 b1 sg carry cscr rcap Hb1'.
        apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
        case E: (c1 == Pointer.component ptr) => //=.
        case Eb: (b1 == Pointer.block ptr) => //.
        move/eqP: E => E. subst c1.
        move/eqP: Eb => Eb. subst b1.
        by rewrite HbFp in Hb1'. }
      have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
      have Evt0 : vt = Other.
      { rewrite Evt. apply: (di_rtag HI). exact: (is_r_neq E2ra). }
      have Eia : (moved_tag vt) = Other
        by rewrite Evt0.
      rewrite Eia.
      have Hx : forall r0, r0 <> r2 ->
          Transitional.Register.get r0
            (Transitional.Register.set r2
               (Transitional.val (Transitional.Register.get r2 regs))
               Other regs)
          = Transitional.Register.get r0 regs.
      { move=> r0 E0. by rewrite (tget_set_neq _ _ _ E0). }
      constructor.
      -- move=> r0 Hr0.
         case E0: (is_r r0 r2).
         ++ by rewrite (is_r_eq E0) tget_set_eq.
         ++ rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
            exact: (di_rtag HI).
      -- move=> r0 H1 H2 H3 H4.
         case E0: (is_r r0 r2).
         ++ rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
            rewrite tget_set_eq /=.
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have Hx1 : Transitional.val
             (Transitional.Register.get R_AUX1
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_AUX1 regs).
         { case E21: (is_r r2 R_AUX1).
           - by rewrite (is_r_eq E21) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq' E21)). }
         rewrite Hx1.
         apply: (aux_claim_le Eph' Esg Epd' Ht1).
         apply: (store_aux_claim Hcm Emem').
         exact: (di_a1 HI Ev).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have Hx2 : Transitional.val
             (Transitional.Register.get R_AUX2
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_AUX2 regs).
         { case E22: (is_r r2 R_AUX2).
           - by rewrite (is_r_eq E22) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq' E22)). }
         rewrite Hx2.
         apply: (aux_claim_le Eph' Esg Epd' Ht2).
         apply: (store_aux_claim Hcm Emem').
         exact: (di_a2 HI Ev).
      -- move=> w0; rewrite Ew => -[<-] Hon1.
         have Hx1 : Transitional.val
             (Transitional.Register.get R_ONE
                (Transitional.Register.set r2
                   (Transitional.val
                      (Transitional.Register.get r2 regs))
                   Other regs))
           = Transitional.val (Transitional.Register.get R_ONE regs).
         { case E0: (is_r R_ONE r2).
           - by rewrite -(is_r_eq E0) tget_set_eq.
           - by rewrite (tget_set_neq _ _ _ (is_r_neq E0)). }
         rewrite Hx1.
         apply: (di_one HI Ev).
         exact: o_le_true Hon Hon1.
      -- move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
         by case: HP.
      -- move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
         by exists b.
      -- move=> w0 b0; rewrite Ew => -[<-] _.
         rewrite Hcur => -[<-].
         rewrite (Hx _ (is_r_neq' E2sp)) Esg Ec.
         exact: Hsp.
      -- move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> w0 b0; rewrite Ew => -[<-].
         rewrite Hcur => -[<-].
         rewrite Esg Ec.
         exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
      -- move=> w0 b0 k1; rewrite Ew => -[<-] _.
         by rewrite Epd' Epd0.
      -- move=> w0; rewrite Ew => -[<-].
         rewrite Eph' Esg Epd' => HP HPd HK.
         rewrite (Hx _ (is_r_neq' E2ra)).
         exact: (di_ra HI Ev HP HPd HK).
      -- move=> c0 b0 j cv tg0 Hcell HbF.
         case Etgt: ([&& c0 == Pointer.component ptr,
                        b0 == Pointer.block ptr
                      & j == Z.to_nat (Pointer.offset ptr)]).
         ++ case/and3P: Etgt => /eqP T1 /eqP T2 /eqP T3.
            subst c0 b0 j.
            have Hcs2 := store_cell_same Hupd Emem'.
            rewrite Hcs2 in Hcell.
            move: Hcell => -[<- _].
            split.
            ** apply: (di_rtag HI). exact: (is_r_neq E2ra).
            ** move=> _. exact: (Hupmem _ Hg2).
         ++ rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
              in Hcell.
            have [T1 T2] := di_mem HI Hcell HbF.
            split=> // Hb1'.
            exact: (Hupmem _ (T2 Hb1')).
      -- move=> c0 cm0 Hcm0.
         have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
         { move: Hcm0. rewrite Emem' setmE.
           case E: (c0 == Pointer.component ptr) => H.
           - move/eqP: E => E. subst c0. by exists cm.
           - by exists cm0. }
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm1.
         exists cv, tg0. split=> //.
         have Hne3 : [&& c0 == Pointer.component ptr,
                        1 == Pointer.block ptr
                      & 0 == Z.to_nat (Pointer.offset ptr)] = false.
         { by rewrite Hb1e /= andbF. }
         by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
      -- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
         have HD := di_scr HI Ev.
         move: Hsc. rewrite /sc_le.
         case/orP => /sc_eqb_eq Escw; last first.
         { by rewrite Escw. }
         rewrite -Escw.
         case: (sv_sc v) HD => HD /=.
         ++ exact: Hupscr HD.
         ++ rewrite Eph' => HPB.
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp)).
            exact: Hupscr (HD HPB).
         ++ exact: Hupscr HD.
         ++ by [].
      -- move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
      -- move=> c0 A. rewrite Ec => Hc0 HA.
         have [W1 W2] := di_scrfor HI Hc0 HA.
         split=> //.
         exact: (Hupscr _ _ W2).
      -- move=> i A HA.
         have [W1 W2 W3 W4 W5] := di_chain HI HA.
         split=> //.
         exact: (Hupfr _ _ _ _ _ _ W3 W4).
      -- move=> i A b0 HA Hb0. rewrite Ec => HcA.
         exact: (di_dist HI HA Hb0 HcA).
      -- exact: (di_dist2 HI).
      -- move=> c0 b0 HbF.
         have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
         case Ec0: (c0 == Pointer.component ptr).
         ++ move/eqP: Ec0 => Ec0. subst c0.
            eexists. split; first by rewrite Emem' setmE eqxx.
            move=> /=.
            have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
            by subst cm0.
         ++ exists cm0. split=> //.
            rewrite (store_getm_other Emem') //.
            by move=> E; rewrite E eqxx in Ec0.
      -- exact: (di_f01 HI).
      -- move=> c0 cm0.
         apply: (store_nb2 Hcm Emem').
         exact: (di_nb2 HI).
      -- move=> c0 S Hs.
         apply: (store_dom Emem').
         exact: (di_dom HI Hs).
      -- exact: (di_level HI).
      -- move=> c0 cm0 Hcm0.
         have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
         { move: Hcm0. rewrite Emem' setmE.
           case E: (c0 == Pointer.component ptr) => H.
           - move/eqP: E => E. subst c0. by exists cm.
           - by exists cm0. }
         have [cv [tg0 [Hcell [Htag Hgd2]]]] := di_flag HI Hcm1.
         exists cv, tg0.
         have Hne3 : [&& c0 == Pointer.component ptr,
                        1 == Pointer.block ptr
                      & 1 == Z.to_nat (Pointer.offset ptr)] = false.
         { by rewrite Hb1e /= andbF. }
         rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         split=> //. split=> //.
         exact: (Hupmem _ Hgd2).
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         apply: (di_ek HI Ev).
         rewrite ?wone_ek ?wtaint_ek in Eek'.
         move: Hekw. by rewrite Eek'.
      -- move=> i X HX Hnw.
         case: (di_nwshadow HI HX Hnw)
           => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
         { right. exists j, W. by split. }
         left. split; last exact: HPre.
         by rewrite Ec.
      -- move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
      -- move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
         apply: Hupscr.
         exact: (di_scr0 HI Hc0 Hg0 Htw).
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         apply: (di_ekwin HI Ev).
         move: Hekw. by rewrite Eek'.
      -- move=> w0; rewrite Ew => -[<-] Hekw.
         rewrite (pend_sig_eq Esg Epd').
         apply: (di_bodycarg HI Ev).
         move: Hekw. by rewrite Eek'.
      -- exact: (di_chain2 HI).
Qed.

Lemma disc_step_store :
  forall mem mem' regs pc tg c pct ptr r1 r2 vt,
    Transitional.executing cde pc (TrStore r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Register.get_tag r2 regs = Some vt ->
    Transitional.Memory.store mem ptr
      (Transitional.Register.get r2 regs,
       {| vtag := vt; color := c; entry := None; is_code := false |})
      = Some mem' ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem',
       Transitional.Register.set r2
         (Transitional.val (Transitional.Register.get r2 regs))
         (moved_tag vt) regs,
       Pointer.inc pc, pct).
Proof.
  move=> mem mem' regs pc tg c pct ptr r1 r2 vt Hex Hpc Htg1 Hval1
         Hcptr Hgt2 Hstore [cur [chain [F [cs HI]]]].
  exists cur, chain, F, cs.
  exact: (dinv_step_store Hex Hpc Htg1 Hval1 Hcptr Hgt2 Hstore HI).
Qed.

Lemma dinv_step_load :
  forall mem mem' regs pc tg c pct r1 r2 ptr v cur chain F cs,
    Transitional.executing cde pc (TrLoad r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Memory.load mem ptr = Some v ->
    Transitional.Memory.store mem ptr
      ({| Transitional.val := Transitional.val v.1;
          tvtag := moved_tag (tvtag v.1) |},
       {| vtag := moved_tag (tvtag v.1);
          color := c; entry := None; is_code := false |}) = Some mem' ->
    dinv cur chain F cs mem regs pc pct ->
    dinv cur chain F cs mem'
       (Transitional.Register.set r2 (Transitional.val v.1) (tvtag v.1)
          regs)
       (Pointer.inc pc) pct.
Proof.
  move=> mem mem' regs pc tg c pct r1 r2 ptr cl cur chain F cs
         Hex Hpc Htg1 Hval1 Hcptr Hload Hwb HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have [cm [chunk [chunk' [Hcm Hchunk Hoff Hupd Emem']]]]
    := store_shape Hwb.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  have Hload_cell : cell_at mem (Pointer.component ptr)
      (Pointer.block ptr) (Z.to_nat (Pointer.offset ptr)) = Some cl.
  { move: Hload.
    rewrite /Transitional.Memory.load /Transitional.Memory.load_b
            /cell_at /=.
    case: (getm mem (Pointer.component ptr)) => [cm0|] //=.
    case: (getm (Transitional.Memory.content cm0) (Pointer.block ptr))
      => [blk|] //=.
    by case: (0 <=? Pointer.offset ptr)%Z. }
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  +
    case E1sp: (is_r r1 R_SP).
    *
      case Epd0: (sv_pend v) => [k0|] //.
      case: k0 Epd0 => Epd0.
      --
         case E2ra: (is_r r2 R_RA) => // -[Evv]. subst v'.
         have Er1 : r1 = R_SP := is_r_eq E1sp. subst r1.
         have Er2 : r2 = R_RA := is_r_eq E2ra. subst r2.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have Eptr : ptr
           = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
         { move: Hval1. rewrite Hsp. by move=> [->]. }
         have [F0 F1] := di_f01 HI (Pointer.component pc).
         have Hb1 : (1 == Pointer.block ptr) = false.
         { rewrite Eptr /=.
           case E: (1 == b) => //.
           move/eqP: E => E.
           rewrite -E in HbF1.
           by rewrite HbF1 in F1. }
         have [cv [tg0 [Hcell Hrow]]] := di_pend HI Ev Hcur Epd0.
         have Ecl : cl = (cv, tg0).
         { move: Hload_cell. rewrite Eptr /= Nat2Z.id Hcell.
           by move=> [->]. }
         subst cl.
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
           => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have Hupscr : forall c0 x,
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x.
           apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
           by rewrite Hb1 andbF. }
         constructor.
         ++ move=> r0 Hr0.
            rewrite (tget_set_neq _ _ _ Hr0).
            exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            rewrite (tget_set_neq _ _ _ H1).
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA1 : R_AUX1 <> R_RA by [].
            rewrite (tget_set_neq _ _ _ HA1).
            apply: (aux_claim_le_nopd Ephw Esg Ht1).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA2 : R_AUX2 <> R_RA by [].
            rewrite (tget_set_neq _ _ _ HA2).
            apply: (aux_claim_le_nopd Ephw Esg Ht2).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            have HO : R_ONE <> R_RA by [].
            rewrite (tget_set_neq _ _ _ HO).
            apply: (di_one HI Ev).
            exact: o_le_true Hon Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            have HSPr : R_SP <> R_RA by [].
            rewrite (tget_set_neq _ _ _ HSPr) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec => j k1 Hk1.
            have HF := di_frame HI Ev Hcur.
            have [cv1 [tg1 [Hcell1 Hrow1]]] := HF j k1 Hk1.
            exists cv1, tg1.
            have Hjlt : j < size (sv_sig v) := nth_error_size Hk1.
            have Hne3 : [&& Pointer.component pc
                              == Pointer.component ptr,
                           b == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)] = false.
            { rewrite Eptr /= !eqxx /= Nat2Z.id.
              by rewrite (ltn_eqF Hjlt). }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //.
            case: k1 {Hk1} Hrow1 => //= -[T1 T2]; split=> //;
            exact: (Hupmem _ T2).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd'.
         ++ move=> w0; rewrite Ew => -[<-] _ _ _.
            rewrite tget_set_eq /= Hrow.
            by case: (cap chain).
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1 /eqP T2 _.
               subst c0 b0.
               move: HbF. rewrite Eptr /=.
               by rewrite HbF1.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1 T2] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2 Hb1')).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
            exists cv1, tg1. split=> //.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 0 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 andbF. }
            by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HD := di_scr HI Ev.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            case: (sv_sc v) HD => HD /=.
            ** exact: Hupscr HD.
            ** rewrite Eph' => _.
               have HSPr : R_SP <> R_RA by [].
               rewrite (tget_set_neq _ _ _ HSPr).
               exact: Hupscr (HD Eph).
            ** exact: Hupscr HD.
            ** by [].
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            exact: (Hupscr _ _ W2).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
            rewrite Eptr /=.
            case EcA: (a_comp A == Pointer.component pc) => //=.
            move/eqP: EcA => EcA.
            have Hne := di_dist HI HA Hcur EcA.
            case Eb: (a_blk A == b) => //.
            move/eqP: Eb => Eb. by case: (Hne Eb).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
            exists cv1, tg1.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 /= andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: Hupscr.
            exact: (di_scr0 HI Hc0 Hg0 Htw).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            have Hek : sv_ek v = true.
            { rewrite ?wone_ek ?wtaint_ek in Eek'.
              move: Hekw. by rewrite Eek'. }
            have HB := di_bodycarg HI Ev Hek.
            rewrite (pend_sig_some Epd0) in HB.
            rewrite (pend_sig_none Epd') Esg.
            exact: (bodycarg_pop HB).
         ++ exact: (di_chain2 HI).
      --
         case E2sp: (is_r r2 R_SP && cseq_eqb (sv_sig v) [::]).
         ++ move=> -[Evv]. subst v'.
            case/andP: E2sp => /is_r_eq Er2 /cseq_eqb_eq Esg0.
            subst r2.
            have Er1 : r1 = R_SP := is_r_eq E1sp. subst r1.
            have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
            have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
            have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
            have Hsp := di_sp HI Ev Eph Hcur.
            have Eptr : ptr
              = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
            { move: Hval1. rewrite Hsp. by move=> [->]. }
            have [F0 F1] := di_f01 HI (Pointer.component pc).
            have Hb1 : (1 == Pointer.block ptr) = false.
            { rewrite Eptr /=.
              case E: (1 == b) => //.
              move/eqP: E => E.
              rewrite -E in HbF1.
              by rewrite HbF1 in F1. }
            have [cv [tg0 [Hcell [T1 T2]]]] := di_pend HI Ev Hcur Epd0.
            rewrite Esg0 /= in T2.
            have Ecl : cl = (cv, tg0).
            { move: Hload_cell. rewrite Eptr /= Nat2Z.id Hcell.
              by move=> [->]. }
            subst cl.
            have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
            move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
              => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
            have Hupmem : forall x, goodu mem F x -> goodu mem' F x
              := fun x => store_goodu Hcm Emem' (F := F) (x := x).
            have Hupscr : forall c0 x,
                scr_val mem c0 x -> scr_val mem' c0 x.
            { move=> c0 x.
              apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
              by rewrite Hb1 andbF. }
            constructor.
            ** move=> r0 Hr0.
               case E0: (is_r r0 R_SP).
               --- by rewrite (is_r_eq E0) tget_set_eq /= T1.
               --- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
                   exact: (di_rtag HI).
            ** move=> r0 H1 H2 H3 H4.
               rewrite (tget_set_neq _ _ _ H2).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               have HA1 : R_AUX1 <> R_SP by [].
               rewrite (tget_set_neq _ _ _ HA1).
               move: Ht1. rewrite /t_le.
               case/orP => /t_eqb_eq E1w; last first.
               { by rewrite /aux_claim E1w. }
               rewrite -E1w.
               have HD := di_a1 HI Ev.
               case Ea1v: (sv_a1 v) HD => HD.
               --- by rewrite /aux_claim Eph'.
               --- exact: HD.
               --- exact: HD.
               --- exact: (Hupmem _ HD).
               --- by [].
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               have HA2 : R_AUX2 <> R_SP by [].
               rewrite (tget_set_neq _ _ _ HA2).
               move: Ht2. rewrite /t_le.
               case/orP => /t_eqb_eq E2w; last first.
               { by rewrite /aux_claim E2w. }
               rewrite -E2w.
               have HD := di_a2 HI Ev.
               case Ea2v: (sv_a2 v) HD => HD.
               --- by rewrite /aux_claim Eph'.
               --- exact: HD.
               --- exact: HD.
               --- exact: (Hupmem _ HD).
               --- by [].
            ** move=> w0; rewrite Ew => -[<-] Hon1.
               have HO : R_ONE <> R_SP by [].
               rewrite (tget_set_neq _ _ _ HO).
               apply: (di_one HI Ev).
               exact: o_le_true Hon Hon1.
            ** move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
               by case: HP.
            ** move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
               by exists b.
            ** move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> w0; rewrite Ew => -[<-] _.
               by rewrite tget_set_eq /= T2.
            ** move=> w0 b0; rewrite Ew => -[<-].
               rewrite Hcur => -[<-].
               rewrite Esg Esg0 Ec => j k1 Hk1.
               by case: j Hk1.
            ** move=> w0 b0 k1; rewrite Ew => -[<-] _.
               by rewrite Epd'.
            ** move=> w0; rewrite Ew => -[<-].
               rewrite Eph' Esg Epd' => HP HPd HK.
               have HSPr : R_RA <> R_SP by [].
               rewrite (tget_set_neq _ _ _ HSPr).
               apply: (di_ra HI Ev) => //.
               --- by rewrite Eph.
               --- by rewrite Epd0.
            ** move=> c0 b0 j cv1 tg1 Hcell1 HbF.
               case Etgt: ([&& c0 == Pointer.component ptr,
                              b0 == Pointer.block ptr
                            & j == Z.to_nat (Pointer.offset ptr)]).
               --- case/and3P: Etgt => /eqP T1' /eqP T2' _.
                   subst c0 b0.
                   move: HbF. rewrite Eptr /=.
                   by rewrite HbF1.
               --- rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                     in Hcell1.
                   have [T1' T2'] := di_mem HI Hcell1 HbF.
                   split=> // Hb1'.
                   exact: (Hupmem _ (T2' Hb1')).
            ** move=> c0 cm0 Hcm0.
               have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
               exists cv1, tg1. split=> //.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 0 == Z.to_nat (Pointer.offset ptr)] = false.
               { by rewrite Hb1 andbF. }
               by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               have HD := di_scr HI Ev.
               move: Hsc. rewrite /sc_le.
               case/orP => /sc_eqb_eq Escw; last first.
               { by rewrite Escw. }
               rewrite -Escw.
               case: (sv_sc v) HD => HD /=.
               --- exact: Hupscr HD.
               --- by rewrite Eph'.
               --- exact: Hupscr HD.
               --- by [].
            ** move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> c0 A. rewrite Ec => Hc0 HA.
               have [W1 W2] := di_scrfor HI Hc0 HA.
               split=> //.
               exact: (Hupscr _ _ W2).
            ** move=> i A HA.
               have [W1 W2 W3 W4 W5] := di_chain HI HA.
               split=> //.
               apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
               rewrite Eptr /=.
               case EcA: (a_comp A == Pointer.component pc) => //=.
               move/eqP: EcA => EcA.
               have Hne := di_dist HI HA Hcur EcA.
               case Eb: (a_blk A == b) => //.
               move/eqP: Eb => Eb. by case: (Hne Eb).
            ** move=> i A b0 HA Hb0. rewrite Ec => HcA.
               exact: (di_dist HI HA Hb0 HcA).
            ** exact: (di_dist2 HI).
            ** move=> c0 b0 HbF.
               have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
               case Ec0: (c0 == Pointer.component ptr).
               --- move/eqP: Ec0 => Ec0. subst c0.
                   eexists. split; first by rewrite Emem' setmE eqxx.
                   move=> /=.
                   have Ecm0 : cm0 = cm
                     by move: Hcm0; rewrite Hcm => -[].
                   by subst cm0.
               --- exists cm0. split=> //.
                   rewrite (store_getm_other Emem') //.
                   by move=> E; rewrite E eqxx in Ec0.
            ** exact: (di_f01 HI).
            ** move=> c0 cm0.
               apply: (store_nb2 Hcm Emem').
               exact: (di_nb2 HI).
            ** move=> c0 S Hs.
               apply: (store_dom Emem').
               exact: (di_dom HI Hs).
            ** exact: (di_level HI).
            ** move=> c0 cm0 Hcm0.
               have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
               exists cv1, tg1.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 1 == Z.to_nat (Pointer.offset ptr)] = false.
               { by rewrite Hb1 /= andbF. }
               rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
               split=> //. split=> //.
               exact: (Hupmem _ Hgd1).
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               apply: (di_ek HI Ev).
               rewrite ?wone_ek ?wtaint_ek in Eek'.
               move: Hekw. by rewrite Eek'.
            ** move=> i X HX Hnw.
               case: (di_nwshadow HI HX Hnw)
                 => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
               { right. exists j, W. by split. }
               left. split; last exact: HPre.
               by rewrite Ec.
            ** move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
            ** move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
               apply: Hupscr.
               exact: (di_scr0 HI Hc0 Hg0 Htw).
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               apply: (di_ekwin HI Ev).
               rewrite ?wone_ek ?wtaint_ek in Eek'.
               move: Hekw. by rewrite Eek'.
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               have Hek : sv_ek v = true.
               { rewrite ?wone_ek ?wtaint_ek in Eek'.
                 move: Hekw. by rewrite Eek'. }
               have HB := di_bodycarg HI Ev Hek.
               rewrite (pend_sig_some Epd0) in HB.
               rewrite (pend_sig_none Epd') Esg.
               exact: (bodycarg_pop HB).
            ** exact: (di_chain2 HI).
         ++ case E2a1: (is_r r2 R_AUX1 && ~~ cseq_eqb (sv_sig v) [::])
              => // -[Evv]. subst v'.
            case/andP: E2a1 => E2a1 Hsgne.
            have Er2 : r2 = R_AUX1 := is_r_eq E2a1. subst r2.
            have Er1 : r1 = R_SP := is_r_eq E1sp. subst r1.
            have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
            have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
            have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
            have Hsp := di_sp HI Ev Eph Hcur.
            have Eptr : ptr
              = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
            { move: Hval1. rewrite Hsp. by move=> [->]. }
            have [F0 F1] := di_f01 HI (Pointer.component pc).
            have Hb1 : (1 == Pointer.block ptr) = false.
            { rewrite Eptr /=.
              case E: (1 == b) => //.
              move/eqP: E => E.
              rewrite -E in HbF1.
              by rewrite HbF1 in F1. }
            have [cv [tg0 [Hcell [T1 T2]]]] := di_pend HI Ev Hcur Epd0.
            have Ecl : cl = (cv, tg0).
            { move: Hload_cell. rewrite Eptr /= Nat2Z.id Hcell.
              by move=> [->]. }
            subst cl.
            have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
            move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
              => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
            have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
            have Hupmem : forall x, goodu mem F x -> goodu mem' F x
              := fun x => store_goodu Hcm Emem' (F := F) (x := x).
            have Hupscr : forall c0 x,
                scr_val mem c0 x -> scr_val mem' c0 x.
            { move=> c0 x.
              apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
              by rewrite Hb1 andbF. }
            constructor.
            ** move=> r0 Hr0.
               case E0: (is_r r0 R_AUX1).
               --- by rewrite (is_r_eq E0) tget_set_eq /= T1.
               --- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
                   exact: (di_rtag HI).
            ** move=> r0 H1 H2 H3 H4.
               rewrite (tget_set_neq _ _ _ H3).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               rewrite tget_set_eq /=.
               move: Ht1. rewrite /t_le.
               case/orP => /t_eqb_eq E1w; last first.
               { by rewrite /aux_claim E1w. }
               rewrite -E1w.
               rewrite /aux_claim Eph' Esg.
               case Esgv: (sv_sig v) T2 => [|kk tl] T2.
               --- exact: T2.
               --- by case: kk T2 {Esgv} => // T2; case: tl T2 => //.
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               have HA2 : R_AUX2 <> R_AUX1 by [].
               rewrite (tget_set_neq _ _ _ HA2).
               apply: (aux_claim_le_nopd Ephw Esg Ht2).
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a2 HI Ev).
            ** move=> w0; rewrite Ew => -[<-] Hon1.
               have HO : R_ONE <> R_AUX1 by [].
               rewrite (tget_set_neq _ _ _ HO).
               apply: (di_one HI Ev).
               exact: o_le_true Hon Hon1.
            ** move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
               by case: HP.
            ** move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
               by exists b.
            ** move=> w0 b0; rewrite Ew => -[<-] _.
               rewrite Hcur => -[<-].
               have HSPa : R_SP <> R_AUX1 by [].
               rewrite (tget_set_neq _ _ _ HSPa) Esg Ec.
               exact: Hsp.
            ** move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> w0 b0; rewrite Ew => -[<-].
               rewrite Hcur => -[<-].
               rewrite Esg Ec => j k1 Hk1.
               have HF := di_frame HI Ev Hcur.
               have [cv1 [tg1 [Hcell1 Hrow1]]] := HF j k1 Hk1.
               exists cv1, tg1.
               have Hjlt : j < size (sv_sig v) := nth_error_size Hk1.
               have Hne3 : [&& Pointer.component pc
                                 == Pointer.component ptr,
                              b == Pointer.block ptr
                            & j == Z.to_nat (Pointer.offset ptr)]
                           = false.
               { rewrite Eptr /= !eqxx /= Nat2Z.id.
                 by rewrite (ltn_eqF Hjlt). }
               rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
               split=> //.
               case: k1 {Hk1} Hrow1 => //= -[T1' T2']; split=> //;
               exact: (Hupmem _ T2').
            ** move=> w0 b0 k1; rewrite Ew => -[<-] _.
               by rewrite Epd'.
            ** move=> w0; rewrite Ew => -[<-].
               rewrite Eph' Esg Epd' => HP HPd HK.
               have HRAa : R_RA <> R_AUX1 by [].
               rewrite (tget_set_neq _ _ _ HRAa).
               apply: (di_ra HI Ev) => //.
               --- by rewrite Eph.
               --- by rewrite Epd0.
            ** move=> c0 b0 j cv1 tg1 Hcell1 HbF.
               case Etgt: ([&& c0 == Pointer.component ptr,
                              b0 == Pointer.block ptr
                            & j == Z.to_nat (Pointer.offset ptr)]).
               --- case/and3P: Etgt => /eqP T1' /eqP T2' _.
                   subst c0 b0.
                   move: HbF. rewrite Eptr /=.
                   by rewrite HbF1.
               --- rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                     in Hcell1.
                   have [T1' T2'] := di_mem HI Hcell1 HbF.
                   split=> // Hb1'.
                   exact: (Hupmem _ (T2' Hb1')).
            ** move=> c0 cm0 Hcm0.
               have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
               exists cv1, tg1. split=> //.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 0 == Z.to_nat (Pointer.offset ptr)]
                           = false.
               { by rewrite Hb1 andbF. }
               by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            ** move=> w0; rewrite Ew => -[<-]. rewrite Ec.
               have HD := di_scr HI Ev.
               move: Hsc. rewrite /sc_le.
               case/orP => /sc_eqb_eq Escw; last first.
               { by rewrite Escw. }
               rewrite -Escw.
               case: (sv_sc v) HD => HD /=.
               --- exact: Hupscr HD.
               --- rewrite Eph' => _.
                   have HSPa : R_SP <> R_AUX1 by [].
                   rewrite (tget_set_neq _ _ _ HSPa).
                   exact: Hupscr (HD Eph).
               --- exact: Hupscr HD.
               --- by [].
            ** move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
            ** move=> c0 A. rewrite Ec => Hc0 HA.
               have [W1 W2] := di_scrfor HI Hc0 HA.
               split=> //.
               exact: (Hupscr _ _ W2).
            ** move=> i A HA.
               have [W1 W2 W3 W4 W5] := di_chain HI HA.
               split=> //.
               apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
               rewrite Eptr /=.
               case EcA: (a_comp A == Pointer.component pc) => //=.
               move/eqP: EcA => EcA.
               have Hne := di_dist HI HA Hcur EcA.
               case Eb: (a_blk A == b) => //.
               move/eqP: Eb => Eb. by case: (Hne Eb).
            ** move=> i A b0 HA Hb0. rewrite Ec => HcA.
               exact: (di_dist HI HA Hb0 HcA).
            ** exact: (di_dist2 HI).
            ** move=> c0 b0 HbF.
               have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
               case Ec0: (c0 == Pointer.component ptr).
               --- move/eqP: Ec0 => Ec0. subst c0.
                   eexists. split; first by rewrite Emem' setmE eqxx.
                   move=> /=.
                   have Ecm0 : cm0 = cm
                     by move: Hcm0; rewrite Hcm => -[].
                   by subst cm0.
               --- exists cm0. split=> //.
                   rewrite (store_getm_other Emem') //.
                   by move=> E; rewrite E eqxx in Ec0.
            ** exact: (di_f01 HI).
            ** move=> c0 cm0.
               apply: (store_nb2 Hcm Emem').
               exact: (di_nb2 HI).
            ** move=> c0 S Hs.
               apply: (store_dom Emem').
               exact: (di_dom HI Hs).
            ** exact: (di_level HI).
            ** move=> c0 cm0 Hcm0.
               have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
               exists cv1, tg1.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 1 == Z.to_nat (Pointer.offset ptr)]
                           = false.
               { by rewrite Hb1 /= andbF. }
               rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
               split=> //. split=> //.
               exact: (Hupmem _ Hgd1).
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               apply: (di_ek HI Ev).
               rewrite ?wone_ek ?wtaint_ek in Eek'.
               move: Hekw. by rewrite Eek'.
            ** move=> i X HX Hnw.
               case: (di_nwshadow HI HX Hnw)
                 => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
               { right. exists j, W. by split. }
               left. split; last exact: HPre.
               by rewrite Ec.
            ** move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
            ** move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
               apply: Hupscr.
               exact: (di_scr0 HI Hc0 Hg0 Htw).
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               apply: (di_ekwin HI Ev).
               rewrite ?wone_ek ?wtaint_ek in Eek'.
               move: Hekw. by rewrite Eek'.
            ** move=> w0; rewrite Ew => -[<-] Hekw.
               have Hek : sv_ek v = true.
               { rewrite ?wone_ek ?wtaint_ek in Eek'.
                 move: Hekw. by rewrite Eek'. }
               have HB := di_bodycarg HI Ev Hek.
               rewrite (pend_sig_some Epd0) in HB.
               rewrite (pend_sig_none Epd') Esg.
               exact: (bodycarg_pop HB).
            ** exact: (di_chain2 HI).
      --
         case E2or: (is_r r2 R_SP || is_r r2 R_RA) => // -[Evv].
         subst v'.
         have E2sp' : is_r r2 R_SP = false.
         { by move: E2or; case: (is_r r2 R_SP). }
         have E2ra : is_r r2 R_RA = false.
         { by move: E2or; case: (is_r r2 R_RA) => //; rewrite orbT. }
         have Er1 : r1 = R_SP := is_r_eq E1sp. subst r1.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have Eptr : ptr
           = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
         { move: Hval1. rewrite Hsp. by move=> [->]. }
         have [F0 F1] := di_f01 HI (Pointer.component pc).
         have Hb1 : (1 == Pointer.block ptr) = false.
         { rewrite Eptr /=.
           case E: (1 == b) => //.
           move/eqP: E => E.
           rewrite -E in HbF1.
           by rewrite HbF1 in F1. }
         have [cv [tg0 [Hcell [T1 T2]]]] := di_pend HI Ev Hcur Epd0.
         have Ecl : cl = (cv, tg0).
         { move: Hload_cell. rewrite Eptr /= Nat2Z.id Hcell.
           by move=> [->]. }
         subst cl.
         have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields r2 AU
           (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v) (sv_sc v)
               (sv_one v) (sv_ek v) (sv_arg v)).
         have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
           := wone_fields r2 false (wtaint r2 AU
                (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                    (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))).
         have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
           := warg_w_fields r2 (wone r2 false (wtaint r2 AU
                (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                    (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v)))).
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         rewrite G1 W2ph W1ph /= in Eph'.
         rewrite G2 W2sg W1sg /= in Esg.
         rewrite G3 W2pd W1pd /= in Epd'.
         rewrite G4 W2sc W1sc /= in Hsc.
         rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
         rewrite G7 in Hon. rewrite G8 in Eek'.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have Hupscr : forall c0 x,
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x.
           apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
           by rewrite Hb1 andbF. }
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 r2).
            ** by rewrite (is_r_eq E0) tget_set_eq /= T1.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            case E0: (is_r r0 r2).
            ** rewrite (is_r_eq E0) tget_set_eq /=.
               exact: (Hupmem _ T2).
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E21: (is_r r2 R_AUX1).
            ** have Ea1 : sv_a1 (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))) = AU
                 by rewrite /wtaint E21.
               move: Ht1. rewrite Ea1 /t_le.
               case/orP => /t_eqb_eq E1w; last first.
               { by rewrite /aux_claim E1w. }
               rewrite -E1w.
               rewrite (is_r_eq E21) tget_set_eq /=.
               exact: (Hupmem _ T2).
            ** have Ea1 : sv_a1 (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))) = sv_a1 v.
               { rewrite /wtaint E21. by case: (is_r r2 R_AUX2). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E21)).
               move: Ht1. rewrite Ea1 => Ht1'.
               apply: (aux_claim_le_nopd Ephw Esg Ht1').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E22: (is_r r2 R_AUX2).
            ** have Ea2 : sv_a2 (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))) = AU.
               { rewrite /wtaint E22.
                 by case E21: (is_r r2 R_AUX1);
                    rewrite //= (is_r_eq E21) in E22. }
               move: Ht2. rewrite Ea2 /t_le.
               case/orP => /t_eqb_eq E2w; last first.
               { by rewrite /aux_claim E2w. }
               rewrite -E2w.
               rewrite (is_r_eq E22) tget_set_eq /=.
               exact: (Hupmem _ T2).
            ** have Ea2 : sv_a2 (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))) = sv_a2 v.
               { rewrite /wtaint E22. by case: (is_r r2 R_AUX1). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E22)).
               move: Ht2. rewrite Ea2 => Ht2'.
               apply: (aux_claim_le_nopd Ephw Esg Ht2').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            case E0: (is_r r2 R_ONE).
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v)))) = false
                 by rewrite /wone E0.
               move: (o_le_true Hon Hon1). by rewrite Eone.
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v)))) = sv_one v.
               { rewrite /wone E0.
                 by have [_ _ _ _ ->] := wtaint_fields r2 AU
                   (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                       (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v)). }
               move: Hon. rewrite Eone => Hon'.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E0)).
               apply: (di_one HI Ev).
               exact: o_le_true Hon' Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec => j k1 Hk1.
            have HF := di_frame HI Ev Hcur.
            have [cv1 [tg1 [Hcell1 Hrow1]]] := HF j k1 Hk1.
            exists cv1, tg1.
            have Hjlt : j < size (sv_sig v) := nth_error_size Hk1.
            have Hne3 : [&& Pointer.component pc
                              == Pointer.component ptr,
                           b == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)] = false.
            { rewrite Eptr /= !eqxx /= Nat2Z.id.
              by rewrite (ltn_eqF Hjlt). }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //.
            case: k1 {Hk1} Hrow1 => //= -[T1' T2']; split=> //;
            exact: (Hupmem _ T2').
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd'.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2ra)).
            apply: (di_ra HI Ev) => //.
            ** by rewrite Eph.
            ** by rewrite Epd0.
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1' /eqP T2' _.
               subst c0 b0.
               move: HbF. rewrite Eptr /=.
               by rewrite HbF1.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1' T2'] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2' Hb1')).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
            exists cv1, tg1. split=> //.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 0 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 andbF. }
            by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HD := di_scr HI Ev.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            case: (sv_sc v) HD => HD /=.
            ** exact: Hupscr HD.
            ** rewrite Eph' => _.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')).
               exact: Hupscr (HD Eph).
            ** exact: Hupscr HD.
            ** by [].
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            exact: (Hupscr _ _ W2).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
            rewrite Eptr /=.
            case EcA: (a_comp A == Pointer.component pc) => //=.
            move/eqP: EcA => EcA.
            have Hne := di_dist HI HA Hcur EcA.
            case Eb: (a_blk A == b) => //.
            move/eqP: Eb => Eb. by case: (Hne Eb).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
            exists cv1, tg1.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 /= andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: Hupscr.
            exact: (di_scr0 HI Hc0 Hg0 Htw).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            have Hek : sv_ek v = true.
            { rewrite ?wone_ek ?wtaint_ek in Eek'.
              move: Hekw. by rewrite Eek'. }
            have HB := di_bodycarg HI Ev Hek.
            rewrite (pend_sig_some Epd0) in HB.
            rewrite (pend_sig_none Epd') Esg.
            exact: (bodycarg_pop HB).
         ++ exact: (di_chain2 HI).
      --
         case E2arg: (is_r r2 R_ARG) => // -[Evv]. subst v'.
         have Er2 : r2 = R_ARG := is_r_eq E2arg. subst r2.
         have Er1 : r1 = R_SP := is_r_eq E1sp. subst r1.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have Eptr : ptr
           = (Pointer.component pc, b, Z.of_nat (size (sv_sig v))).
         { move: Hval1. rewrite Hsp. by move=> [->]. }
         have [F0 F1] := di_f01 HI (Pointer.component pc).
         have Hb1 : (1 == Pointer.block ptr) = false.
         { rewrite Eptr /=.
           case E: (1 == b) => //.
           move/eqP: E => E.
           rewrite -E in HbF1.
           by rewrite HbF1 in F1. }
         have [cv [tg0 [Hcell [T1 T2]]]] := di_pend HI Ev Hcur Epd0.
         have Ecl : cl = (cv, tg0).
         { move: Hload_cell. rewrite Eptr /= Nat2Z.id Hcell.
           by move=> [->]. }
         subst cl.
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
           => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph' Eph.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have Hupscr : forall c0 x,
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x.
           apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
           by rewrite Hb1 andbF. }
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 R_ARG).
            ** by rewrite (is_r_eq E0) tget_set_eq /= T1.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            case E0: (is_r r0 R_ARG).
            ** rewrite (is_r_eq E0) tget_set_eq /=.
               exact: (Hupmem _ T2).
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA1 : R_AUX1 <> R_ARG by [].
            rewrite (tget_set_neq _ _ _ HA1).
            apply: (aux_claim_le_nopd Ephw Esg Ht1).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA2 : R_AUX2 <> R_ARG by [].
            rewrite (tget_set_neq _ _ _ HA2).
            apply: (aux_claim_le_nopd Ephw Esg Ht2).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            have HO : R_ONE <> R_ARG by [].
            rewrite (tget_set_neq _ _ _ HO).
            apply: (di_one HI Ev).
            exact: o_le_true Hon Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            have HSPr : R_SP <> R_ARG by [].
            rewrite (tget_set_neq _ _ _ HSPr) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec => j k1 Hk1.
            have HF := di_frame HI Ev Hcur.
            have [cv1 [tg1 [Hcell1 Hrow1]]] := HF j k1 Hk1.
            exists cv1, tg1.
            have Hjlt : j < size (sv_sig v) := nth_error_size Hk1.
            have Hne3 : [&& Pointer.component pc
                              == Pointer.component ptr,
                           b == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)] = false.
            { rewrite Eptr /= !eqxx /= Nat2Z.id.
              by rewrite (ltn_eqF Hjlt). }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //.
            case: k1 {Hk1} Hrow1 => //= -[T1' T2']; split=> //;
            exact: (Hupmem _ T2').
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd'.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            have HRAr : R_RA <> R_ARG by [].
            rewrite (tget_set_neq _ _ _ HRAr).
            apply: (di_ra HI Ev) => //.
            ** by rewrite Eph.
            ** by rewrite Epd0.
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1' /eqP T2' _.
               subst c0 b0.
               move: HbF. rewrite Eptr /=.
               by rewrite HbF1.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1' T2'] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2' Hb1')).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
            exists cv1, tg1. split=> //.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 0 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 andbF. }
            by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HD := di_scr HI Ev.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            case: (sv_sc v) HD => HD /=.
            ** exact: Hupscr HD.
            ** rewrite Eph' => _.
               have HSPr : R_SP <> R_ARG by [].
               rewrite (tget_set_neq _ _ _ HSPr).
               exact: Hupscr (HD Eph).
            ** exact: Hupscr HD.
            ** by [].
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            exact: (Hupscr _ _ W2).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            apply: (store_frame_ok_away Hcm Hchunk Hupd Emem') W4.
            rewrite Eptr /=.
            case EcA: (a_comp A == Pointer.component pc) => //=.
            move/eqP: EcA => EcA.
            have Hne := di_dist HI HA Hcur EcA.
            case Eb: (a_blk A == b) => //.
            move/eqP: Eb => Eb. by case: (Hne Eb).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
            exists cv1, tg1.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1 /= andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: Hupscr.
            exact: (di_scr0 HI Hc0 Hg0 Htw).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            have Hek : sv_ek v = true.
            { rewrite ?wone_ek ?wtaint_ek in Eek'.
              move: Hekw. by rewrite Eek'. }
            have HB := di_bodycarg HI Ev Hek.
            rewrite (pend_sig_some Epd0) in HB.
            rewrite (pend_sig_none Epd') Esg.
            exact: (bodycarg_pop HB).
         ++ exact: (di_chain2 HI).
    *
      case Epd0: (sv_pend v) => [k0|] //.
      case Etr1: (rtaint v r1) => //.
      --
         case Eg: ([&& is_r r2 R_AUX1, sc_eqb (sv_sc v) SCnone
                     & cseq_eqb (sv_sig v) [:: CSp]]) => // -[Evv].
         subst v'.
         case/and3P: Eg => /is_r_eq Er2 /sc_eqb_eq Esc0 /cseq_eqb_eq Esg1.
         subst r2.
         have E1ra : is_r r1 R_RA = false.
         { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
         have Hp1 : Transitional.val (Transitional.Register.get r1 regs)
                    = Ptr (Pointer.component pc, 1, 0%Z).
         { have Hrc := rtaint_claim HI Ev E1sp E1ra.
           by rewrite Etr1 in Hrc. }
         have Eptr : ptr = (Pointer.component pc, 1, 0%Z).
         { move: Hval1. rewrite Hp1. by move=> [->]. }
         have Ecp : Pointer.component ptr = Pointer.component pc
           by rewrite Eptr.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have [F0 F1] := di_f01 HI (Pointer.component pc).
         have HcmC : getm mem (Pointer.component pc) = Some cm.
         { by rewrite -Ecp. }
         have HD0 := di_scr HI Ev.
         rewrite Esc0 in HD0.
         have [cvS [tgS [HcellS HvS]]] := HD0.
         have [cvT [tgT [HcellT HtagT]]] := di_scrtag HI HcmC.
         rewrite HcellS in HcellT.
         case: HcellT => E1 E2. subst cvT tgT.
         have Ecl : cl = (cvS, tgS).
         { move: Hload_cell. rewrite Eptr /= HcellS.
           by move=> [->]. }
         subst cl.
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields R_AUX1 ASp v.
         rewrite W1ph in Eph'. rewrite W1sg in Esg.
         rewrite W1pd in Epd'. rewrite W1sc in Hsc.
         have Ea1' : sv_a1 (wtaint R_AUX1 ASp v) = ASp by [].
         rewrite Ea1' in Ht1.
         have Ea2' : sv_a2 (wtaint R_AUX1 ASp v) = sv_a2 v by [].
         rewrite Ea2' in Ht2.
         have Eon' : sv_one (wtaint R_AUX1 ASp v) = sv_one v by [].
         rewrite Eon' in Hon.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph'.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have Hupscr_o : forall c0 x,
             (c0 == Pointer.component pc) = false ->
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x Hne.
           apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
           by rewrite Ecp Hne. }
         have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg
             carry cscr rcap,
             b1 \in F c1 ->
             frame_ok F mem c1 b1 sg carry cscr rcap ->
             frame_ok F mem' c1 b1 sg carry cscr rcap.
         { move=> c1 b1 sg carry cscr rcap Hb1'.
           apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
           rewrite Eptr /=.
           case E: (c1 == Pointer.component pc) => //=.
           case Eb: (b1 == 1) => //.
           move/eqP: Eb => Eb. subst b1.
           move/eqP: E => E. subst c1.
           by rewrite F1 in Hb1'. }
         have Hcs := store_cell_same Hupd Emem'.
         move: Hcs. rewrite Eptr /= => Hcs.
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 R_AUX1).
            ** by rewrite (is_r_eq E0) tget_set_eq /= HtagT.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            rewrite (tget_set_neq _ _ _ H3).
            apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            rewrite tget_set_eq /=.
            move: Ht1. rewrite /t_le.
            case/orP => /t_eqb_eq E1w; last first.
            { by rewrite /aux_claim E1w. }
            rewrite -E1w.
            rewrite /aux_claim Eph' Eph Esg Esg1.
            by rewrite HvS.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HA2 : R_AUX2 <> R_AUX1 by [].
            rewrite (tget_set_neq _ _ _ HA2).
            apply: (aux_claim_le_nopd Ephw Esg Ht2).
            apply: (store_aux_claim Hcm Emem').
            exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            have HO : R_ONE <> R_AUX1 by [].
            rewrite (tget_set_neq _ _ _ HO).
            apply: (di_one HI Ev).
            exact: o_le_true Hon Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            have HSPa : R_SP <> R_AUX1 by [].
            rewrite (tget_set_neq _ _ _ HSPa) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec.
            exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd' Epd0.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            have HRAa : R_RA <> R_AUX1 by [].
            rewrite (tget_set_neq _ _ _ HRAa).
            by apply: (di_ra HI Ev) => //; rewrite Eph.
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1' /eqP T2' /eqP T3'.
               subst c0 b0 j.
               move: Hcell1. rewrite Eptr /= Hcs => -[<- _].
               split.
               --- by rewrite /= HtagT.
               --- move=> Hb1'. by case: Hb1'.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1' T2'] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2' Hb1')).
         ++ move=> c0 cm0 Hcm0.
            case Ec0: (c0 == Pointer.component pc).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists _, _. split; first exact: Hcs.
               by rewrite /= HtagT.
            ** have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
               exists cv1, tg1. split=> //.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 0 == Z.to_nat (Pointer.offset ptr)]
                           = false.
               { by rewrite Ecp Ec0. }
               by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            move: Hsc. rewrite Esc0 /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            eexists _, _. split; first exact: Hcs.
            by rewrite /= HvS.
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            apply: (Hupscr_o _ _ _ W2).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            exact: (Hupfr _ _ _ _ _ _ W3 W4).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
            exists cv1, tg1.
            have E31 : (1 == Z.to_nat (Pointer.offset ptr)) = false
              by rewrite Eptr.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite E31 !andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: (Hupscr_o _ _ _ (di_scr0 HI Hc0 Hg0 Htw)).
            case E: (c0 == Pointer.component pc) => //.
            move/eqP: E => E. by case: (Hc0 E).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            rewrite (pend_sig_eq Esg Epd').
            apply: (di_bodycarg HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ exact: (di_chain2 HI).
      --
         case E2or: (is_r r2 R_SP || is_r r2 R_RA) => // -[Evv].
         subst v'.
         have E2sp' : is_r r2 R_SP = false.
         { by move: E2or; case: (is_r r2 R_SP). }
         have E2ra : is_r r2 R_RA = false.
         { by move: E2or; case: (is_r r2 R_RA) => //; rewrite orbT. }
         have E1ra : is_r r1 R_RA = false.
         { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
         have Hp1 : Transitional.val (Transitional.Register.get r1 regs)
                    = Ptr (Pointer.component pc, 1, 1%Z).
         { have Hrc := rtaint_claim HI Ev E1sp E1ra.
           by rewrite Etr1 in Hrc. }
         have Eptr : ptr = (Pointer.component pc, 1, 1%Z).
         { move: Hval1. rewrite Hp1. by move=> [->]. }
         have Ecp : Pointer.component ptr = Pointer.component pc
           by rewrite Eptr.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have [F0 F1] := di_f01 HI (Pointer.component pc).
         have HcmC : getm mem (Pointer.component pc) = Some cm.
         { by rewrite -Ecp. }
         have [cvF [tgF [HcellF [HtagF HgdF]]]] := di_flag HI HcmC.
         have Ecl : cl = (cvF, tgF).
         { move: Hload_cell. rewrite Eptr /= HcellF.
           by move=> [->]. }
         subst cl.
         have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields r2 AU v.
         have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
           := wone_fields r2 false (wtaint r2 AU v).
         have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
           := warg_w_fields r2 (wone r2 false (wtaint r2 AU v)).
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         rewrite G1 W2ph W1ph in Eph'.
         rewrite G2 W2sg W1sg in Esg.
         rewrite G3 W2pd W1pd in Epd'.
         rewrite G4 W2sc W1sc in Hsc.
         rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
         rewrite G7 in Hon. rewrite G8 in Eek'.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph'.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have E30 : (0 == Z.to_nat (Pointer.offset ptr)) = false
           by rewrite Eptr.
         have Hupscr : forall c0 x,
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x [cv' [tg' [Hcell' Hv']]].
           exists cv', tg'. split=> //.
           have Hne3 : [&& c0 == Pointer.component ptr,
                          1 == Pointer.block ptr
                        & 0 == Z.to_nat (Pointer.offset ptr)] = false.
           { by rewrite E30 !andbF. }
           by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3). }
         have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg
             carry cscr rcap,
             b1 \in F c1 ->
             frame_ok F mem c1 b1 sg carry cscr rcap ->
             frame_ok F mem' c1 b1 sg carry cscr rcap.
         { move=> c1 b1 sg carry cscr rcap Hb1'.
           apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
           rewrite Eptr /=.
           case E: (c1 == Pointer.component pc) => //=.
           case Eb: (b1 == 1) => //.
           move/eqP: Eb => Eb. subst b1.
           move/eqP: E => E. subst c1.
           by rewrite F1 in Hb1'. }
         have Hcs := store_cell_same Hupd Emem'.
         move: Hcs. rewrite Eptr /= => Hcs.
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 r2).
            ** by rewrite (is_r_eq E0) tget_set_eq /= HtagF.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            case E0: (is_r r0 r2).
            ** rewrite (is_r_eq E0) tget_set_eq /=.
               exact: (Hupmem _ HgdF).
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E21: (is_r r2 R_AUX1).
            ** have Ea1 : sv_a1 (wtaint r2 AU v) = AU
                 by rewrite /wtaint E21.
               move: Ht1. rewrite Ea1 /t_le.
               case/orP => /t_eqb_eq E1w; last first.
               { by rewrite /aux_claim E1w. }
               rewrite -E1w.
               rewrite (is_r_eq E21) tget_set_eq /=.
               exact: (Hupmem _ HgdF).
            ** have Ea1 : sv_a1 (wtaint r2 AU v) = sv_a1 v.
               { rewrite /wtaint E21. by case: (is_r r2 R_AUX2). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E21)).
               move: Ht1. rewrite Ea1 => Ht1'.
               apply: (aux_claim_le_nopd Ephw Esg Ht1').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E22: (is_r r2 R_AUX2).
            ** have Ea2 : sv_a2 (wtaint r2 AU v) = AU.
               { rewrite /wtaint E22.
                 by case E21: (is_r r2 R_AUX1);
                    rewrite //= (is_r_eq E21) in E22. }
               move: Ht2. rewrite Ea2 /t_le.
               case/orP => /t_eqb_eq E2w; last first.
               { by rewrite /aux_claim E2w. }
               rewrite -E2w.
               rewrite (is_r_eq E22) tget_set_eq /=.
               exact: (Hupmem _ HgdF).
            ** have Ea2 : sv_a2 (wtaint r2 AU v) = sv_a2 v.
               { rewrite /wtaint E22. by case: (is_r r2 R_AUX1). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E22)).
               move: Ht2. rewrite Ea2 => Ht2'.
               apply: (aux_claim_le_nopd Ephw Esg Ht2').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            case E0: (is_r r2 R_ONE).
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU v))
                           = false
                 by rewrite /wone E0.
               move: (o_le_true Hon Hon1). by rewrite Eone.
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU v))
                           = sv_one v.
               { rewrite /wone E0.
                 by have [_ _ _ _ ->] := wtaint_fields r2 AU v. }
               move: Hon. rewrite Eone => Hon'.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E0)).
               apply: (di_one HI Ev).
               exact: o_le_true Hon' Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec.
            exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd' Epd0.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2ra)).
            exact: (di_ra HI Ev HP HPd HK).
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1' /eqP T2' /eqP T3'.
               subst c0 b0 j.
               move: Hcell1. rewrite Eptr /= Hcs => -[<- _].
               split.
               --- by rewrite /= HtagF.
               --- move=> Hb1'. by case: Hb1'.
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1' T2'] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2' Hb1')).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
            exists cv1, tg1. split=> //.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 0 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite E30 !andbF. }
            by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HD := di_scr HI Ev.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            case: (sv_sc v) HD => HD /=.
            ** exact: Hupscr HD.
            ** rewrite Eph' => HPB.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')).
               exact: Hupscr (HD HPB).
            ** exact: Hupscr HD.
            ** by [].
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            exact: (Hupscr _ _ W2).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            exact: (Hupfr _ _ _ _ _ _ W3 W4).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            case Ec0: (c0 == Pointer.component pc).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists _, _. split; first exact: Hcs.
               split.
               --- by rewrite /= HtagF.
               --- rewrite /=. exact: (Hupmem _ HgdF).
            ** have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
               { move: Hcm0. rewrite Emem' setmE.
                 case E: (c0 == Pointer.component ptr) => H.
                 - move/eqP: E => E. subst c0. by exists cm.
                 - by exists cm0. }
               have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
               exists cv1, tg1.
               have Hne3 : [&& c0 == Pointer.component ptr,
                              1 == Pointer.block ptr
                            & 1 == Z.to_nat (Pointer.offset ptr)]
                           = false.
               { by rewrite Ecp Ec0. }
               rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
               split=> //. split=> //.
               exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: Hupscr.
            exact: (di_scr0 HI Hc0 Hg0 Htw).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            rewrite (pend_sig_eq Esg Epd').
            apply: (di_bodycarg HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ exact: (di_chain2 HI).
      --
         case E2or: (is_r r2 R_SP || is_r r2 R_RA) => // -[Evv].
         subst v'.
         have E2sp' : is_r r2 R_SP = false.
         { by move: E2or; case: (is_r r2 R_SP). }
         have E2ra : is_r r2 R_RA = false.
         { by move: E2or; case: (is_r r2 R_RA) => //; rewrite orbT. }
         have E1ra : is_r r1 R_RA = false.
         { by move: Etr1; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
         have Hgd : goodu mem F (Ptr ptr).
         { have Hrc := rtaint_claim HI Ev E1sp E1ra.
           rewrite Etr1 Hval1 in Hrc.
           exact: Hrc. }
         have [HbFp Hb1p Hvb] := Hgd ptr (erefl _).
         have Hb1e : (1 == Pointer.block ptr) = false.
         { case E: (1 == Pointer.block ptr) => //.
           move/eqP: E => E. case: Hb1p. by rewrite -E. }
         have Ecl : cl = (cl.1, cl.2) by case: (cl).
         rewrite Ecl in Hload_cell.
         have [T1c T2c] := di_mem HI Hload_cell HbFp.
         have Hgv : goodu mem F (Transitional.val cl.1) := T2c Hb1p.
         have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
         have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
         have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
         have Hsp := di_sp HI Ev Eph Hcur.
         have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields r2 AU v.
         have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
           := wone_fields r2 false (wtaint r2 AU v).
         have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
           := warg_w_fields r2 (wone r2 false (wtaint r2 AU v)).
         have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
         rewrite G1 W2ph W1ph in Eph'.
         rewrite G2 W2sg W1sg in Esg.
         rewrite G3 W2pd W1pd in Epd'.
         rewrite G4 W2sc W1sc in Hsc.
         rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
         rewrite G7 in Hon. rewrite G8 in Eek'.
         have Ephw : sv_ph w = sv_ph v by rewrite Eph'.
         have Hupmem : forall x, goodu mem F x -> goodu mem' F x
           := fun x => store_goodu Hcm Emem' (F := F) (x := x).
         have Hupscr : forall c0 x,
             scr_val mem c0 x -> scr_val mem' c0 x.
         { move=> c0 x.
           apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
           by rewrite Hb1e andbF. }
         have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg
             carry cscr rcap,
             b1 \in F c1 ->
             frame_ok F mem c1 b1 sg carry cscr rcap ->
             frame_ok F mem' c1 b1 sg carry cscr rcap.
         { move=> c1 b1 sg carry cscr rcap Hb1'.
           apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
           case E: (c1 == Pointer.component ptr) => //=.
           case Eb: (b1 == Pointer.block ptr) => //.
           move/eqP: E => E. subst c1.
           move/eqP: Eb => Eb. subst b1.
           by rewrite HbFp in Hb1'. }
         have Hcs := store_cell_same Hupd Emem'.
         constructor.
         ++ move=> r0 Hr0.
            case E0: (is_r r0 r2).
            ** by rewrite (is_r_eq E0) tget_set_eq /= T1c.
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               exact: (di_rtag HI).
         ++ move=> r0 H1 H2 H3 H4.
            case E0: (is_r r0 r2).
            ** rewrite (is_r_eq E0) tget_set_eq /=.
               exact: (Hupmem _ Hgv).
            ** rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
               apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E21: (is_r r2 R_AUX1).
            ** have Ea1 : sv_a1 (wtaint r2 AU v) = AU
                 by rewrite /wtaint E21.
               move: Ht1. rewrite Ea1 /t_le.
               case/orP => /t_eqb_eq E1w; last first.
               { by rewrite /aux_claim E1w. }
               rewrite -E1w.
               rewrite (is_r_eq E21) tget_set_eq /=.
               exact: (Hupmem _ Hgv).
            ** have Ea1 : sv_a1 (wtaint r2 AU v) = sv_a1 v.
               { rewrite /wtaint E21. by case: (is_r r2 R_AUX2). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E21)).
               move: Ht1. rewrite Ea1 => Ht1'.
               apply: (aux_claim_le_nopd Ephw Esg Ht1').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a1 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            case E22: (is_r r2 R_AUX2).
            ** have Ea2 : sv_a2 (wtaint r2 AU v) = AU.
               { rewrite /wtaint E22.
                 by case E21: (is_r r2 R_AUX1);
                    rewrite //= (is_r_eq E21) in E22. }
               move: Ht2. rewrite Ea2 /t_le.
               case/orP => /t_eqb_eq E2w; last first.
               { by rewrite /aux_claim E2w. }
               rewrite -E2w.
               rewrite (is_r_eq E22) tget_set_eq /=.
               exact: (Hupmem _ Hgv).
            ** have Ea2 : sv_a2 (wtaint r2 AU v) = sv_a2 v.
               { rewrite /wtaint E22. by case: (is_r r2 R_AUX1). }
               rewrite (tget_set_neq _ _ _ (is_r_neq' E22)).
               move: Ht2. rewrite Ea2 => Ht2'.
               apply: (aux_claim_le_nopd Ephw Esg Ht2').
               apply: (store_aux_claim Hcm Emem').
               exact: (di_a2 HI Ev).
         ++ move=> w0; rewrite Ew => -[<-] Hon1.
            case E0: (is_r r2 R_ONE).
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU v))
                           = false
                 by rewrite /wone E0.
               move: (o_le_true Hon Hon1). by rewrite Eone.
            ** have Eone : sv_one (wone r2 false (wtaint r2 AU v))
                           = sv_one v.
               { rewrite /wone E0.
                 by have [_ _ _ _ ->] := wtaint_fields r2 AU v. }
               move: Hon. rewrite Eone => Hon'.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E0)).
               apply: (di_one HI Ev).
               exact: o_le_true Hon' Hon1.
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
            by case: HP.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
            by exists b.
         ++ move=> w0 b0; rewrite Ew => -[<-] _.
            rewrite Hcur => -[<-].
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')) Esg Ec.
            exact: Hsp.
         ++ move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> w0 b0; rewrite Ew => -[<-].
            rewrite Hcur => -[<-].
            rewrite Esg Ec.
            exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
         ++ move=> w0 b0 k1; rewrite Ew => -[<-] _.
            by rewrite Epd' Epd0.
         ++ move=> w0; rewrite Ew => -[<-].
            rewrite Eph' Esg Epd' => HP HPd HK.
            rewrite (tget_set_neq _ _ _ (is_r_neq' E2ra)).
            exact: (di_ra HI Ev HP HPd HK).
         ++ move=> c0 b0 j cv1 tg1 Hcell1 HbF.
            case Etgt: ([&& c0 == Pointer.component ptr,
                           b0 == Pointer.block ptr
                         & j == Z.to_nat (Pointer.offset ptr)]).
            ** case/and3P: Etgt => /eqP T1' /eqP T2' /eqP T3'.
               subst c0 b0 j.
               move: Hcell1. rewrite Hcs => -[<- _].
               split.
               --- by rewrite /= T1c.
               --- move=> _. rewrite /=.
                   exact: (Hupmem _ Hgv).
            ** rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
                 in Hcell1.
               have [T1' T2'] := di_mem HI Hcell1 HbF.
               split=> // Hb1'.
               exact: (Hupmem _ (T2' Hb1')).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
            exists cv1, tg1. split=> //.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 0 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1e andbF. }
            by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
         ++ move=> w0; rewrite Ew => -[<-]. rewrite Ec.
            have HD := di_scr HI Ev.
            move: Hsc. rewrite /sc_le.
            case/orP => /sc_eqb_eq Escw; last first.
            { by rewrite Escw. }
            rewrite -Escw.
            case: (sv_sc v) HD => HD /=.
            ** exact: Hupscr HD.
            ** rewrite Eph' => HPB.
               rewrite (tget_set_neq _ _ _ (is_r_neq' E2sp')).
               exact: Hupscr (HD HPB).
            ** exact: Hupscr HD.
            ** by [].
         ++ move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
         ++ move=> c0 A. rewrite Ec => Hc0 HA.
            have [W1 W2] := di_scrfor HI Hc0 HA.
            split=> //.
            exact: (Hupscr _ _ W2).
         ++ move=> i A HA.
            have [W1 W2 W3 W4 W5] := di_chain HI HA.
            split=> //.
            exact: (Hupfr _ _ _ _ _ _ W3 W4).
         ++ move=> i A b0 HA Hb0. rewrite Ec => HcA.
            exact: (di_dist HI HA Hb0 HcA).
         ++ exact: (di_dist2 HI).
         ++ move=> c0 b0 HbF.
            have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            case Ec0: (c0 == Pointer.component ptr).
            ** move/eqP: Ec0 => Ec0. subst c0.
               eexists. split; first by rewrite Emem' setmE eqxx.
               move=> /=.
               have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
               by subst cm0.
            ** exists cm0. split=> //.
               rewrite (store_getm_other Emem') //.
               by move=> E; rewrite E eqxx in Ec0.
         ++ exact: (di_f01 HI).
         ++ move=> c0 cm0.
            apply: (store_nb2 Hcm Emem').
            exact: (di_nb2 HI).
         ++ move=> c0 S Hs.
            apply: (store_dom Emem').
            exact: (di_dom HI Hs).
         ++ exact: (di_level HI).
         ++ move=> c0 cm0 Hcm0.
            have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
            { move: Hcm0. rewrite Emem' setmE.
              case E: (c0 == Pointer.component ptr) => H.
              - move/eqP: E => E. subst c0. by exists cm.
              - by exists cm0. }
            have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
            exists cv1, tg1.
            have Hne3 : [&& c0 == Pointer.component ptr,
                           1 == Pointer.block ptr
                         & 1 == Z.to_nat (Pointer.offset ptr)] = false.
            { by rewrite Hb1e /= andbF. }
            rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
            split=> //. split=> //.
            exact: (Hupmem _ Hgd1).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ek HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> i X HX Hnw.
            case: (di_nwshadow HI HX Hnw)
              => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
            { right. exists j, W. by split. }
            left. split; last exact: HPre.
            by rewrite Ec.
         ++ move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
         ++ move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
            apply: Hupscr.
            exact: (di_scr0 HI Hc0 Hg0 Htw).
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            apply: (di_ekwin HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ move=> w0; rewrite Ew => -[<-] Hekw.
            rewrite (pend_sig_eq Esg Epd').
            apply: (di_bodycarg HI Ev).
            rewrite ?wone_ek ?wtaint_ek in Eek'.
            move: Hekw. by rewrite Eek'.
         ++ exact: (di_chain2 HI).
  +
    case Epd0: (sv_pend v) => //.
    case Eg: ([&& t_eqb (rtaint v r1) AScr, is_r r2 R_SP
              & ~~ nocra (sv_sig v)]) => // -[Evv].
    subst v'.
    case/and3P: Eg => /t_eqb_eq Er1t /is_r_eq Er2 Hcra.
    subst r2.
    have E1sp : is_r r1 R_SP = false.
    { by move: Er1t; rewrite /rtaint; case: (is_r r1 R_SP). }
    have E1ra : is_r r1 R_RA = false.
    { by move: Er1t; rewrite /rtaint E1sp; case: (is_r r1 R_RA). }
    have Hp1 : Transitional.val (Transitional.Register.get r1 regs)
               = Ptr (Pointer.component pc, 1, 0%Z).
    { have Hrc := rtaint_claim HI Ev E1sp E1ra.
      by rewrite Er1t in Hrc. }
    have Eptr : ptr = (Pointer.component pc, 1, 0%Z).
    { move: Hval1. rewrite Hp1. by move=> [->]. }
    have Ecp : Pointer.component ptr = Pointer.component pc
      by rewrite Eptr.
    have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
    have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
    have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
    have [F0 F1] := di_f01 HI (Pointer.component pc).
    have HcmC : getm mem (Pointer.component pc) = Some cm.
    { by rewrite -Ecp. }
    have [cvS [tgS [HcellS HvS]]] := di_post HI Ev Eph Hcur.
    have [cvT [tgT [HcellT HtagT]]] := di_scrtag HI HcmC.
    rewrite HcellS in HcellT.
    case: HcellT => E1 E2. subst cvT tgT.
    have Ecl : cl = (cvS, tgS).
    { move: Hload_cell. rewrite Eptr /= HcellS.
      by move=> [->]. }
    subst cl.
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
    have Hupmem : forall x, goodu mem F x -> goodu mem' F x
      := fun x => store_goodu Hcm Emem' (F := F) (x := x).
    have Hupscr_o : forall c0 x,
        (c0 == Pointer.component pc) = false ->
        scr_val mem c0 x -> scr_val mem' c0 x.
    { move=> c0 x Hne.
      apply: (store_scr_val_away Hcm Hchunk Hupd Emem').
      by rewrite Ecp Hne. }
    have Hupfr : forall (c1 : Component.id) (b1 : Block.id) sg carry
        cscr rcap,
        b1 \in F c1 ->
        frame_ok F mem c1 b1 sg carry cscr rcap ->
        frame_ok F mem' c1 b1 sg carry cscr rcap.
    { move=> c1 b1 sg carry cscr rcap Hb1'.
      apply: (store_frame_ok_away Hcm Hchunk Hupd Emem').
      rewrite Eptr /=.
      case E: (c1 == Pointer.component pc) => //=.
      case Eb: (b1 == 1) => //.
      move/eqP: Eb => Eb. subst b1.
      move/eqP: E => E. subst c1.
      by rewrite F1 in Hb1'. }
    have Hcs := store_cell_same Hupd Emem'.
    move: Hcs. rewrite Eptr /= => Hcs.
    have hasCRa_nth : forall sg : seq class3,
        has (fun k => c3_eqb k CRa) sg ->
        exists j, nth_error sg j = Some CRa.
    { elim=> [|x sg IH] //=.
      case E: (c3_eqb x CRa) => /=.
      - move=> _. move/c3_eqb_eq: E => E. subst x. by exists 0.
      - move=> H. have [j Hj] := IH H. by exists j.+1. }
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 R_SP).
      -- by rewrite (is_r_eq E0) tget_set_eq /= HtagT.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      rewrite (tget_set_neq _ _ _ H2).
      apply: Hupmem. exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HA1 : R_AUX1 <> R_SP by [].
      rewrite (tget_set_neq _ _ _ HA1).
      move: Ht1. rewrite /t_le.
      case/orP => /t_eqb_eq E1w; last first.
      { by rewrite /aux_claim E1w. }
      rewrite -E1w.
      have HD := di_a1 HI Ev.
      case Ea1v: (sv_a1 v) HD => HD.
      -- rewrite /aux_claim Eph' Esg.
         move: Hcra.
         case: (sv_sig v) => [|kk tl] //.
         case: kk => //.
         by case: tl.
      -- exact: HD.
      -- exact: HD.
      -- exact: (Hupmem _ HD).
      -- by [].
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HA2 : R_AUX2 <> R_SP by [].
      rewrite (tget_set_neq _ _ _ HA2).
      move: Ht2. rewrite /t_le.
      case/orP => /t_eqb_eq E2w; last first.
      { by rewrite /aux_claim E2w. }
      rewrite -E2w.
      have HD := di_a2 HI Ev.
      case Ea2v: (sv_a2 v) HD => HD.
      -- rewrite /aux_claim Eph' Esg.
         move: Hcra.
         case: (sv_sig v) => [|kk tl] //.
         case: kk => //.
         by case: tl.
      -- exact: HD.
      -- exact: HD.
      -- exact: (Hupmem _ HD).
      -- by [].
    * move=> w0; rewrite Ew => -[<-] Hon1.
      have HO : R_ONE <> R_SP by [].
      rewrite (tget_set_neq _ _ _ HO).
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
      by exists b.
    * move=> w0 b0; rewrite Ew => -[<-] _.
      rewrite Hcur => -[<-].
      by rewrite tget_set_eq /= HvS Esg Ec.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b0; rewrite Ew => -[<-].
      rewrite Hcur => -[<-].
      rewrite Esg Ec.
      exact: (Hupfr _ _ _ _ _ _ HbF1 (di_frame HI Ev Hcur)).
    * move=> w0 b0 k1; rewrite Ew => -[<-] _.
      by rewrite Epd'.
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Esg Epd' => HP HPd HK.
      exfalso.
      move: Hcra. rewrite /nocra negbK => Hh.
      have [j Hj] := hasCRa_nth _ Hh.
      exact: (HK j Hj).
    * move=> c0 b0 j cv1 tg1 Hcell1 HbF.
      case Etgt: ([&& c0 == Pointer.component ptr,
                     b0 == Pointer.block ptr
                   & j == Z.to_nat (Pointer.offset ptr)]).
      -- case/and3P: Etgt => /eqP T1' /eqP T2' /eqP T3'.
         subst c0 b0 j.
         move: Hcell1. rewrite Eptr /= Hcs => -[<- _].
         split.
         ++ by rewrite /= HtagT.
         ++ move=> Hb1'. by case: Hb1'.
      -- rewrite (store_cell_other Hcm Hchunk Hupd Emem' Etgt)
           in Hcell1.
         have [T1' T2'] := di_mem HI Hcell1 HbF.
         split=> // Hb1'.
         exact: (Hupmem _ (T2' Hb1')).
    * move=> c0 cm0 Hcm0.
      case Ec0: (c0 == Pointer.component pc).
      -- move/eqP: Ec0 => Ec0. subst c0.
         eexists _, _. split; first exact: Hcs.
         by rewrite /= HtagT.
      -- have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
         { move: Hcm0. rewrite Emem' setmE.
           case E: (c0 == Pointer.component ptr) => H.
           - move/eqP: E => E. subst c0. by exists cm.
           - by exists cm0. }
         have [cv1 [tg1 [Hcell1 Htag1]]] := di_scrtag HI Hcm1.
         exists cv1, tg1. split=> //.
         have Hne3 : [&& c0 == Pointer.component ptr,
                        1 == Pointer.block ptr
                      & 0 == Z.to_nat (Pointer.offset ptr)] = false.
         { by rewrite Ecp Ec0. }
         by rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
    * move=> w0; rewrite Ew => -[<-].
      move: Hsc. rewrite /sc_le.
      case/orP => /sc_eqb_eq Escw.
      -- by rewrite -Escw.
      -- by rewrite Escw.
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> c0 A. rewrite Ec => Hc0 HA.
      have [W1 W2] := di_scrfor HI Hc0 HA.
      split=> //.
      apply: (Hupscr_o _ _ _ W2).
      case E: (c0 == Pointer.component pc) => //.
      move/eqP: E => E. by case: (Hc0 E).
    * move=> i A HA.
      have [W1 W2 W3 W4 W5] := di_chain HI HA.
      split=> //.
      exact: (Hupfr _ _ _ _ _ _ W3 W4).
    * move=> i A b0 HA Hb0. rewrite Ec => HcA.
      exact: (di_dist HI HA Hb0 HcA).
    * exact: (di_dist2 HI).
    * move=> c0 b0 HbF.
      have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
      case Ec0: (c0 == Pointer.component ptr).
      -- move/eqP: Ec0 => Ec0. subst c0.
         eexists. split; first by rewrite Emem' setmE eqxx.
         move=> /=.
         have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
         by subst cm0.
      -- exists cm0. split=> //.
         rewrite (store_getm_other Emem') //.
         by move=> E; rewrite E eqxx in Ec0.
    * exact: (di_f01 HI).
    * move=> c0 cm0.
      apply: (store_nb2 Hcm Emem').
      exact: (di_nb2 HI).
    * move=> c0 S Hs.
      apply: (store_dom Emem').
      exact: (di_dom HI Hs).
    * exact: (di_level HI).
    * move=> c0 cm0 Hcm0.
      have [cm1 Hcm1] : exists cm1, getm mem c0 = Some cm1.
      { move: Hcm0. rewrite Emem' setmE.
        case E: (c0 == Pointer.component ptr) => H.
        - move/eqP: E => E. subst c0. by exists cm.
        - by exists cm0. }
      have [cv1 [tg1 [Hcell1 [Htag1 Hgd1]]]] := di_flag HI Hcm1.
      exists cv1, tg1.
      have E31 : (1 == Z.to_nat (Pointer.offset ptr)) = false
        by rewrite Eptr.
      have Hne3 : [&& c0 == Pointer.component ptr,
                     1 == Pointer.block ptr
                   & 1 == Z.to_nat (Pointer.offset ptr)] = false.
      { by rewrite E31 !andbF. }
      rewrite (store_cell_other Hcm Hchunk Hupd Emem' Hne3).
      split=> //. split=> //.
      exact: (Hupmem _ Hgd1).
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
      apply: (Hupscr_o _ _ _ (di_scr0 HI Hc0 Hg0 Htw)).
      case E: (c0 == Pointer.component pc) => //.
      move/eqP: E => E. by case: (Hc0 E).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      have Hek : sv_ek v = true.
      { rewrite ?wone_ek ?wtaint_ek in Eek'.
        move: Hekw. by rewrite Eek'. }
      rewrite (pend_sig_none Epd') Esg -(pend_sig_none Epd0).
      exact: (di_bodycarg HI Ev Hek).
    * exact: (di_chain2 HI).
Qed.

Lemma disc_step_load :
  forall mem mem' regs pc tg c pct r1 r2 ptr v,
    Transitional.executing cde pc (TrLoad r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Memory.load mem ptr = Some v ->
    Transitional.Memory.store mem ptr
      ({| Transitional.val := Transitional.val v.1;
          tvtag := moved_tag (tvtag v.1) |},
       {| vtag := moved_tag (tvtag v.1);
          color := c; entry := None; is_code := false |}) = Some mem' ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem',
       Transitional.Register.set r2 (Transitional.val v.1) (tvtag v.1) regs,
       Pointer.inc pc, pct).
Proof.
  move=> mem mem' regs pc tg c pct r1 r2 ptr cl Hex Hpc Htg1 Hval1
         Hcptr Hload Hwb [cur [chain [F [cs HI]]]].
  exists cur, chain, F, cs.
  exact: (dinv_step_load Hex Hpc Htg1 Hval1 Hcptr Hload Hwb HI).
Qed.

Lemma dinv_step_jal :
  forall mem regs pc tg c pct pc' l cur chain F cs,
    Transitional.executing cde pc (TrJalNat l) tg c ->
    Transitional.find_label_in_comp cde c l = Some pc' ->
    Transitional.check_pc_jump cde tg pc' c ->
    dinv cur chain F cs mem regs pc pct ->
    exists b cvnew,
      [/\ cur = Some b
        & dinv None
            ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
                MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |}
               :: chain)
            F cvnew mem
            (Transitional.Register.set R_RA (Ptr (Pointer.inc pc))
               InternalJump regs)
            pc' pct].
Proof.
  move=> mem regs pc tg c pct pc' l cur chain F cs Hex Hfl Hcj HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have [Ecpc' EvT] := jal_target HMM Huniq Hex Ev Hfl.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  have [C_code0 [EcX [EgX _]]] := Hex.
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  case Epd0: (sv_pend v) => //.
  case Eg0: (sv_one v && ~~ nocra (sv_sig v)) => // -[Evv]. subst v'.
  case/andP: Eg0 => Eon Hncr.
  have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
  have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
  have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
  have Hsp := di_sp HI Ev Eph Hcur.
  have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
  move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
    => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
  have Ea1w : sv_a1 w = ADead.
  { move: Ht1. rewrite /t_le.
    by case/orP => /t_eqb_eq E; [rewrite -E | rewrite E]. }
  have Ea2w : sv_a2 w = ADead.
  { move: Ht2. rewrite /t_le.
    by case/orP => /t_eqb_eq E; [rewrite -E | rewrite E]. }
  have Escw : sv_sc w = SCused.
  { move: Hsc. rewrite /sc_le.
    by case/orP => /sc_eqb_eq E; [rewrite -E | rewrite E]. }
  have [cm0 HcmC] := di_dom HI EgX.
  have [cvT [tgT [HcellT HtagT]]] := di_scrtag HI HcmC.
  set A := {| a_comp := Pointer.component pc; a_blk := b;
              a_ret := Pointer.inc pc; a_scr := cs |}.
  have Hiw : in_window A = false.
  { by rewrite /in_window /asv /= Ew /= Eph'. }
  exists b, (Transitional.val cvT).
  split; first exact: Hcur.
  constructor.
  * move=> r0 Hr0.
    rewrite (tget_set_neq _ _ _ Hr0).
    exact: (di_rtag HI).
  * move=> r0 H1 H2 H3 H4.
    rewrite (tget_set_neq _ _ _ H1).
    exact: (di_rval HI H1 H2 H3 H4).
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-] _.
    have HOr : R_ONE <> R_RA by [].
    rewrite (tget_set_neq _ _ _ HOr).
    exact: (di_one HI Ev Eon).
  * move=> w0; rewrite EvT => -[<-] _. by [].
  * move=> w0; rewrite EvT => -[<-] _.
    have HSPr : R_SP <> R_RA by [].
    rewrite (tget_set_neq _ _ _ HSPr).
    rewrite /carry0 Hiw /sp_of /asv /= Ew /= Esg.
    exact: Hsp.
  * move=> w0; rewrite EvT => -[<-] HP _. by case: HP.
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> w0 b0 k1; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-] _ _ _.
    rewrite tget_set_eq /cap /= Hiw.
    by [].
  * exact: (di_mem HI).
  * exact: (di_scrtag HI).
  * move=> w0; rewrite EvT => -[<-] /=.
    rewrite Ecpc'.
    by exists cvT, tgT.
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> c0 A0. rewrite Ecpc' => Hc0 HA0.
    have Hc0' : c0 <> Pointer.component pc by rewrite Ecc.
    have E0 : Nat.eqb (Pointer.component pc) c0 = false.
    { case E0: (Nat.eqb _ _) => //.
      move/PeanoNat.Nat.eqb_eq: E0 => E0.
      case: Hc0. by rewrite -E0 Ecc. }
    move: HA0. rewrite /= E0 => HA0.
    exact: (di_scrfor HI Hc0' HA0).
  * move=> i A0 HA0.
    case: i HA0 => [|i] HA0.
    -- move: HA0 => -[<-].
       split=> //=.
       ++ by exists w; rewrite Ew.
       ++ rewrite /asv /= Ew /=.
          split.
          ** split; [by left| by []| exact: Ea1w| exact: Ea2w
                    | exact: Escw].
          ** by rewrite Eph'.
       ++ rewrite /asv /= Ew /= Esg drop0.
          exact: (di_frame HI Ev Hcur).
       ++ split.
          ** by case: (pc) => [[c0 b0] o0].
          ** move=> _. rewrite /asv /= Ew /= Esg.
             exact: Hncr.
          ** rewrite /asv /= Ew /= => Hekw.
             have Hekv : sv_ek v = true.
             { move: Hekw. by rewrite Eek'. }
             move: (di_ek HI Ev Hekv).
             by rewrite /= drop0.
          ** rewrite /= drop0 => Hh.
             exact: (di_cswin HI Hh).
    -- exact: (di_chain HI HA0).
  * move=> i A0 b0 _ HN. by [].
  * move=> i1 i2 A1 A2 Hne HA1 HA2 HcA.
    case: i1 HA1 Hne => [|i1] HA1 Hne;
    case: i2 HA2 Hne => [|i2] HA2 Hne.
    -- by case: Hne.
    -- move: HA1 => -[E1]. subst A1.
       have HD := di_dist HI HA2 Hcur.
       exact: (not_eq_sym (HD (esym HcA))).
    -- move: HA2 => -[E2]. subst A2.
       have HD := di_dist HI HA1 Hcur.
       exact: (HD HcA).
    -- have Hne' : i1 <> i2.
       { move=> E. case: Hne. by rewrite E. }
       exact: (di_dist2 HI Hne' HA1 HA2 HcA).
  * exact: (di_fbound HI).
  * exact: (di_f01 HI).
  * exact: (di_nb2 HI).
  * exact: (di_dom HI).
  * rewrite /= Hiw /=. exact: (di_level HI).
  * exact: (di_flag HI).
  * move=> w0; rewrite EvT => -[<-] _.
    exact: Hiw.
  * move=> i X HX Hnwx.
    case: i HX => [|i] HX.
    -- move: HX => -[E1]. subst X.
       left. split.
       ++ by rewrite Ecpc'.
       ++ by [].
    -- case: (di_nwshadow HI HX Hnwx)
         => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
       { right. exists j.+1, W.
         split=> //.
         move=> k B Hjk Hki HB.
         case: k HB Hjk Hki => [|k] HB Hjk Hki; first by [].
         exact: (HSeg k B Hjk Hki HB). }
       left. split.
       ++ by rewrite Ecpc' -Ecc HcX.
       ++ move=> k B Hk HB.
          case: k HB Hk => [|k] HB Hk.
          ** move: HB => -[E1]. subst B.
             split; last exact: Hiw.
             by rewrite HcX.
          ** exact: (HPre k B Hk HB).
  * move=> Hh. by rewrite /= Hiw in Hh.
  * move=> c0 S0. rewrite Ecpc' -Ecc => Hc0 Hg0 Htw.
    move: Htw. rewrite /= Hiw andbF => Htw.
    exact: (di_scr0 HI Hc0 Hg0 Htw).
  * move=> w0; rewrite EvT => -[<-] Hekw.
    by [].
  * move=> w0; rewrite EvT => -[<-] _.
    exact: bodycarg_nil.
  * move=> i A0 HA0.
    case: i HA0 => [|i] HA0.
    -- move: HA0 => -[<-].
       split.
       ++ by rewrite /asv /= Ew /= Eph'.
       ++ rewrite /asv /= Ew /= => Hekw.
          have Hekv : sv_ek v = false.
          { move: Hekw. by rewrite Eek'. }
          move: (di_ekwin HI Ev Hekv).
          by rewrite /= drop0.
       ++ rewrite /asv /= Ew /= => Hekw.
          have Hekv : sv_ek v = true.
          { move: Hekw. by rewrite Eek'. }
          rewrite Esg -(pend_sig_none Epd0).
          exact: (di_bodycarg HI Ev Hekv).
       ++ by rewrite Hiw.
    -- exact: (di_chain2 HI HA0).
Qed.

Lemma disc_step_jal :
  forall mem regs pc tg c pct pc' l,
    Transitional.executing cde pc (TrJalNat l) tg c ->
    Transitional.find_label_in_comp cde c l = Some pc' ->
    Transitional.check_pc_jump cde tg pc' c ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem,
       Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) InternalJump regs,
       pc', pct).
Proof.
  move=> mem regs pc tg c pct pc' l Hex Hfl Hcj [cur [chain [F [cs HI]]]].
  have [b [cvnew [Hcur HI']]] := dinv_step_jal Hex Hfl Hcj HI.
  by eexists _, _, _, _; exact: HI'.
Qed.

Lemma dinv_step_jump :
  forall mem regs pc tg c pct pc' r cur chain F cs,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.Register.get r regs = MVal InternalJump (Ptr pc') ->
    Pointer.component pc' = Pointer.component pc ->
    Transitional.check_pc_jump cde tg pc' c ->
    dinv cur chain F cs mem regs pc pct ->
    exists A chain',
      [/\ chain = A :: chain', in_window A = false, pc' = MDisc.a_ret A
        & dinv (Some (MDisc.a_blk A)) chain' F (MDisc.a_scr A)
            mem regs pc' pct].
Proof.
  move=> mem regs pc tg c pct pc' r cur chain F cs Hex Hget Hcomp Hcj
         HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  case Epd0: (sv_pend v) => //.
  case Eg0: ([&& sv_one v, cseq_eqb (sv_sig v) [::]
             & sv_ek v || match sv_sc v with
                          | SCrest | SCnone => true
                          | _ => false
                          end]) => // -[Evv].
  subst v'.
  case/and3P: Eg0 => Eon /cseq_eqb_eq Esg0 _.
  have Er : r = R_RA.
  { case E: (is_r r R_RA); first exact: (is_r_eq E).
    have HT := di_rtag HI (is_r_neq E).
    by rewrite Hget in HT. }
  subst r.
  have Hra : Transitional.Register.get R_RA regs = cap chain.
  { apply: (di_ra HI Ev).
    - by rewrite Eph.
    - by rewrite Epd0.
    - move=> j. rewrite Esg0. by case: j. }
  have [A [chain' [Echain Hnw Epc']]] :
      exists A chain',
        [/\ chain = A :: chain', in_window A = false & pc' = a_ret A].
  { move: Hra Hget.
    case Ech: (chain) => [|A0 ch'].
    - by move=> E1; rewrite E1.
    - rewrite /cap /=.
      case Ei: (in_window A0).
      + move=> E1 E2. by rewrite E1 in E2.
      + move=> E1 E2. rewrite E1 in E2.
        case: E2 => E2.
        exists A0, ch'. by split. }
  have HAh : nth_error chain 0 = Some A by rewrite Echain.
  have [W1 W2 W3 W4 W5] := di_chain HI HAh.
  case: W5 => Ecomp Hnocra Hek5 Hpin.
  case: W2 => [[Hor Hpd Ha1 Ha2 Hsc1] Hone1].
  case: W1 => w' Ew'.
  have Ewp : svat pc' = Some w' by rewrite Epc'.
  have Easv : asv A = w' by rewrite /asv Ew'.
  have Ephr : sv_ph (asv A) = PBody.
  { case: Hor => // E.
    move: Hnw. by rewrite /in_window E. }
  rewrite Echain /= drop0 in W4.
  exists A, chain'.
  split; [exact: Echain | exact: Hnw | exact: Epc' |].
  constructor.
  * exact: (di_rtag HI).
  * exact: (di_rval HI).
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Ha1.
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Ha2.
  * move=> w0; rewrite Ewp => -[<-] _.
    exact: (di_one HI Ev Eon).
  * move=> w0; rewrite Ewp => -[<-].
    rewrite -Easv Ephr => HP. by case: HP.
  * move=> w0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> w0; rewrite Ewp => -[<-] _ _.
    exists (a_blk A). split=> //.
    by rewrite Epc' -Ecomp.
  * move=> w0 b0; rewrite Ewp => -[<-] _.
    move=> -[<-].
    have Hspt := di_sptear HI Ev Eph.
    rewrite Hspt Echain /carry0 Hnw /sp_of.
    by rewrite Epc' -Ecomp -Easv.
  * move=> w0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> w0 b0; rewrite Ewp => -[<-].
    move=> -[<-].
    rewrite Epc' -Ecomp -Easv.
    exact: W4.
  * move=> w0 b0 k1; rewrite Ewp => -[<-] _.
    by rewrite -Easv Hpd.
  * move=> w0; rewrite Ewp => -[<-] _ _ HK.
    exfalso.
    have hasCRa_nth : forall sg : seq class3,
        has (fun k => c3_eqb k CRa) sg ->
        exists j, nth_error sg j = Some CRa.
    { elim=> [|x sg IH] //=.
      case E: (c3_eqb x CRa) => /=.
      - move=> _. move/c3_eqb_eq: E => E. subst x. by exists 0.
      - move=> H. have [j Hj] := IH H. by exists j.+1. }
    have Hh : has (fun k => c3_eqb k CRa) (sv_sig w').
    { move: (Hnocra Hnw). rewrite /nocra negbK.
      by rewrite Easv. }
    have [j Hj] := hasCRa_nth _ Hh.
    exact: (HK j Hj).
  * exact: (di_mem HI).
  * exact: (di_scrtag HI).
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Hsc1.
  * move=> w0 b0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> c0 A0 Hc0 HA0.
    have Hc0' : c0 <> Pointer.component pc.
    { by rewrite -Hcomp. }
    have E0 : Nat.eqb (a_comp A) c0 = false.
    { case E0: (Nat.eqb _ _) => //.
      move/PeanoNat.Nat.eqb_eq: E0 => E0.
      case: Hc0. rewrite -E0 Ecomp. by rewrite -Epc'. }
    have HA0' : topc c0 chain = Some A0.
    { rewrite Echain /=. by rewrite E0. }
    exact: (di_scrfor HI Hc0' HA0').
  * move=> i A0 HA0.
    have HA0' : nth_error chain i.+1 = Some A0 by rewrite Echain.
    have HH := di_chain HI HA0'.
    rewrite Echain /= in HH.
    exact: HH.
  * move=> i A0 b0 HA0 -[<-] HcA.
    have HA0' : nth_error chain i.+1 = Some A0 by rewrite Echain.
    have Hne0 : i.+1 <> 0 by [].
    have HcA' : a_comp A0 = a_comp A.
    { rewrite HcA Ecomp. by rewrite Epc'. }
    exact: (di_dist2 HI Hne0 HA0' HAh HcA').
  * move=> i1 i2 A1 A2 Hne HA1 HA2 HcA.
    have Hne' : i1.+1 <> i2.+1 by move=> E; case: Hne; case: E.
    apply: (di_dist2 HI Hne' _ _ HcA); by rewrite Echain.
  * exact: (di_fbound HI).
  * exact: (di_f01 HI).
  * exact: (di_nb2 HI).
  * exact: (di_dom HI).
  * move: (di_level HI). rewrite Echain /= Hnw /=. by [].
  * exact: (di_flag HI).
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have Hek' : sv_ek (asv A) = true.
    { by rewrite Easv. }
    move: (Hek5 Hek'). by rewrite Echain /= drop0.
  * move=> i X HX Hnwx.
    have HX' : nth_error chain i.+1 = Some X by rewrite Echain.
    case: (di_nwshadow HI HX' Hnwx)
      => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
    { case: j Hj HW HSeg => [|j] Hj HW HSeg.
      - rewrite HAh in HW. case: HW => E. subst W.
        by rewrite HwW in Hnw.
      - right. exists j, W.
        rewrite Echain in HW.
        split=> //.
        move=> k B Hjk Hki HB.
        have HB' : nth_error chain k.+1 = Some B by rewrite Echain.
        exact: (HSeg k.+1 B Hjk Hki HB'). }
    left. split.
    -- by rewrite Hcomp.
    -- move=> k B Hk HB.
       have HB' : nth_error chain k.+1 = Some B by rewrite Echain.
       exact: (HPre k.+1 B Hk HB').
  * move=> Hh.
    have Hpin' := Hpin.
    rewrite Echain /= drop0 in Hpin'.
    rewrite Epc' -Ecomp.
    exact: (Hpin' Hh).
  * move=> c0 S0 Hc0 Hg0 Htw.
    rewrite Hcomp in Hc0.
    have Enc : Nat.eqb (a_comp A) c0 = false.
    { case E: (Nat.eqb _ _) => //.
      move/PeanoNat.Nat.eqb_eq: E => E.
      case: Hc0. by rewrite -E Ecomp -Epc' Hcomp. }
    have Htw' : topw c0 chain = None.
    { by rewrite Echain /= Enc. }
    exact: (di_scr0 HI Hc0 Hg0 Htw').
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have [_ R3 _ _] := di_chain2 HI HAh.
    have Hek' : sv_ek (asv A) = false by rewrite Easv.
    move: (R3 Hek'). by rewrite Echain /= drop0.
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have [_ _ R4 _] := di_chain2 HI HAh.
    have Hek' : sv_ek (asv A) = true by rewrite Easv.
    have Hpd' : sv_pend w' = None by rewrite -Easv Hpd.
    rewrite (pend_sig_none Hpd') -Easv.
    exact: (R4 Hek').
  * move=> i A0 HA0.
    have HA0' : nth_error chain i.+1 = Some A0 by rewrite Echain.
    have HH := di_chain2 HI HA0'.
    rewrite Echain /= in HH.
    exact: HH.
Qed.

Lemma disc_step_jump :
  forall mem regs pc tg c pct pc' r,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.Register.get r regs = MVal InternalJump (Ptr pc') ->
    Pointer.component pc' = Pointer.component pc ->
    Transitional.check_pc_jump cde tg pc' c ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem, regs, pc', pct).
Proof.
  move=> mem regs pc tg c pct pc' r Hex Hget Hcomp Hcj
         [cur [chain [F [cs HI]]]].
  have [A [chain' [_ _ _ HI']]] := dinv_step_jump Hex Hget Hcomp Hcj HI.
  by eexists _, _, _, _; exact: HI'.
Qed.

Lemma dinv_step_jumpret :
  forall mem regs pc tg c pct pc' r rcomval cur chain F cs,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.val (Transitional.Register.get r regs) = Ptr pc' ->
    Pointer.component pc' <> Pointer.component pc ->
    Some pct = value_to_pc_tag (tvtag (Transitional.Register.get r regs)) ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int rcomval ->
    Transitional.check_pc_jump cde tg pc' (Pointer.component pc') ->
    dinv cur chain F cs mem regs pc pct ->
    exists A chain',
      [/\ chain = A :: chain', in_window A = true, pc' = MDisc.a_ret A
        & dinv (Some (MDisc.a_blk A)) chain' F (MDisc.a_scr A)
            mem (TS.invalidate_ret regs) pc' (dec_pc_tag pct)].
Proof.
  move=> mem regs pc tg c pct pc' r rcomval cur chain F cs
         Hex Hval Hcomp Hpct Hcom Hcj HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  case Epd0: (sv_pend v) => //.
  case Eg0: ([&& sv_one v, cseq_eqb (sv_sig v) [::]
             & sv_ek v || match sv_sc v with
                          | SCrest | SCnone => true
                          | _ => false
                          end]) => // -[Evv].
  subst v'.
  case/and3P: Eg0 => Eon /cseq_eqb_eq Esg0 Hscg.
  have Er : r = R_RA.
  { case E: (is_r r R_RA); first exact: (is_r_eq E).
    have HT := di_rtag HI (is_r_neq E).
    move: Hpct. by rewrite HT. }
  subst r.
  have Hra : Transitional.Register.get R_RA regs = cap chain.
  { apply: (di_ra HI Ev).
    - by rewrite Eph.
    - by rewrite Epd0.
    - move=> j. rewrite Esg0. by case: j. }
  have [A [chain' [Echain Hwin Epc']]] :
      exists A chain',
        [/\ chain = A :: chain', in_window A = true & pc' = a_ret A].
  { move: Hra Hval Hpct.
    case Ech: (chain) => [|A0 ch'].
    - move=> E1. rewrite E1 /=. by [].
    - rewrite /cap /=.
      case Ei: (in_window A0).
      + move=> E1. rewrite E1 /= => E2 _.
        case: E2 => E2.
        exists A0, ch'. by split.
      + move=> E1. rewrite E1 /=. by []. }
  have HAh : nth_error chain 0 = Some A by rewrite Echain.
  have [W1 W2 W3 W4 W5] := di_chain HI HAh.
  case: W5 => Ecomp Hnocra Hek5 Hpin.
  case: W2 => [[Hor Hpd Ha1 Ha2 Hsc1] Hone1].
  case: W1 => w' Ew'.
  have Ewp : svat pc' = Some w' by rewrite Epc'.
  have Easv : asv A = w' by rewrite /asv Ew'.
  have Ephr : sv_ph (asv A) = PPost.
  { move: Hwin. rewrite /in_window.
    by case: (sv_ph (asv A)). }
  rewrite Echain /= drop0 in W4.
  have Hcna : a_comp A <> Pointer.component pc.
  { rewrite Ecomp -Epc'. exact: Hcomp. }
  have Enc : Nat.eqb (a_comp A) (Pointer.component pc) = false.
  { by apply/PeanoNat.Nat.eqb_neq. }
  have Hekf : sv_ek v = false.
  { case E: (sv_ek v) => //.
    have HH := di_ek HI Ev E.
    move: HH. rewrite Echain /=. by rewrite Hwin. }
  move: Hscg. rewrite Hekf /= => Hscm.
  have Hcell : scr_val mem (Pointer.component pc) cs.
  { have HD := di_scr HI Ev.
    move: Hscm HD.
    by case: (sv_sc v) => //=. }
  have Hpin0 : cs = scrpin (Pointer.component pc) chain.
  { apply: (di_cswin HI). by rewrite Echain /= Hwin. }
  have topc_nth : forall (c1 : Component.id) (ch : seq act) (X : act),
      topc c1 ch = Some X ->
      exists i1, [/\ nth_error ch i1 = Some X, a_comp X = c1
                   & forall k B, k < i1 -> nth_error ch k = Some B ->
                       a_comp B <> c1].
  { move=> c1. elim=> [|B0 ch1 IH] X //=.
    case E: (Nat.eqb (a_comp B0) c1).
    - move=> [<-]. exists 0. split=> //.
      by move/PeanoNat.Nat.eqb_eq: E.
    - move=> H. have [i1 [Hn Hc HPr]] := IH _ H.
      exists i1.+1. split=> //.
      move=> k B Hk HB.
      case: k HB Hk => [|k] HB Hk.
      + move: HB => -[<-]. by move/PeanoNat.Nat.eqb_neq: E.
      + exact: (HPr k B Hk HB). }
  have Hg_com : Transitional.Register.get R_COM
      (TS.invalidate_ret regs) = Transitional.Register.get R_COM regs.
  { rewrite /TS.invalidate_ret.
    have HC : R_COM <> R_RA by [].
    by rewrite (tget_set_neq _ _ _ HC) tget_invalidate_com. }
  have Hg_oth : forall r0, r0 <> R_RA -> r0 <> R_COM ->
      Transitional.Register.get r0 (TS.invalidate_ret regs)
      = Transitional.tUndef.
  { move=> r0 H1 H2.
    rewrite /TS.invalidate_ret (tget_set_neq _ _ _ H1).
    exact: (tget_invalidate _ H2 H1). }
  exists A, chain'.
  split; [exact: Echain | exact: Hwin | exact: Epc' |].
  constructor.
  * move=> r0 Hr0.
    case E0: (is_r r0 R_COM).
    -- rewrite (is_r_eq E0) Hg_com.
       by apply: (di_rtag HI).
    -- by rewrite (Hg_oth _ Hr0 (is_r_neq E0)).
  * move=> r0 H1 H2 H3 H4.
    case E0: (is_r r0 R_COM).
    -- rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
       rewrite Hg_com.
       exact: (di_rval HI H1 H2 H3 H4).
    -- rewrite (Hg_oth _ H1 (is_r_neq E0)).
       by [].
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Ha1.
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Ha2.
  * move=> w0; rewrite Ewp => -[<-].
    rewrite -Easv (Hone1 Ephr). by [].
  * move=> w0; rewrite Ewp => -[<-].
    rewrite -Easv Ephr => HP. by case: HP.
  * move=> w0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> w0; rewrite Ewp => -[<-] _ _.
    exists (a_blk A). split=> //.
    by rewrite Epc' -Ecomp.
  * move=> w0 b0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> w0; rewrite Ewp => -[<-]. by rewrite -Easv Ephr.
  * move=> w0 b0; rewrite Ewp => -[<-].
    move=> -[<-].
    rewrite Epc' -Ecomp -Easv.
    exact: W4.
  * move=> w0 b0 k1; rewrite Ewp => -[<-] _.
    by rewrite -Easv Hpd.
  * move=> w0; rewrite Ewp => -[<-].
    rewrite -Easv Ephr => HP _ _. by case: HP.
  * exact: (di_mem HI).
  * exact: (di_scrtag HI).
  * move=> w0; rewrite Ewp => -[<-].
    by rewrite -Easv Hsc1.
  * move=> w0 b0; rewrite Ewp => -[<-] _.
    move=> -[<-].
    have Htc : topc (a_comp A) chain = Some A.
    { by rewrite Echain /= PeanoNat.Nat.eqb_refl. }
    have [_ Hscr] := di_scrfor HI Hcna Htc.
    rewrite Epc' -Ecomp -Easv.
    exact: Hscr.
  * move=> c0 A0. rewrite Epc' -Ecomp => Hc0 HA0.
    case E0: (Nat.eqb (Pointer.component pc) c0).
    -- move/PeanoNat.Nat.eqb_eq: E0 => E0. subst c0.
       have [i1 [Hn1 Hc1 HPr1]] := topc_nth _ _ _ HA0.
       case Ew0: (in_window A0); last first.
       { exfalso.
         have Hn1' : nth_error chain i1.+1 = Some A0 by rewrite Echain.
         case: (di_nwshadow HI Hn1' Ew0)
           => [[_ HPre]|[j [W [Hj HW HcW HwW HSeg]]]].
         - have [HcA _] := HPre 0 A isT HAh.
           case: Hcna. by rewrite HcA Hc1.
         - case: j Hj HW HSeg => [|j] Hj HW HSeg.
           + rewrite HAh in HW. case: HW => E. subst W.
             case: Hcna. by rewrite HcW Hc1.
           + rewrite Echain in HW.
             case: (HPr1 j W Hj HW).
             by rewrite HcW Hc1. }
       split=> //.
       have Htw : topw (Pointer.component pc) chain = Some A0.
       { rewrite Echain /= Enc /=.
         exact: (topc_window_topw HA0 Ew0). }
       move: Hcell. rewrite Hpin0 /scrpin Htw => Hcell0.
       exact: Hcell0.
    -- have Hc0' : c0 <> Pointer.component pc.
       { move=> E. move/PeanoNat.Nat.eqb_neq: E0 => E0.
         by case: E0. }
       have HA0' : topc c0 chain = Some A0.
       { rewrite Echain /=.
         have E1 : Nat.eqb (a_comp A) c0 = false.
         { apply/PeanoNat.Nat.eqb_neq => E.
           case: Hc0. by rewrite E. }
         by rewrite E1. }
       exact: (di_scrfor HI Hc0' HA0').
  * move=> i0 A0 HA0.
    have HA0' : nth_error chain i0.+1 = Some A0 by rewrite Echain.
    have HH := di_chain HI HA0'.
    rewrite Echain /= in HH.
    exact: HH.
  * move=> i0 A0 b0 HA0 -[<-] HcA.
    have HA0' : nth_error chain i0.+1 = Some A0 by rewrite Echain.
    have Hne0 : i0.+1 <> 0 by [].
    have HcA' : a_comp A0 = a_comp A.
    { by rewrite HcA Epc' -Ecomp. }
    exact: (di_dist2 HI Hne0 HA0' HAh HcA').
  * move=> i1 i2 A1 A2 Hne HA1 HA2 HcA.
    have Hne' : i1.+1 <> i2.+1 by move=> E; case: Hne; case: E.
    apply: (di_dist2 HI Hne' _ _ HcA); by rewrite Echain.
  * exact: (di_fbound HI).
  * exact: (di_f01 HI).
  * exact: (di_nb2 HI).
  * exact: (di_dom HI).
  * have Hlv := di_level HI.
    rewrite Hlv Echain /= Hwin /=.
    rewrite /Transitional.dec_pc_tag /=.
    congr (Transitional.Level _). by lia.
  * exact: (di_flag HI).
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have Hek' : sv_ek (asv A) = true.
    { by rewrite Easv. }
    move: (Hek5 Hek'). by rewrite Echain /= drop0.
  * move=> i0 X HX Hnwx.
    have HX' : nth_error chain i0.+1 = Some X by rewrite Echain.
    case: (di_nwshadow HI HX' Hnwx)
      => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]].
    -- exfalso.
       have [HcA _] := HPre 0 A isT HAh.
       case: Hcna. by rewrite HcA HcX.
    -- case: j Hj HW HSeg => [|j] Hj HW HSeg.
       ++ rewrite HAh in HW. case: HW => E. subst W.
          left. split.
          ** by rewrite -HcW Ecomp -Epc'.
          ** move=> k B Hk HB.
             have HB' : nth_error chain k.+1 = Some B by rewrite Echain.
             have H0k : (0 : nat) < k.+1 by [].
             exact: (HSeg k.+1 B H0k Hk HB').
       ++ right. exists j, W.
          rewrite Echain in HW.
          split=> //.
          move=> k B Hjk Hki HB.
          have HB' : nth_error chain k.+1 = Some B by rewrite Echain.
          exact: (HSeg k.+1 B Hjk Hki HB').
  * move=> Hh.
    have Hpin' := Hpin.
    rewrite Echain /= drop0 in Hpin'.
    rewrite Epc' -Ecomp.
    exact: (Hpin' Hh).
  * move=> c0 S0 Hc0 Hg0 Htw.
    case E0: (Nat.eqb (Pointer.component pc) c0).
    -- move/PeanoNat.Nat.eqb_eq: E0 => E0. subst c0.
       have Htw0 : topw (Pointer.component pc) chain = None.
       { by rewrite Echain /= Enc. }
       move: Hcell. rewrite Hpin0 /scrpin Htw0 => Hcell0.
       exact: Hcell0.
    -- have Hc0' : c0 <> Pointer.component pc.
       { move=> E. move/PeanoNat.Nat.eqb_neq: E0 => E0.
         by case: E0. }
       have E1 : Nat.eqb (a_comp A) c0 = false.
       { apply/PeanoNat.Nat.eqb_neq => E.
         case: Hc0. rewrite -E Ecomp. by rewrite -Epc'. }
       have Htw' : topw c0 chain = None.
       { by rewrite Echain /= E1. }
       exact: (di_scr0 HI Hc0' Hg0 Htw').
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have [_ R3 _ _] := di_chain2 HI HAh.
    have Hek' : sv_ek (asv A) = false by rewrite Easv.
    move: (R3 Hek'). by rewrite Echain /= drop0.
  * move=> w0; rewrite Ewp => -[<-] Hekw.
    have [_ _ R4 _] := di_chain2 HI HAh.
    have Hek' : sv_ek (asv A) = true by rewrite Easv.
    have Hpd' : sv_pend w' = None by rewrite -Easv Hpd.
    rewrite (pend_sig_none Hpd') -Easv.
    exact: (R4 Hek').
  * move=> i0 A0 HA0.
    have HA0' : nth_error chain i0.+1 = Some A0 by rewrite Echain.
    have HH := di_chain2 HI HA0'.
    rewrite Echain /= in HH.
    exact: HH.
Qed.

Lemma disc_step_jumpret :
  forall mem regs pc tg c pct pc' r rcomval,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.val (Transitional.Register.get r regs) = Ptr pc' ->
    Pointer.component pc' <> Pointer.component pc ->
    Some pct = value_to_pc_tag (tvtag (Transitional.Register.get r regs)) ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int rcomval ->
    Transitional.check_pc_jump cde tg pc' (Pointer.component pc') ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem, TS.invalidate_ret regs, pc', dec_pc_tag pct).
Proof.
  move=> mem regs pc tg c pct pc' r rcomval Hex Hval Hcomp Hpct Hcom
         Hcj [cur [chain [F [cs HI]]]].
  have [A [chain' [_ _ _ HI']]] :=
    dinv_step_jumpret Hex Hval Hcomp Hpct Hcom Hcj HI.
  by eexists _, _, _, _; exact: HI'.
Qed.

Lemma dinv_step_call :
  forall mem regs pc tg c pct pc' i tni c' pid call_arg n cur chain F cs,
    Transitional.executing cde pc (TrJalProc (c', pid)) tg c ->
    Transitional.find_plabel_in_code cde c' pid = Some pc' ->
    Transitional.executing cde pc' i tni c' ->
    c <> c' ->
    Transitional.check_pc_call c tni pid ->
    pct = Level n ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int call_arg ->
    dinv cur chain F cs mem regs pc pct ->
    exists b cvnew,
      [/\ cur = Some b
        & dinv None
            ({| MDisc.a_comp := Pointer.component pc; MDisc.a_blk := b;
                MDisc.a_ret := Pointer.inc pc; MDisc.a_scr := cs |}
               :: chain)
            F cvnew mem
            (Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n)
               (Transitional.Register.invalidate regs))
            pc' (inc_pc_tag pct)].
Proof.
  move=> mem regs pc tg c pct pc' i tni c' pid call_arg n cur chain F cs
         Hex Hfl Hex' Hneq Hcpc Epct Hcom HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have [Ecpc' EvT] := plabel_target HMM Hfl.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  have [C1 [Ec1 [Eg1 _]]] := Hex'.
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  case Epd0: (sv_pend v) => //.
  case Esc0: (sv_sc v) => //.
  case Eg6: (if sv_ek v then nth1carg (sv_sig v) else true) => //.
  move=> -[Evv]. subst v'.
  have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
  move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
    => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
  have Ea1w : sv_a1 w = ADead.
  { move: Ht1. rewrite /t_le.
    by case/orP => /t_eqb_eq E; [rewrite -E | rewrite E]. }
  have Ea2w : sv_a2 w = ADead.
  { move: Ht2. rewrite /t_le.
    by case/orP => /t_eqb_eq E; [rewrite -E | rewrite E]. }
  have Escw : sv_sc w = SCused.
  { move: Hsc. rewrite /sc_le.
    by case/orP => /sc_eqb_eq E; [rewrite -E | rewrite E]. }
  have Eonw : sv_one w = false.
  { case E: (sv_one w) => //.
    move: Hon. by rewrite /o_le E. }
  have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
  have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
  have [b [Hcur HbF1]] := di_body HI Ev Hnp1 Hnp2.
  have Hsp := di_sp HI Ev Eph Hcur.
  have HD0 := di_scr HI Ev.
  rewrite Esc0 in HD0.
  have [cvS [tgS [HcellS HvS]]] := HD0 Eph.
  have [cm1 HcmC'] := di_dom HI Eg1.
  have [cvT [tgT [HcellT HtagT]]] := di_scrtag HI HcmC'.
  set A := {| a_comp := Pointer.component pc; a_blk := b;
              a_ret := Pointer.inc pc; a_scr := cs |}.
  have Hiw : in_window A = true.
  { by rewrite /in_window /asv /= Ew /= Eph'. }
  have En : n = count in_window chain.
  { move: (di_level HI). rewrite Epct. by move=> [->]. }
  exists b, (Transitional.val cvT).
  split; first exact: Hcur.
  constructor.
  * move=> r0 Hr0.
    rewrite (tget_set_neq _ _ _ Hr0).
    case E0: (is_r r0 R_COM).
    -- rewrite (is_r_eq E0) tget_invalidate_com.
       by apply: (di_rtag HI).
    -- by rewrite (tget_invalidate _ (is_r_neq E0) Hr0).
  * move=> r0 H1 H2 H3 H4.
    rewrite (tget_set_neq _ _ _ H1).
    case E0: (is_r r0 R_COM).
    -- rewrite (is_r_eq E0) in H1 H2 H3 H4 *.
       rewrite tget_invalidate_com.
       exact: (di_rval HI H1 H2 H3 H4).
    -- rewrite (tget_invalidate _ (is_r_neq E0) H1).
       by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-] _. by [].
  * move=> w0; rewrite EvT => -[<-] _.
    have HSPr : R_SP <> R_RA by [].
    have HSPc : R_SP <> R_COM by [].
    rewrite (tget_set_neq _ _ _ HSPr) (tget_invalidate _ HSPc HSPr).
    by rewrite /carry0 /= Hiw.
  * move=> w0; rewrite EvT => -[<-] HP _. by case: HP.
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> w0 b0 k1; rewrite EvT => -[<-]. by [].
  * move=> w0; rewrite EvT => -[<-] _ _ _.
    rewrite tget_set_eq /cap /= Hiw /=.
    by rewrite En.
  * exact: (di_mem HI).
  * exact: (di_scrtag HI).
  * move=> w0; rewrite EvT => -[<-] /=.
    rewrite Ecpc'.
    by exists cvT, tgT.
  * move=> w0 b0; rewrite EvT => -[<-]. by [].
  * move=> c0 A0. rewrite Ecpc' => Hc0 HA0.
    case E0: (Nat.eqb (Pointer.component pc) c0).
    -- move/PeanoNat.Nat.eqb_eq: E0 => E0.
       move: HA0. rewrite /= E0 PeanoNat.Nat.eqb_refl.
       move=> -[<-].
       split; first exact: Hiw.
       rewrite -E0 /sp_of /asv /= Ew /= Esg.
       exists cvS, tgS. split; first exact: HcellS.
       by rewrite HvS Hsp.
    -- move: HA0. rewrite /= E0 => HA0.
       have Hc0' : c0 <> Pointer.component pc.
       { move=> E. move/PeanoNat.Nat.eqb_neq: E0 => E0.
         case: E0. by rewrite E. }
       exact: (di_scrfor HI Hc0' HA0).
  * move=> i0 A0 HA0.
    case: i0 HA0 => [|i0] HA0.
    -- move: HA0 => -[<-].
       split=> //=.
       ++ by exists w; rewrite Ew.
       ++ rewrite /asv /= Ew /=.
          split.
          ** split; [by right| by []| exact: Ea1w| exact: Ea2w
                    | exact: Escw].
          ** move=> _. exact: Eonw.
       ++ rewrite /asv /= Ew /= Esg drop0.
          exact: (di_frame HI Ev Hcur).
       ++ split.
          ** by case: (pc) => [[c0 b0] o0].
          ** by rewrite Hiw.
          ** rewrite /asv /= Ew /= => Hekw.
             have Hekv : sv_ek v = true.
             { move: Hekw. by rewrite Eek'. }
             move: (di_ek HI Ev Hekv).
             by rewrite /= drop0.
          ** rewrite /= drop0 => Hh.
             exact: (di_cswin HI Hh).
    -- exact: (di_chain HI HA0).
  * move=> i0 A0 b0 _ HN. by [].
  * move=> i1 i2 A1 A2 Hne HA1 HA2 HcA.
    case: i1 HA1 Hne => [|i1] HA1 Hne;
    case: i2 HA2 Hne => [|i2] HA2 Hne.
    -- by case: Hne.
    -- move: HA1 => -[E1]. subst A1.
       have HD := di_dist HI HA2 Hcur.
       exact: (not_eq_sym (HD (esym HcA))).
    -- move: HA2 => -[E2]. subst A2.
       have HD := di_dist HI HA1 Hcur.
       exact: (HD HcA).
    -- have Hne' : i1 <> i2.
       { move=> E. case: Hne. by rewrite E. }
       exact: (di_dist2 HI Hne' HA1 HA2 HcA).
  * exact: (di_fbound HI).
  * exact: (di_f01 HI).
  * exact: (di_nb2 HI).
  * exact: (di_dom HI).
  * rewrite Epct /= Hiw /= En.
    rewrite /Transitional.inc_pc_tag /=.
    congr (Transitional.Level _). by lia.
  * exact: (di_flag HI).
  * move=> w0; rewrite EvT => -[<-]. by [].
  * move=> i0 X HX Hnwx.
    case: i0 HX => [|i0] HX.
    -- move: HX => -[E1]. subst X.
       by rewrite Hiw in Hnwx.
    -- case: (di_nwshadow HI HX Hnwx)
         => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
       { right. exists j.+1, W.
         split=> //.
         move=> k B Hjk Hki HB.
         case: k HB Hjk Hki => [|k] HB Hjk Hki; first by [].
         exact: (HSeg k B Hjk Hki HB). }
       right. exists 0, A.
       split=> //.
       move=> k B H0k Hki HB.
       case: k HB H0k Hki => [|k] HB H0k Hki; first by [].
       exact: (HPre k B Hki HB).
  * move=> _.
    rewrite Ecpc'.
    have Hc'ne : c' <> Pointer.component pc.
    { move=> E. case: Hneq. by rewrite -Ecc E. }
    have Enc' : Nat.eqb (Pointer.component pc) c' = false.
    { apply/PeanoNat.Nat.eqb_neq. rewrite Ecc. exact: Hneq. }
    rewrite /scrpin /= Enc' /=.
    case Etc: (topc c' chain) => [X|].
    -- have [Wx Hscr] := di_scrfor HI Hc'ne Etc.
       rewrite (topc_window_topw Etc Wx).
       case: Hscr => cvX [tgX [HcellX HvX]].
       rewrite HcellX in HcellT.
       case: HcellT => E1 E2. subst cvT tgT.
       exact: HvX.
    -- have Hscr := di_scr0 HI Hc'ne Eg1 (topc_none_topw MM Etc).
       rewrite (topc_none_topw MM Etc).
       case: Hscr => cvX [tgX [HcellX HvX]].
       rewrite HcellX in HcellT.
       case: HcellT => E1 E2. subst cvT tgT.
       exact: HvX.
  * move=> c0 S0 Hc0 Hg0 Htw.
    move: Htw. rewrite /= Hiw andbT.
    case E0: (Nat.eqb (Pointer.component pc) c0) => // Htw.
    have Hc0' : c0 <> Pointer.component pc.
    { move=> E. move/PeanoNat.Nat.eqb_neq: E0 => E0.
      by case: E0. }
    exact: (di_scr0 HI Hc0' Hg0 Htw).
  * move=> w0; rewrite EvT => -[<-] _.
    exact: Hiw.
  * move=> w0; rewrite EvT => -[<-] Hekw.
    by [].
  * move=> i0 A0 HA0.
    case: i0 HA0 => [|i0] HA0.
    -- move: HA0 => -[<-].
       split.
       ++ move=> _.
          have Hargw : sv_arg w = false.
          { move: Hle => /and5P [_ _ _ Harg _].
            move: Harg. by case: (sv_arg w). }
          rewrite /asv /= Ew /=.
          exact: Hargw.
       ++ rewrite /asv /= Ew /= => Hekw.
          have Hekv : sv_ek v = false.
          { move: Hekw. by rewrite Eek'. }
          move: (di_ekwin HI Ev Hekv).
          by rewrite /= drop0.
       ++ rewrite /asv /= Ew /= => Hekw.
          have Hekv : sv_ek v = true.
          { move: Hekw. by rewrite Eek'. }
          rewrite Esg -(pend_sig_none Epd0).
          exact: (di_bodycarg HI Ev Hekv).
       ++ move=> _.
          rewrite /asv /= Ew /= => Hekw.
          have Hekv : sv_ek v = true.
          { move: Hekw. by rewrite Eek'. }
          rewrite Esg.
          apply: nth1cargP.
          move: Eg6. by rewrite Hekv.
    -- exact: (di_chain2 HI HA0).
Qed.

Lemma disc_step_call :
  forall mem regs pc tg c pct pc' i tni c' pid call_arg n,
    Transitional.executing cde pc (TrJalProc (c', pid)) tg c ->
    Transitional.find_plabel_in_code cde c' pid = Some pc' ->
    Transitional.executing cde pc' i tni c' ->
    c <> c' ->
    Transitional.check_pc_call c tni pid ->
    pct = Level n ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int call_arg ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem,
       Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n)
         (Transitional.Register.invalidate regs),
       pc', inc_pc_tag pct).
Proof.
  move=> mem regs pc tg c pct pc' i tni c' pid call_arg n
         Hex Hfl Hex' Hneq Hcpc Epct Hcom [cur [chain [F [cs HI]]]].
  have [b [cvnew [Hcur HI']]] :=
    dinv_step_call Hex Hfl Hex' Hneq Hcpc Epct Hcom HI.
  by eexists _, _, _, _; exact: HI'.
Qed.

End DiscStepC.

(** * T2M — [disc_inv]-preservation lemmas for the Alloc case of [TS.step]. *)

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

Section DiscStepD.

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

Lemma dinv_step_alloc :
  forall mem mem' regs pc tg c pct rsize rptr size ptr cur chain F cs,
    Transitional.executing cde pc (TrAlloc rptr rsize) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get rsize regs) = Other ->
    Transitional.val (Transitional.Register.get rsize regs) = Int size ->
    (size > 0)%Z ->
    Transitional.Memory.alloc mem c (Z.to_nat size) = Some (mem', ptr) ->
    dinv cur chain F cs mem regs pc pct ->
    ((exists v0, MDisc.svat MM pc = Some v0 /\ sv_ph v0 = PBody) /\
     dinv cur chain F cs mem'
       (Transitional.Register.set rptr (Ptr ptr) Other regs)
       (Pointer.inc pc) pct)
    \/ (exists cm,
        [/\ getm mem c = Some cm,
            ptr = (c, Transitional.Memory.nextblock cm, 0%Z),
            (exists v0, MDisc.svat MM pc = Some v0 /\ sv_ph v0 = PProlB)
          & dinv (Some (Transitional.Memory.nextblock cm)) chain
              (fun c0 => if Nat.eqb c0 c
                         then Transitional.Memory.nextblock cm :: F c0
                         else F c0) cs mem'
              (Transitional.Register.set rptr (Ptr ptr) Other regs)
              (Pointer.inc pc) pct]).
Proof.
  move=> mem mem' regs pc tg c pct rsize rptr size ptr cur chain F cs
         Hex Hpc Htg Hval Hpos Halloc HI.
  have [v [v' [Ev Evs Hnx]]] := exec_sv HMM Hex.
  have [w [Ew Hle]] := Hnx isT.
  have [cm [Hcm [Eptr Emem']]] := alloc_shape Halloc.
  have Ecc : Pointer.component pc = c.
  { by case: Hex => C_code [E _]. }
  have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
  { by case: (pc) => [[c0 b0] o0]. }
  have Hnb2 : (2 <= Transitional.Memory.nextblock cm)%N
    := di_nb2 HI Hcm.
  move: Evs => /=.
  case Eph: (sv_ph v) => //.
  +
    case E12: (is_r rptr R_SP && is_r rsize R_SP) => //.
    have Hsplit : forall P : Prop,
        (sc_eqb (sv_sc v) SCpark = false ->
         v' = SV PBody [::] None (sv_a1 v) (sv_a2 v) (sv_sc v)
                (sv_one v) (sv_ek v) (sv_arg v) -> P) ->
        (match sv_sc v with
         | SCpark => None
         | _ => Some (SV PBody [::] None (sv_a1 v) (sv_a2 v)
                        (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
         end = Some v' -> P).
    { move=> P HP.
      by case: (sv_sc v) HP => HP // -[E]; apply: HP. }
    apply: Hsplit => Hnp Evv. subst v'.
    case/andP: E12 => E1s E2s.
    have Er1 : rptr = R_SP := is_r_eq E1s.
    have Er2 : rsize = R_SP := is_r_eq E2s.
    subst rptr rsize.
    have [Hcur [Hsig Hpend]] := di_prol HI Ev (or_intror Eph).
    right. exists cm.
    split; [exact: Hcm | exact: Eptr | by exists v; split |].
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    move: Eph' Esg Epd' Ht1 Ht2 Hsc Hon
      => /= Eph' Esg Epd' Ht1 Ht2 Hsc Hon.
    have HFsub : forall c0 b0, (b0 \in F c0) = false ->
        (b0 \in (if Nat.eqb c0 c
                 then Transitional.Memory.nextblock cm :: F c0
                 else F c0)) = false ->
        True by [].
    move=> {HFsub}.
    have Hgup : forall x, goodu mem F x ->
        goodu mem'
          (fun c0 => if Nat.eqb c0 c
                     then Transitional.Memory.nextblock cm :: F c0
                     else F c0) x.
    { move=> x Hg p E.
      have [H1 H2 H3] := Hg p E.
      split.
      - case E0: (Nat.eqb (Pointer.component p) c); last exact: H1.
        move/PeanoNat.Nat.eqb_eq: E0 => E0.
        rewrite in_cons H1 orbF.
        have [cm0 [Hcm0 Hlt]] := H3.
        have Ecm0 : cm0 = cm.
        { move: Hcm0. rewrite E0 Hcm. by move=> [<-]. }
        subst cm0.
        by rewrite ltn_eqF.
      - exact: H2.
      - exact: (alloc_vblock Hcm Emem' H3). }
    have HRA : R_RA <> R_SP by [].
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
      apply: Hgup.
      exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA1).
      move: Ht1. rewrite /t_le.
      case/orP => /t_eqb_eq E1w; last first.
      { by rewrite /aux_claim E1w. }
      rewrite -E1w.
      move: (di_a1 HI Ev).
      rewrite /aux_claim Eph Eph' Esg.
      by case: (sv_a1 v) => //=; exact: Hgup.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      rewrite (tget_set_neq _ _ _ HA2).
      move: Ht2. rewrite /t_le.
      case/orP => /t_eqb_eq E2w; last first.
      { by rewrite /aux_claim E2w. }
      rewrite -E2w.
      move: (di_a2 HI Ev).
      rewrite /aux_claim Eph Eph' Esg.
      by case: (sv_a2 v) => //=; exact: Hgup.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      rewrite (tget_set_neq _ _ _ HO1).
      apply: (di_one HI Ev).
      exact: o_le_true Hon Hon1.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec Ecc.
      exists (Transitional.Memory.nextblock cm).
      split=> //.
      by rewrite PeanoNat.Nat.eqb_refl in_cons eqxx.
    * move=> w0 b0; rewrite Ew => -[<-] _ => -[<-].
      by rewrite Eptr tget_set_eq /= Ec Ecc Esg.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> w0 b0; rewrite Ew => -[<-] -[<-].
      rewrite Esg => j k.
      by rewrite nth_error_nil.
    * move=> w0 b0 k; rewrite Ew => -[<-] _. by rewrite Epd'.
    * move=> w0; rewrite Ew => -[<-] _ _ _.
      rewrite (tget_set_neq _ _ _ HRA).
      apply: (di_ra HI Ev).
      -- by rewrite Eph.
      -- by rewrite Hpend.
      -- move=> j. by rewrite Hsig nth_error_nil.
    * move=> c0 b0 j cv tg0 Hcell HbF'.
      case Enew: ((c0 == c)
                  && (b0 == Transitional.Memory.nextblock cm)).
      -- case/andP: Enew => /eqP E1 /eqP E2. subst c0 b0.
         move: HbF'.
         by rewrite PeanoNat.Nat.eqb_refl in_cons eqxx.
      -- rewrite (alloc_cell_old Hcm Emem' j Enew) in Hcell.
         have HbF : (b0 \in F c0) = false.
         { move: HbF'.
           case E0: (Nat.eqb c0 c) => //.
           rewrite in_cons.
           by case: (b0 == Transitional.Memory.nextblock cm);
              case: (b0 \in F c0). }
         have [T1 T2] := di_mem HI Hcell HbF.
         split=> // Hb1.
         exact: (Hgup _ (T2 Hb1)).
    * move=> c0 cm0 Hcm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm.
         exists cv, tg0. split=> //.
         rewrite (alloc_cell_old Hcm Emem' 0) //.
         rewrite eqxx /=.
         case E1: (1 == Transitional.Memory.nextblock cm) => //.
         move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         have Hcm0' : getm mem c0 = Some cm0.
         { by rewrite -(alloc_getm_other Emem' Hne). }
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm0'.
         exists cv, tg0. split=> //.
         by rewrite (alloc_cell_old Hcm Emem' 0) // Ec0.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      case: (sv_sc v) HD Hnp => HD Hnp0 //=.
      -- exact: (alloc_scr_val Hcm Emem' Hnb2 HD).
      -- exact: (alloc_scr_val Hcm Emem' Hnb2 HD).
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph'.
    * move=> c0 A. rewrite Ec => Hc0 HA.
      have [W1 W2] := di_scrfor HI Hc0 HA.
      split=> //.
      exact: (alloc_scr_val Hcm Emem' Hnb2 W2).
    * move=> i A HA.
      have [W1 W2 W3 W4 W5] := di_chain HI HA.
      have Hblt : a_blk A < Transitional.Memory.nextblock cm ->
          (a_comp A == c) && (a_blk A == Transitional.Memory.nextblock
             cm) = false.
      { move=> Hlt.
        by rewrite (ltn_eqF Hlt) andbF. }
      split=> //.
      -- case E0: (Nat.eqb (a_comp A) c); last by [].
         by rewrite in_cons W3 orbT.
      -- move=> j k Hk.
         have [cv [tg0 [Hcell Hrow]]] := W4 j k Hk.
         exists cv, tg0.
         have Hne : (a_comp A == c)
                    && (a_blk A == Transitional.Memory.nextblock cm)
                    = false.
         { case E0: (a_comp A == c); last by [].
           move/eqP: E0 => E0.
           have [cm0 [Hcm0 Hlt]] := di_fbound HI W3.
           have Ecm0 : cm0 = cm.
           { move: Hcm0. rewrite E0 Hcm. by move=> [<-]. }
           subst cm0.
           by rewrite (ltn_eqF Hlt). }
         rewrite (alloc_cell_old Hcm Emem' j Hne).
         split=> //.
         case: k {Hk} Hrow => //= -[T1 T2]; split=> //;
         exact: (Hgup _ T2).
    * move=> i A b0 HA Hb0. rewrite Ec Ecc => HcA.
      have Eb0 : b0 = Transitional.Memory.nextblock cm.
      { by move: Hb0 => -[<-]. }
      subst b0.
      have [W1 W2 W3 W4 W5] := di_chain HI HA.
      have [cm0 [Hcm0 Hlt]] := di_fbound HI W3.
      have Ecm0 : cm0 = cm.
      { move: Hcm0. rewrite HcA Hcm. by move=> [<-]. }
      subst cm0.
      move=> Eblk. by rewrite Eblk ltnn in Hlt.
    * exact: (di_dist2 HI).
    * move=> c0 b0.
      case E0: (Nat.eqb c0 c).
      -- move/PeanoNat.Nat.eqb_eq: E0 => E0. subst c0.
         rewrite in_cons.
         case/orP => [/eqP Eb0|HbF].
         ++ subst b0.
            exists {| Transitional.Memory.content :=
                        setm (Transitional.Memory.content cm)
                          (Transitional.Memory.nextblock cm)
                          (repeat (Transitional.tUndef,
                                   def_mem_tag c false)
                             (Z.to_nat size));
                      Transitional.Memory.nextblock :=
                        (1 + Transitional.Memory.nextblock cm)%N |}.
            split; first by rewrite (alloc_getm_same Emem').
            by rewrite /= add1n ltnSn.
         ++ have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
            have Ecm0 : cm0 = cm.
            { move: Hcm0. rewrite Hcm. by move=> [<-]. }
            subst cm0.
            exists {| Transitional.Memory.content :=
                        setm (Transitional.Memory.content cm)
                          (Transitional.Memory.nextblock cm)
                          (repeat (Transitional.tUndef,
                                   def_mem_tag c false)
                             (Z.to_nat size));
                      Transitional.Memory.nextblock :=
                        (1 + Transitional.Memory.nextblock cm)%N |}.
            split; first by rewrite (alloc_getm_same Emem').
            by rewrite /= add1n ltnS (ltnW Hlt).
      -- move=> HbF.
         have Hne : c0 <> c by move=> E; rewrite E PeanoNat.Nat.eqb_refl in E0.
         have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
         exists cm0. split=> //.
         by rewrite (alloc_getm_other Emem' Hne).
    * move=> c0.
      case E0: (Nat.eqb c0 c).
      -- move/PeanoNat.Nat.eqb_eq: E0 => E0. subst c0.
         have [F0 F1] := di_f01 HI c.
         rewrite !in_cons F0 F1 !orbF.
         split.
         ++ case E1: (0 == Transitional.Memory.nextblock cm) => //.
            move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
         ++ case E1: (1 == Transitional.Memory.nextblock cm) => //.
            move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
      -- exact: (di_f01 HI c0).
    * move=> c0 cm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         rewrite (alloc_getm_same Emem') => -[<-] /=.
         by rewrite add1n (leqW Hnb2).
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         rewrite (alloc_getm_other Emem' Hne).
         exact: (di_nb2 HI).
    * move=> c0 S Hs.
      have [cm0 Hcm0] := di_dom HI Hs.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         eexists. by rewrite (alloc_getm_same Emem').
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         exists cm0.
         by rewrite (alloc_getm_other Emem' Hne).
    * exact: (di_level HI).
    * move=> c0 cm0 Hcm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm.
         exists cv, tg0.
         split; last by split=> //; exact: (Hgup _ Hgd).
         rewrite (alloc_cell_old Hcm Emem' 1) //.
         rewrite eqxx /=.
         case E1: (1 == Transitional.Memory.nextblock cm) => //.
         move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         have Hcm0' : getm mem c0 = Some cm0.
         { by rewrite -(alloc_getm_other Emem' Hne). }
         have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm0'.
         exists cv, tg0.
         split; last by split=> //; exact: (Hgup _ Hgd).
         by rewrite (alloc_cell_old Hcm Emem' 1) // Ec0.
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
      apply: (alloc_scr_val Hcm Emem' Hnb2).
      exact: (di_scr0 HI Hc0 Hg0 Htw).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] _.
      rewrite (pend_sig_none Epd') Esg.
      exact: bodycarg_nil.
    * exact: (di_chain2 HI).
  +
    case E123: [|| is_r rptr R_SP, is_r rsize R_SP | is_r rptr R_RA]
      => //.
    case Epd0: (sv_pend v) => //.
    case Eau: (t_eqb (rtaint v rsize) AU) => // -[Evv]. subst v'.
    move/negbT: E123. rewrite !negb_or.
    case/andP => E1s /andP [E2s E1r].
    left. split.
    { exists v. by split. }
    have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields rptr AU v.
    have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
      := wone_fields rptr false (wtaint rptr AU v).
    have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
      := warg_w_fields rptr (wone rptr false (wtaint rptr AU v)).
    have [[Eph' Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
    rewrite G1 W2ph W1ph in Eph'. rewrite G2 W2sg W1sg in Esg.
    rewrite G3 W2pd W1pd in Epd'. rewrite G4 W2sc W1sc in Hsc.
    rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
    rewrite G7 in Hon. rewrite G8 in Eek'.
    have Hgnew : goodu mem' F (Ptr ptr).
    { rewrite Eptr. move=> p [<-].
      split=> /=.
      - case E: (Transitional.Memory.nextblock cm \in F c) => //.
        have [cm0 [Hcm0 Hlt]] := di_fbound HI E.
        have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
        subst cm0. by rewrite ltnn in Hlt.
      - move=> E1. by rewrite E1 in Hnb2.
      - eexists. split; first by rewrite (alloc_getm_same Emem').
        by rewrite /= ltnSn. }
    have Hgup : forall x, goodu mem F x -> goodu mem' F x
      := fun x => alloc_goodu Hcm Emem' (F := F) (x := x).
    have HbneA : forall (cA : Component.id) (b1 : Block.id),
        b1 \in F cA ->
        (cA == c) && (b1 == Transitional.Memory.nextblock cm) = false.
    { move=> cA b1 Hb1.
      case E0: (cA == c) => //=.
      have [cm0 [Hcm0 Hlt]] := di_fbound HI Hb1.
      move/eqP: E0 => E0.
      have Ecm0 : cm0 = cm by move: Hcm0; rewrite E0 Hcm => -[].
      subst cm0. by rewrite (ltn_eqF Hlt). }
    constructor.
    * move=> r0 Hr0.
      case E0: (is_r r0 rptr).
      -- have -> : r0 = rptr := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         exact: (di_rtag HI).
    * move=> r0 H1 H2 H3 H4.
      case E0: (is_r r0 rptr).
      -- have -> : r0 = rptr := is_r_eq E0.
         by rewrite tget_set_eq.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
         apply: Hgup.
         exact: (di_rval HI H1 H2 H3 H4).
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E01: (is_r rptr R_AUX1).
      -- have Er : rptr = R_AUX1 := is_r_eq E01. subst rptr.
         rewrite tget_set_eq /=.
         have Ea1 : sv_a1 (wtaint R_AUX1 AU v) = AU by [].
         move: Ht1. rewrite Ea1 => Ht1.
         apply: (aux_claim_le Eph' Esg Epd' Ht1).
         exact: Hgnew.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E01)).
         have Ea1 : sv_a1 (wtaint rptr AU v) = sv_a1 v.
         { rewrite /wtaint E01.
           by case: (is_r rptr R_AUX2). }
         move: Ht1. rewrite Ea1 => Ht1.
         apply: (aux_claim_le Eph' Esg Epd' Ht1).
         apply: (alloc_aux_claim Hcm Emem').
         move: (di_a1 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec Ecc.
      case E02: (is_r rptr R_AUX2).
      -- have Er : rptr = R_AUX2 := is_r_eq E02. subst rptr.
         rewrite tget_set_eq /=.
         have Ea2 : sv_a2 (wtaint R_AUX2 AU v) = AU by [].
         move: Ht2. rewrite Ea2 => Ht2.
         apply: (aux_claim_le Eph' Esg Epd' Ht2).
         exact: Hgnew.
      -- rewrite (tget_set_neq _ _ _ (is_r_neq' E02)).
         have Ea2 : sv_a2 (wtaint rptr AU v) = sv_a2 v.
         { rewrite /wtaint E02.
           by case: (is_r rptr R_AUX1). }
         move: Ht2. rewrite Ea2 => Ht2.
         apply: (aux_claim_le Eph' Esg Epd' Ht2).
         apply: (alloc_aux_claim Hcm Emem').
         move: (di_a2 HI Ev). by rewrite Ecc.
    * move=> w0; rewrite Ew => -[<-] Hon1.
      have Hone' : sv_one (wone rptr false (wtaint rptr AU v)) = true
        := o_le_true Hon Hon1.
      move: Hone'. rewrite /wone.
      case E0o: (is_r rptr R_ONE) => //= Hone'.
      rewrite (tget_set_neq _ _ _ (is_r_neq' E0o)).
      apply: (di_one HI Ev).
      move: Hone'. by rewrite W1on.
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
      by case: HP.
    * move=> w0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> w0; rewrite Ew => -[<-] _ _. rewrite Ec.
      have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
      have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
      exact: (di_body HI Ev Hnp1 Hnp2).
    * move=> w0 b0; rewrite Ew => -[<-]. rewrite Eph' Esg Ec => HP Hb.
      rewrite (tget_set_neq _ _ _ (is_r_neq' (negbTE E1s))).
      exact: (di_sp HI Ev HP Hb).
    * move=> w0; rewrite Ew => -[<-]. rewrite Eph' Eph => HP.
      by [].
    * move=> w0 b0; rewrite Ew => -[<-].
      rewrite Esg Ec => Hb j k Hk.
      have Hnp1 : sv_ph v <> PProlA by rewrite Eph.
      have Hnp2 : sv_ph v <> PProlB by rewrite Eph.
      have [b1 [Hcur1 HbF1]] := di_body HI Ev Hnp1 Hnp2.
      have Eb : b0 = b1 by move: Hb; rewrite Hcur1 => -[].
      subst b0.
      have HF := di_frame HI Ev Hcur1.
      have [cv [tg0 [Hcell Hrow]]] := HF j k Hk.
      exists cv, tg0.
      rewrite (alloc_cell_old Hcm Emem' j (HbneA _ _ HbF1)).
      split=> //.
      case: k {Hk} Hrow => //= -[T1 T2]; split=> //;
      exact: (Hgup _ T2).
    * move=> w0 b0 k; rewrite Ew => -[<-] _.
      by rewrite Epd' Epd0.
    * move=> w0; rewrite Ew => -[<-].
      rewrite Eph' Eph Esg Epd' => HP HPd HK.
      rewrite (tget_set_neq _ _ _ (is_r_neq' (negbTE E1r))).
      apply: (di_ra HI Ev).
      -- by rewrite Eph.
      -- by rewrite Epd0.
      -- exact: HK.
    * move=> c0 b0 j cv tg0 Hcell HbF.
      case Enew: ((c0 == c)
                  && (b0 == Transitional.Memory.nextblock cm)).
      -- case/andP: Enew => /eqP Ea /eqP Eb. subst c0 b0.
         rewrite (alloc_cell_new Emem') in Hcell.
         have Ecv := nth_error_repeat_inv Hcell.
         case: Ecv => -> _.
         by split.
      -- rewrite (alloc_cell_old Hcm Emem' j Enew) in Hcell.
         have [T1 T2] := di_mem HI Hcell HbF.
         split=> // Hb1.
         exact: (Hgup _ (T2 Hb1)).
    * move=> c0 cm0 Hcm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm.
         exists cv, tg0. split=> //.
         rewrite (alloc_cell_old Hcm Emem' 0) //.
         rewrite eqxx /=.
         case E1: (1 == Transitional.Memory.nextblock cm) => //.
         move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         have Hcm0' : getm mem c0 = Some cm0.
         { by rewrite -(alloc_getm_other Emem' Hne). }
         have [cv [tg0 [Hcell Htag]]] := di_scrtag HI Hcm0'.
         exists cv, tg0. split=> //.
         by rewrite (alloc_cell_old Hcm Emem' 0) // Ec0.
    * move=> w0; rewrite Ew => -[<-]. rewrite Ec.
      have HD := di_scr HI Ev.
      move: Hsc. rewrite /sc_le.
      case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
      { by rewrite Escw. }
      rewrite -Escw.
      case: (sv_sc v) HD => HD /=.
      -- exact: (alloc_scr_val Hcm Emem' Hnb2 HD).
      -- rewrite Eph' Eph => _.
         rewrite (tget_set_neq _ _ _ (is_r_neq' (negbTE E1s))).
         exact: (alloc_scr_val Hcm Emem' Hnb2 (HD Eph)).
      -- exact: (alloc_scr_val Hcm Emem' Hnb2 HD).
      -- by [].
    * move=> w0 b0; rewrite Ew => -[<-]. by rewrite Eph' Eph.
    * move=> c0 A. rewrite Ec => Hc0 HA.
      have [W1 W2] := di_scrfor HI Hc0 HA.
      split=> //.
      exact: (alloc_scr_val Hcm Emem' Hnb2 W2).
    * move=> i A HA.
      have [W1 W2 W3 W4 W5] := di_chain HI HA.
      split=> //.
      move=> j k Hk.
      have [cv [tg0 [Hcell Hrow]]] := W4 j k Hk.
      exists cv, tg0.
      rewrite (alloc_cell_old Hcm Emem' j (HbneA _ _ W3)).
      split=> //.
      case: k {Hk} Hrow => //= -[T1 T2]; split=> //;
      exact: (Hgup _ T2).
    * move=> i A b0 HA Hb0. rewrite Ec => HcA.
      exact: (di_dist HI HA Hb0 HcA).
    * exact: (di_dist2 HI).
    * move=> c0 b0 HbF.
      have [cm0 [Hcm0 Hlt]] := di_fbound HI HbF.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         have Ecm0 : cm0 = cm by move: Hcm0; rewrite Hcm => -[].
         subst cm0.
         eexists. split; first by rewrite (alloc_getm_same Emem').
         by rewrite /= add1n ltnS (ltnW Hlt).
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         exists cm0. split=> //.
         by rewrite (alloc_getm_other Emem' Hne).
    * exact: (di_f01 HI).
    * move=> c0 cm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         rewrite (alloc_getm_same Emem') => -[<-] /=.
         by rewrite add1n (leqW Hnb2).
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         rewrite (alloc_getm_other Emem' Hne).
         exact: (di_nb2 HI).
    * move=> c0 S Hs.
      have [cm0 Hcm0] := di_dom HI Hs.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         eexists. by rewrite (alloc_getm_same Emem').
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         exists cm0.
         by rewrite (alloc_getm_other Emem' Hne).
    * exact: (di_level HI).
    * move=> c0 cm0 Hcm0.
      case Ec0: (c0 == c).
      -- move/eqP: Ec0 => Ec0. subst c0.
         have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm.
         exists cv, tg0.
         split; last by split=> //; exact: (Hgup _ Hgd).
         rewrite (alloc_cell_old Hcm Emem' 1) //.
         rewrite eqxx /=.
         case E1: (1 == Transitional.Memory.nextblock cm) => //.
         move/eqP: E1 => E1. by rewrite -E1 in Hnb2.
      -- have Hne : c0 <> c by move=> E; rewrite E eqxx in Ec0.
         have Hcm0' : getm mem c0 = Some cm0.
         { by rewrite -(alloc_getm_other Emem' Hne). }
         have [cv [tg0 [Hcell [Htag Hgd]]]] := di_flag HI Hcm0'.
         exists cv, tg0.
         split; last by split=> //; exact: (Hgup _ Hgd).
         by rewrite (alloc_cell_old Hcm Emem' 1) // Ec0.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ek HI Ev).
      rewrite -(wtaint_ek rptr AU v)
              -(wone_ek rptr false (wtaint rptr AU v)).
      by rewrite -Eek'.
    * move=> i X HX Hnw.
      case: (di_nwshadow HI HX Hnw)
        => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
      { right. exists j, W. by split. }
      left. split; last exact: HPre.
      by rewrite Ec.
    * move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
    * move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
      apply: (alloc_scr_val Hcm Emem' Hnb2).
      exact: (di_scr0 HI Hc0 Hg0 Htw).
    * move=> w0; rewrite Ew => -[<-] Hekw.
      apply: (di_ekwin HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * move=> w0; rewrite Ew => -[<-] Hekw.
      rewrite (pend_sig_eq Esg Epd').
      apply: (di_bodycarg HI Ev).
      rewrite ?wone_ek ?wtaint_ek in Eek'.
      move: Hekw. by rewrite Eek'.
    * exact: (di_chain2 HI).
Qed.

Lemma disc_step_alloc :
  forall mem mem' regs pc tg c pct rsize rptr size ptr,
    Transitional.executing cde pc (TrAlloc rptr rsize) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get rsize regs) = Other ->
    Transitional.val (Transitional.Register.get rsize regs) = Int size ->
    (size > 0)%Z ->
    Transitional.Memory.alloc mem c (Z.to_nat size) = Some (mem', ptr) ->
    disc_inv (mem, regs, pc, pct) ->
    disc_inv (mem', Transitional.Register.set rptr (Ptr ptr) Other regs,
       Pointer.inc pc, pct).
Proof.
  move=> mem mem' regs pc tg c pct rsize rptr size ptr Hex Hpc Htg
         Hval Hpos Halloc [cur [chain [F [cs HI]]]].
  case: (dinv_step_alloc Hex Hpc Htg Hval Hpos Halloc HI)
    => [[_ HI']|[cm [_ _ _ HI']]].
  - by exists cur, chain, F, cs.
  - by exists (Some (Transitional.Memory.nextblock cm)), chain,
       (fun c0 => if Nat.eqb c0 c
                  then Transitional.Memory.nextblock cm :: F c0
                  else F c0), cs.
Qed.

End DiscStepD.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceWF(jal_head_tret, mem_unchanged_jal).
Import TraceBracket(switch_val_color, switch_val_iscode, setm_self).
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepSilentWeak.

(* The s2/LEFT weak silent-step diagram square: s2 (= prog', L2) takes a silent step while
   LEFT-matched (s1/p is the strongly-related side), so the recomposed run s3 (= prog'') does
   NOT move; only M / the weak (Right) equivalence with s2 update.  PROVEN (Qed): s2 steps via
   [step_me] (Merged.transfer) in [sem']; the bridge [step_me_mp] converts it to a [step_mp]
   (LRC.transfer) step so the whole weak1 LRC step-machinery applies, and the Right-side
   [preserves_weak_*_r] mirrors rebuild both equivalences. *)

Module StepWeak2 (S: RecompositionContext).

  (* Chain off StepWeak so the whole recomposition shares ONE Defs instance. *)
  Include StepWeak S.
  Import PCCM.

  (* [Step sem'] IS [step_me] (sem'.(step) = step1, and step1 _ _ [::] _ = step_me _ _ None). *)
  Lemma weak2_step1 : forall s2 s2', Step sem' s2 E0 s2' -> step_me (NC:=NC) s2 s2' None.
  Proof. move=> s2 s2' H. exact: H. Qed.

  (* ===================================================================================== *)
  (* RIGHT-SIDE MIRRORS of the weak1 [preserves_weak_*] reconstruction lemmas.  These rebuild *)
  (* [weak_equiv Right M s2' s3] + [common_equiv M s1 s2' s3] (the stepping state s2 sits in   *)
  (* the SECOND common-equiv slot; s1/s3 are fixed).  Proofs mirror the Left versions, with     *)
  (* the running component's non-relevance ([~ is_relevant_comp Right (color_of s2)]) now        *)
  (* obtained via the [domm ip]/[domm ic] DISJOINTNESS (on the Left it was free).                *)
  (* ===================================================================================== *)

  (* The running component of an s2 weakly-Right-matched state is NOT a [Right]-relevant
     component: it sits in [domm ip] (its side is [Left]) which is disjoint from [domm ic]. *)
  Lemma running_not_relevant_right : forall (s s' : state) M,
      weak_equiv Right M s s' -> ~ is_relevant_comp Right (color_of s).
  Proof.
    move=> s s' M weak.
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    have Hip : color_of s \in domm ip.
    { case Hni: (color_of s \in domm ip) => //.
      by move: side_eqw; rewrite /side_of /other_side Hni. }
    rewrite /is_relevant_comp. apply/negP.
    pose proof Hmergeable_ifaces as [[_ Hdis] _]. exact: (fdisjointP Hdis _ Hip).
  Qed.

  (* bare [points_to_comp_code] (the m2/m3 stack slots) survives a confined non-code write:
     the pointed-to cell is CODE, the written cell [w0] holds non-code [old], so they differ. *)
  Lemma pts_code_data_write : forall (m : memory) (w0 : mword mt) v old v2 C,
    m w0 = Some old -> ~ is_code (taga old) ->
    points_to_comp_code m v2 C -> points_to_comp_code (setm m w0 v) v2 C.
  Proof.
    move=> m w0 v old v2 C Hold Hnco Hpts. move: Hpts.
    rewrite /points_to_comp_code setmE. case: eqP => [Heq|Hne]; last by [].
    rewrite Heq Hold /= => -[_ Hcd]. by case: (Hnco Hcd).
  Qed.

  Lemma pts_code_extend : forall (m m' : memory) v2 C,
    (forall w d, m w = Some d -> m' w = Some d) ->
    points_to_comp_code m v2 C -> points_to_comp_code m' v2 C.
  Proof.
    move=> m m' v2 C Hext. rewrite /points_to_comp_code.
    case Hm: (m v2) => [d|] //=. by rewrite (Hext _ _ Hm).
  Qed.

  Lemma wf_stack_data_write_r : forall (m1 m2 m3 : memory) (w0 : mword mt) v old n M,
    m2 w0 = Some old -> ~ is_code (taga old) ->
    wf_stack m1 m2 m3 n M -> wf_stack m1 (setm m2 w0 v) m3 n M.
  Proof.
    move=> m1 m2 m3 w0 v old n M Hold Hnco H.
    elim: H => [| n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH
                 | n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH].
    - exact: wf_stack_empty.
    - apply: wf_stack_cons_left; eauto.
      exact: (pts_code_data_write v Hold Hnco PTS2).
    - apply: wf_stack_cons_right; eauto.
      exact: (pts_code_data_write v Hold Hnco PTS2).
  Qed.

  Lemma wf_stack_extend_r : forall (m1 m2 m2' m3 : memory) n M,
    (forall w d, m2 w = Some d -> m2' w = Some d) ->
    wf_stack m1 m2 m3 n M -> wf_stack m1 m2' m3 n M.
  Proof.
    move=> m1 m2 m2' m3 n M Hext H.
    elim: H => [| n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH
                 | n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH].
    - exact: wf_stack_empty.
    - apply: wf_stack_cons_left; eauto. exact: (pts_code_extend Hext PTS2).
    - apply: wf_stack_cons_right; eauto. exact: (pts_code_extend Hext PTS2).
  Qed.

  Lemma preserves_weak_local_r : forall s1 s2 s3 M s2',
    weak_equiv Right M s2 s3 -> common_equiv M s1 s2 s3 ->
    mem s2' = mem s2 -> taga (pc s2') = taga (pc s2) ->
    register_domm (regs s2') -> capability_correctness M WS_S2 s2' ->
    pc_code_color s2' ->
    weak_equiv Right M s2' s3 /\ common_equiv M s1 s2' s3.
  Proof.
    move=> s1 s2 s3 M s2' weak common Hmem Htag Hrd Hcap Hpcc2.
    have Hcol : color_of s2' = color_of s2
      by rewrite (color_of_pc_tag s2') (color_of_pc_tag s2) Htag.
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    inversion common as [m0 c1 c2 c3 n c0 tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m0 c1 c2 c3.
    split.
    - apply: weak_equiv_def.
      + by rewrite Hcol.
      + by rewrite Hcol.
      + move=> v w Hrel. rewrite Hmem => Hmw. exact: (w_mem v w Hrel Hmw).
      + exact: w'_mem.
      + rewrite Hmem. exact: entry_offw.
      + move=> w d Hcode Hrel. rewrite Hmem. exact: (mem_matchw w d Hcode Hrel).
    - eapply common_equiv_def with (n := n) (c := c0).
      + exact: tag_pc1.
      + by rewrite Htag.
      + exact: tag_pc3.
      + rewrite Hmem. exact: wfst.
      + exact: reg_domm1.
      + exact: Hrd.
      + exact: reg_domm3.
      + exact: gmc1.
      + rewrite Hmem. exact: gmc2.
      + exact: gmc3.
      + exact: capa_cor1.
      + exact: Hcap.
      + exact: capa_cor3.
      + exact: code_left.
      + exact: (combined_codes_mem_cong_w (esym Hmem) (erefl (mem s3)) code_right).
      + exact: Hcval.
      + exact: wpcc1.
      + exact: Hpcc2.
  Qed.

  Lemma preserves_weak_mem_write_r : forall s1 s2 s3 M s2' w0 v old,
    weak_equiv Right M s2 s3 -> common_equiv M s1 s2 s3 ->
    mem s2 w0 = Some old ->
    mem s2' = setm (mem s2) w0 v ->
    taga (pc s2') = taga (pc s2) ->
    color (taga v) = color_of s2 -> color (taga old) = color_of s2 ->
    ~ is_code (taga v) -> ~ is_code (taga old) ->
    register_domm (regs s2') ->
    capability_correctness M WS_S2 s2' ->
    general_memory_correctness (mem s2') ->
    pc_code_color s2' ->
    weak_equiv Right M s2' s3 /\ common_equiv M s1 s2' s3.
  Proof.
    move=> s1 s2 s3 M s2' w0 v old weak common Hmemw0 Hmem' Htag Hcolv Hcolold Hncv Hncold Hrd Hcap Hgmc Hpcc2.
    have Hcol : color_of s2' = color_of s2
      by rewrite (color_of_pc_tag s2') (color_of_pc_tag s2) Htag.
    have Hcolvo : color (taga v) = color (taga old) by rewrite Hcolv Hcolold.
    have Hnrel_c0 : ~ is_relevant_comp Right (color_of s2) by exact: (running_not_relevant_right weak).
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    inversion common as [m0 c1 c2 c3 n c0 tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m0 c1 c2 c3.
    have addr_cong : forall (ww : mword mt) (tt : value_tag),
        address_correctness Right ww tt (mem s2) -> address_correctness Right ww tt (mem s2').
      move=> ww tt. rewrite /address_correctness. case: tt => [r0||| ] //=;
        move=> [u [Hu Himp]]; rewrite Hmem' setmE; case: eqP => [Heq|Hne];
        [ exists v; (split; first by []); move=> Hrel; exfalso; apply: Hnrel_c0; by rewrite -Hcolv
        | exists u; by rewrite Hu
        | exists v; (split; first by []); move=> Hrel; exfalso; apply: Hnrel_c0; by rewrite -Hcolv
        | exists u; by rewrite Hu ].
    split.
    - apply: weak_equiv_def.
      + by rewrite Hcol.
      + by rewrite Hcol.
      + move=> v0 w Hrelv0 Hw. apply: addr_cong.
        move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|Hne].
        * move=> [= Hvv]; subst v0; exfalso; apply: Hnrel_c0; move: Hrelv0; by rewrite Hcolv.
        * move=> Hw1; exact: (w_mem v0 w Hrelv0 Hw1).
      + exact: w'_mem.
      + move=> c w w' d d' proc l l' Hrelc Hw Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd'.
        have Hw1 : mem s2 w = Some d.
          move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|//].
          move=> [= Hdv]. exfalso; apply: Hncv. by rewrite -Hdv in Hcd.
        exact: (entry_offw c w w' d d' proc l l' Hrelc Hw1 Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd').
      + move=> w d Hncode Hrel.
        case: (@eqP _ w w0) => [Heq|Hne].
        * subst w. split.
          -- move=> Hs3d. exfalso.
             move: (mem_matchw w0 d Hncode Hrel) => [H1 _].
             move: (H1 Hs3d) => [d' [Hdm' Hs1d']].
             rewrite Hmemw0 in Hs1d'. case: Hs1d' => Hod. subst d'.
             have Htagd := data_match'_taga Hdm'. apply: Hnrel_c0.
             move: Hrel. rewrite /is_relevant_comp -Htagd Hcolold. done.
          -- move=> Hs1'd. move: Hs1'd; rewrite Hmem' setmE eq_refl.
             move=> [= Hdv]. subst d. exfalso; apply: Hnrel_c0.
             move: Hrel. by rewrite Hcolv.
        * have Hrw : mem s2' w = mem s2 w
            by rewrite Hmem' setmE; case: eqP => // ?; subst w.
          rewrite Hrw. exact: (mem_matchw w d Hncode Hrel).
    - eapply common_equiv_def with (n := n) (c := c0).
      + exact: tag_pc1.
      + by rewrite Htag.
      + exact: tag_pc3.
      + rewrite Hmem'. exact: (wf_stack_data_write_r v Hmemw0 Hncold wfst).
      + exact: reg_domm1.
      + exact: Hrd.
      + exact: reg_domm3.
      + exact: gmc1.
      + exact: Hgmc.
      + exact: gmc3.
      + exact: capa_cor1.
      + exact: Hcap.
      + exact: capa_cor3.
      + exact: code_left.
      + (* combined_codes Right s2' s3 *)
        move=> w v0 t off c Hrelc Hoff Hcodet Hcolt.
        move: (code_right w v0 t off c Hrelc Hoff Hcodet Hcolt) => [H1 H2]. split.
        * move=> Hs2'.
          have Hs2 : mem s2 w = Some (v0@t).
            move: Hs2'; rewrite Hmem' setmE; case: eqP => [Heq|//].
            move=> [= Hva]. exfalso; apply: Hncv. by rewrite Hva.
          move: (H1 Hs2) => [v' [Hdm Hs3]]. exists v'. split; last exact: Hs3.
          rewrite Hmem'. exact: (decode_match_data_write_l v Hmemw0 Hncold Hdm).
        * move=> Hs3.
          move: (H2 Hs3) => [v' [Hdm Hs2]]. exists v'. split.
          -- rewrite Hmem'. exact: (decode_match_data_write_l v Hmemw0 Hncold Hdm).
          -- rewrite Hmem' setmE; case: eqP => [Heq|Hne]; last exact: Hs2.
             exfalso; apply: Hncold. move: Hs2; rewrite Heq Hmemw0.
             move=> [= Hoa]. by rewrite Hoa.
      + exact: Hcval.
      + exact: wpcc1.
      + exact: Hpcc2.
  Qed.

  Lemma preserves_weak_alloc_r : forall s1 s2 s3 M s2',
    weak_equiv Right M s2 s3 -> common_equiv M s1 s2 s3 ->
    taga (pc s2') = taga (pc s2) ->
    (forall w d, mem s2 w = Some d -> mem s2' w = Some d) ->
    (forall w d, mem s2' w = Some d ->
       mem s2 w = Some d \/ (color (taga d) = color_of s2 /\ ~ is_code (taga d))) ->
    register_domm (regs s2') ->
    capability_correctness M WS_S2 s2' ->
    general_memory_correctness (mem s2') ->
    pc_code_color s2' ->
    weak_equiv Right M s2' s3 /\ common_equiv M s1 s2' s3.
  Proof.
    move=> s1 s2 s3 M s2' weak common Htag Hext1 Hext2 Hrd Hcap Hgmc Hpcc2.
    have Hcol : color_of s2' = color_of s2
      by rewrite (color_of_pc_tag s2') (color_of_pc_tag s2) Htag.
    have Hnrel_c0 : ~ is_relevant_comp Right (color_of s2) by exact: (running_not_relevant_right weak).
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    inversion common as [m0 c1 c2 c3 n c0 tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m0 c1 c2 c3.
    have addr_cong : forall (ww : mword mt) (tt : value_tag),
        address_correctness Right ww tt (mem s2) -> address_correctness Right ww tt (mem s2').
      move=> ww tt. rewrite /address_correctness. case: tt => [r0||| ] //=;
        move=> [u [Hu Himp]]; exists u; (split; [exact: (Hext1 _ _ Hu) | exact: Himp]).
    split.
    - apply: weak_equiv_def.
      + by rewrite Hcol.
      + by rewrite Hcol.
      + move=> v0 w Hrelv0 Hw. apply: addr_cong.
        case: (Hext2 _ _ Hw) => [Hw1|[Hcol' _]].
        * exact: (w_mem v0 w Hrelv0 Hw1).
        * exfalso; apply: Hnrel_c0; move: Hrelv0; by rewrite Hcol'.
      + exact: w'_mem.
      + move=> c w w' d d' proc l l' Hrelc Hw Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd'.
        case: (Hext2 _ _ Hw) => [Hw1|[_ Hnc]].
        * exact: (entry_offw c w w' d d' proc l l' Hrelc Hw1 Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd').
        * by case: (Hnc Hcd).
      + move=> w d Hncode Hrel. split.
        * move=> Hs3d. move: (mem_matchw w d Hncode Hrel) => [H1 _].
          move: (H1 Hs3d) => [d' [Hdm' Hs1d']]. exists d'.
          split; [exact: Hdm' | exact: (Hext1 _ _ Hs1d')].
        * move=> Hs1'd. case: (Hext2 _ _ Hs1'd) => [Hs1d|[Hcol' _]].
          -- move: (mem_matchw w d Hncode Hrel) => [_ H2]. exact: (H2 Hs1d).
          -- exfalso; apply: Hnrel_c0; move: Hrel; by rewrite Hcol'.
    - eapply common_equiv_def with (n := n) (c := c0).
      + exact: tag_pc1.
      + by rewrite Htag.
      + exact: tag_pc3.
      + exact: (wf_stack_extend_r Hext1 wfst).
      + exact: reg_domm1.
      + exact: Hrd.
      + exact: reg_domm3.
      + exact: gmc1.
      + exact: Hgmc.
      + exact: gmc3.
      + exact: capa_cor1.
      + exact: Hcap.
      + exact: capa_cor3.
      + exact: code_left.
      + move=> w v0 t off c Hrelc Hoff Hcodet Hcolt.
        move: (code_right w v0 t off c Hrelc Hoff Hcodet Hcolt) => [H1 H2]. split.
        * move=> Hs2'. case: (Hext2 _ _ Hs2') => [Hs2|[_ Hnc]]; last by case: (Hnc Hcodet).
          move: (H1 Hs2) => [v' [Hdm Hs3]]. exists v'. split; last exact: Hs3.
          exact: (decode_match_extend_l Hext1 Hdm).
        * move=> Hs3. move: (H2 Hs3) => [v' [Hdm Hs2]]. exists v'. split.
          -- exact: (decode_match_extend_l Hext1 Hdm).
          -- exact: (Hext1 _ _ Hs2).
      + exact: Hcval.
      + exact: wpcc1.
      + exact: Hpcc2.
  Qed.

  Lemma preserves_weak_load_r : forall s1 s2 s3 M s2' w1 w2 (t2 : tag_type lrc_tags Symbolic.M),
    weak_equiv Right M s2 s3 -> common_equiv M s1 s2 s3 ->
    mem s2 w1 = Some (w2 @ t2) ->
    mem s2' = setm (mem s2) w1
                (w2 @ (switch_val t2 (moved_tag (vtag t2))).1) ->
    taga (pc s2') = taga (pc s2) ->
    (is_code t2 \/ color t2 = color_of s2) ->
    register_domm (regs s2') ->
    capability_correctness M WS_S2 s2' ->
    general_memory_correctness (mem s2') ->
    pc_code_color s2' ->
    weak_equiv Right M s2' s3 /\ common_equiv M s1 s2' s3.
  Proof.
    move=> s1 s2 s3 M s2' w1 w2 t2 weak common Hmw1 Hmem' Htag Hguard Hrd Hcap Hgmc Hpcc2.
    have Hcvo2 : code_vtag_other (mem s2).
    { inversion common as [m0 c1 c2 c3 wn wc wtpc1 wtpc2 wtpc3 wwfst wrd1 wrd2 wrd3
                            wgmc1 wgmc2 wgmc3 wcap1 wcap2 wcap3 wcl wcr wval].
      by move: wgmc2 => [_ [_ [_ [_ [_ [_ [_ [_ Hc]]]]]]]]. }
    case Hia: (is_address (vtag t2)).
    - have Hnc : ~~ is_code t2.
      { apply/negP => Hic. move: (Hcvo2 w1 (w2 @ t2) Hmw1 Hic) => /= Hvo.
        by move: Hia; rewrite Hvo. }
      have Hncp : ~ is_code t2 by (apply/negP; exact: Hnc).
      have Hcol : color t2 = color_of s2.
      { case: Hguard => [Hic | Hcol]; last exact: Hcol.
        by move: Hic; rewrite (negbTE Hnc). }
      apply: (preserves_weak_mem_write_r weak common Hmw1 Hmem' Htag _ _ _ _ Hrd Hcap Hgmc Hpcc2).
      + by rewrite /= switch_val_color Hcol.
      + by rewrite /= Hcol.
      + by rewrite /= switch_val_iscode; exact: Hncp.
      + by rewrite /=; exact: Hncp.
    - have Hnt : forall (tt : tag_type lrc_tags Symbolic.M),
          is_address (vtag tt) = false ->
          (switch_val tt (moved_tag (vtag tt))).1 = tt.
      { move=> [vt ct et bt] /=. by case: vt. }
      have Hid : mem s2' = mem s2 by (rewrite Hmem' (Hnt t2 Hia); exact: (setm_self Hmw1)).
      exact: (preserves_weak_local_r weak common Hid Htag Hrd Hcap Hpcc2).
  Qed.

  Lemma step_silent_weak2:
    forall s2 s2', Step sem' s2 E0 s2' ->
    forall s1 s3 M, strong_equiv Left M s1 s3 ->
             weak_equiv Right M s2 s3 ->
             common_equiv M s1 s2 s3 ->
    exists M', strong_equiv Left M' s1 s3 /\
            weak_equiv Right M' s2' s3 /\
            common_equiv M' s1 s2' s3.
  Proof.
    import_context.
    intros s2 s2' step_s2 s1 s3 M strong weak common.
    pose proof (step_me_mp (weak2_step1 step_s2)) as step_mp. clear step_s2.
    exists M. split; [exact strong | ].
    inversion common as [m0 c1 c2 c3 wn wc wtpc1 wtpc2 wtpc3 wwfst wrd1 wrd2 wrd3
                          wgmc1 wgmc2 wgmc3 wcap1 wcap2 wcap3 wcl wcr wval].
    subst m0 c1 c2 c3.
    inversion step_mp.
    - (* 1  nop *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 2  const *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 3  mov *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 4  binop *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 5  load *)
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (preserves_weak_load_r weak common Hw0 Hmem' Htag Hguard).
      + exact: (lrc_silent_regdomm step_mp wrd2).
      + exact: (lrc_silent_cap step_mp wcap2).
      + apply: (lrc_silent_gmc step_mp _ wgmc2).
        by rewrite (color_of_pc_tag s2) wtpc2.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    - (* 6  store *)
      have [vnew [oldd [Hw0 [Hmem' [Htag [Hcolv [Hcolold [Hncv [Hncold _Hentvo]]]]]]]]] :=
        weak_store_facts ST OLD NEXT.
      apply: (preserves_weak_mem_write_r weak common Hw0 Hmem' Htag Hcolv Hcolold Hncv Hncold).
      + exact: (lrc_silent_regdomm step_mp wrd2).
      + exact: (lrc_silent_cap step_mp wcap2).
      + apply: (lrc_silent_gmc step_mp _ wgmc2).
        by rewrite (color_of_pc_tag s2) wtpc2.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    - (* 7  jump *)
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 8  bnz *)
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s2') = taga (pc s2) by (rewrite Htt ST).
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 9  jal — confined identity MemRead, mem unchanged (inlined, cf. weak1) *)
      unfold mvec, pc' in NEXT.
      have Hmemcell : mem s2 (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have [Hmm Htag] : mem s2' = mem s2 /\ taga (pc s2') = taga (pc s2).
      { move: NEXT. rewrite /next_state_updates_and_pc /next_state.
        case Hevi: (evi s2) => [evinp|] //=.
        case Hpc'2: (mem s2 (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
          ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
            case: ov_ev Htr Hk => ov ev Htr Hk;
            have Hhead := jal_head_tret Htr;
            move: Hk => /= Hk;
            case: (obind_inv Hk) => st' [Hndsu Hfin];
            move: Hfin => [= Hfins Hev]; rewrite -Hfins;
            have Htrpc := op_silent_trpc Htr Hev;
            split;
              [ rewrite /=;
                apply: (@mem_unchanged_jal s2 st' (pc0+1)%w vret tret (nseq 12 R) (tr ov)
                          (RegWrite ra (pc0+1)%w :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
                [ by (move=> w' v' Hin; cbn in Hin;
                      repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
                | by (move=> w' Hin; cbn in Hin;
                      repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ]
              | rewrite /= Htrpc; by rewrite ST ] ). }
      apply: (preserves_weak_local_r weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd2) | exact: (lrc_silent_cap step_mp wcap2) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 10 syscall (alloc) — confined memory extension by the running component *)
      have [Htag [Hext1 Hext2]] := weak_alloc_facts GETCALL CALL.
      apply: (preserves_weak_alloc_r weak common Htag Hext1 Hext2).
      + exact: (lrc_silent_regdomm step_mp wrd2).
      + exact: (lrc_silent_cap step_mp wcap2).
      + apply: (lrc_silent_gmc step_mp _ wgmc2).
        by rewrite (color_of_pc_tag s2) wtpc2.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
  Qed.

  (* [Print Assumptions step_silent_weak2] (checked once, not left in the functor body so it is not
     re-run on every downstream [Include]) lists ONLY the policy-allowed low-level LRC axioms
     ([shlw_*], [mask_*], [component_memory_prefix_*], [register_index_bound], [colors_bounded]) plus
     the module's [RecompositionContext] parameters.  No recomposition-substantive lemma is admitted:
     the [step_me]->[step_mp] bridge ([merged_transfer_lrc]/[step_me_mp]) and the Right-side
     [preserves_weak_*_r] reconstructions are all proved (Qed), and no [Classical] is used. *)

End StepWeak2.

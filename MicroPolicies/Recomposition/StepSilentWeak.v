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
Import TraceWF(ndsu_mem_noM, jal_head_tret, mem_unchanged_jal).
Import TraceBracket(jal_do_updates_result, jump_do_updates_result, nsu_silent_extract, mkfmap_const_val, check_belong_color, store_transfer, load_transfer, load_guard, switch_val_color, switch_val_iscode, switch_val_entry, switch_val_vtag, setm_reg_nonret, ndsu_nil_updts, const_transfer, bnz_transfer, mov_transfer, binop_transfer, switch_val_snd, jump_transfer, jal_transfer, setm_self).
Require Import MicroPolicies.Recomposition.PreservationLemmas.

Module StepWeak (S: RecompositionContext) (P: PresT S).

  Include P.
  Import PCCM.

  Lemma weak1_step2 : forall s1 s1', Step sem s1 E0 s1' -> step2 tt s1 E0 s1'.
  Proof. move=> s1 s1' H. by inversion H. Qed.

  Lemma combined_codes_mem_cong_w : forall (i : side) (s s' t t' : state),
    mem s = mem s' -> mem t = mem t' -> combined_codes i s t -> combined_codes i s' t'.
  Proof. move=> i s s' t t' Hs Ht H. rewrite /combined_codes -Hs -Ht. exact: H. Qed.

  Lemma preserves_weak_local : forall s1 s2 s3 M s1',
    weak_equiv Left M s1 s3 -> common_equiv M s1 s2 s3 ->
    mem s1' = mem s1 -> taga (pc s1') = taga (pc s1) ->
    register_domm (regs s1') -> capability_correctness M WS_S1 s1' ->
    pc_code_color s1' ->
    weak_equiv Left M s1' s3 /\ common_equiv M s1' s2 s3.
  Proof.
    move=> s1 s2 s3 M s1' weak common Hmem Htag Hrd Hcap Hpcc1.
    have Hcol : color_of s1' = color_of s1
      by rewrite (color_of_pc_tag s1') (color_of_pc_tag s1) Htag.
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
      + by rewrite Htag.
      + exact: tag_pc2.
      + exact: tag_pc3.
      + rewrite Hmem. exact: wfst.
      + exact: Hrd.
      + exact: reg_domm2.
      + exact: reg_domm3.
      + rewrite Hmem. exact: gmc1.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap.
      + exact: capa_cor2.
      + exact: capa_cor3.
      + exact: (combined_codes_mem_cong_w (esym Hmem) (erefl (mem s3)) code_left).
      + exact: code_right.
      + exact: Hcval.
      + exact: Hpcc1.
      + exact: wpcc2.
  Qed.

  Lemma decode_match_data_write_l : forall (i : side) (m m3 : memory) (w0 : mword mt) v old a b,
    m w0 = Some old -> ~ is_code (taga old) ->
    decode_match i m m3 a b -> decode_match i (setm m w0 v) m3 a b.
  Proof.
    move=> i m m3 w0 v old a b Hold Hnco H. case: H.
    - move=> H1 H2 Heq. exact: decode_match_no_JAL.
    - move=> H1 H2. exact: decode_match_alloc_JAL.
    - move=> imm imm' d d' Hda Hdb Hm Hm3 Hcd Htd Hoff.
      apply: (@decode_match_JAL _ _ _ _ _ imm imm' d d') => //.
      rewrite setmE. case: eqP => [Heq|//]. exfalso. apply: Hnco.
      move: Hm; rewrite Heq Hold; case=> Hd; rewrite Hd; exact: Hcd.
  Qed.

  Lemma pts_code'_data_write : forall (m : memory) (w0 : mword mt) v old j C v1,
    m w0 = Some old -> color (taga v) = color (taga old) ->
    ~ is_code (taga v) -> ~ is_code (taga old) ->
    points_to_comp_code' Right j m v1 C -> points_to_comp_code' Right j (setm m w0 v) v1 C.
  Proof.
    move=> m w0 v old j C v1 Hold Hcolvo Hncv Hnco Hpts.
    move: Hpts; rewrite /points_to_comp_code' setmE.
    case: eqP => [Heq|Hne]; last by [].
    rewrite Heq Hold /= => -[HcC Hdisj]. split; first by rewrite Hcolvo.
    case: Hdisj => [Hjr|Hco]; first by left. by case: (Hnco Hco).
  Qed.

  Lemma wf_stack_data_write_l : forall (m1 m2 m3 : memory) (w0 : mword mt) v old n M,
    m1 w0 = Some old -> color (taga v) = color (taga old) ->
    ~ is_code (taga v) -> ~ is_code (taga old) ->
    wf_stack m1 m2 m3 n M -> wf_stack (setm m1 w0 v) m2 m3 n M.
  Proof.
    move=> m1 m2 m3 w0 v old n M Hold Hcolvo Hncv Hnco H.
    elim: H => [| n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH
                 | n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH].
    - exact: wf_stack_empty.
    - apply: wf_stack_cons_left; eauto.
      exact: (pts_code'_data_write Hold Hcolvo Hncv Hnco PTS1).
    - apply: wf_stack_cons_right; eauto.
      exact: (pts_code'_data_write Hold Hcolvo Hncv Hnco PTS1).
  Qed.

  Lemma decode_match_extend_l : forall (i : side) (m m' m3 : memory) a b,
    (forall w d, m w = Some d -> m' w = Some d) ->
    decode_match i m m3 a b -> decode_match i m' m3 a b.
  Proof.
    move=> i m m' m3 a b Hext H. case: H.
    - move=> *; exact: decode_match_no_JAL.
    - move=> *; exact: decode_match_alloc_JAL.
    - move=> imm imm' d d' Hda Hdb Hm Hm3 Hcd Htd Hoff.
      apply: (@decode_match_JAL _ _ _ _ _ imm imm' d d') => //. exact: (Hext _ _ Hm).
  Qed.

  Lemma pts_code'_extend : forall (m m' : memory) j C v1,
    (forall w d, m w = Some d -> m' w = Some d) ->
    points_to_comp_code' Right j m v1 C -> points_to_comp_code' Right j m' v1 C.
  Proof.
    move=> m m' j C v1 Hext. rewrite /points_to_comp_code'.
    case Hm: (m v1) => [d|] //=. by rewrite (Hext _ _ Hm).
  Qed.

  Lemma wf_stack_extend_l : forall (m1 m1' m2 m3 : memory) n M,
    (forall w d, m1 w = Some d -> m1' w = Some d) ->
    wf_stack m1 m2 m3 n M -> wf_stack m1' m2 m3 n M.
  Proof.
    move=> m1 m1' m2 m3 n M Hext H.
    elim: H => [| n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH
                 | n' st v1 v2 v3 C off SIDE OFF PTS1 PTS2 PTS3 VALA WF IH].
    - exact: wf_stack_empty.
    - apply: wf_stack_cons_left; eauto. exact: (pts_code'_extend Hext PTS1).
    - apply: wf_stack_cons_right; eauto. exact: (pts_code'_extend Hext PTS1).
  Qed.

  Lemma data_match'_taga : forall i m d d', data_match' i m d d' -> taga d = taga d'.
  Proof. move=> i m [v1 t1] [v2 t2]; rewrite /data_match' /= => -[Ht _]; exact: Ht. Qed.

  Lemma preserves_weak_mem_write : forall s1 s2 s3 M s1' w0 v old,
    weak_equiv Left M s1 s3 -> common_equiv M s1 s2 s3 ->
    mem s1 w0 = Some old ->
    mem s1' = setm (mem s1) w0 v ->
    taga (pc s1') = taga (pc s1) ->
    color (taga v) = color_of s1 -> color (taga old) = color_of s1 ->
    ~ is_code (taga v) -> ~ is_code (taga old) ->
    register_domm (regs s1') ->
    capability_correctness M WS_S1 s1' ->
    general_memory_correctness (mem s1') ->
    pc_code_color s1' ->
    weak_equiv Left M s1' s3 /\ common_equiv M s1' s2 s3.
  Proof.
    move=> s1 s2 s3 M s1' w0 v old weak common Hmemw0 Hmem' Htag Hcolv Hcolold Hncv Hncold Hrd Hcap Hgmc Hpcc1.
    have Hcol : color_of s1' = color_of s1
      by rewrite (color_of_pc_tag s1') (color_of_pc_tag s1) Htag.
    have Hcolvo : color (taga v) = color (taga old) by rewrite Hcolv Hcolold.
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    have Hnrel_c0 : ~ is_relevant_comp Left (color_of s1).
      rewrite /is_relevant_comp => Hin.
      by move: side_eqw; rewrite /side_of /other_side Hin.
    inversion common as [m0 c1 c2 c3 n c0 tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m0 c1 c2 c3.
    have addr_cong : forall (ww : mword mt) (tt : value_tag),
        address_correctness Left ww tt (mem s1) -> address_correctness Left ww tt (mem s1').
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
      +
        move=> v0 w Hrelv0 Hw. apply: addr_cong.
        move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|Hne].
        * move=> [= Hvv]; subst v0; exfalso; apply: Hnrel_c0; move: Hrelv0; by rewrite Hcolv.
        * move=> Hw1; exact: (w_mem v0 w Hrelv0 Hw1).
      + exact: w'_mem.
      +
        move=> c w w' d d' proc l l' Hrelc Hw Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd'.
        have Hw1 : mem s1 w = Some d.
          move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|//].
          move=> [= Hdv]. exfalso; apply: Hncv. by rewrite -Hdv in Hcd.
        exact: (entry_offw c w w' d d' proc l l' Hrelc Hw1 Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd').
      +
        move=> w d Hncode Hrel.
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
        * have Hrw : mem s1' w = mem s1 w
            by rewrite Hmem' setmE; case: eqP => // ?; subst w.
          rewrite Hrw. exact: (mem_matchw w d Hncode Hrel).
    - eapply common_equiv_def with (n := n) (c := c0).
      + by rewrite Htag.
      + exact: tag_pc2.
      + exact: tag_pc3.
      +
        rewrite Hmem'. exact: (wf_stack_data_write_l Hmemw0 Hcolvo Hncv Hncold wfst).
      + exact: Hrd.
      + exact: reg_domm2.
      + exact: reg_domm3.
      + exact: Hgmc.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap.
      + exact: capa_cor2.
      + exact: capa_cor3.
      +
        move=> w v0 t off c Hrelc Hoff Hcodet Hcolt.
        move: (code_left w v0 t off c Hrelc Hoff Hcodet Hcolt) => [H1 H2]. split.
        * move=> Hs1'.
          have Hs1 : mem s1 w = Some (v0@t).
            move: Hs1'; rewrite Hmem' setmE; case: eqP => [Heq|//].
            move=> [= Hva]. exfalso; apply: Hncv. by rewrite Hva.
          move: (H1 Hs1) => [v' [Hdm Hs3]]. exists v'. split; last exact: Hs3.
          rewrite Hmem'. exact: (decode_match_data_write_l v Hmemw0 Hncold Hdm).
        * move=> Hs3.
          move: (H2 Hs3) => [v' [Hdm Hs1]]. exists v'. split.
          -- rewrite Hmem'. exact: (decode_match_data_write_l v Hmemw0 Hncold Hdm).
          -- rewrite Hmem' setmE; case: eqP => [Heq|Hne]; last exact: Hs1.
             exfalso; apply: Hncold. move: Hs1; rewrite Heq Hmemw0.
             move=> [= Hoa]. by rewrite Hoa.
      + exact: code_right.
      + exact: Hcval.
      + exact: Hpcc1.
      + exact: wpcc2.
  Qed.

  Lemma preserves_weak_alloc : forall s1 s2 s3 M s1',
    weak_equiv Left M s1 s3 -> common_equiv M s1 s2 s3 ->
    taga (pc s1') = taga (pc s1) ->
    (forall w d, mem s1 w = Some d -> mem s1' w = Some d) ->
    (forall w d, mem s1' w = Some d ->
       mem s1 w = Some d \/ (color (taga d) = color_of s1 /\ ~ is_code (taga d))) ->
    register_domm (regs s1') ->
    capability_correctness M WS_S1 s1' ->
    general_memory_correctness (mem s1') ->
    pc_code_color s1' ->
    weak_equiv Left M s1' s3 /\ common_equiv M s1' s2 s3.
  Proof.
    move=> s1 s2 s3 M s1' weak common Htag Hext1 Hext2 Hrd Hcap Hgmc Hpcc1.
    have Hcol : color_of s1' = color_of s1
      by rewrite (color_of_pc_tag s1') (color_of_pc_tag s1) Htag.
    inversion weak as [mw0 sw0 sw0' color_eqw side_eqw w_mem w'_mem entry_offw mem_matchw].
    subst mw0 sw0 sw0'.
    have Hnrel_c0 : ~ is_relevant_comp Left (color_of s1).
      rewrite /is_relevant_comp => Hin.
      by move: side_eqw; rewrite /side_of /other_side Hin.
    inversion common as [m0 c1 c2 c3 n c0 tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m0 c1 c2 c3.
    have addr_cong : forall (ww : mword mt) (tt : value_tag),
        address_correctness Left ww tt (mem s1) -> address_correctness Left ww tt (mem s1').
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
      + by rewrite Htag.
      + exact: tag_pc2.
      + exact: tag_pc3.
      + exact: (wf_stack_extend_l Hext1 wfst).
      + exact: Hrd.
      + exact: reg_domm2.
      + exact: reg_domm3.
      + exact: Hgmc.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap.
      + exact: capa_cor2.
      + exact: capa_cor3.
      + move=> w v0 t off c Hrelc Hoff Hcodet Hcolt.
        move: (code_left w v0 t off c Hrelc Hoff Hcodet Hcolt) => [H1 H2]. split.
        * move=> Hs1'. case: (Hext2 _ _ Hs1') => [Hs1|[_ Hnc]]; last by case: (Hnc Hcodet).
          move: (H1 Hs1) => [v' [Hdm Hs3]]. exists v'. split; last exact: Hs3.
          exact: (decode_match_extend_l Hext1 Hdm).
        * move=> Hs3. move: (H2 Hs3) => [v' [Hdm Hs1]]. exists v'. split.
          -- exact: (decode_match_extend_l Hext1 Hdm).
          -- exact: (Hext1 _ _ Hs1).
      + exact: code_right.
      + exact: Hcval.
      + exact: Hpcc1.
      + exact: wpcc2.
  Qed.

  Lemma ndsu1_regs_domm : forall (st st' : state) (tk : tag_kind) (tag : tag_type lrc_tags tk) updt,
    next_state_do_update st tag updt = Some st' -> domm (regs st') = domm (regs st).
  Proof.
    move=> st st' tk tag updt. case: tk tag => /= tag.
    - case: updt => //= [r x|r].
      + case E: (updm (regs st) r x@tag) => [rs'|] //= [<-] /=. exact: (updm_domm E).
      + case Er: (regs st r) => [a|] //=.
        case E: (updm (regs st) r (vala a)@tag) => [rs'|] //= [<-] /=. exact: (updm_domm E).
    - case: updt => //= [w1 w2|w].
      + case E: (updm (mem st) w1 w2@tag) => [m'|] //= [<-] //.
      + case Ew: (mem st w) => [a|] //=.
        case E: (updm (mem st) w (vala a)@tag) => [m'|] //= [<-] //.
    - by [].
  Qed.

  Lemma ndsu_regs_domm : forall (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks)
      (updts : seq update) (st st' : state),
    next_state_do_updates st tags updts = Some st' -> domm (regs st') = domm (regs st).
  Proof.
    elim => [|tk tks IH] tags updts st st' /=.
    - by move=> [<-].
    - case: updts => [|u us] //=.
      case E1: (next_state_do_update st (hshead tags) u) => [st1|] //= H.
      rewrite (IH _ _ _ _ H). exact: (ndsu1_regs_domm E1).
  Qed.

  Lemma weak_opcode_facts :
    forall (st : state) (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (fun tk => tag_type lrc_tags tk) (vinputs (OP op))) (updts : seq update)
           (pc' : mword mt) (s' : state),
      @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st (IVec (OP op) tpc ti ts)
        updts pc' = Some (s', None) ->
      (forall w v, ~ List.In (MemWrite w v) updts) ->
      (forall w, ~ List.In (MemRead w) updts) ->
      mem s' = mem st /\ taga (pc s') = tpc.
  Proof.
    move=> st op tpc ti ts updts pc' s' NEXT Hnmw Hnmr.
    move: NEXT. rewrite /next_state_updates_and_pc /next_state.
    case Hevi: (evi st) => [evinp|] //=.
    case Hni: (mem st pc') => [ni|];
      (case Htr: (LRC.transfer (IVec (OP op) tpc ti ts _) evinp) => [[ov ev]|] //=;
       case Edsu: (next_state_do_updates st (tr ov) updts) => [st0|] //=;
       move=> [= Hs Hev]; subst s';
       split; [ exact: (ndsu_mem_noM Hnmw Hnmr Edsu)
              | by rewrite /= (op_silent_trpc Htr Hev) ]).
  Qed.

  Lemma alloc_fun_effect : forall (s s' : state),
    alloc_fun (NC:=NC) s = Some s' ->
    domm (regs s') = domm (regs s) /\ taga (pc s') = taga (pc s) /\
    (forall w d, mem s w = Some d -> mem s' w = Some d) /\
    (forall w d, mem s' w = Some d ->
       mem s w = Some d \/ (color (taga d) = color_of s /\ ~ is_code (taga d))).
  Proof.
    move=> s s' H. move: H. rewrite /alloc_fun. cbv zeta. move=> H.
    case: (obind_inv H) => ra_val [Hra {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => reta [_ {}H].
    case: (obind_inv H) => uretchk [_ {}H].
    case: (obind_inv H) => sz [Hsz {}H].
    case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => len [Hlen {}H].
    case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    case: (obind_inv H) => addr [Haddr {}H].
    case: (obind_inv H) => regs' [Hregs' {}H].
    move: H => [= HSt]. subst s'.
    split; [|split; [|split]].
    - exact: (updm_domm Hregs').
    - by [].
    - move=> w d Hw /=. by rewrite unionmE Hw.
    - move=> w d /=. rewrite unionmE. case Ew: (mem s w) => [d0|].
      + by move=> [= ->]; left.
      + move=> Hb.
        have -> : d = (word.as_word (ssrint.Posz 0)) @
                    (def_mem_tag (match taga (pc s) with Level _ c => c end) false).
        { move: Hb; apply: mkfmap_const_val; by move=> p /mapP [n _ ->]. }
        right. rewrite /=. by rewrite color_of_pc_tag.
  Qed.

  Lemma alloc_fun_cap : forall (s s' : state),
    alloc_fun (NC:=NC) s = Some s' ->
    (forall w v t n, mem s' w = Some (v @ t) -> vtag t = Ret n -> mem s w = Some (v @ t)) /\
    (forall r v n, regs s' r = Some (v @ (Ret n)) -> regs s r = Some (v @ (Ret n))).
  Proof.
    move=> s s' H. move: H. rewrite /alloc_fun. cbv zeta. move=> H.
    case: (obind_inv H) => ra_val [Hra {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => reta [_ {}H].
    case: (obind_inv H) => uretchk [_ {}H].
    case: (obind_inv H) => sz [Hsz {}H].
    case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => len [Hlen {}H].
    case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    case: (obind_inv H) => addr [Haddr {}H].
    case: (obind_inv H) => regs' [Hregs' {}H].
    move: H => [= HSt]. subst s'. split.
    - move=> w v t n /=. rewrite unionmE. case Ew: (mem s w) => [d0|] /=.
      + by move=> H _.
      + move=> Hb Hvt. exfalso. move: Hvt.
        have [= _ Ht] : (v @ t) = (word.as_word (ssrint.Posz 0)) @
            (def_mem_tag (match taga (pc s) with Level _ c => c end) false).
        { move: Hb. apply: mkfmap_const_val. by move=> p /mapP [m _ ->]. }
        rewrite Ht /=. by [].
    - move=> r v n /=. rewrite (updm_set Hregs') setmE.
      case: eqP => [_ H|_ H]; last exact: H.
      by move: H => [= _ Hc]; discriminate Hc.
  Qed.

  Lemma step_regs_domm : forall (s s' : state),
    step_mp (NC:=NC) s s' None -> domm (regs s') = domm (regs s).
  Proof.
    move=> s s' Hstep. inversion Hstep.
    all: try (try rewrite /next_state_updates in NEXT;
              move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [_ [Hregs _]]]]]];
              rewrite Hregs; exact: (ndsu_regs_domm Edsu)).
    have Halloc := run_syscall_alloc GETCALL CALL.
    by have [Hd _] := alloc_fun_effect Halloc.
  Qed.

  Lemma lrc_silent_regdomm : forall (s s' : state),
      step_mp (NC:=NC) s s' None -> register_domm (regs s) -> register_domm (regs s').
  Proof.
    move=> s s' Hstep Hrd. rewrite /register_domm (step_regs_domm Hstep). exact: Hrd.
  Qed.

  Lemma cap_subset : forall (s s' : state) (M : metadata) (ws : which_state),
    (forall w v t n, mem s' w = Some (v @ t) -> vtag t = Ret n -> mem s w = Some (v @ t)) ->
    (forall r v n, regs s' r = Some (v @ (Ret n)) -> regs s r = Some (v @ (Ret n))) ->
    capability_correctness M ws s -> capability_correctness M ws s'.
  Proof.
    move=> s s' M ws Hmem Hreg Hcap v n p Hp.
    case: p Hp => [r|w] Hp.
    - have Hr : regs s r = Some (v @ (Ret n)) by exact: (Hreg r v n Hp).
      move: (Hcap v n (inl r) Hr) => [Hin Huniq]; split; first exact: Hin.
      move=> p' v'; case: p' => [r'|w'].
      + move=> Hr'; apply: (Huniq (inl r') v'); exact: (Hreg r' v' n Hr').
      + move=> [t' [Hw' Ht']]; apply: (Huniq (inr w') v'); exists t';
          split; [exact: (Hmem w' v' t' n Hw' Ht') | exact: Ht'].
    - case: Hp => t [Hw Ht].
      have Hwc : exists t0, mem s w = Some (v @ t0) /\ vtag t0 = Ret n
        by (exists t; split; [exact: (Hmem w v t n Hw Ht) | exact: Ht]).
      move: (Hcap v n (inr w) Hwc) => [Hin Huniq]; split; first exact: Hin.
      move=> p' v'; case: p' => [r'|w'].
      + move=> Hr'; apply: (Huniq (inl r') v'); exact: (Hreg r' v' n Hr').
      + move=> [t' [Hw'' Ht']]; apply: (Huniq (inr w') v'); exists t';
          split; [exact: (Hmem w' v' t' n Hw'' Ht') | exact: Ht'].
  Qed.

  Definition cap_at (s : state) (p : Types.reg mt + mword mt) (v : mword mt) (n : nat) : Prop :=
    match p with
    | inr w => exists t, mem s w = Some (v @ t) /\ vtag t = Ret n
    | inl r => regs s r = Some (v @ (Ret n))
    end.

  Lemma cap_correct_to_cap_at : forall M ws s,
    capability_correctness M ws s ->
    forall v n p, cap_at s p v n ->
      in_stack M ws v n /\ (forall p' v', cap_at s p' v' n -> p = p').
  Proof.
    move=> M ws s Hcap v n p Hp.
    move: (Hcap v n p Hp) => [Hin Huniq]. split; first exact: Hin.
    move=> p' v'. case: p Hp Huniq => [r|w] Hp Huniq; case: p' => [r'|w'] /=.
    - by move=> Hr'; move: (Huniq (inl r') v' Hr') => ->.
    - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))).
    - by move=> Hr'; move: (Huniq (inl r') v' Hr').
    - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))) => ->.
  Qed.

  Lemma cap_correct_via_cap_at : forall M ws s,
    (forall v n p, cap_at s p v n ->
       in_stack M ws v n /\ (forall p' v', cap_at s p' v' n -> p = p')) ->
    capability_correctness M ws s.
  Proof.
    move=> M ws s H v n p Hp.
    move: (H v n p Hp) => [Hin Huniq]. split; first exact: Hin.
    move=> p' v'. case: p Hp Huniq => [r|w] Hp Huniq; case: p' => [r'|w'] /=.
    - by move=> Hr'; move: (Huniq (inl r') v' Hr') => [= ->].
    - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))).
    - by move=> Hr'; move: (Huniq (inl r') v' Hr').
    - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))) => [= ->].
  Qed.

  Lemma cap_bijection : forall (s s' : state) (M : metadata) (ws : which_state)
      (f : Types.reg mt + mword mt -> Types.reg mt + mword mt),
    (forall p v n, cap_at s' p v n -> cap_at s (f p) v n) ->
    (forall p1 p2 v1 v2 n, cap_at s' p1 v1 n -> cap_at s' p2 v2 n -> f p1 = f p2 -> p1 = p2) ->
    capability_correctness M ws s -> capability_correctness M ws s'.
  Proof.
    move=> s s' M ws f H1 H2 /cap_correct_to_cap_at Hcap.
    apply: cap_correct_via_cap_at => v n p Hp.
    move: (Hcap v n (f p) (H1 p v n Hp)) => [Hin Huniq]. split; first exact: Hin.
    move=> p' v' Hp'. exact: (H2 p p' v v' n Hp Hp' (Huniq (f p') v' (H1 p' v' n Hp'))).
  Qed.

  Lemma cap_reloc : forall (s s' : state) (M : metadata) (ws : which_state)
      (src dst : Types.reg mt + mword mt),
    (forall v n, cap_at s' dst v n -> cap_at s src v n) ->
    (forall v n, ~ cap_at s' src v n) ->
    (forall p v n, p <> src -> p <> dst -> cap_at s' p v n -> cap_at s p v n) ->
    capability_correctness M ws s -> capability_correctness M ws s'.
  Proof.
    move=> s s' M ws src dst Hdst Hsrc Hoth Hcap.
    pose f := fun p : Types.reg mt + mword mt => if p == dst then src else p.
    apply: (cap_bijection (f := f) _ _ Hcap).
    - move=> p v n Hp. rewrite /f. case: (p =P dst) => [E|E].
      + subst p. exact: (Hdst v n Hp).
      + case: (p =P src) => [Es|Es].
        * subst p. exfalso. exact: (Hsrc v n Hp).
        * exact: (Hoth p v n Es E Hp).
    - move=> p1 p2 v1 v2 n Hp1 Hp2. rewrite /f.
      case: (p1 =P dst) => [E1|E1]; case: (p2 =P dst) => [E2|E2].
      + by rewrite E1 E2.
      + move=> Hf. exfalso. apply: (Hsrc v2 n). by rewrite Hf.
      + move=> Hf. exfalso. apply: (Hsrc v1 n). by rewrite -Hf.
      + by [].
  Qed.

  Lemma lrc_silent_cap : forall (s s' : state) (M : metadata) (ws : which_state),
      step_mp (NC:=NC) s s' None ->
      capability_correctness M ws s -> capability_correctness M ws s'.
  Proof.
    move=> s s' M ws Hstep Hcap. inversion Hstep.
    -
      move: NEXT; rewrite /next_state_updates => /nsu_silent_extract [op0 [ov0 [st0 [Edsu [Hm [Hr _]]]]]].
      have Hs0 := ndsu_nil_updts Edsu. rewrite Hs0 in Hm Hr.
      apply: (cap_subset _ _ Hcap); [by move=> w v t n0; rewrite Hm | by move=> r0 v n0; rewrite Hr].
    -
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := const_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => st1 [Hndsu1 Hrest]; move: Hrest => [= Hr1];
          case: (obind_inv Hndsu1) => rg' [Hupd Hr2]; move: Hr2 => [= Hr2];
          apply: (cap_subset _ _ Hcap);
            [ by move=> w v t n0; rewrite /= -Hr1 -Hr2 /=
            | move=> r0 v n0; rewrite /= -Hr1 -Hr2 /= (updm_set Hupd); move=> Hset;
              exact: (setm_reg_nonret (t := Other) ltac:(move=> ?; discriminate) Hset) ] ).
    -
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (mov_transfer Htr) => Htrov. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        move: HndsuC => [= Hfin2].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        case: (r2 =P r1) => [Er2|Er2].
        -
          subst r2. apply: (cap_subset _ _ Hcap).
          + by move=> w v t n0; rewrite -Hfin2 -HstbE /=.
          + move=> r v n0. rewrite -Hfin2 -HstbE /= (updm_set Hupdb) setmE (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite ST /= R1W. by [].
            * by [].
        -
          apply: (cap_reloc (s := s) (src := inl r1) (dst := inl r2)).
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE eqxx.
            move=> [= Hw1 Hvt]. rewrite /cap_at ST /= R1W Hvt -Hw1. by [].
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE.
            have Hr1r2 : r1 != r2 by apply/eqP => Hc; apply: Er2; rewrite Hc.
            rewrite (negbTE Hr1r2) (updm_set Hupda) setmE eqxx.
            move=> [= _ Ht]. move: Ht. by case: (t1).
          + move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
            * have Hrr1 : r != r1 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
              have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
              rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE (negbTE Hrr1). by [].
            * rewrite /cap_at -Hfin2 -HstbE /=. by [].
          + exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (mov_transfer Htr) => Htrov. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        move: HndsuC => [= Hfin2].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        case: (r2 =P r1) => [Er2|Er2].
        - subst r2. apply: (cap_subset _ _ Hcap).
          + by move=> w v t n0; rewrite -Hfin2 -HstbE /=.
          + move=> r v n0. rewrite -Hfin2 -HstbE /= (updm_set Hupdb) setmE (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite ST /= R1W. by [].
            * by [].
        - apply: (cap_reloc (s := s) (src := inl r1) (dst := inl r2)).
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE eqxx.
            move=> [= Hw1 Hvt]. rewrite /cap_at ST /= R1W Hvt -Hw1. by [].
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE.
            have Hr1r2 : r1 != r2 by apply/eqP => Hc; apply: Er2; rewrite Hc.
            rewrite (negbTE Hr1r2) (updm_set Hupda) setmE eqxx.
            move=> [= _ Ht]. move: Ht. by case: (t1).
          + move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
            * have Hrr1 : r != r1 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
              have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
              rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE (negbTE Hrr1). by [].
            * rewrite /cap_at -Hfin2 -HstbE /=. by [].
          + exact: Hcap. }
    -
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := binop_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => sta [Hnda HndsuB];
          case: (obind_inv Hnda) => a1 [Ha1 Hnda2];
          case: (obind_inv Hnda2) => rga [Hupda HstaE]; move: HstaE => [= HstaE];
          case: (obind_inv HndsuB) => stb [Hndb HndsuC];
          move: Hndb; rewrite -HstaE /= => Hndb;
          case: (obind_inv Hndb) => a2 [Ha2 Hndb2];
          case: (obind_inv Hndb2) => rgb [Hupdb HstbE]; move: HstbE => [= HstbE];
          case: (obind_inv HndsuC) => stc [Hndc Hfin2]; move: Hfin2 => [= Hfin2];
          move: Hndc; rewrite -HstbE /= => Hndc;
          case: (obind_inv Hndc) => rgc [Hupdc HstcE]; move: HstcE => [= HstcE];
          (have Ha1w : a1 = w1 @ t1 by (move: (Ha1); rewrite ST /= R1W; move=> [= <-]));
          (have Ha2w : a2 = w2 @ t2 by
            (move: Ha2; rewrite (updm_set Hupda) setmE Ha1w /=;
             case: eqP => [Hr21|Hr21];
               [ move: R2W; rewrite Hr21 R1W; move=> [= <- <-]; move=> [= <-]
               | rewrite ST /= R2W; move=> [= <-] ]));
          apply: (cap_subset _ _ Hcap);
            [ by move=> w v t n0; rewrite /= -Hfin2 -HstcE /=
            | move=> r0 v n0; rewrite /= -Hfin2 -HstcE /= (updm_set Hupdc) setmE;
              case: eqP => [Heq3|Hne3];
                [ by move=> [= _ Hcon]
                | rewrite (updm_set Hupdb) setmE;
                  case: eqP => [Heq2|Hne2];
                    [ subst r0; rewrite Ha2w /=; move=> Hpre; rewrite ST /= R2W; exact: Hpre
                    | rewrite (updm_set Hupda) setmE;
                      case: eqP => [Heq1|Hne1];
                        [ subst r0; rewrite Ha1w /=; move=> Hpre; rewrite ST /= R1W; exact: Hpre
                        | move=> Hpre; exact: Hpre ] ] ] ] ).
    -
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (load_transfer Htr) => [_ [_ Htrov]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => b1 [Hb1 Hndb2].
        case: (obind_inv Hndb2) => mmb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => rgc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        have Hb1w : b1 = w2 @ t2 by move: Hb1; rewrite ST /= MEM1; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inr w1) (dst := inl r2)).
        -
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx switch_val_snd.
          move=> [= Hw2 Hvt]. exists t2. rewrite ST /= MEM1 -Hw2. by split.
        -
          move=> v n [t [Hmem Hvt]]. move: Hmem Hvt.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (vtag t2).
        -
          move=> p v n Hpw Hpr. case: p Hpw Hpr => [r|w] Hpw Hpr.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (load_transfer Htr) => [_ [_ Htrov]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => b1 [Hb1 Hndb2].
        case: (obind_inv Hndb2) => mmb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => rgc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inr w1) (dst := inl r2)).
        - move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx switch_val_snd.
          move=> [= Hw2 Hvt]. exists t2. rewrite ST /= MEM1 -Hw2. by split.
        - move=> v n [t [Hmem Hvt]]. move: Hmem Hvt.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (vtag t2).
        - move=> p v n Hpw Hpr. case: p Hpw Hpr => [r|w] Hpw Hpr.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    -
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (store_transfer Htr) => [_ [_ [Htrov _]]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => a2 [Ha2 Hndb2].
        case: (obind_inv Hndb2) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => mmc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inl r2) (dst := inr w1)).
        -
          move=> v n [t [Hmem Hvt]]. move: Hmem.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx.
          move=> [= Hw2 Ht]. move: Hvt. rewrite -Ht switch_val_vtag => Hvt.
          rewrite /cap_at ST /= R2W Hvt -Hw2. by [].
        -
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ Ht]. move: Ht. by case: (t2).
        -
          move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (store_transfer Htr) => [_ [_ [Htrov _]]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => a2 [Ha2 Hndb2].
        case: (obind_inv Hndb2) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => mmc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inl r2) (dst := inr w1)).
        - move=> v n [t [Hmem Hvt]]. move: Hmem.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx.
          move=> [= Hw2 Ht]. move: Hvt. rewrite -Ht switch_val_vtag => Hvt.
          rewrite /cap_at ST /= R2W Hvt -Hw2. by [].
        - move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ Ht]. move: Ht. by case: (t2).
        - move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    -
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst Hev]; subst s';
          (have Htrov := jump_transfer Htr Hev); rewrite Htrov in Hndsu;
          (have HRA : regs s ra = Some (rav @ rat) by (rewrite ST; exact: RA));
          (have HRWj : regs s r = Some (w @ t1) by (rewrite ST; exact: RW));
          (have HCL : reg_clear_list (regs s) t1 = Some l by (rewrite ST; exact: CLEAR));
          (have Hjd := jump_do_updates_result HRA HRWj HCL);
          (have Hss : Some st0 = Some s by (rewrite -Hndsu; exact: Hjd));
          move: Hss => [= ->];
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /= | by move=> r0 v n0; rewrite /= ] ).
    -
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc'2: (mem s pc') => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := bnz_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => st1 [Hndsu1 Hrest]; move: Hrest => [= Hr1];
          case: (obind_inv Hndsu1) => a [Ha Hndsu2];
          case: (obind_inv Hndsu2) => rg' [Hupd Hr2]; move: Hr2 => [= Hr2];
          (have Haw : a = w @ t1 by (move: (Ha); rewrite ST /= RW; move=> [= <-]));
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /= -Hr1 -Hr2 /=
            | move=> r0 v n0; rewrite /= -Hr1 -Hr2 /= (updm_set Hupd) setmE;
              case: eqP => [Heq|Hne];
                [ subst r0; rewrite Ha Haw /=; move=> Hpre; exact: Hpre
                | move=> Hpre; exact: Hpre ] ] ).
    -
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst Hev]; subst s';
          (have Htrov := jal_transfer Htr Hev); rewrite Htrov in Hndsu;
          (have HmemRA : mem s (pc0 + 1)%w = Some (vret @ tret) by (rewrite ST; exact: RA));
          (have Ha4 : regs s (as_word (ssrint.Posz 4)) = Some (old @ told) by (rewrite ST; exact: OLD));
          (have HCL : reg_clear_list (regs s) told = Some l by (rewrite ST; exact: CLEAR));
          (have Hjd := jal_do_updates_result HmemRA Ha4 HCL);
          (have Hstep1 : next_state_do_update s (InternalJump : tag_type lrc_tags R)
             (RegWrite (as_word (ssrint.Posz 4)) (pc0 + 1)%w) = Some st0
             by (rewrite -Hjd; exact: Hndsu));
          move: Hstep1; rewrite /= => Hstep1;
          case: (obind_inv Hstep1) => regs' [Hupd Hst0];
          move: Hst0 => [= Hst0]; subst st0;
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /=
            | move=> r0 v n0; rewrite /= (updm_set Hupd) setmE;
              case: eqP => [_|_]; [ by move=> [= _ Hc]; discriminate Hc | by [] ] ] ).
    -
      have Halloc := run_syscall_alloc GETCALL CALL.
      have [Hmem Hreg] := alloc_fun_cap Halloc.
      apply: (cap_subset _ _ Hcap); [ exact: Hmem | exact: Hreg ].
  Qed.

  Lemma gmc_retag : forall (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (w0 : mword mt) (d d' : atom (mword mt) (tag_type lrc_tags Symbolic.M)),
    m w0 = Some d ->
    color (taga d') = color (taga d) ->
    is_code (taga d') = is_code (taga d) ->
    entry (taga d') = entry (taga d) ->
    (is_code (taga d) -> vala d' = vala d) ->
    (is_code (taga d') -> vtag (taga d') = Other) ->
    general_memory_correctness m ->
    general_memory_correctness (setm m w0 d').
  Proof.
    move=> m w0 d d' Hw0 Hcol Hic Hent Hval Hcvo'.
    move=> [Hmpc [Hmpc' [Hcpc [Hae [Hbnz [Hend [Hcim [Heic Hcvo]]]]]]]].
    have lift_target : forall (a : mword mt) (v' : atom (mword mt) (tag_type lrc_tags Symbolic.M)),
        m a = Some v' -> is_code (taga v') ->
        exists v'', setm m w0 d' a = Some v'' /\ is_code (taga v'').
    { move=> a v' Hma Hicv'. rewrite setmE. case: eqP => [Heq|Hne].
      - exists d'. split; first by []. move: Hma; rewrite Heq Hw0 => [= Ev]. by rewrite Hic Ev.
      - by exists v'. }
    have bnz_lift : forall (iw a : mword mt),
        match decode_instr iw with
        | Some (Bnz _ n) => exists v', m (addw a (swcast n)) = Some v' /\ is_code (taga v')
        | Some (Jal n) =>
            (exists v', m (swcast n) = Some v' /\ is_code (taga v')) \/ word_of_nat alloc_label = n
        | _ => True end ->
        match decode_instr iw with
        | Some (Bnz _ n) => exists v', setm m w0 d' (addw a (swcast n)) = Some v' /\ is_code (taga v')
        | Some (Jal n) =>
            (exists v', setm m w0 d' (swcast n) = Some v' /\ is_code (taga v')) \/ word_of_nat alloc_label = n
        | _ => True end.
    { move=> iw a. case: (decode_instr iw) => [instr|] //. case: instr => //=.
      - move=> r n [v' [Hmv' Hicv']]. exact: (lift_target _ _ Hmv' Hicv').
      - move=> n [[v' [Hmv' Hicv']]|Halloc];
          [ left; exact: (lift_target _ _ Hmv' Hicv') | by right ]. }
    rewrite /general_memory_correctness.
    split; last split; last split; last split; last split; last split; last split; last split.
    -
      move=> c w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hcv Hncv.
        have Hcd : color (taga d) = c by rewrite -Hcol.
        have Hncd : ~ is_code (taga d) by rewrite -Hic.
        exact: (Hmpc c w0 d Hw0 Hcd Hncd).
      + move=> Hw Hcv Hncv. exact: (Hmpc c w v Hw Hcv Hncv).
    -
      move=> c w v Hlt. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Haddr.
        have [Hc Hnc] := Hmpc' c w0 d Hlt Hw0 Haddr.
        split; [by rewrite Hcol | by rewrite Hic].
      + move=> Hw Haddr. exact: (Hmpc' c w v Hlt Hw Haddr).
    -
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        exact: (Hcpc w0 d Hw0 Hicd).
      + move=> Hw Hicv. exact: (Hcpc w v Hw Hicv).
    -
      rewrite /alloc_empty setmE. case: eqP => [Heq|Hne]; last exact: Hae.
      by move: Hw0; rewrite -Heq Hae.
    -
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        rewrite (Hval Hicd). exact: (bnz_lift _ _ (Hbnz w0 d Hw0 Hicd)).
      + move=> Hw Hicv. exact: (bnz_lift _ _ (Hbnz w v Hw Hicv)).
    -
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        rewrite (Hval Hicd). move: (Hend w0 d Hw0 Hicd) => [Hh|[v' [Hmv' Hicv']]].
        * by left.
        * right. exact: (lift_target _ _ Hmv' Hicv').
      + move=> Hw Hicv. move: (Hend w v Hw Hicv) => [Hh|[v' [Hmv' Hicv']]].
        * by left.
        * right. exact: (lift_target _ _ Hmv' Hicv').
    -
      move=> w d0. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. rewrite Hcol. exact: (Hcim w0 d Hw0).
      + move=> Hw. exact: (Hcim w d0 Hw).
    -
      move=> w d0 e. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. rewrite Hent Hic. move=> He. exact: (Heic w0 d e Hw0 He).
      + move=> Hw He. exact: (Heic w d0 e Hw He).
    -
      move=> w d0. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. exact: Hcvo'.
      + move=> Hw. exact: (Hcvo w d0 Hw).
  Qed.


  Lemma gmc_alloc : forall (s s' : state) (n0 c0 : nat),
    taga (pc s) = Level n0 c0 ->
    (1 + c0 < 2 ^ NC)%nat ->
    (c0 \in domm ip) || (c0 \in domm ic) ->
    alloc_fun (NC := NC) s = Some s' ->
    general_memory_correctness (mem s) -> general_memory_correctness (mem s').
  Proof.
    move=> s s' n0 c0 Htag Hbnd Hval Halloc Hgmc.
    move: Halloc. rewrite /alloc_fun. cbv zeta. move=> H.
    case: (obind_inv H) => ra_val [Hra {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => reta [_ {}H].
    case: (obind_inv H) => uretchk [_ {}H].
    case: (obind_inv H) => sz [Hsz {}H].
    case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => len [Hlen {}H].
    case: (obind_inv H) => u3 [Hbound {}H].
    have Hszbound : leq (len + 1) (2 ^ (word_size mt - NC)).
    { by move: Hbound; case: (leq (len + 1) (2 ^ (word_size mt - NC))). }
    move: H. case: ifP => [Hg|Hg]; first by []. move=> H.
    case: (obind_inv H) => addr [Haddr {}H].
    case: (obind_inv H) => regs' [Hregs' {}H].
    move: H => [= HSt]. subst s'. cbn [Symbolic.mem].
    set CC := (match taga (pc s) with Level _ c => c end).
    have HCC : CC = c0 by rewrite /CC Htag.
    set PFX := (@component_memory_prefix mt NC (ssrint.Posz (1 + CC))).
    set MA := (List.last (List.filter (fun mw => andw mw (@mask mt NC) == PFX) (domm (mem s))) PFX).
    rewrite -/MA in Hg.
    have Hmk : forall k, (k \in iota 0 len)%nat ->
      andw (addw MA (word.as_word (ssrint.Posz (k + 1)))) (@mask mt NC) = PFX.
    { apply: mask_range.
      - exact: Hszbound.
      - exact: (andw_last_component_prefix (ssrint.Posz (1 + CC)) (mem s)).
      - by move: Hg => /negb_false_iff /eqP. }
    move: Hgmc => [Hmpc [Hmpc' [Hcpc [Hae [Hbnz [Hend [Hcim [Heic Hcvo]]]]]]]].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    -
      rewrite /memory_prefix_condition => c w' v'. rewrite unionmE.
      case: ifP => _; [exact: Hmpc|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2 H0 _.
      left. subst v' w'. rewrite (Hmk x x_in_iota).
      by move: H0 => /= <-.
    -
      rewrite /memory_prefix_condition' => c w' v' Hb. rewrite unionmE.
      case: ifP => _; [exact: (Hmpc' _ _ _ Hb)|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2 H3 /=.
      rewrite H2 /=. split; last by [].
      have HbCC : 1 + CC < 2 ^ NC by rewrite HCC.
      move: H3; rewrite H1 (Hmk x x_in_iota).
      move=> /(component_memory_prefix_inj _ _ (ltnW NC_lt_word) HbCC Hb) /addnI Hcc.
      exact: Hcc.
    -
      move=> w v. rewrite unionmE.
      case: ifP => _; [exact: Hcpc|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
      move=> Hcode; rewrite H2 in Hcode; discriminate Hcode.
    -
      rewrite /alloc_empty unionmE. case: ifP => _; [exact: Hae|].
      destruct (mkfmap _ _) eqn:Hmkf; auto.
      apply mkfmap_Some in Hmkf. move: Hmkf => /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota.
      remember (word_of_nat alloc_label) as w.
      move=> [] H1 _. exfalso.
      have Hwp : andw w (@mask mt NC) = PFX by rewrite H1; exact: (Hmk x x_in_iota).
      move: Hwp; rewrite Heqw mask_alloc_label => Hz.
      apply: (component_memory_prefix_succ_not_zero (NC := NC) CC (ltnW NC_lt_word)); first by rewrite HCC.
      rewrite /PFX in Hz.
      transitivity (0%w : word (word_size mt));
        [exact: (esym Hz) | exact: (esym component_memory_prefix_zero)].
    -
      move=> w d. rewrite unionmE. case: ifP => Hin.
      + move=> Hd Hcode. move: (Hbnz w d Hd Hcode).
        case: (decode_instr (vala d)) => [[]|] //=.
        * move=> r n [v' [Hv' Hcv']]. exists v'. split; last exact: Hcv'.
          by rewrite unionmE Hv'.
        * move=> n [[v' [Hv' Hcv']]|Halc]; last by right.
          left. exists v'. split; last exact: Hcv'. by rewrite unionmE Hv'.
      + move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
        move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    -
      move=> w d. rewrite unionmE. case: ifP => Hin.
      + move=> Hd Hcode. move: (Hend w d Hd Hcode) => [Hh|[d' [Hd' Hcd']]]; [by left|].
        right. exists d'. split; last exact: Hcd'.
        by rewrite unionmE Hd'.
      + move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
        move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    -
      move=> w d. rewrite unionmE. case: ifP => _; [exact: Hcim|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. rewrite /= HCC.
      case/orP: Hval => [Hip|Hic]; [left|right]; exact/Extra.In_in.
    -
      move=> w d e. rewrite unionmE. case: ifP => _; [exact: Heic|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    -
      move=> w d. rewrite unionmE. case: ifP => _; [exact: Hcvo|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
  Qed.

  Lemma weak_alloc_facts : forall (pc0 : mword mt) (s1 s1' : state) (sc : syscall lrc_tags unit),
    Instance.table (NC:=NC) pc0 = Some sc ->
    @run_syscall _ _ lrc_tags LRC.transfer unit sc s1 = Some (s1', None) ->
    taga (pc s1') = taga (pc s1) /\
    (forall w d, mem s1 w = Some d -> mem s1' w = Some d) /\
    (forall w d, mem s1' w = Some d ->
       mem s1 w = Some d \/ (color (taga d) = color_of s1 /\ ~ is_code (taga d))).
  Proof.
    move=> pc0 s1 s1' sc Htbl Hrun.
    have Halloc := run_syscall_alloc Htbl Hrun.
    by have [_ [Htag [Hext1 Hext2]]] := alloc_fun_effect Halloc.
  Qed.


  Lemma lrc_silent_gmc : forall (s s' : state),
      step_mp (NC:=NC) s s' None ->
      (color_of s \in domm ip) || (color_of s \in domm ic) ->
      general_memory_correctness (mem s) -> general_memory_correctness (mem s').
  Proof.
    move=> s s' Hstep Hval Hgmc. inversion Hstep.
    all: try (try rewrite /next_state_updates in NEXT;
              move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]];
              (have Hmem0 : Symbolic.mem st0 = Symbolic.mem s
                 by (apply: (ndsu_mem_noM _ _ Edsu); [nomw|nomr]));
              rewrite Hmem Hmem0; assumption).
    -
      have [Hw0 [Hmem' _]] := weak_load_facts ST MEM1 NEXT.
      rewrite Hmem'. apply: (gmc_retag Hw0 _ _ _ _ _ Hgmc).
      + by rewrite switch_val_color.
      + by rewrite switch_val_iscode.
      + by rewrite switch_val_entry.
      + by [].
      +
        rewrite switch_val_iscode switch_val_vtag => Hic.
        have [_ [_ [_ [_ [_ [_ [_ [_ Hcvo_in]]]]]]]] := Hgmc.
        by rewrite (Hcvo_in w1 (w2 @ t2) Hw0 Hic).
    -
      have [v [old' [Hw0 [Hmem' [_ [Hcolv [Hcolold [Hncv [Hncold Hentvo]]]]]]]]] :=
        weak_store_facts ST OLD NEXT.
      rewrite Hmem'. apply: (gmc_retag Hw0 _ _ Hentvo _ _ Hgmc).
      + by rewrite Hcolv Hcolold.
      + by rewrite (introF idP Hncv) (introF idP Hncold).
      + by move=> Hc; case: (Hncold Hc).
      +
        by move=> Hic; case: (Hncv Hic).
    -
      unfold mvec, pc' in NEXT.
      suff E : Symbolic.mem s' = Symbolic.mem s by rewrite E; exact: Hgmc.
      have Hmemcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Hhead := jal_head_tret Htr;
          move: Hk => /= Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hfins _]; subst s';
          rewrite /=;
          apply: (@mem_unchanged_jal s st0 (pc0+1)%w vret tret (nseq 12 R) (tr ov)
                    (RegWrite ra (pc0+1)%w :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
          [ by (move=> w' v' Hin; cbn in Hin;
                repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
          | by (move=> w' Hin; cbn in Hin;
                repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ] ).
    -
      have Halloc := run_syscall_alloc GETCALL CALL.
      move: Hval; rewrite (color_of_pc_tag s).
      case Etag: (taga (Symbolic.pc s)) => [n0 c0] /= Hval'.
      exact: (gmc_alloc Etag (colors_bounded Hval') Hval' Halloc Hgmc).
  Qed.

  Lemma preserves_weak_load : forall s1 s2 s3 M s1' w1 w2 (t2 : tag_type lrc_tags Symbolic.M),
    weak_equiv Left M s1 s3 -> common_equiv M s1 s2 s3 ->
    mem s1 w1 = Some (w2 @ t2) ->
    mem s1' = setm (mem s1) w1
                (w2 @ (switch_val t2 (moved_tag (vtag t2))).1) ->
    taga (pc s1') = taga (pc s1) ->
    (is_code t2 \/ color t2 = color_of s1) ->
    register_domm (regs s1') ->
    capability_correctness M WS_S1 s1' ->
    general_memory_correctness (mem s1') ->
    pc_code_color s1' ->
    weak_equiv Left M s1' s3 /\ common_equiv M s1' s2 s3.
  Proof.
    move=> s1 s2 s3 M s1' w1 w2 t2 weak common Hmw1 Hmem' Htag Hguard Hrd Hcap Hgmc Hpcc1.
    have Hcvo1 : code_vtag_other (mem s1).
    { inversion common as [m0 c1 c2 c3 wn wc wtpc1 wtpc2 wtpc3 wwfst wrd1 wrd2 wrd3
                            wgmc1 wgmc2 wgmc3 wcap1 wcap2 wcap3 wcl wcr wval].
      by move: wgmc1 => [_ [_ [_ [_ [_ [_ [_ [_ Hc]]]]]]]]. }
    case Hia: (is_address (vtag t2)).
    -
      have Hnc : ~~ is_code t2.
      { apply/negP => Hic. move: (Hcvo1 w1 (w2 @ t2) Hmw1 Hic) => /= Hvo.
        by move: Hia; rewrite Hvo. }
      have Hncp : ~ is_code t2 by (apply/negP; exact: Hnc).
      have Hcol : color t2 = color_of s1.
      { case: Hguard => [Hic | Hcol]; last exact: Hcol.
        by move: Hic; rewrite (negbTE Hnc). }
      apply: (preserves_weak_mem_write weak common Hmw1 Hmem' Htag _ _ _ _ Hrd Hcap Hgmc Hpcc1).
      + by rewrite /= switch_val_color Hcol.
      + by rewrite /= Hcol.
      + by rewrite /= switch_val_iscode; exact: Hncp.
      + by rewrite /=; exact: Hncp.
    -
      have Hnt : forall (tt : tag_type lrc_tags Symbolic.M),
          is_address (vtag tt) = false ->
          (switch_val tt (moved_tag (vtag tt))).1 = tt.
      { move=> [vt ct et bt] /=. by case: vt. }
      have Hid : mem s1' = mem s1 by (rewrite Hmem' (Hnt t2 Hia); exact: (setm_self Hmw1)).
      exact: (preserves_weak_local weak common Hid Htag Hrd Hcap Hpcc1).
  Qed.

  Lemma step_silent_weak1:
    forall s1 s1', Step sem s1 E0 s1' ->
    forall s2 s3 M, strong_equiv Right M s2 s3 ->
             weak_equiv Left M s1 s3 ->
             common_equiv M s1 s2 s3 ->
    exists M', strong_equiv Right M' s2 s3 /\
          weak_equiv Left M' s1' s3 /\
          common_equiv M' s1' s2 s3.
  Proof.
    import_context.
    intros s1 s1' step_s1 s2 s3 M strong weak common. simpl in step_s1.
    pose proof (weak1_step2 step_s1) as step_mp. clear step_s1.
    unfold step2 in step_mp. simpl in step_mp.
    exists M. split; [exact strong | ].
    inversion common as [m0 c1 c2 c3 wn wc wtpc1 wtpc2 wtpc3 wwfst wrd1 wrd2 wrd3
                          wgmc1 wgmc2 wgmc3 wcap1 wcap2 wcap3 wcl wcr wval].
    subst m0 c1 c2 c3.
    inversion step_mp.
    -
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (preserves_weak_load weak common Hw0 Hmem' Htag Hguard).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    -
      have [vnew [oldd [Hw0 [Hmem' [Htag [Hcolv [Hcolold [Hncv [Hncold _Hentvo]]]]]]]]] :=
        weak_store_facts ST OLD NEXT.
      apply: (preserves_weak_mem_write weak common Hw0 Hmem' Htag Hcolv Hcolold Hncv Hncold).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    -
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      unfold mvec, pc' in NEXT.
      have Hmemcell : mem s1 (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have [Hmm Htag] : mem s1' = mem s1 /\ taga (pc s1') = taga (pc s1).
      { move: NEXT. rewrite /next_state_updates_and_pc /next_state.
        case Hevi: (evi s1) => [evinp|] //=.
        case Hpc'2: (mem s1 (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
          ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
            case: ov_ev Htr Hk => ov ev Htr Hk;
            have Hhead := jal_head_tret Htr;
            move: Hk => /= Hk;
            case: (obind_inv Hk) => st' [Hndsu Hfin];
            move: Hfin => [= Hfins Hev]; rewrite -Hfins;
            have Htrpc := op_silent_trpc Htr Hev;
            split;
              [ rewrite /=;
                apply: (@mem_unchanged_jal s1 st' (pc0+1)%w vret tret (nseq 12 R) (tr ov)
                          (RegWrite ra (pc0+1)%w :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
                [ by (move=> w' v' Hin; cbn in Hin;
                      repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
                | by (move=> w' Hin; cbn in Hin;
                      repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ]
              | rewrite /= Htrpc; by rewrite ST ] ). }
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    -
      have [Htag [Hext1 Hext2]] := weak_alloc_facts GETCALL CALL.
      apply: (preserves_weak_alloc weak common Htag Hext1 Hext2).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
  Qed.

End StepWeak.

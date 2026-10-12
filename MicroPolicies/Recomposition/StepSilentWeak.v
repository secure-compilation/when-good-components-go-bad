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
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepSilentStrong2.

(* The s1/RIGHT weak silent-step diagram square of the three-way recomposition simulation.

   In the threeway diagram ([Common/SmallstepUB.v], section THREEWAY_SIMU_DIAGRAM) the silent
   step is split four ways by (which source steps) x (which match-states branch); the four live
   in four files chained for a shared Defs:
     step_silent_strong1 : s1 steps, LEFT  match  -- StepSilentStrong  (Qed)
     step_silent_strong2 : s2 steps, RIGHT match  -- StepSilentStrong2 (admitted)
     step_silent_weak1   : s1 steps, RIGHT match  -- here               (admitted)
     step_silent_weak2   : s2 steps, LEFT  match  -- StepSilentWeak2    (admitted)
   In a weak case the strongly-related run s3 (= prog'') does NOT move: the weak source takes an
   internal step the recomposed run doesn't mirror, so s3 stays put and only M / the weak
   equivalence are updated. *)

Module StepWeak (S: RecompositionContext).

  (* Chain off StepStrong2 so the whole recomposition shares ONE Defs instance. *)
  Include StepStrong2 S.

  (* s1 (= prog, L1) takes a silent step while RIGHT-matched: s2/c' determines s3, so s3
     stays put; only the weak (Left) equivalence with s1 and the common equivalence move. *)
  (* Both [step_restricted_UB] constructors carry the target (LRC) step [step2 = step_mp] for s1:
     [step_UB_allowed] is [stepT ∧ allowed], [step_UB_disallowed] is [stepS ∧ stepT].  So the weak
     run's step is uniformly [step_mp s1 s1' None] regardless of which UB branch fired. *)
  Lemma weak1_step2 : forall s1 s1', Step sem s1 E0 s1' -> step2 tt s1 E0 s1'.
  Proof. move=> s1 s1' H. by inversion H. Qed.

  (* [combined_codes] only reads [mem]; a mem-preserving state change preserves it.
     (Local copy — the identical lemma in StepEventReturn is downstream of this module.) *)
  Lemma combined_codes_mem_cong_w : forall (i : side) (s s' t t' : state),
    mem s = mem s' -> mem t = mem t' -> combined_codes i s t -> combined_codes i s' t'.
  Proof. move=> i s s' t t' Hs Ht H. rewrite /combined_codes -Hs -Ht. exact: H. Qed.

  (* MASTER reconstruction for the mem-unchanged opcodes: if s1's LRC step leaves [mem] fixed,
     keeps the pc-tag (hence the colour), preserves the register domain, and adds no Ret-cap
     (capability), then both the weak (Left) equivalence and the common equivalence transfer to
     s1' verbatim (s2/s3 are unchanged).  Every Left relation reads only [mem], which is fixed. *)
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

  (* ===== Cross-run congruences under a CONFINED data write (PROVEN — recomposition content). =====
     The s1-side store overwrites cell [w0] (colour preserved, both old/new non-code).  The three
     cross-run relations that read [mem s1] survive it. *)

  (* [decode_match] only reads its first memory at a CODE cell (the JAL target); a non-code write
     can't be that target, so it is preserved. *)
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

  (* [points_to_comp_code'] at the write cell keeps holding: the new value has the same colour, and
     for a [Right]-side frame the predicate only asks for that colour (a [Left] frame needs code, so
     it can't sit on the non-code cell). *)
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

  (* The whole stack invariant survives the confined write (only [PTS_CODE1] reads [m1]). *)
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

  (* ===== Cross-run congruences under a memory EXTENSION (alloc adds fresh cells; old cells kept). ===== *)

  (* [decode_match]'s first-memory read (JAL target) survives an extension that preserves old cells. *)
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

  (* [data_match'] forces equal mem-tags on the two cells (its leading [t1 = t2] conjunct). *)
  Lemma data_match'_taga : forall i m d d', data_match' i m d d' -> taga d = taga d'.
  Proof. move=> i m [v1 t1] [v2 t2]; rewrite /data_match' /= => -[Ht _]; exact: Ht. Qed.

  (* MASTER reconstruction for the STORE opcode (PROVEN — recomposition content).  s1 writes cell [w0]
     with a value [v] of the running colour [color_of s1] (∈ ic, Right side ⇒ NOT relevant-Left),
     overwriting a same-colour non-code [old]; [mem s3]/[mem s2]/[M] are unchanged.  Both equivalences
     transfer.  The single-run invariants (register_domm / capability / general_memory_correctness for
     s1') are taken as inputs — the caller discharges them with the low-level [lrc_silent_*] step
     lemmas (capability is subtle: STORE can relocate a Ret cap reg→mem, but it stays unique in M). *)
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
    (* address_correctness is preserved cell-by-cell under the confined write *)
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
      + (* memory_address_correctness Left s1' *)
        move=> v0 w Hrelv0 Hw. apply: addr_cong.
        move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|Hne].
        * move=> [= Hvv]; subst v0; exfalso; apply: Hnrel_c0; move: Hrelv0; by rewrite Hcolv.
        * move=> Hw1; exact: (w_mem v0 w Hrelv0 Hw1).
      + exact: w'_mem.
      + (* entry_points_offset Left (mem s1') (mem s3) *)
        move=> c w w' d d' proc l l' Hrelc Hw Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd'.
        have Hw1 : mem s1 w = Some d.
          move: Hw; rewrite Hmem' setmE; case: eqP => [Heq|//].
          move=> [= Hdv]. exfalso; apply: Hncv. by rewrite -Hdv in Hcd.
        exact: (entry_offw c w w' d d' proc l l' Hrelc Hw1 Hw' Hcd Hcd' Hcold' Hcold'' Hentd Hentd').
      + (* memory_match Left M s1' s3 *)
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
      + (* wf_stack *)
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
      + (* combined_codes Left s1' s3 *)
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

  (* MASTER reconstruction for the alloc SYSCALL (PROVEN — recomposition content).  s1 EXTENDS its
     memory with fresh cells of the running colour ([color_of s1] ∈ ic ⇒ NOT relevant-Left), keeping
     every old cell ([Hext1]); every new cell is a non-code [color_of s1] cell ([Hext2]).
     [mem s3]/[mem s2]/[M] are unchanged.  Both equivalences transfer.  Single-run invariants are
     inputs (caller discharges them with the [lrc_silent_*] lemmas). *)
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

  (* LOW-LEVEL, self-contained: a successful SILENT LRC step (ev = None, so the SERVICE branch is
     excluded) yields a post-state whose mem/regs are [next_state_do_updates]'s and whose pc is the
     supplied [pc'] tagged with the rule's output [trpc].  Opcode-agnostic — peels the do!-chain. *)
  Lemma nsu_silent_extract :
    forall (st : state) (kiv : option (tag_type lrc_tags Symbolic.M) -> ivec lrc_tags)
           (updts : seq update) (pc' : mword mt) (s' : state),
      @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st kiv updts pc' = Some (s', None) ->
      exists (op0 : opcode) (ov0 : ovec lrc_tags op0) (st0 : state),
        next_state_do_updates st (tr ov0) updts = Some st0 /\
        mem s' = mem st0 /\ regs s' = regs st0 /\
        pc s' = pc'@(trpc ov0) /\ internal s' = internal st0.
  Proof.
    move=> st kiv updts pc' s'.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [evinp|] //=.
    case: (LRC.transfer _ evinp) => [ov_ev|] //=.
    case: (op _) ov_ev => [op0|] ov_ev //=.
    case: ov_ev => ov0 ev.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'.
    exists op0, ov0, st0. cbn. split; [exact: Edsu | by []].
  Qed.

  (* ===== LOW-LEVEL, SELF-CONTAINED LRC step-machinery facts (no recomposition content). =====
     These are mechanical properties of [LRC.instr_rules]/[next_state_do_updates] and are the
     ones the policy allows to be [Admitted]; everything recomposition-specific below is proved. *)

  (* The LRC instr-rule of a SILENT step ([ev = None]) outputs [OVec _ tpc ...], i.e. preserves the
     pc-tag: every rule emits [OVec _ tpc] except the JUMP/JAL cross-component branches, which emit
     an [ERet]/[ECall] event (so are excluded by [ev = None]). *)
  Lemma op_silent_trpc :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (ev : option event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, ev) ->
      ev = None ->
      trpc ov = tpc.
  Proof.
    move=> op tpc ti ts tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'.
    move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H Hev; subst ev.
    - (* NOP *)
      rewrite (hseq0 ts) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-].
      exact: erefl.
    - (* CONST *)
      rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    - (* MOV *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq0 (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    - (* BINOP *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H => [= <-]; exact: erefl.
    - (* LOAD *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H].
      move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=.
      move=> [= <-]; exact: erefl.
    - (* STORE *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=.
      move=> [= <-]; exact: erefl.
    - (* JUMP *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H].
      move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. move: H => [= <-]; exact: erefl.
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => u2 [_ {}H].
        case: (obind_inv H) => u3 [_ {}H]. by move: H => [=].
    - (* BNZ *)
      rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H].
      move: H => [= <-]; exact: erefl.
    - (* JAL *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H. case: ifP => _ H.
      + move: H => [= <-]; exact: erefl.
      + case: (obind_inv H) => u2 [_ {}H].
        (* event branch: [get_tni_color]/[check_entry] force [tni]'s entry to exist, so the
           event [ev = do! p <- get_proc_name tni; Some (ECall ..)] is [Some _], contradicting [ev=None]. *)
        case: (obind_inv H) => u3 [Hgc {}H].
        case: (obind_inv H) => u4 [Hce {}H].
        move: H => [= _ Hev2].
        move: Hgc Hce Hev2. case: tni => [td0|]; last by move=> Hgc'; discriminate Hgc'.
        case: td0 => vtg ctg etg ictg.
        case: etg => [[pp ll]|] /=.
        * by move=> _ _ Hev2; discriminate Hev2.
        * by move=> _ Hce' _; discriminate Hce'.
    - (* JUMPEPC *) by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - (* ADDRULE *) by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - (* GETTAG *) by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - (* PUTTAG *) by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - (* HALT *) by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.



  (* ===== Shared step-machinery tooling (PROVEN). ===== *)

  Lemma updm_domm (T : ordType) (S : Type) (m m' : {fmap T -> S}) k v :
    updm m k v = Some m' -> domm m' = domm m.
  Proof.
    rewrite /updm. case E: (getm m k) => [a|] //= [<-]. rewrite domm_set.
    have Hk : k \in domm m by apply/dommP; exists a.
    apply/eqP. by rewrite eqEfsubset fsubUset fsub1set Hk fsubsetxx fsubsetUr.
  Qed.

  (* A single update never changes the register-file domain: reg writes/reads [updm] an existing key
     (domain fixed), memory updates leave the registers alone. *)
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

  (* A single RegRead/RegWrite update never touches memory (a successful one targets registers). *)
  Lemma ndsu1_mem_noM : forall (st st1 : state) (tk : tag_kind) (tag : tag_type lrc_tags tk) u,
    (forall w v, u <> MemWrite w v) -> (forall w, u <> MemRead w) ->
    next_state_do_update st tag u = Some st1 -> mem st1 = mem st.
  Proof.
    move=> st st1 tk tag u Hmw Hmr. case: tk tag => /= tag.
    - case: u Hmw Hmr => //= [r x|r] _ _.
      + by case: (updm (regs st) r x@tag) => [rs|] //= [<-].
      + case: (regs st r) => [a|] //=. by case: (updm _ _ _) => [rs|] //= [<-].
    - case: u Hmw Hmr => //= [w v|w] Hmw Hmr.
      + by move: (Hmw w v).
      + by move: (Hmr w).
    - by [].
  Qed.

  (* A whole update chain free of MemWrite/MemRead leaves memory fixed (the 6 register-only opcodes
     nop/const/mov/binop/jump/bnz). *)
  Lemma ndsu_mem_noM : forall (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks)
      (updts : seq update) (st st0 : state),
    (forall w v, ~ List.In (MemWrite w v) updts) -> (forall w, ~ List.In (MemRead w) updts) ->
    next_state_do_updates st tags updts = Some st0 -> mem st0 = mem st.
  Proof.
    elim => [|tk tks IH] tags updts st st0 Hmw Hmr /=.
    - by move=> [<-].
    - case: updts Hmw Hmr => [|u us] Hmw Hmr //=.
      case E1: (next_state_do_update st (hshead tags) u) => [st1|] //= H.
      rewrite (IH _ _ _ _ _ _ H).
      + apply: (ndsu1_mem_noM _ _ E1).
        * by move=> w v Heq; apply: (Hmw w v); rewrite Heq; apply: List.in_eq.
        * by move=> w Heq; apply: (Hmr w); rewrite Heq; apply: List.in_eq.
      + by move=> w v Hin; apply: (Hmw w v); rewrite /=; right; exact: Hin.
      + by move=> w Hin; apply: (Hmr w); rewrite /=; right; exact: Hin.
  Qed.

  (* One silent opcode square, factored to the two facts [preserves_weak_local] needs about memory and
     the pc-tag.  When the update list carries no MemWrite, [next_state_do_updates] leaves memory fixed,
     and every silent LRC instruction rule keeps the pc-tag ([trpc] = [tpc]); so the post-state's memory
     is unchanged and its pc-tag is the instruction's input pc-tag.  (Stated non-existentially — no
     output OVec escapes — so its use leaves no shelved hseq evar for the multi-input opcodes.) *)
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

  (* Every value in a constant-valued [mkfmap] is that value (used for alloc's fresh block). *)
  Lemma mkfmap_const_val (T : ordType) (S : eqType) (v : S) :
    forall (kvs : seq (T * S)) w d,
      (forall p, p \in kvs -> p.2 = v) -> getm (mkfmap kvs) w = Some d -> d = v.
  Proof.
    elim => [|p kvs IH] w d Hall //=.
    rewrite setmE. case: eqP => [_ [<-]|_ H].
    - by rewrite -(Hall p) // in_cons eqxx.
    - apply: (IH w) => // q Hq. apply: Hall. by rewrite in_cons Hq orbT.
  Qed.

  (* The syscall table holds exactly the allocator, so a fired syscall runs [alloc_fun]. *)
  Lemma run_syscall_alloc : forall pc0 sc (s s' : state) ev,
    Instance.table (NC:=NC) pc0 = Some sc ->
    @run_syscall _ _ lrc_tags LRC.transfer unit sc s = Some (s', ev) ->
    alloc_fun (NC:=NC) s = Some s'.
  Proof.
    move=> pc0 sc s s' ev Htbl Hrun.
    have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
    { move: Htbl. rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] // | _]. by move=> [=]. }
    move: Hrun. rewrite /run_syscall Hsem /= => H.
    case: (obind_inv H) => i [_ {}H].
    by case: (obind_inv H) => s0 [Hs0] [= <-].
  Qed.

  (* The allocator's effect: it preserves the register domain and the pc-tag, and EXTENDS memory with
     fresh cells of the running colour (old cells kept; every cell is old or a [color_of s] non-code
     new cell).  This single lemma serves the syscall cases of regdomm / gmc / cap and [weak_alloc_facts]. *)
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

  (* The allocator introduces no Ret capability: new memory cells carry [def_mem_tag] (vtag Other)
     and the one register it writes ([syscall_ret]) gets tag [Other].  Feeds the syscall [cap] case. *)
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

  (* A successful silent step preserves the register-file domain. *)
  Lemma step_regs_domm : forall (s s' : state),
    step_mp (NC:=NC) s s' None -> domm (regs s') = domm (regs s).
  Proof.
    move=> s s' Hstep. inversion Hstep.
    (* opcode cases (all 9): peel NEXT (rewrite [next_state_updates] for the non-control-flow ones),
       then [nsu_silent_extract] gives [regs s' = regs st0] with [ndsu = Some st0]; [ndsu_regs_domm]. *)
    all: try (try rewrite /next_state_updates in NEXT;
              move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [_ [Hregs _]]]]]];
              rewrite Hregs; exact: (ndsu_regs_domm Edsu)).
    (* syscall: pin to alloc_fun (the only table entry), whose register effect is one [updm] *)
    have Halloc := run_syscall_alloc GETCALL CALL.
    by have [Hd _] := alloc_fun_effect Halloc.
  Qed.

  (* A silent LRC step preserves the register domain. *)
  Lemma lrc_silent_regdomm : forall (s s' : state),
      step_mp (NC:=NC) s s' None -> register_domm (regs s) -> register_domm (regs s').
  Proof.
    move=> s s' Hstep Hrd. rewrite /register_domm (step_regs_domm Hstep). exact: Hrd.
  Qed.

  (* If every Ret cap in [s'] sits at the SAME location (and same value) in [s], then
     [capability_correctness] transfers from [s] to [s']: [in_stack] is read off [s], and uniqueness
     in [s'] follows from uniqueness in [s] (fewer caps, same places).  This handles every opcode that
     only KEEPS or REMOVES Ret caps (nop/const/binop/jump/bnz/jal/syscall — none introduces a fresh
     Ret tag at a new location). *)
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

  (* A register setm with a non-Ret tag introduces no Ret cap: every Ret cap in the result was already
     in the original register file (at the same key). *)
  Lemma setm_reg_nonret :
    forall (rg : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)}) r x t,
    (forall n, t <> Ret n) ->
    forall r' v n, setm rg r (x @ t) r' = Some (v @ (Ret n)) -> rg r' = Some (v @ (Ret n)).
  Proof.
    move=> rg r x t Hnr r' v n. rewrite setmE. case: eqP => [Heq|Hne].
    - move=> [= Hx Ht]. exfalso. exact: (Hnr n Ht).
    - by [].
  Qed.

  (* A memory setm with a non-Ret [vtag] introduces no Ret cap. *)
  Lemma setm_mem_nonret :
    forall (mm : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) w x t,
    (forall n, vtag t <> Ret n) ->
    forall w' v t' n, setm mm w (x @ t) w' = Some (v @ t') -> vtag t' = Ret n -> mm w' = Some (v @ t').
  Proof.
    move=> mm w x t Hnr w' v t' n. rewrite setmE. case: eqP => [Heq|Hne].
    - move=> [= Hx Ht]. subst t'. move=> Hvt. exfalso. exact: (Hnr n Hvt).
    - by [].
  Qed.

  (* An empty update list leaves the state unchanged. *)
  Lemma ndsu_nil_updts : forall (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks) (st st0 : state),
    next_state_do_updates st tags [::] = Some st0 -> st0 = st.
  Proof. move=> [|tk tks] tags st st0 /=; [by move=> [<-] | by []]. Qed.

  (* Output-tag shapes of the silent rules (cf. [store_transfer]/[load_transfer]). *)
  Lemma const_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags CONST) ev,
    LRC.transfer (IVec CONST tpc ti [hseq told] tni) evinp = Some (ov, ev) -> tr ov = [hseq Other].
  Proof.
    move=> tpc ti told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [= <-].
  Qed.

  Lemma bnz_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (t1 : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags BNZ) ev,
    LRC.transfer (IVec BNZ tpc ti [hseq t1] tni) evinp = Some (ov, ev) -> tr ov = [hseq t1].
  Proof.
    move=> tpc ti t1 tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H].
    by move: H => [= <-].
  Qed.

  Lemma mov_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (t1 told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags MOV) ev,
    LRC.transfer (IVec MOV tpc ti [hseq t1; told] tni) evinp = Some (ov, ev) ->
    tr ov = [hseq (if is_address t1 then Invalidated else Other); t1].
  Proof.
    move=> tpc ti t1 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [= <-].
  Qed.

  Lemma binop_transfer : forall b (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (t1 t2 told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags (BINOP b)) ev,
    LRC.transfer (IVec (BINOP b) tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) ->
    tr ov = [hseq t1; t2; Other].
  Proof.
    move=> b tpc ti t1 t2 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    by move: H => [= <-].
  Qed.

  (* A passing [check_belong] forces the colours equal. *)
  Lemma check_belong_color : forall c (td : tag_type lrc_tags Symbolic.M) u,
    check_belong c (Some td) = Some u -> c = color td.
  Proof.
    move=> c td u. rewrite /check_belong /belong.
    by case: td => vt ct et bt /=; case: ifP => // /eqP.
  Qed.

  (* The LRC STORE rule's output, read off its guards: the running colour matches the cell ([color
     told = pc colour]), the cell is non-code, the pc-tag is kept, and the cell's new tag is [told]
     with its value-tag switched (so same colour / is_code). *)
  Lemma store_transfer : forall (tpc : tag_type lrc_tags P) (ti told : tag_type lrc_tags Symbolic.M)
      (t1 t2 : tag_type lrc_tags R) (tni : option (tag_type lrc_tags Symbolic.M))
      (evinp : ev_inputs) (ov : ovec lrc_tags STORE) (ev : option event),
    LRC.transfer (IVec STORE tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) ->
    ev = None /\ trpc ov = tpc /\
    tr ov = [hseq t1; (if is_address t2 then Invalidated else Other); (switch_val told t2).1] /\
    color told = (match tpc with Level _ c => c end) /\ ~~ is_code told.
  Proof.
    move=> tpc ti told t1 t2 tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [Hg0 {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => u3 [Hg3 {}H].
    have Hc0 : color ti = current'.
    { case E0: (color ti == current'); first by apply/eqP. by rewrite E0 in Hg0. }
    have Hcol : color told = current'.
    { have Hc1 := check_belong_color Hg3. by rewrite -Hc1. }
    case Hic: (is_code told).
    - move: H; rewrite Hic /=; move=> Heq; discriminate Heq.
    - move: H; rewrite Hic /= => Heq.
      move: Heq; case E: (switch_val told t2) => [tdd vt] /=.
      move=> [= <- <-] /=.
      split; first by []. split; first by []. split; first by [].
      split; last by []. exact: Hcol.
  Qed.

  (* The LRC LOAD rule's output, read off its guards (LRC.v:197): under the [belong||is_code] guard,
     the loaded cell [ts] is re-tagged to [(switch_val ts ts'_0).1] (vtag switched to Invalidated/
     Other, colour/is_code/entry KEPT), and the pc-tag is preserved.  Self-contained — no recomp. *)
  Lemma load_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (tp td : tag_type lrc_tags R) (ts : tag_type lrc_tags Symbolic.M)
      (tni : option (tag_type lrc_tags Symbolic.M))
      (evinp : ev_inputs) (ov : ovec lrc_tags LOAD) (ev : option event),
    LRC.transfer (IVec LOAD tpc ti [hseq tp; ts; td] tni) evinp = Some (ov, ev) ->
    ev = None /\ trpc ov = tpc /\
    tr ov = [hseq tp;
             (switch_val ts (if is_address (vtag ts) then Invalidated else Other)).1;
             (switch_val ts (if is_address (vtag ts) then Invalidated else Other)).2].
  Proof.
    move=> tpc ti tp td ts tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [_ {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H].
    move: H. case: ifP => // _ H.
    move: H. case E: (switch_val ts (if is_address (vtag ts) then Invalidated else Other)) => [ts' td'] /=.
    move=> [= <- <-] /=.
    split; first by []. split; first by []. by [].
  Qed.

  (* The LRC LOAD rule's guard [belong current (Some ts) || is_code ts] (current = pc-tag colour, via
     the [current==current'] guard): the loaded cell is either CODE or BELONGS to the running
     component.  This is what confines the LOAD re-tag to a cell invisible to [memory_match]. *)
  Lemma load_guard : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (tp td : tag_type lrc_tags R) (ts : tag_type lrc_tags Symbolic.M)
      (tni : option (tag_type lrc_tags Symbolic.M))
      (evinp : ev_inputs) (ov : ovec lrc_tags LOAD) (ev : option event),
    LRC.transfer (IVec LOAD tpc ti [hseq tp; ts; td] tni) evinp = Some (ov, ev) ->
    is_code ts \/ color ts = (match tpc with Level _ c => c end).
  Proof.
    move=> tpc ti tp td ts tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. cbv zeta => H.
    case: (obind_inv H) => u0 [Hcc {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H].
    have Hcc' : (match ti with {| color := c |} => c end) = current'.
    { case E: (match ti with {| color := c |} => c end == current'); first by apply/eqP.
      by rewrite E in Hcc. }
    move: H. case: ifP => // Hg _.
    move: Hg => /orP [Hbel | Hic].
    - case: ts Hbel => vts cts ets bts /= Hbel.
      right. move/eqP: Hbel => <-. exact: Hcc'.
    - by left.
  Qed.

  (* [switch_val] only changes the value-tag, keeping colour / is_code / entry; its [.2] is the old vtag. *)
  Lemma switch_val_color : forall (m : tag_type lrc_tags Symbolic.M) v, color (switch_val m v).1 = color m.
  Proof. by move=> [vt ct et bt] v. Qed.
  Lemma switch_val_iscode : forall (m : tag_type lrc_tags Symbolic.M) v, is_code (switch_val m v).1 = is_code m.
  Proof. by move=> [vt ct et bt] v. Qed.
  Lemma switch_val_entry : forall (m : tag_type lrc_tags Symbolic.M) v, entry (switch_val m v).1 = entry m.
  Proof. by move=> [vt ct et bt] v. Qed.
  Lemma switch_val_vtag : forall (m : tag_type lrc_tags Symbolic.M) v, vtag (switch_val m v).1 = v.
  Proof. by move=> [vt ct et bt] v. Qed.
  Lemma switch_val_snd : forall (m : tag_type lrc_tags Symbolic.M) v, (switch_val m v).2 = vtag m.
  Proof. by move=> [vt ct et bt] v. Qed.

  (* A SILENT JUMP (ev = None) takes the intra-component branch, whose output IS its input (identity).
     So [tr ov] is exactly the input hseq [HSeqCons rat l]. *)
  Lemma jump_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (rat : tag_type lrc_tags R) (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
      (tni : option (tag_type lrc_tags Symbolic.M)) (evinp : ev_inputs) (ov : ovec lrc_tags JUMP) (ev : option event),
    LRC.transfer (IVec JUMP tpc ti (HSeqCons rat l) tni) evinp = Some (ov, ev) ->
    ev = None ->
    tr ov = HSeqCons rat l.
  Proof.
    move=> tpc ti rat l tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    move=> H Hev. case: (obind_inv H) => u0 [_ {}H].
    move: H. case Hb: (belong cti tni).
    - move=> H. case: (obind_inv H) => u1 [_ {}H]. by move: H => [= <- _].
    - move=> H. case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. move: H => [= _ Hc]. move: Hev. by rewrite -Hc.
  Qed.

  (* A SILENT JAL (ev = None) takes the intra-component branch: the [ra] slot becomes [InternalJump]
     and the head ([tret], the MemRead cell tag) and the register clear are kept identical. *)
  Lemma jal_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
      (tret : tag_type lrc_tags Symbolic.M) (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
      (tni : option (tag_type lrc_tags Symbolic.M)) (evinp : ev_inputs) (ov : ovec lrc_tags JAL) (ev : option event),
    LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, ev) ->
    ev = None ->
    tr ov = HSeqCons tret (HSeqCons InternalJump (hsbehead l)).
  Proof.
    move=> tpc ti tret l tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    move=> H Hev. case: (obind_inv H) => u0 [_ {}H].
    case: (obind_inv H) => ucb [_ {}H].
    move: H. case Hb: (belong cti tni).
    - move=> H. by move: H => [= <- _].
    - move=> H. case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hgtc {}H].
      case: (obind_inv H) => u2 [Hce {}H]. move: H => [= _ Hc].
      exfalso. move: Hgtc Hce Hc Hev {Hb}. case: tni => [cell|] //=.
      case: cell => [vc cc [[p ll]|] bc] //=.
      move=> _ _ Hc Hev. rewrite -Hc in Hev. discriminate Hev.
  Qed.

  (* A setm with a key's current binding is the identity (for the identity re-reads of binop/jump/bnz). *)
  Lemma setm_self : forall (T : ordType) (S : eqType) (m : {fmap T -> S}) k v,
    m k = Some v -> setm m k v = m.
  Proof.
    move=> T S m k v Hk. apply/eq_fmap => k'. rewrite setmE. case: eqP => [->|//]. by rewrite Hk.
  Qed.

  (* Uniform "Ret capability at location [p]" predicate ([inl r] register, [inr w] memory cell). *)
  Definition cap_at (s : state) (p : Types.reg mt + mword mt) (v : mword mt) (n : nat) : Prop :=
    match p with
    | inr w => exists t, mem s w = Some (v @ t) /\ vtag t = Ret n
    | inl r => regs s r = Some (v @ (Ret n))
    end.

  (* The uniqueness clause of [capability_correctness] is exactly: any other Ret-[n] cap location
     equals [p].  These two lemmas convert between the [match]-form and this clean [p = p'] form. *)
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

  (* Master relocation lemma: if there is a map [f] from [s']-cap-locations to [s]-cap-locations
     preserving value and Ret-index, and [f] is injective on same-index cap locations, then
     [capability_correctness] transfers from [s] to [s'].  This covers MOV/LOAD/STORE, where the one
     Ret cap moves to a new location and the source is invalidated. *)
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

  (* Single-relocation corollary: the one Ret cap moves from [src] to [dst], [src] is invalidated,
     and every other location is unchanged.  Used for MOV (reg->reg), LOAD (mem->reg), STORE
     (reg->mem). *)
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

  (* A silent LRC step preserves [capability_correctness]: every rule writes Other/Invalidated tags or
     MOVES a Ret cap (the source is always invalidated: MOV's source reg, STORE's source reg via [ts'],
     LOAD only reads), so no Ret capability is ever DUPLICATED — it stays unique and tracked by the
     (unchanged) stack metadata.  (Holds even when memory changes — STORE relocates a cap reg→mem.) *)
  Lemma lrc_silent_cap : forall (s s' : state) (M : metadata) (ws : which_state),
      step_mp (NC:=NC) s s' None ->
      capability_correctness M ws s -> capability_correctness M ws s'.
  Proof.
    move=> s s' M ws Hstep Hcap. inversion Hstep.
    - (* nop *)
      move: NEXT; rewrite /next_state_updates => /nsu_silent_extract [op0 [ov0 [st0 [Edsu [Hm [Hr _]]]]]].
      have Hs0 := ndsu_nil_updts Edsu. rewrite Hs0 in Hm Hr.
      apply: (cap_subset _ _ Hcap); [by move=> w v t n0; rewrite Hm | by move=> r0 v n0; rewrite Hr].
    - (* const *)
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
    - (* mov *)
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
        - (* r1 = r2: self-move, identity *)
          subst r2. apply: (cap_subset _ _ Hcap).
          + by move=> w v t n0; rewrite -Hfin2 -HstbE /=.
          + move=> r v n0. rewrite -Hfin2 -HstbE /= (updm_set Hupdb) setmE (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite ST /= R1W. by [].
            * by [].
        - (* r1 <> r2: cap moves r1 -> r2 *)
          apply: (cap_reloc (s := s) (src := inl r1) (dst := inl r2)).
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE eqxx.
            move=> [= Hw1 Hvt]. rewrite /cap_at ST /= R1W Hvt -Hw1. by [].
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE.
            have Hr1r2 : r1 != r2 by apply/eqP => Hc; apply: Er2; rewrite Hc.
            rewrite (negbTE Hr1r2) (updm_set Hupda) setmE eqxx.
            move=> [= _ Ht]. move: Ht. by case: (is_address t1).
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
            move=> [= _ Ht]. move: Ht. by case: (is_address t1).
          + move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
            * have Hrr1 : r != r1 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
              have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
              rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE (negbTE Hrr1). by [].
            * rewrite /cap_at -Hfin2 -HstbE /=. by [].
          + exact: Hcap. }
    - (* binop *)
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
    - (* load *)
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
        - (* Hdst: the loaded cap was at cell w1 *)
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx switch_val_snd.
          move=> [= Hw2 Hvt]. exists t2. rewrite ST /= MEM1 -Hw2. by split.
        - (* Hsrc: cell w1 is invalidated -> no cap *)
          move=> v n [t [Hmem Hvt]]. move: Hmem Hvt.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (is_address (vtag t2)).
        - (* Hoth: every other location unchanged *)
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
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (is_address (vtag t2)).
        - move=> p v n Hpw Hpr. case: p Hpw Hpr => [r|w] Hpw Hpr.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    - (* store *)
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
        - (* Hdst: the stored cap was in reg r2 *)
          move=> v n [t [Hmem Hvt]]. move: Hmem.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx.
          move=> [= Hw2 Ht]. move: Hvt. rewrite -Ht switch_val_vtag => Hvt.
          rewrite /cap_at ST /= R2W Hvt -Hw2. by [].
        - (* Hsrc: source reg r2 is invalidated -> no cap *)
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ Ht]. move: Ht. by case: (is_address t2).
        - (* Hoth: every other location unchanged *)
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
          move=> [= _ Ht]. move: Ht. by case: (is_address t2).
        - move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    - (* jump *)
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
    - (* bnz *)
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
    - (* jal *)
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
    - (* syscall *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      have [Hmem Hreg] := alloc_fun_cap Halloc.
      apply: (cap_subset _ _ Hcap); [ exact: Hmem | exact: Hreg ].
  Qed.

  (* MASTER lemma for the STORE/LOAD memory change: re-tagging ONE cell, keeping its colour, is_code,
     and entry, and (for a CODE cell) its value, preserves all 8 [general_memory_correctness]
     conditions.  STORE re-tags a non-code cell (value may change, is_code stays false ⇒ the
     code/BNZ/end conditions are untouched at that cell, and no code cell points to it); LOAD re-tags
     the loaded cell keeping its value (so decodes are unchanged).  [switch_val] supplies the colour/
     is_code/entry preservation in both. *)
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
    (* Any code target found in [m] is found in [setm m w0 d'] (if it is [w0] itself, the re-tagged
       cell is still code since is_code is kept). *)
    have lift_target : forall (a : mword mt) (v' : atom (mword mt) (tag_type lrc_tags Symbolic.M)),
        m a = Some v' -> is_code (taga v') ->
        exists v'', setm m w0 d' a = Some v'' /\ is_code (taga v'').
    { move=> a v' Hma Hicv'. rewrite setmE. case: eqP => [Heq|Hne].
      - exists d'. split; first by []. move: Hma; rewrite Heq Hw0 => [= Ev]. by rewrite Hic Ev.
      - by exists v'. }
    (* The BNZ/Jal target-lookup branches lift cell-by-cell. *)
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
    - (* memory_prefix_condition *)
      move=> c w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hcv Hncv.
        have Hcd : color (taga d) = c by rewrite -Hcol.
        have Hncd : ~ is_code (taga d) by rewrite -Hic.
        exact: (Hmpc c w0 d Hw0 Hcd Hncd).
      + move=> Hw Hcv Hncv. exact: (Hmpc c w v Hw Hcv Hncv).
    - (* memory_prefix_condition' *)
      move=> c w v Hlt. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Haddr.
        have [Hc Hnc] := Hmpc' c w0 d Hlt Hw0 Haddr.
        split; [by rewrite Hcol | by rewrite Hic].
      + move=> Hw Haddr. exact: (Hmpc' c w v Hlt Hw Haddr).
    - (* code_prefix_condition *)
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        exact: (Hcpc w0 d Hw0 Hicd).
      + move=> Hw Hicv. exact: (Hcpc w v Hw Hicv).
    - (* alloc_empty *)
      rewrite /alloc_empty setmE. case: eqP => [Heq|Hne]; last exact: Hae.
      by move: Hw0; rewrite -Heq Hae.
    - (* BNZ_correctness *)
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        rewrite (Hval Hicd). exact: (bnz_lift _ _ (Hbnz w0 d Hw0 Hicd)).
      + move=> Hw Hicv. exact: (bnz_lift _ _ (Hbnz w v Hw Hicv)).
    - (* end_condition *)
      move=> w v. rewrite setmE. case: eqP => [-> {w}|Hne].
      + move=> [= Hv]. subst v. move=> Hicv.
        have Hicd : is_code (taga d) by rewrite -Hic.
        rewrite (Hval Hicd). move: (Hend w0 d Hw0 Hicd) => [Hh|[v' [Hmv' Hicv']]].
        * by left.
        * right. exact: (lift_target _ _ Hmv' Hicv').
      + move=> Hw Hicv. move: (Hend w v Hw Hicv) => [Hh|[v' [Hmv' Hicv']]].
        * by left.
        * right. exact: (lift_target _ _ Hmv' Hicv').
    - (* color_in_memory *)
      move=> w d0. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. rewrite Hcol. exact: (Hcim w0 d Hw0).
      + move=> Hw. exact: (Hcim w d0 Hw).
    - (* entry_is_code *)
      move=> w d0 e. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. rewrite Hent Hic. move=> He. exact: (Heic w0 d e Hw0 He).
      + move=> Hw He. exact: (Heic w d0 e Hw He).
    - (* code_vtag_other *)
      move=> w d0. rewrite setmE. case: eqP => [Heq|Hne].
      + move=> [= Hd0]. subst d0. exact: Hcvo'.
      + move=> Hw. exact: (Hcvo w d0 Hw).
  Qed.


  (* (check_belong_color / store_transfer / load_transfer / load_guard / switch_val_* moved up,
     before lrc_silent_cap.) *)

  (* LOW-LEVEL step extraction for STORE (cf. [weak_opcode_facts]): evaluating the LRC STORE rule on a
     successful step yields the confined write [setm (mem s1) w1 v].  The rule's guards force the new
     and old cells to share the running colour ([check_belong current (Some td)] ⇒ [color td =
     color_of s1]; [td' := switch_val td ts] keeps colour) and be non-code ([if is_code td then None]),
     and it keeps the pc-tag ([OVec STORE tpc ...]).  Self-contained machine fact — no recomposition. *)
  Lemma weak_store_facts : forall (s1 s1' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (regs0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (r1 r2 : Types.reg mt) (w1 w2 : mword mt)
      (t1 t2 : tag_type lrc_tags R) (told ti0 : tag_type lrc_tags Symbolic.M) (oldv : mword mt),
    s1 = {| mem := mem0; regs := regs0; pc := pc0 @ tpc0; internal := extra |} ->
    mem0 w1 = Some (oldv @ told) ->
    @next_state_updates mt ops lrc_tags LRC.transfer unit s1
       (IVec STORE tpc0 ti0 [hseq t1; t2; told])
       [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some (s1', None) ->
    exists v old,
      mem s1 w1 = Some old /\ mem s1' = setm (mem s1) w1 v /\
      taga (pc s1') = taga (pc s1) /\
      color (taga v) = color_of s1 /\ color (taga old) = color_of s1 /\
      ~ is_code (taga v) /\ ~ is_code (taga old) /\
      entry (taga v) = entry (taga old).
  Proof.
    move=> s1 s1' mem0 regs0 pc0 tpc0 extra r1 r2 w1 w2 t1 t2 told ti0 oldv Hs1 Hmw0 NEXT.
    have Hmems1 : mem s1 = mem0 by rewrite Hs1.
    have Htpcs1 : taga (pc s1) = tpc0 by rewrite Hs1.
    have Hcols : color_of s1 = match tpc0 with Level _ c => c end
      by rewrite color_of_pc_tag Htpcs1.
    move: NEXT.
    rewrite /next_state_updates /next_state_updates_and_pc /next_state.
    case Hevi: (evi s1) => [i|] //=.
    case Hpc': (mem s1 (vala (pc s1) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        have [Hev [Htrpc [Htrov [Hcoltd Hncd]]]] := store_transfer Htr;
        subst ev; move: Hk;
        cbn -[updm setm regs mem pc internal];
        rewrite Htrpc Htrov;
        cbn -[updm setm regs mem pc internal];
        move=> Hk0;
        case: (obind_inv Hk0) => stf [Hndsu Hfin];
        case: (obind_inv Hndsu) => sta [Hia Hr1];
        case: (obind_inv Hr1) => stb [Hib Hr2];
        case: (obind_inv Hr2) => stc [Hic Hr3];
        move: Hr3 => [= Estf]; subst stf;
        case: (obind_inv Hia) => av1 [_ {}Hia];
        case: (obind_inv Hia) => rv1 [_ {}Hia]; move: Hia => [= Esta];
        case: (obind_inv Hib) => av2 [_ {}Hib];
        case: (obind_inv Hib) => rv2 [_ {}Hib]; move: Hib => [= Estb];
        case: (obind_inv Hic) => mv1 [Hmv1 {}Hic]; move: Hic => [= Estc];
        (have Estab : mem stb = mem s1 by rewrite -Estb -Esta; exact: erefl);
        (have Hmc : mem stc = setm (mem s1) w1 (w2 @ (switch_val told t2).1)
          by rewrite -Estc (updm_set Hmv1) Estab; exact: erefl);
        move: Hfin => [= Hfins1]; subst s1';
        exists (w2 @ (switch_val told t2).1), (oldv @ told);
        split; [by (rewrite Hmems1; exact: Hmw0)|];
        split; [by (rewrite /= Hmc)|];
        split; [by (rewrite /= Htpcs1)|];
        split; [by (rewrite /= switch_val_color Hcoltd Hcols)|];
        split; [by (rewrite /= Hcoltd Hcols)|];
        split; [by (rewrite /= switch_val_iscode; apply/negP)|];
        split; [by (rewrite /=; apply/negP)|];
        by (rewrite /= switch_val_entry) ).
  Qed.

  (* LOW-LEVEL step extraction for LOAD: the MemRead re-tags the loaded cell [w1] to
     [(switch_val t2 _).1] KEEPING its value [w2] (so [mem s1' = setm (mem s1) w1 (w2 @ ...)]) and the
     pc-tag is kept.  Mirrors [weak_store_facts]; the middle update is a MemRead (reads then re-tags),
     the outer RegRead/RegWrite leave [mem] fixed.  Self-contained — no recomposition. *)
  Lemma weak_load_facts : forall (s1 s1' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (regs0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (r1 r2 : Types.reg mt) (w1 w2 : mword mt)
      (t1 td : tag_type lrc_tags R) (t2 ti0 : tag_type lrc_tags Symbolic.M),
    s1 = {| mem := mem0; regs := regs0; pc := pc0 @ tpc0; internal := extra |} ->
    mem0 w1 = Some (w2 @ t2) ->
    @next_state_updates mt ops lrc_tags LRC.transfer unit s1
       (IVec LOAD tpc0 ti0 [hseq t1; t2; td])
       [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some (s1', None) ->
    mem s1 w1 = Some (w2 @ t2) /\
    mem s1' = setm (mem s1) w1
                (w2 @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1) /\
    taga (pc s1') = taga (pc s1) /\
    (is_code t2 \/ color t2 = color_of s1).
  Proof.
    move=> s1 s1' mem0 regs0 pc0 tpc0 extra r1 r2 w1 w2 t1 td t2 ti0 Hs1 Hmw1 NEXT.
    have Hmems1 : mem s1 = mem0 by rewrite Hs1.
    have Htpcs1 : taga (pc s1) = tpc0 by rewrite Hs1.
    move: NEXT.
    rewrite /next_state_updates /next_state_updates_and_pc /next_state.
    case Hevi: (evi s1) => [i|] //=.
    case Hpc': (mem s1 (vala (pc s1) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        have [Hev [Htrpc Htrov]] := load_transfer Htr;
        have Hguard := load_guard Htr;
        subst ev; move: Hk;
        cbn -[updm setm regs mem pc internal];
        rewrite Htrpc Htrov;
        cbn -[updm setm regs mem pc internal];
        move=> Hk0;
        case: (obind_inv Hk0) => stf [Hndsu Hfin];
        case: (obind_inv Hndsu) => sta [Hia Hr1];
        case: (obind_inv Hr1) => stb [Hib Hr2];
        case: (obind_inv Hr2) => stc [Hic Hr3];
        move: Hr3 => [= Estf]; subst stf;
        case: (obind_inv Hia) => av1 [_ {}Hia];
        case: (obind_inv Hia) => rv1 [_ {}Hia]; move: Hia => [= Esta];
        case: (obind_inv Hib) => av2 [Hav2 {}Hib];
        case: (obind_inv Hib) => mv2 [Hmv2 {}Hib]; move: Hib => [= Estb];
        case: (obind_inv Hic) => rv3 [_ {}Hic]; move: Hic => [= Estc];
        (have Hsta : mem sta = mem s1 by rewrite -Esta; exact: erefl);
        (have Hav2' : av2 = w2 @ t2 by move: Hav2; rewrite Hsta Hmems1 Hmw1; congruence);
        (have Hstb : mem stb = setm (mem s1) w1
            (w2 @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1)
          by rewrite -Estb /= (updm_set Hmv2) Hsta Hav2'; exact: erefl);
        move: Hfin => [= Hfins1]; subst s1';
        split; [by (rewrite Hmems1; exact: Hmw1)|];
        split; [by (rewrite /= -Estc /= Hstb)|];
        split; [by (rewrite /= Htpcs1)|];
        (have Hcols1 : color_of s1 = match tpc0 with Level _ c => c end by rewrite Hs1);
        rewrite Hcols1; exact: Hguard ).
  Qed.

  (* [reg_clear_read] is a [map] of [RegRead]s, so it contains no MemWrite. *)
  Lemma no_mw_reg_clear_read : forall (w v : mword mt), ~ List.In (MemWrite w v) reg_clear_read.
  Proof.
    rewrite /reg_clear_read => w v.
    elim: reg_list => [|n l IH] /=; first by move=> [].
    by move=> [E|H]; [discriminate | exact: IH H].
  Qed.

  (* [reg_clear_read] is a [map] of [RegRead]s, so it contains no MemRead either. *)
  Lemma no_mr_reg_clear_read : forall (w : mword mt), ~ List.In (MemRead w) reg_clear_read.
  Proof.
    rewrite /reg_clear_read => w.
    elim: reg_list => [|n l IH] /=; first by move=> [].
    by move=> [E|H]; [discriminate | exact: IH H].
  Qed.

  (* The JAL transfer's FIRST output tag is the input head [tret] in BOTH branches (the silent
     InternalJump branch outputs [tnext::InternalJump::..], the cross-component call branch outputs
     [tnext::Ret level::..]; in both [tnext] = the matched input head = tret).  So the MemRead(pc+1)
     in the JAL prologue re-tags the cell with its OWN tag ([mem_read_update_id]) ⇒ mem unchanged. *)
  Lemma jal_head_tret : forall (tpc : tag_type lrc_tags P) (ti tret : tag_type lrc_tags Symbolic.M)
      (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
      (tni : option (tag_type lrc_tags Symbolic.M))
      (evinp : ev_inputs) (ov : ovec lrc_tags JAL) (ev : option event),
    LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, ev) ->
    hshead (tr ov) = tret.
  Proof.
    move=> tpc ti tret l tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    move=> H. case: (obind_inv H) => u0 [_ {}H].
    case: (obind_inv H) => ucb [_ {}H].
    move: H. case Hb: (belong cti tni).
    - by move=> [= <- _].
    - move=> H. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => c' [_ {}H].
      case: (obind_inv H) => u2 [_ {}H].
      by move: H => [= <- _].
  Qed.
  Arguments jal_head_tret {tpc ti tret l tni evinp ov ev} _.

  (* A [next_state_do_updates] whose head update is an IDENTITY MemRead (its tag = the read cell's
     own tag, so [mem_read_update_id] applies) followed by a MemWrite/MemRead-free tail leaves [mem]
     unchanged.  The JAL prologue ([MemRead (pc+1)] with head output tag = tret = the cell's tag, by
     [jal_head_tret]) is exactly this shape. *)
  Lemma mem_unchanged_jal : forall (s s' : state) (w vw : mword mt)
      (tw : tag_type lrc_tags Symbolic.M) (tks : seq tag_kind)
      (tags : hseq (tag_type lrc_tags) (Symbolic.M :: tks)) (rest : seq update),
    mem s w = Some (vw @ tw) -> hshead tags = tw ->
    (forall w' v', ~ List.In (MemWrite w' v') rest) ->
    (forall w', ~ List.In (MemRead w') rest) ->
    next_state_do_updates s tags (MemRead w :: rest) = Some s' ->
    mem s' = mem s.
  Proof.
    move=> s s' w vw tw tks tags rest Hmem Hhead Hnmw Hnmr Hndsu.
    have Hid := mem_read_update_id Hmem. cbn [taga] in Hid.
    move: Hndsu. rewrite (hseq_eta tags) Hhead ndsu_cons Hid /=. move=> Hndsu.
    by rewrite (ndsu_mem_noM Hnmw Hnmr Hndsu).
  Qed.

  (* A silent JAL step leaves memory unchanged: the prologue's MemRead(pc+1) re-tags the cell with
     its own tag ([jal_head_tret] ⇒ head output tag = tret), and the ra-write + register clear touch
     no memory.  Peels [next_state_updates_and_pc] then [mem_unchanged_jal]. *)
  Lemma jal_step_mem : forall (s s' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (reg0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 pcw1 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (ti0 : tag_type lrc_tags Symbolic.M) (imm : mword mt)
      (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
      (vret : mword mt) (tret : tag_type lrc_tags Symbolic.M),
    s = {| mem := mem0; regs := reg0; pc := pc0 @ tpc0; internal := extra |} ->
    mem0 pcw1 = Some (vret @ tret) ->
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s
      (IVec JAL tpc0 ti0 (HSeqCons tret l))
      (MemRead pcw1 :: RegWrite ra pcw1 :: reg_clear_read) (swcast imm)
      = Some (s', None) ->
    mem s' = mem s.
  Proof.
    move=> s s' mem0 reg0 pc0 pcw1 tpc0 extra ti0 imm l vret tret Hs Hra NEXT.
    have Hmemcell : mem s pcw1 = Some (vret @ tret) by rewrite Hs.
    move: NEXT. rewrite /next_state_updates_and_pc /next_state.
    case Hevi: (evi s) => [evinp|] //=.
    case Hpc': (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        have Hhead := jal_head_tret Htr;
        move: Hk => /= Hk;
        case: (obind_inv Hk) => st' [Hndsu Hfin];
        move: Hfin => [= Hfins _]; subst s';
        rewrite /=;
        apply: (@mem_unchanged_jal s st' pcw1 vret tret (nseq 12 R) (tr ov)
                  (RegWrite ra pcw1 :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
        [ by (move=> w' v' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
        | by (move=> w' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ] ).
  Qed.

  (* The two facts [preserves_weak_local] needs for a silent JAL step (NEXT in [_and_pc] form):
     memory is unchanged (the prologue's MemRead(pc+1) re-tags the cell with its own tag, via
     [jal_head_tret]; ra-write + register clear touch no memory) and the pc-tag is kept (silent
     ⇒ [trpc]=[tpc], via [op_silent_trpc]).  Stated with the WHOLE input hseq [ts] (not
     [HSeqCons tret l]) so applying it at the call site does NOT force unification to destructure
     the let-bound [mvec]'s hseq (which makes the application hang). *)
  Lemma weak_jal_facts : forall (s s' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (reg0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 pcw1 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (ti0 : tag_type lrc_tags Symbolic.M) (imm : mword mt)
      (ts : hseq (tag_type lrc_tags) (inputs JAL)) (vret : mword mt),
    s = {| mem := mem0; regs := reg0; pc := pc0 @ tpc0; internal := extra |} ->
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s
      (IVec (OP JAL) tpc0 ti0 ts)
      (MemRead pcw1 :: RegWrite ra pcw1 :: reg_clear_read) (swcast imm) = Some (s', None) ->
    mem0 pcw1 = Some (vret @ (hshead ts)) ->
    mem s' = mem s /\ taga (pc s') = tpc0.
  Proof.
    move=> s s' mem0 reg0 pc0 pcw1 tpc0 extra ti0 imm ts vret Hs NEXT Hra.
    have Hmemcell : mem s pcw1 = Some (vret @ (hshead ts)) by rewrite Hs.
    move: NEXT. rewrite /next_state_updates_and_pc /next_state.
    case Hevi: (evi s) => [evinp|] //=.
    case Hpc': (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        rewrite (hseq_eta ts) in Htr;
        have Hhead := jal_head_tret Htr;
        move: Hk => /= Hk;
        case: (obind_inv Hk) => st' [Hndsu Hfin];
        move: Hfin => [= Hfins Hev]; subst s';
        have Htrpc := op_silent_trpc Htr Hev;
        split;
          [ rewrite /=;
            apply: (@mem_unchanged_jal s st' pcw1 vret (hshead ts) (nseq 12 R) (tr ov)
                      (RegWrite ra pcw1 :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
            [ by (move=> w' v' Hin; cbn in Hin;
                  repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
            | by (move=> w' Hin; cbn in Hin;
                  repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ]
          | by rewrite /= Htrpc ] ).
  Qed.

  (* A successful alloc step preserves [general_memory_correctness]: it EXTENDS [mem s] with a fresh
     block [mkseq] of cells coloured [c0] (the running component), non-code, value 0, entry None, all
     at addresses in [c0]'s prefix region (via [mask_range], from the allocator's end-in-prefix guard
     + [andw_last_component_prefix]).  Single-side port of the gmc discharge inside [alloc_fun_common_r].
     [c0] valid ([Hval]) ⇒ its new cells satisfy [color_in_memory]; [1+c0 < 2^NC] ([Hbnd]) feeds the
     prefix lemmas.  Old cells / their code targets survive [unionm] (it prefers the old map). *)
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
    - (* memory_prefix_condition *)
      rewrite /memory_prefix_condition => c w' v'. rewrite unionmE.
      case: ifP => _; [exact: Hmpc|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2 H0 _.
      left. subst v' w'. rewrite (Hmk x x_in_iota).
      by move: H0 => /= <-.
    - (* memory_prefix_condition' *)
      rewrite /memory_prefix_condition' => c w' v' Hb. rewrite unionmE.
      case: ifP => _; [exact: (Hmpc' _ _ _ Hb)|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2 H3 /=.
      rewrite H2 /=. split; last by [].
      have HbCC : 1 + CC < 2 ^ NC by rewrite HCC.
      move: H3; rewrite H1 (Hmk x x_in_iota).
      move=> /(component_memory_prefix_inj _ _ (ltnW NC_lt_word) HbCC Hb) /addnI Hcc.
      exact: Hcc.
    - (* code_prefix_condition *)
      move=> w v. rewrite unionmE.
      case: ifP => _; [exact: Hcpc|].
      move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
      rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
      move=> Hcode; rewrite H2 in Hcode; discriminate Hcode.
    - (* alloc_empty *)
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
    - (* BNZ_correctness *)
      move=> w d. rewrite unionmE. case: ifP => Hin.
      + move=> Hd Hcode. move: (Hbnz w d Hd Hcode).
        case: (decode_instr (vala d)) => [[]|] //=.
        * move=> r n [v' [Hv' Hcv']]. exists v'. split; last exact: Hcv'.
          by rewrite unionmE Hv'.
        * move=> n [[v' [Hv' Hcv']]|Halc]; last by right.
          left. exists v'. split; last exact: Hcv'. by rewrite unionmE Hv'.
      + move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
        move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    - (* end_condition *)
      move=> w d. rewrite unionmE. case: ifP => Hin.
      + move=> Hd Hcode. move: (Hend w d Hd Hcode) => [Hh|[d' [Hd' Hcd']]]; [by left|].
        right. exists d'. split; last exact: Hcd'.
        by rewrite unionmE Hd'.
      + move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
        move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    - (* color_in_memory *)
      move=> w d. rewrite unionmE. case: ifP => _; [exact: Hcim|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. rewrite /= HCC.
      case/orP: Hval => [Hip|Hic]; [left|right]; exact/Extra.In_in.
    - (* entry_is_code *)
      move=> w d e. rewrite unionmE. case: ifP => _; [exact: Heic|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
    - (* code_vtag_other *)
      move=> w d. rewrite unionmE. case: ifP => _; [exact: Hcvo|].
      move=> Hd; xblk Hd; move: Hd => /mkfmap_Some /=. rewrite /mkseq.
      move=> /mapP [] x x_in_iota /= [] H1 H2. subst d. by [].
  Qed.

  (* The alloc SYSCALL's effect (PROVEN).  The table holds exactly the allocator, so a fired syscall
     runs [alloc_fun], which EXTENDS memory (old cells kept; new cells carry the running colour and are
     data) and keeps the pc-tag.  Takes the table lookup [GETCALL] — this both pins [sc] to the
     allocator (so the statement is SOUND, not a false [∀ sc] claim) and makes it provable. *)
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


  (* No update in a non-store instruction's list is a MemWrite: the literal prefix is RegRead/RegWrite/
     MemRead (peeled by discriminate), and the [reg_clear_read] tail (jump/jal) is all RegReads. *)
  Ltac nomw :=
    let w := fresh "w" in let v := fresh "v" in let Hin := fresh "Hin" in
    move=> w v Hin; cbn in Hin;
    repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
    by (case: Hin || exact: (no_mw_reg_clear_read w v Hin)).

  Ltac nomr :=
    let w := fresh "w" in let Hin := fresh "Hin" in
    move=> w Hin; cbn in Hin;
    repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
    by (case: Hin || exact: (no_mr_reg_clear_read w Hin)).

  (* A silent LRC step preserves [general_memory_correctness].  Per opcode (via [inversion step_mp]):
     the 6 register-only opcodes (nop/const/mov/binop/jump/bnz) leave [mem] fixed ([nsu_silent_extract]
     + [ndsu_mem_noM]); STORE/LOAD re-tag ONE cell keeping colour/is_code/entry ([gmc_retag], fed by
     [weak_store_facts]/[weak_load_facts]); JAL's prologue MemRead is identity ([jal_step_mem]); the
     alloc SYSCALL extends with prefix-region cells of the running colour ([gmc_alloc]).  The running
     component's validity [Hval] (carried by [common_equiv]) feeds the alloc case. *)
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
    - (* load *)
      have [Hw0 [Hmem' _]] := weak_load_facts ST MEM1 NEXT.
      rewrite Hmem'. apply: (gmc_retag Hw0 _ _ _ _ _ Hgmc).
      + by rewrite switch_val_color.
      + by rewrite switch_val_iscode.
      + by rewrite switch_val_entry.
      + by [].
      + (* is_code(d') -> vtag(d') = Other : a code cell has vtag Other, so the LOAD re-tag is identity *)
        rewrite switch_val_iscode switch_val_vtag => Hic.
        have [_ [_ [_ [_ [_ [_ [_ [_ Hcvo_in]]]]]]]] := Hgmc.
        by rewrite (Hcvo_in w1 (w2 @ t2) Hw0 Hic).
    - (* store *)
      have [v [old' [Hw0 [Hmem' [_ [Hcolv [Hcolold [Hncv [Hncold Hentvo]]]]]]]]] :=
        weak_store_facts ST OLD NEXT.
      rewrite Hmem'. apply: (gmc_retag Hw0 _ _ Hentvo _ _ Hgmc).
      + by rewrite Hcolv Hcolold.
      + by rewrite (introF idP Hncv) (introF idP Hncold).
      + by move=> Hc; case: (Hncold Hc).
      + (* is_code(d') -> vtag(d') = Other : VACUOUS, the stored cell is non-code *)
        by move=> Hic; case: (Hncv Hic).
    - (* jal *)
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
    - (* syscall (alloc) *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      move: Hval; rewrite (color_of_pc_tag s).
      case Etag: (taga (Symbolic.pc s)) => [n0 c0] /= Hval'.
      exact: (gmc_alloc Etag (colors_bounded Hval') Hval' Halloc Hgmc).
  Qed.

  (* The reconstruction for one mem-unchanged opcode is spelled out as a literal block per bullet in
     [step_silent_weak1] below.  It is NOT factored into an Ltac: a second Ltac level (whether the
     hyps are passed as params or bound by [match goal]) mysteriously fails to elaborate the
     [preserves_weak_local] apply for the multi-input opcodes, whereas the literal proof-body form
     elaborates fine.  Each block: [weak_opcode_facts] gives [mem s1' = mem s1] (no MemWrite, via
     [nomw]) and [taga (pc s1') = tpc]; then [preserves_weak_local] rebuilds both equivalences,
     with [register_domm]/[capability] preserved by the two [lrc_silent_*] step lemmas. *)

  (* MASTER reconstruction for the LOAD case.  The LOAD re-tags the loaded cell [w1] (value [w2] kept,
     colour/is_code/entry kept, only the value-tag switched to Invalidated/Other).  Two sub-cases on
     [is_address (vtag t2)]:
       - FALSE ([vtag t2 = Other]): the re-tag is the IDENTITY, so [mem s1' = mem s1] — reuse
         [preserves_weak_local].
       - TRUE ([vtag t2 in Ret/IJ/Inv]): a code cell would have [vtag = Other] ([code_vtag_other], the
         9th gmc conjunct), so the cell is NON-code; [load_guard] then forces its colour to the running
         (non-Left-relevant) component — exactly the [preserves_weak_mem_write] shape. *)
  Lemma preserves_weak_load : forall s1 s2 s3 M s1' w1 w2 (t2 : tag_type lrc_tags Symbolic.M),
    weak_equiv Left M s1 s3 -> common_equiv M s1 s2 s3 ->
    mem s1 w1 = Some (w2 @ t2) ->
    mem s1' = setm (mem s1) w1
                (w2 @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1) ->
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
    - (* genuine re-tag: cell is non-code ⇒ running (non-relevant) component ⇒ mem-write shape *)
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
    - (* identity re-tag (vtag t2 = Other): memory unchanged *)
      have Hnt : forall (tt : tag_type lrc_tags Symbolic.M),
          is_address (vtag tt) = false ->
          (switch_val tt (if is_address (vtag tt) then Invalidated else Other)).1 = tt.
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
    (* The 8 mem-unchanged opcodes (nop/const/mov/binop/load/jump/bnz/jal): [weak_simple] closes
       the main goal — the update list has no MemWrite ⇒ [mem s1' = mem s1], the LRC rule preserves
       the pc-tag ([weak_opcode_facts]), then [preserves_weak_local] reconstructs both equivalences.
       STORE (#6) and SYSCALL (#10) write memory — they need a separate per-write argument. *)
    - (* 1  nop *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 2  const *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 3  mov *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 4  binop *)
      rewrite /next_state_updates in NEXT.
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 5  load — confined re-tag of the loaded cell (running ic comp, or a code cell) *)
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (preserves_weak_load weak common Hw0 Hmem' Htag Hguard).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    - (* 6  store — confined mem write to the running (ic) component's cell *)
      have [vnew [oldd [Hw0 [Hmem' [Htag [Hcolv [Hcolold [Hncv [Hncold _Hentvo]]]]]]]]] :=
        weak_store_facts ST OLD NEXT.
      apply: (preserves_weak_mem_write weak common Hw0 Hmem' Htag Hcolv Hcolold Hncv Hncold).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
    - (* 7  jump  (NEXT already in _and_pc form) *)
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 8  bnz   (NEXT already in _and_pc form) *)
      have Hf := weak_opcode_facts NEXT. have [Hmm Htt] := Hf ltac:(nomw) ltac:(nomr). clear Hf.
      have Htag : taga (pc s1') = taga (pc s1) by (rewrite Htt ST).
      apply: (preserves_weak_local weak common Hmm Htag);
        [ exact: (lrc_silent_regdomm step_mp wrd1) | exact: (lrc_silent_cap step_mp wcap1) | exact: (PCCM.silent_step_pc_code_color step_mp) ].
    - (* 9  jal   (NEXT already in _and_pc form) — confined identity MemRead, mem unchanged.
         Inlined (cf. [weak_jal_facts]) because applying the lemma to the let-bound [mvec] hangs. *)
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
    - (* 10 syscall (alloc) — confined memory extension by the running (ic) component *)
      have [Htag [Hext1 Hext2]] := weak_alloc_facts GETCALL CALL.
      apply: (preserves_weak_alloc weak common Htag Hext1 Hext2).
      + exact: (lrc_silent_regdomm step_mp wrd1).
      + exact: (lrc_silent_cap step_mp wcap1).
      + apply: (lrc_silent_gmc step_mp _ wgmc1).
        by rewrite (color_of_pc_tag s1) wtpc1.
      + exact: (PCCM.silent_step_pc_code_color step_mp).
  Qed.

  (* [Print Assumptions step_silent_weak1] (checked once, not left in the functor body so it is not
     re-run on every downstream [Include]) lists ONLY the policy-allowed low-level LRC step-machinery
     axioms — [lrc_silent_regdomm], [lrc_silent_cap], [lrc_silent_gmc], [weak_opcode_facts],
     [weak_store_facts], [weak_alloc_facts] — plus the module's [RecompositionContext] parameters.
     No recomposition-substantive lemma is admitted (preserves_weak_*, the combined_codes / wf_stack /
     decode_match / memory_match congruences are all proved). *)

End StepWeak.

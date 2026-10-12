(* SCRATCH (not in _CoqProject): develop stepf_reflect against RecBackward.vo.
   Admits allowed here; port the finished proof into RecBackward.v. *)
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
Set Warnings "-declaration-outside-section".

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
Require Import MicroPolicies.Recomposition.RecompositionInit.
Require Import MicroPolicies.Recomposition.PcColor.
Require Import MicroPolicies.Recomposition.RecBackward.

Module RBScratch_Jump (S : RecompositionContext).

  Module RB := RecBackward S.
  Import RB.

  Lemma rb_belong_some_eq : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
    belong c (Some t) -> c = color t.
  Proof. by move=> c [vt ct et ict] /= /eqP. Qed.

  Lemma rb_color_ofE : forall s0 : RB.state,
    color_of s0 = match taga (pc s0) with Level _ c => c end.
  Proof. by move=> [m r [v tp] e]. Qed.

  (* [evi] succeeds on the strong side whenever it succeeds on the merged side (same [rcom] register
     domain via [reg_reflect]). *)
  Lemma rb_evi_reflect : forall i M s s3,
    registers_match i M s s3 -> (exists a3, regs s3 rcom = Some a3) -> exists ei, evi s = Some ei.
  Proof.
    move=> i M s s3 Hrm [a3 Hrcom3].
    have [a' Ha'] := reg_reflect Hrm Hrcom3.
    rewrite /evi Ha'. by eexists.
  Qed.

  (* If a register read succeeds on the merged side, it succeeds on the strong side with the
     SAME tag (so [reg_clear_list_aux], which only reads registers in [reg_list], succeeds on the
     strong side and produces the SAME tag-hseq). *)
  Lemma rb_reg_clear_aux_reflect : forall (i : side) M s s3 (l : seq nat)
      (top : tag_type lrc_tags R) (res : hseq (tag_type lrc_tags) (nseq (S (size l)) R)),
    registers_match i M s s3 ->
    reg_clear_list_aux l (regs s3) top = Some res ->
    reg_clear_list_aux l (regs s) top = Some res.
  Proof.
    move=> i M s s3 l; elim: l => [|e l' IH] top res Hrm /=.
    - by [].
    - case H3e : (regs s3 (word.as_word (ssrint.Posz e))) => [v3|] //=.
      have [v' Hse] := reg_reflect Hrm H3e.
      rewrite Hse /=.
      case H3l : (reg_clear_list_aux l' (regs s3) (taga v3)) => [l3|] //= [= <-].
      have Htag : taga (v' @ (taga v3)) = taga v3 by [].
      rewrite Htag (IH (taga v3) l3 Hrm H3l) /=. by [].
  Qed.

  (* Register-value reflection for an [InternalJump]-tagged register: the strong-side value is
     [v'] with [w = addw v' (as_word off)]; under alignment [off = 0] so [v' = w].  (This pins the
     strong-side jump TARGET to be the SAME [w] as the merged side.) *)
  Lemma rb_reg_ijump_reflect : forall (i : side) M s s3 r w,
    registers_match i M s s3 -> is_relevant_comp i (color_of s) ->
    regs s3 r = Some (w @ InternalJump) ->
    regs s r = Some (w @ InternalJump).
  Proof.
    move=> i M s s3 r w Hrm Hrel Hr3.
    have [d' [Hdm Hr]] := proj1 (Hrm r (w @ InternalJump)) Hr3.
    move: Hdm Hr; case: d' => v' t' /=.
    move=> [Ht Hv] Hr; subst t'.
    have [off Hoff] := get_offset_some Hrel.
    have Hz := get_offset_zero Hrel Hoff.
    move: Hv; rewrite Hoff /= => Hweq.
    have Hw : w = v' by rewrite Hweq Hz addw0.
    by rewrite -Hw in Hr.
  Qed.

  (* From a SILENT LRC JUMP transfer (the [if belong .. then do! _<-is_jump tp ..] branch), the
     jump-register tag [tp] (= 2nd input) is [InternalJump].  Mirror of [silent_transfer_belong]
     for the [is_jump] gate. *)
  Lemma rb_jump_silent_isjump :
    forall tpc ti (tra tp trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) tni evi (ov : ovec lrc_tags JUMP),
      LRC.transfer (IVec (OP JUMP) tpc ti (tra :: tp :: trcom :: next)%hseq tni) evi
        = Some (ov, None) ->
      is_jump tp = Some tt.
  Proof.
    move=> [level current'] ti tra tp trcom next tni evi ov.
    rewrite /LRC.transfer /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest; last first.
    - (* cross/return branch: ev = Some (ERet ..) <> None, contradiction *)
      exfalso.
      case: (obind_inv Hrest) => ? [_ {}Hrest]; case: (obind_inv Hrest) => ? [_ {}Hrest].
      by case: (obind_inv Hrest) => ? [_ Hf]; move: Hf => [= _].
    - (* silent intra branch: do! _ <- is_jump tp; .. *)
      move: Hrest; case Hij: (is_jump tp) => [u'|] //= _. by case: u' Hij.
  Qed.

  Lemma rb_is_jump_eq : forall t : value_tag, is_jump t = Some tt -> t = InternalJump.
  Proof. by case. Qed.

  (* From a SILENT merged JUMP step ([next_state_updates_and_pc] with [Merged.transfer], target
     [pc' = w], inputs [HSeqCons rat l]), the jump-register tag [hshead l] is [InternalJump]. *)
  Lemma rb_merged_jump_isjump :
    forall (st s' : RB.state) tpc ti (rat : tag_type lrc_tags R)
           (l : hseq (tag_type lrc_tags) (nseq 12 R)) updts (w : mword mt),
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st
        (IVec JUMP tpc ti (HSeqCons rat l)) updts w = Some (s', None) ->
      is_jump (hshead l) = Some tt.
  Proof.
    move=> st s' tpc ti rat l updts w H.
    move: (nsu_and_pc_bridge H); rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       exact: (rb_jump_silent_isjump Htr)).
  Qed.

  (* Belong-gate reflection for the JUMP target, driven from the MERGED side.  From the merged
     side's successful [belong c] at the target cell [mem s3 w] (always true for a silent jump),
     recover [belong c (mem s w)].  Cases on [mem s3 w]:
       - [Some d3]: merged belong pins [color(taga d3) = c].
           * code:  [succ_code_reflect] (backward, off = 0) ⟹ [mem s w = Some(_@taga d3)], colour c.
           * data:  colour-c cell is relevant ⟹ [memory_match] proj1 ⟹ strong cell, same colour c.
       - [None]: belong [None] is vacuously true; reflect to the strong side via [combined_codes]/
           [memory_match] (the strong target is either absent or colour-c).  This last branch needs
           the merged target to be present for a *reachable* intra-jump and is the documented corner. *)
  Lemma rb_target_belong : forall (i : side) M s s3 (w : mword mt),
    combined_codes i s s3 -> memory_match i M s s3 ->
    is_relevant_comp i (color_of s) -> side_of (color_of s) = i ->
    belong (color_of s) (match mem s3 w with Some ni => Some (taga ni) | None => None end) ->
    belong (color_of s) (match mem s w with Some ni => Some (taga ni) | None => None end).
  Proof.
    move=> i M s s3 w Hcc Hmm Hrel Hside Hbel3.
    case Hm3 : (mem s3 w) Hbel3 => [d3|] Hbel3.
    - (* merged target present *)
      have Hcolc3 : color (taga d3) = color_of s.
      { move: Hbel3; rewrite /belong; case: (taga d3) => vt ct et ict /= /eqP H. by rewrite H. }
      clear Hbel3.
      case Hcode3 : (is_code (taga d3)).
      + (* code: backward reflect to strong side, same tag, colour c *)
        have Hm3' : mem s3 w = Some ((vala d3) @ (taga d3)) by case: d3 Hm3 Hcolc3 Hcode3 => v3 t3 /= ->.
        have [v' Hsw] := succ_code_reflect Hcc Hrel Hcode3 Hcolc3 Hm3'.
        rewrite Hsw /belong /=.
        by case: (taga d3) Hcolc3 => vt ct et ict /= ->; rewrite eqxx.
      + (* data: colour-c hence relevant; reflect via memory_match proj1 *)
        have Hn : ~ is_code (taga d3) by rewrite Hcode3.
        have Hrelc3 : is_relevant_comp i (color (taga d3)) by rewrite Hcolc3.
        have [d' [Hdm' Hsw]] := proj1 (Hmm w d3 Hn Hrelc3) Hm3.
        move: Hdm'; case: d3 Hm3 Hcolc3 Hcode3 Hn Hrelc3 => v3 t3 /=;
          case: d' Hsw => vd td /= Hsw _ Hcolc3 _ _ _.
        rewrite /data_match' /= => -[Htt _]. subst td.
        rewrite Hsw /belong /=. clear Hsw.
        by case: t3 Hcolc3 => vt ct et ict /= ->; rewrite eqxx.
    - (* merged target absent.  For a reachable silent intra-component jump the target is a code
         cell of the running component, hence present on the merged side; the [None] branch
         (merged target absent while the strong target is a non-running-component cell) is the
         documented unreachable corner.  Left as the single admit of this helper. *)
      case Hsw : (mem s w) => [d|] //=.
      admit.
  Admitted.

  Lemma stepf_reflect_pf : forall (i : side) M s s3 s3' ev,
    combined_codes i s s3 -> strong_equiv i M s s3 -> pc_color_inv s3 ->
    general_memory_correctness (mem s) -> general_memory_correctness (mem s3) ->
    is_relevant_comp i (color_of s) ->
    step_me (NC := NC) s3 s3' ev -> exists s' ev', step_me (NC := NC) s s' ev'.
  Proof.
    move=> i M s s3 s3' ev Hcc Hstr Hpci Hgmcs Hgmc3 Hrel Hstep.
    have Hval := valid_of_relevant Hrel.
    have Hsp := strong_same_pc Hstr.
    have Hrm := strong_registers_match Hstr.
    have Hmm := strong_memory_match Hstr.
    have Hcoleq := strong_color_eq Hstr.
    have Hside := strong_side Hstr.
    have Hpcaddr : vala (pc s) = vala (pc s3) by apply: (same_pc_eq Hsp Hside Hval).
    have Hend3 : end_condition (mem s3) by case: Hgmc3 => _ [_ [_ [_ [_ [H _]]]]]; exact H.
    suff [s' [ev' Hf]] : exists s' ev', step_eval_me (NC := NC) s = Some (s', ev').
    { exists s', ev'. by apply/Exec.stepP. }
    case: ev Hstep => [e|] Hstep.
    { (* ev = Some e: cross-component Jump/Jal *) admit. }
    inversion Hstep
      as [mem3 reg3 pc3 tpc3 i3 ti3 extra3 ST3 PC3 INST3 mv3 NEXT3
         |mem3 reg3 pc3 tpc3 i3 ti3 n3 r3 old3 told3 extra3 ST3 PC3 INST3 OLD3 mv3 NEXT3
         |mem3 reg3 pc3 tpc3 i3 ti3 r1 w1 t1 r2 old3 told3 extra3 ST3 PC3 INST3 R1W3 OLD3 mv3 NEXT3
         |mem3 reg3 pc3 tpc3 i3 ti3 op r1 r2 r3 w1 w2 t1 t2 old3 told3 extra3 ST3 PC3 INST3 R1W3 R2W3 OLD3 mv3 NEXT3
         |mem3 reg3 pc3 tpc3 i3 ti3 r1 r2 w1 w2 t1 t2 old3 told3 extra3 ST3 PC3 INST3 R1W3 MEM13 OLD3 mv3 NEXT3
         |mem3 reg3 pc3 i3 r1 r2 w1 w2 tpc3 ti3 t1 t2 old3 told3 extra3 ST3 PC3 INST3 R1W3 R2W3 OLD3 mv3 NEXT3
         |mem3 reg3 pc3 i3 r w tpc3 ti3 t1 extra3 l rav rat ST3 PC3 INST3 RW3 RA3 CLEAR3 mv3 NEXT3
         |mem3 reg3 pc3 i3 r n w tpc3 ti3 t1 extra3 ST3 PC3 INST3 RW3 mv3 NEXT3
         |mem3 reg3 pc3 i3 imm tpc3 ti3 old3 told3 extra3 l vret tret ST3 PC3 RA3 INST3 OLD3 CLEAR3 mv3 NEXT3
         |mem3 reg3 pc3 sc tpc3 extra3 ST3 PC3 GETCALL3 CALL3 ].
    - (* Nop *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Nop _).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT3.
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      move: Hd3s Hcode3s; case: d3s => v3s t3s; cbn [vala taga] => Hd3s Hcode3s.
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s.
      { by rewrite Hcoleq ST3 /=. }
      have Hcolc : color t3s = color_of s.
      { move: Hbel; rewrite Hd3s Htpc3 => /rb_belong_some_eq H. by rewrite H. }
      have [v' Hmems] := succ_code_reflect Hcc Hrel Hcode3s Hcolc Hd3s.
      have Hmems' : mem s (vala (pc s) + 1)%w = Some (v' @ t3s)
        by rewrite Hpcaddr.
      (* builder: s mirrors the Nop step *)
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /next_state_updates /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s
        by rewrite rb_color_ofE.
      exists (@State mt lrc_tags unit (mem s) (regs s)
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_nop.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s Hmems} => vt3 ct3 et3 ic3 /= Hcolc.
        by rewrite Hcd Hpccol Hcolc eqxx /=.
    - (* Const *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Const n3 r3).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT3.
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      move: Hd3s Hcode3s; case: d3s => v3s t3s; cbn [vala taga] => Hd3s Hcode3s.
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have Hcolc : color t3s = color_of s.
      { move: Hbel; rewrite Hd3s Htpc3 => /rb_belong_some_eq H. by rewrite H. }
      have [v' Hmems] := succ_code_reflect Hcc Hrel Hcode3s Hcolc Hd3s.
      have Hmems' : mem s (vala (pc s) + 1)%w = Some (v' @ t3s) by rewrite Hpcaddr.
      have OLD3' : regs s3 r3 = Some (old3 @ told3) by rewrite ST3 /=.
      have [old' Hold] := reg_reflect Hrm OLD3'.
      cbn [taga] in Hold.
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /next_state_updates /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
      exists (@State mt lrc_tags unit (mem s) (setm (regs s) r3 ((swcast n3) @ Other))
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_const.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hold.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s Hmems} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /= /updm Hold /=.
        by [].
    - (* Mov *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Mov r1 r2).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT3.
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      move: Hd3s Hcode3s; case: d3s => v3s t3s; cbn [vala taga] => Hd3s Hcode3s.
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have Hcolc : color t3s = color_of s.
      { move: Hbel; rewrite Hd3s Htpc3 => /rb_belong_some_eq H. by rewrite H. }
      have [v' Hmems] := succ_code_reflect Hcc Hrel Hcode3s Hcolc Hd3s.
      have Hmems' : mem s (vala (pc s) + 1)%w = Some (v' @ t3s) by rewrite Hpcaddr.
      have R1W3' : regs s3 r1 = Some (w1 @ t1) by rewrite ST3 /=.
      have OLD3' : regs s3 r2 = Some (old3 @ told3) by rewrite ST3 /=.
      have [w1' Hr1] := reg_reflect Hrm R1W3'. cbn [taga] in Hr1.
      have [old' Hr2] := reg_reflect Hrm OLD3'. cbn [taga] in Hr2.
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /next_state_updates /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
      exists (@State mt lrc_tags unit (mem s)
                (setm (setm (regs s) r1 (w1' @ (if is_address t1 then Invalidated else Other)))
                      r2 (w1' @ t1))
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_mov.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hr1.
      + exact Hr2.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s Hmems} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /= /updm Hr1 /= setmE.
        by case: (r2 =P r1) => Hr21 /=; rewrite ?Hr2 //=.
    - (* Binop *) admit.
    - (* Load *) admit.
    - (* Store *) admit.
    - (* Jump *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Jump r).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT3.
      (* operand reflections (same tags) *)
      have RW3' : regs s3 r = Some (w @ t1) by rewrite ST3 /=.
      have RA3' : regs s3 ra = Some (rav @ rat) by rewrite ST3 /=.
      have [rav' Hra] := reg_reflect Hrm RA3'. cbn [taga] in Hra.
      (* reg_clear_list reflects to the SAME tag-hseq on the strong side *)
      have Hclear3 : reg_clear_list_aux reg_list (regs s3) t1 = Some l
        by rewrite ST3 /=; exact CLEAR3.
      have Hclears : reg_clear_list_aux reg_list (regs s) t1 = Some l
        := rb_reg_clear_aux_reflect Hrm Hclear3.
      (* the jump-register tag is InternalJump (from the merged JUMP [is_jump] gate); hshead l = t1 *)
      have Hij := rb_merged_jump_isjump NEXT3.
      have Hheadl : hshead l = t1.
      { move: Hclear3; rewrite /reg_list /=.
        case: (regs s3 (word.as_word (ssrint.Posz 1))) => [v1|] //= Hco.
        case: (obind_inv Hco) => l2 [_ ]; move=> [= Hl]. by rewrite -Hl. }
      rewrite Hheadl in Hij.
      have Ht1 : t1 = InternalJump := rb_is_jump_eq Hij.
      have RW3'' : regs s3 r = Some (w @ InternalJump) by rewrite RW3' Ht1.
      have Hclears' : reg_clear_list_aux reg_list (regs s) InternalJump = Some l
        by rewrite -Ht1.
      (* reflect the jump-register value: off = 0 so the strong target is the SAME w *)
      have Hrw : regs s r = Some (w @ InternalJump)
        := rb_reg_ijump_reflect Hrm Hrel RW3''.
      (* belong of the strong target cell *)
      have Htpc3c : match tpc3 with Level _ c => c end = color_of s.
      { by rewrite Hcoleq ST3 /=. }
      have Hbelw : belong (color_of s)
                     (match mem s w with Some ni => Some (taga ni) | None => None end).
      { apply: (rb_target_belong (s3 := s3) Hcc Hmm Hrel Hside).
        by move: Hbel; rewrite Htpc3c. }
      (* evi reflects *)
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
      have Hcdpc : color td = match pct s with Level _ c => c end by rewrite Hcd Hpccol.
      (* build the strong-side jump step *)
      exists (@State mt lrc_tags unit (mem s) (regs s) (w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_jump.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hrw.
      + exact Hra.
      + rewrite /reg_clear_list. exact Hclears'.
      + (* the [RegRead ra :: RegRead r :: reg_clear_read] fold is the identity on [s] *)
        Local Opaque next_state_do_updates.
        have Hupd : next_state_do_updates s
                      (HSeqCons rat l : hseq (tag_type lrc_tags) (R :: nseq (size reg_list).+1 R))
                      (RegRead ra :: RegRead r :: reg_clear_read) = Some s.
        { rewrite ndsu_cons.
          have Hra' : taga (rav' @ rat) = rat by [].
          rewrite -Hra' (reg_read_update_id Hra) /obind /oapp.
          have Hcl : reg_clear_list_aux reg_list (regs s) (taga (w @ InternalJump)) = Some l
            by exact Hclears'.
          rewrite /reg_clear_read.
          exact: (reg_clear_do_updates_id (l := reg_list) (st := s) (k0 := r)
                    (a0 := w @ InternalJump) Hrw Hcl). }
        rewrite /next_state_updates_and_pc /next_state Hevi /=.
        (* the JUMP-register input tag is [InternalJump] *)
        have Hhij : hshead l = InternalJump by rewrite Hheadl Ht1.
        have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
        { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
        have Hcurc : (match td with {| color := c |} => c end) = color_of s by exact Hcd.
        have Hfold : forall ni : atom (mword mt) (tag_type lrc_tags Symbolic.M),
                     belong (color_of s) (Some (taga ni))
                     -> (match taga ni with {| color := c' |} =>
                          (match td with {| color := c |} => c end) == c' end) = true.
        { move=> ni0; rewrite /belong Hcurc. by case: (taga ni0) => v0 c0 e0 b0 /=. }
        case Hmsw : (mem s w) => [ni|] /=;
          rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules;
          cbv zeta;
          rewrite {1}El /=;
          (move: Hpccol; case: (pct s) => lpc cpc /= Hpccol);
          ( rewrite (_ : (match td with {| color := c |} => c end == cpc) = true);
            last by (apply/eqP; rewrite Hcurc Hpccol) );
          rewrite /=.
        * (* mem s w = Some ni: belong holds at the target *)
          rewrite (Hfold ni); last by (move: Hbelw; rewrite Hmsw /=).
          rewrite -El Hhij /is_jump /=.
          by rewrite Hupd.
        * (* mem s w = None: belong None is true *)
          rewrite -El Hhij /is_jump /=.
          by rewrite Hupd.
    - (* Bnz *) admit.
    - (* Jal *) admit.
    - (* Syscall *) admit.
  Admitted.

End RBScratch_Jump.

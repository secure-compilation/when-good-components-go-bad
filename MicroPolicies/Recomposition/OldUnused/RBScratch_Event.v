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

Module RBScratch_Event (S : RecompositionContext).

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
     strong side and produces the SAME tag-hseq).  (Copied from RBScratch_Jump.) *)
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

  (* Reflect a [Ret n]-tagged register read on the merged side to a strong-side read with the
     SAME tag [Ret n].  The value [w'] is the strong-side return address; [reg_reflect] gives the
     same tag, and [data_match] for [Ret n] pins [w'] into the metadata stack frame (the value
     itself may differ from the merged [w], hence we expose [w'] existentially). *)
  Lemma rb_reg_ret_reflect : forall (i : side) M s s3 r w n,
    registers_match i M s s3 ->
    regs s3 r = Some (w @ (Ret n)) ->
    exists w', regs s r = Some (w' @ (Ret n)).
  Proof.
    move=> i M s s3 r w n Hrm Hr3.
    have [v' Hr] := reg_reflect Hrm Hr3. by exists v'.
  Qed.

  Lemma rb_is_other_eq : forall t : value_tag, is_other t = Some tt -> t = Other.
  Proof. by case. Qed.

  Lemma rb_check_ret_eq : forall level (t : tag_type lrc_tags R),
    check_ret level t = Some tt -> exists n', t = Ret n' /\ level = S n'.
  Proof.
    move=> level [n' | | |] //=; case: ifP => // /eqP Hl _.
    by exists n'.
  Qed.

  (* From an EVENT LRC JUMP transfer (the [else] return branch [belong = false]): the jump
     register tag [tp] is [Ret (level.-1)], the running-component gate [is_other trcom] holds,
     the target cell colour is recoverable ([get_tni_color tni = Some c']) and the event is the
     return [ERet current _ c'].  This is the LRC return rule read off backwards. *)
  Lemma rb_jump_event_inv :
    forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (tra tp trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evi : ev_inputs) (ov : ovec lrc_tags JUMP) (e : event),
      LRC.transfer (IVec (OP JUMP) tpc ti (tra :: tp :: trcom :: next)%hseq tni) evi
        = Some (ov, Some e) ->
      belong (match ti with {| color := c |} => c end) tni = false /\
      is_other trcom = Some tt /\
      (exists c', get_tni_color tni = Some c' /\
                  e = ERet (match ti with {| color := c |} => c end) (rcom_value evi) c') /\
      (exists n', tp = Ret n' /\ (match tpc with Level level _ => level end) = S n') /\
      (match ti with {| color := c |} => c end) = (match tpc with Level _ c' => c' end).
  Proof.
    move=> [level current'] ti tra tp trcom next tni evi ov e.
    rewrite /LRC.transfer /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    have Hcur : (match ti with {| color := c |} => c end) = current' by apply/eqP.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest.
    - (* silent intra branch: ev = None, contradiction with Some e *)
      exfalso. case: (obind_inv Hrest) => u' [_ {}Hrest]. by move: Hrest => [= _].
    - (* return branch *)
      case: (obind_inv Hrest) => uo [Hother {}Hrest].
      case: uo Hother => Hother.
      case: (obind_inv Hrest) => c' [Hc' {}Hrest].
      case: (obind_inv Hrest) => uret [Hret Hfin].
      case: uret Hret => Hret.
      move: Hfin => [= Hov Hev].
      have Hck := rb_check_ret_eq Hret.
      split; [ by [] |].
      split; [ exact Hother |].
      split; [ exists c'; split; [exact Hc' | by rewrite -Hev] |].
      split; [ exact Hck | exact Hcur ].
  Qed.

  (* Merged version: from a merged JUMP EVENT step (target [w], inputs [HSeqCons rat l]), extract
     the return-branch facts about the target cell tag [tni3 = match mem s3 w with Some ni => Some
     (taga ni) | None => None] and the jump-register tag [hshead l]. *)
  Lemma rb_merged_jump_event :
    forall (st s' : RB.state) (tpc : tag_type lrc_tags P) ti (rat : tag_type lrc_tags R)
           (l : hseq (tag_type lrc_tags) (nseq 12 R)) updts (w : mword mt) e,
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st
        (IVec JUMP tpc ti (HSeqCons rat l)) updts w = Some (s', Some e) ->
      belong (match ti with {| color := c |} => c end)
             (match mem st w with Some ni => Some (taga ni) | None => None end) = false /\
      is_other (hshead (hsbehead l)) = Some tt /\
      (exists c', get_tni_color (match mem st w with Some ni => Some (taga ni) | None => None end) = Some c') /\
      (exists n', hshead l = Ret n' /\ (match tpc with Level level _ => level end) = S n').
  Proof.
    move=> st s' tpc ti rat l updts w e H.
    move: (nsu_and_pc_bridge H); rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       have [Hbel [Hother [[c' [Hc' _]] [Hret _]]]] := rb_jump_event_inv Htr;
       (split; [ exact Hbel |]); (split; [ exact Hother |]);
       (split; [ exists c'; exact Hc' | exact Hret ])).
  Qed.

  (* From an EVENT LRC JAL transfer (the [else] call branch [belong = false]): the running-side
     gates [check_belong current (Some tnext)], [is_other trcom] hold, and the foreign-target gates
     [get_tni_color tni = Some c'], [get_proc_name tni = Some p], [check_entry current tni] succeed,
     with event [ECall current p _ c'].  The LRC call rule read off backwards. *)
  Lemma rb_jal_event_inv :
    forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (tnext : tag_type lrc_tags Symbolic.M) (tra trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evi : ev_inputs) (ov : ovec lrc_tags JAL) (e : event),
      LRC.transfer (IVec (OP JAL) tpc ti (tnext :: tra :: trcom :: next)%hseq tni) evi
        = Some (ov, Some e) ->
      check_belong (match ti with {| color := c |} => c end) (Some tnext) = Some tt /\
      belong (match ti with {| color := c |} => c end) tni = false /\
      is_other trcom = Some tt /\
      (exists c', get_tni_color tni = Some c') /\
      (exists p, get_proc_name tni = Some p) /\
      check_entry (match ti with {| color := c |} => c end) tni = Some tt.
  Proof.
    move=> [level current'] ti tnext tra trcom next tni evi ov e.
    rewrite /LRC.transfer /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    case: (obind_inv Hrest) => ucb [Hcb {}Hrest]. case: ucb Hcb => Hcb.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret get_proc_name check_entry].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest.
    - (* silent intra branch: ev = None, contradiction *)
      exfalso. by move: Hrest => [= _].
    - (* call branch *)
      case: (obind_inv Hrest) => uo [Hother {}Hrest]. case: uo Hother => Hother.
      case: (obind_inv Hrest) => c' [Hc' {}Hrest].
      case: (obind_inv Hrest) => uent [Hent Hfin]. case: uent Hent => Hent.
      (* the event is built from get_proc_name tni; for Some e it must succeed *)
      move: Hfin => [= Hov Hev].
      have Hpn : exists p, get_proc_name tni = Some p.
      { move: Hev; case Hp: (get_proc_name tni) => [p|] //= _. by exists p. }
      split; [ exact Hcb |]. split; [ by [] |]. split; [ exact Hother |].
      split; [ by exists c' | ]. split; [ exact Hpn | exact Hent ].
  Qed.

  Lemma rb_merged_jal_event :
    forall (st s' : RB.state) (tpc : tag_type lrc_tags P) ti (tret : tag_type lrc_tags Symbolic.M)
           (l : hseq (tag_type lrc_tags) (nseq 12 R)) updts (w : mword mt) e,
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st
        (IVec JAL tpc ti (HSeqCons tret l)) updts w = Some (s', Some e) ->
      check_belong (match ti with {| color := c |} => c end) (Some tret) = Some tt /\
      belong (match ti with {| color := c |} => c end)
             (match mem st w with Some ni => Some (taga ni) | None => None end) = false /\
      is_other (hshead (hsbehead l)) = Some tt /\
      (exists c', get_tni_color (match mem st w with Some ni => Some (taga ni) | None => None end) = Some c') /\
      (exists p, get_proc_name (match mem st w with Some ni => Some (taga ni) | None => None end) = Some p) /\
      check_entry (match ti with {| color := c |} => c end)
                  (match mem st w with Some ni => Some (taga ni) | None => None end) = Some tt.
  Proof.
    move=> st s' tpc ti tret l updts w e H.
    move: (nsu_and_pc_bridge H); rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       have [Hcb [Hbel [Hother [[c' Hc'] [[p Hp] Hent]]]]] := rb_jal_event_inv Htr;
       (split; [ exact Hcb |]); (split; [ exact Hbel |]); (split; [ exact Hother |]);
       (split; [ by exists c' |]); (split; [ by exists p | exact Hent ])).
  Qed.

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
    { (* ev = Some e: cross-component Jump/Jal *)
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
      - (* nop: silent transfer cannot emit event *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* const *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* mov *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* binop *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* load *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* store *)
        rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* JUMP — cross-component return *)
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
        (* operand reflections (same tags) *)
        have RW3' : regs s3 r = Some (w @ t1) by rewrite ST3 /=.
        have RA3' : regs s3 ra = Some (rav @ rat) by rewrite ST3 /=.
        have [rav' Hra] := reg_reflect Hrm RA3'. cbn [taga] in Hra.
        (* reg_clear_list reflects to the SAME tag-hseq on the strong side *)
        have Hclear3 : reg_clear_list_aux reg_list (regs s3) t1 = Some l
          by rewrite ST3 /=; exact CLEAR3.
        have Hclears : reg_clear_list_aux reg_list (regs s) t1 = Some l
          := rb_reg_clear_aux_reflect Hrm Hclear3.
        (* hshead l = t1 (the top_reg_tag of reg_clear_list is t1) *)
        have Hheadl : hshead l = t1.
        { move: Hclear3; rewrite /reg_list /=.
          case: (regs s3 (word.as_word (ssrint.Posz 1))) => [v1|] //= Hco.
          case: (obind_inv Hco) => l2 [_ ]; move=> [= Hl]. by rewrite -Hl. }
        (* the merged JUMP event step is a cross-component RETURN: extract the return-branch facts *)
        have [Hbel3 [Hother3 [[c' Hc'3] [n' [Hheadret Hlevel]]]]] := rb_merged_jump_event NEXT3.
        rewrite Hheadl in Hheadret.  (* t1 = Ret n' *)
        (* reflect the jump (return) register: same tag [Ret n'], value [w'] (metadata-related) *)
        have RW3'' : regs s3 r = Some (w @ (Ret n')) by rewrite RW3' Hheadret.
        have [w' Hrw] := rb_reg_ret_reflect Hrm RW3''.
        (* reflect reg_clear_list with the [Ret n'] tag *)
        have Hclears' : reg_clear_list_aux reg_list (regs s) (Ret n') = Some l
          by rewrite -Hheadret.
        have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
        { move: NEXT3; rewrite /next_state_updates_and_pc /next_state /evi.
          by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
        have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
        have Hiscode : is_code td by rewrite Htag.
        have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
        eexists; eexists.
        apply/Exec.stepP.
        eapply step_jump.
        + exact: (Symbolic.state_eta s).
        + exact Hd.
        + exact Hdecs.
        + exact Hrw.
        + exact Hra.
        + rewrite /reg_clear_list. exact Hclears'.
        + rewrite /next_state_updates_and_pc /next_state Hevi /=.
          (* RESIDUAL GAP (foreign-target transfer): the strong-side JUMP must take the SAME
             cross-component RETURN branch, i.e. the Merged.transfer at the strong-side target
             [mem s w'] must succeed with [belong current (tni at w') = false] and
             [get_tni_color (tni at w') = Some _].  [w'] is the strong-side saved return address
             (the [Ret n']-tagged value of register [r], reflected by [rb_reg_ret_reflect]); on the
             merged side the analogous facts hold at [mem s3 w] ([Hbel3], [Hc'3]).  BUT [w'] is a
             FOREIGN-colour cell that [combined_codes] does NOT relate, so [mem s w'] is unknown
             from the hypotheses of [stepf_reflect_pf].  The missing fact is precisely
             [capability_correctness M WS s] + [wf_stack ... M] (the metadata stack invariant
             connecting the [Ret n']-tagged register value [w'] to a valid saved return target),
             which lives in [common_equiv]/[match_states] but is NOT carried by [strong_equiv].
             This is the documented backward-simulation interface (the reason [stepf_reflect] was
             isolated as a Hypothesis in RecBackward.v). *)
          admit.
      - (* bnz *)
        unfold mv3 in NEXT.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      - (* JAL — cross-component call *)
        have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
        have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT).
        have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
        move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
        have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
        (* The strong side also decodes a JAL (decode_match: no_JAL is impossible since i3 is a Jal). *)
        have [imm' Hdecs] : exists imm', decode_instr vd = Some (Jal imm').
        { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm2 imm2' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
          - exfalso. rewrite Heq in Hnj. by move: (Hnj imm); rewrite INST3.
          - by exists (word_of_nat alloc_label).
          - by exists imm2. }
        (* operand reflections (running side): ra register + reg_clear_list + the return cell. *)
        have OLD3' : regs s3 ra = Some (old3 @ told3) by rewrite ST3 /=.
        have [old' Hold] := reg_reflect Hrm OLD3'. cbn [taga] in Hold.
        have Hclear3 : reg_clear_list_aux reg_list (regs s3) told3 = Some l
          by rewrite ST3 /=; exact CLEAR3.
        have Hclears : reg_clear_list_aux reg_list (regs s) told3 = Some l
          := rb_reg_clear_aux_reflect Hrm Hclear3.
        (* The return cell at [pc.+1] is a running-colour code cell (end_condition + check_belong),
           hence reflects to the strong side with the SAME tag [tret]. *)
        have Hra3cell : mem s3 (addw (vala (pc s3)) onew) = Some (vret @ tret).
        { rewrite ST3 /=. move: RA3. by []. }
        have Hcode_ret : is_code tret.
        { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | [v3 [Hv3 Hcv3]]].
          - exfalso. by move: Hhalt; cbn [vala]; rewrite INST3.
          - have Heqv : v3 = (vret @ tret) by congruence.
            move: Hcv3; rewrite Heqv /=. by apply. }
        have [Hcb3 [Hbel3 [Hother3 [[c' Hc'3] [[pn Hpn3] Hent3]]]]] := rb_merged_jal_event NEXT.
        (* check_belong current (Some tret) = Some tt  ==>  color tret = color ti3 = color_of s *)
        have Hcolti3 : color ti3 = color_of s by rewrite (Hpci (i3 @ ti3) Hd3) Hcoleq.
        have Hcolret : color tret = color_of s.
        { have Hbel : belong (color ti3) (Some tret).
          { move: Hcb3; rewrite /check_belong. by case: (belong (color ti3) (Some tret)). }
          by rewrite -Hcolti3 -(rb_belong_some_eq Hbel). }
        have [vret' Hretcell] := succ_code_reflect Hcc Hrel Hcode_ret Hcolret Hra3cell.
        have Hretcell' : mem s (addw (vala (pc s)) onew) = Some (vret' @ tret) by rewrite Hpcaddr.
        have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
        { move: NEXT; rewrite /next_state_updates_and_pc /next_state /evi.
          by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
        have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
        have Hiscode : is_code td by rewrite Htag.
        have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
        eexists; eexists.
        apply/Exec.stepP.
        eapply step_jal.
        + exact: (Symbolic.state_eta s).
        + exact Hd.
        + exact Hretcell'.
        + exact Hdecs.
        + exact Hold.
        + rewrite /reg_clear_list. exact Hclears.
        + rewrite /next_state_updates_and_pc /next_state Hevi /=.
          (* RESIDUAL GAP (foreign-target transfer): the strong-side JAL must take the SAME
             cross-component CALL branch, i.e. the Merged.transfer at the strong-side call target
             [mem s (swcast imm')] must succeed with [belong current (tni at target) = false],
             [get_tni_color (tni at target) = Some _], [get_proc_name (tni at target) = Some _] and
             [check_entry current (tni at target) = Some tt].  [swcast imm'] is the strong-side entry
             point ([imm' = imm + offset] from [decode_match]'s JAL case); on the merged side the
             analogous facts hold at [mem s3 (swcast imm)] ([Hbel3], [Hc'3], [Hpn3], [Hent3]).  BUT the
             entry-point cell is a FOREIGN-colour cell that [combined_codes] does NOT relate; carrying
             it to [s] needs [entry_points_offset i (mem s) (mem s3)] (a [strong_equiv] field) PLUS
             the cross-component entry-point well-formedness from [match_states] (that the called
             entry is a valid foreign entry of the SAME procedure).  Neither the entry-cell content
             ([get_proc_name]/[check_entry]) nor [belong = false] is derivable from the hypotheses of
             [stepf_reflect_pf] alone — this is the documented backward-simulation interface (the
             reason [stepf_reflect] was isolated as a Hypothesis in RecBackward.v). *)
          admit.
      - (* syscall: run_syscall always returns event None *)
        exfalso. move: CALL3; rewrite /run_syscall.
        move=> H. case: (obind_inv H) => evinp [_ {}H].
        move: H; case: (Merged.transfer _ _) => [u|] //= H.
        case: (obind_inv H) => st0 [_ ]. by move=> [= _].
    }
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
    - (* Jump *) admit.
    - (* Bnz *) admit.
    - (* Jal *) admit.
    - (* Syscall *) admit.
  Admitted.

End RBScratch_Event.

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

Module RBScratch_Jal (S : RecompositionContext).

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

  Lemma rb_belong_color : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
    belong c (Some t) -> c = color t.
  Proof. by move=> c [vt ct et bt] /= /eqP. Qed.

  Lemma rb_color_match : forall (t : tag_type lrc_tags Symbolic.M),
    match t with {| color := c |} => c end = color t.
  Proof. by case. Qed.

  Lemma rb_obindSome : forall (A B : Type) (f : A -> option B) (x : A),
    obind f (Some x) = f x.
  Proof. by []. Qed.

  Lemma rb_belong_color_eq : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
    c = color t -> belong c (Some t).
  Proof. by move=> c [vt ct et bt] /= ->; rewrite eqxx. Qed.

  (* [reg_clear_list_aux] reflects across [registers_match]: it only reads register tags, which are
     preserved by [data_match] (the tag component is always equal), so it produces the SAME hseq. *)
  Lemma rb_reg_clear_aux_reflect : forall i M s s3 (ll : seq nat) (top : tag_type lrc_tags R) res,
    registers_match i M s s3 ->
    reg_clear_list_aux ll (regs s3) top = Some res ->
    reg_clear_list_aux ll (regs s) top = Some res.
  Proof.
    move=> i M s s3. elim => [|e ll' IH] top res Hrm.
    - by [].
    - rewrite !reg_clear_list_aux_cons.
      case Hr3: (regs s3 (as_word (ssrint.Posz e))) => [a3|] //=.
      have [v' Hr] := reg_reflect Hrm Hr3. rewrite Hr /=.
      case Hrec3: (reg_clear_list_aux ll' (regs s3) (taga a3)) => [l3|] //=.
      rewrite (IH (taga a3) l3 Hrm Hrec3) /=. by [].
  Qed.

  (* The Merged silent JAL transfer result, computed once with controlled reduction: when the
     colour guards hold (current == pc-colour, head check_belong, target belong), the transfer
     produces the intra OVec with [tr = tret :: InternalJump :: hsbehead l] and event [None]. *)
  Lemma rb_jal_transfer_silent :
    forall (tpc : tag_type lrc_tags P) ti tret
           (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R)) (tjd : tag_type lrc_tags Symbolic.M) ei,
      is_code ti ->
      (match ti with {| color := c |} => c end) == (match tpc with Level _ c' => c' end) ->
      belong (match ti with {| color := c |} => c end) (Some tret) ->
      belong (match ti with {| color := c |} => c end) (Some tjd) ->
      Merged.transfer (IVec JAL tpc ti (HSeqCons tret l) (Some tjd)) ei
      = Some (Symbolic.OVec JAL tpc (HSeqCons tret (HSeqCons InternalJump (hsbehead l))), None).
  Proof.
    move=> [level current'] [vti cti eti bti] [vtr ctr etr btr] l [vjd cjd ejd bjd] ei /= Hcode Hg1 Hg2 Hg3.
    move: Hg2 Hg3; rewrite /belong /= => Hg2 Hg3.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    move: Hcode => /= ->. rewrite /=.
    rewrite /LRC.instr_rules. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    rewrite Hg1 /= /check_belong /belong /= Hg2 /= Hg3 /=.
    by [].
  Qed.

  (* [tni = None] variant (allocator JAL target absent from memory): [belong current None = true]. *)
  Lemma rb_jal_transfer_silent_none :
    forall (tpc : tag_type lrc_tags P) ti tret
           (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R)) ei,
      is_code ti ->
      (match ti with {| color := c |} => c end) == (match tpc with Level _ c' => c' end) ->
      belong (match ti with {| color := c |} => c end) (Some tret) ->
      Merged.transfer (IVec JAL tpc ti (HSeqCons tret l) None) ei
      = Some (Symbolic.OVec JAL tpc (HSeqCons tret (HSeqCons InternalJump (hsbehead l))), None).
  Proof.
    move=> [level current'] [vti cti eti bti] [vtr ctr etr btr] l ei /= Hcode Hg1 Hg2.
    move: Hg2; rewrite /belong /= => Hg2.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    move: Hcode => /= ->. rewrite /=.
    rewrite /LRC.instr_rules. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    rewrite Hg1 /= /check_belong /belong /= Hg2 /=.
    by [].
  Qed.

  (* From a silent merged JAL transfer, the head register-clear tag [tret] (= RA-cell tag) has the
     running (pc-tag) colour: the LRC JAL rule runs [check_belong current (Some tret)] first. *)
  Lemma jal_silent_head_belong :
    forall tpc ti tret (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R)) tni evi
           (ov : ovec lrc_tags JAL),
      LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evi = Some (ov, None) ->
      belong (match ti with {| color := c |} => c end) (Some tret).
  Proof.
    move=> [level current'] [vti cti eti bti] tret l tni evi ov.
    rewrite /LRC.transfer /LRC.instr_rules. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    move=> H. case: (obind_inv H) => u0 [_ {}H].
    case: (obind_inv H) => ucb [Hcb {}H].
    move: Hcb; rewrite /check_belong /belong. clear H.
    by case: tret => vt ct et bt /=; case: (cti == ct).
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
    have Hallocs : mem s (word_of_nat alloc_label) = None
      by case: Hgmcs => _ [_ [_ [H _]]]; exact H.
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
    - (* Jump *) admit.
    - (* Bnz *) admit.
    - (* Jal *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      (* colour of the running pc-tag *)
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
      (* RA cell (pc+1) on the merged side; it is the end_condition successor, hence code colour=current *)
      have HRA3 : mem s3 (vala (pc s3) + 1)%w = Some (vret @ tret) by rewrite ST3 /=.
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (vala (pc s3) + 1)%w = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      (* the end_condition successor IS the RA cell (pc+1): so tret is code *)
      have Htretcode : is_code tret.
      { move: Hd3s; rewrite HRA3 => -[Hd3eq]. by rewrite -Hd3eq in Hcode3s; move: Hcode3s; cbn [taga]. }
      (* target belong from merged silent transfer *)
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT.
      (* head check_belong: color tret = running colour.  Bridge merged->LRC then peel. *)
      have HtretBel : belong (match ti3 with {| color := c |} => c end) (Some tret).
      { have HL := nsu_and_pc_bridge NEXT.
        move: HL; rewrite /next_state_updates_and_pc /next_state.
        case Hevi: (evi s3) => [evinp|] //=.
        rewrite ST3 /=.
        case Hm: (mem3 NEXT3) => [ni|] /= Hgoal;
          ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
            case: ov_ev Htr Hk => ov ev Htr Hk;
            case: (obind_inv Hk) => st0 [Hdsu Hfin];
            move: Hfin => [= Hs Hev]; subst ev;
            exact: (jal_silent_head_belong Htr) ). }
      have Hcolti3 : color ti3 = color_of s.
      { have := Hpci (i3 @ ti3) Hd3; cbn [taga] => H. by rewrite H Hcoleq. }
      have Hcoltret : color tret = color_of s.
      { have HtretEq := rb_belong_color HtretBel. by rewrite -HtretEq -Hcolti3. }
      (* --- strong-side operand facts shared by both decode_match cases --- *)
      (* strong-side RA cell (pc+1): reflect the merged code RA cell *)
      have [vret' HRAs] := succ_code_reflect Hcc Hrel Htretcode Hcoltret HRA3.
      have HRAs' : mem s (vala (pc s) + 1)%w = Some (vret' @ tret) by rewrite Hpcaddr.
      (* strong-side OLD reg (ra) *)
      have OLD3' : regs s3 ra = Some (old3 @ told3) by rewrite ST3 /=.
      have [old' Holds] := reg_reflect Hrm OLD3'. cbn [taga] in Holds.
      (* strong-side reg_clear_list (same l, tags preserved) *)
      have CLEAR3' : reg_clear_list (regs s3) told3 = Some l by rewrite ST3 /=.
      have CLEARs : reg_clear_list (regs s) told3 = Some l
        by apply: (rb_reg_clear_aux_reflect Hrm CLEAR3').
      (* the [evi] succeeds on the strong side *)
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT; rewrite /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a4|] /=; [exists a4 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      (* the two colour guards (tag/pc-colour match, head check_belong) are case-independent *)
      have Hg1 : (match td with {| color := c |} => c end)
                 == (match pct s with Level _ c' => c' end)
        by rewrite !rb_color_match Hcd Hpccol eqxx.
      have Hg2 : belong (match td with {| color := c |} => c end) (Some tret)
        by rewrite rb_color_match; apply: rb_belong_color_eq; rewrite Hcd Hcoltret.
      (* invert decode_match: only JAL or alloc-JAL survive *)
      inversion Hdec as [Hnj Hnj' Heq | Halloc Halloc2 | jimm jimm' jd jd' Hjs Hj3 Htgts Htgt3 Hcodet Htagteq Hoff].
      + (* no_JAL: contradicted, i3 IS a Jal *)
        exfalso. by move: (Hnj' imm); rewrite INST3.
      + (* alloc_JAL: target is the allocator address, absent from memory (alloc_empty) *)
        have Htgtnone : mem s (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label)) = None
          by rewrite swcast_word_of_nat_alloc_label.
        eexists. exists None.
        apply/Exec.stepP.
        eapply step_jal.
        * exact: (Symbolic.state_eta s).
        * exact Hd.
        * exact HRAs'.
        * exact Halloc.
        * exact Holds.
        * exact CLEARs.
        * have HtrS := rb_jal_transfer_silent_none l ei Hiscode Hg1 Hg2.
          rewrite /next_state_updates_and_pc /next_state Htgtnone Hevi.
          rewrite rb_obindSome HtrS rb_obindSome.
          cbn -[next_state_do_updates updm].
          rewrite (jal_do_updates_result (vv := vret') (a4 := old' @ told3) HRAs' Holds CLEARs).
          rewrite /next_state_do_update /updm Holds /=.
          by [].
      + (* genuine JAL *)
        (* jimm' (merged) = imm (NEXT3 target = swcast imm) *)
        have Himm3 : jimm' = imm by move: Hj3; rewrite INST3 => -[].
        (* merged target cell = jd' and its colour = running *)
        have Htgt3' : mem s3 NEXT3 = Some jd'.
        { rewrite -[NEXT3]/(swcast imm) -Himm3. exact Htgt3. }
        have Hcoljd' : color (taga jd') = color_of s.
        { have Hbel' := Hbel. rewrite Htgt3' in Hbel'.
          have := rb_belong_color Hbel'. move=> Heq.
          have Htpc3c : match tpc3 with Level _ c => c end = color_of s
            by rewrite Hcoleq ST3 /=.
          by rewrite -Htpc3c -Heq. }
        have Hcoljd : color (taga jd) = color_of s by rewrite Htagteq.
        (* target colour is running ⇒ offset 0 ⇒ swcast jimm' = swcast jimm *)
        have HtgtRel : is_relevant_comp i (color (taga jd))
          by rewrite Hcoljd; apply: Hrel.
        have [offt Hofft] := get_offset_some HtgtRel.
        have Hzt := get_offset_zero HtgtRel Hofft.
        have HsideJd : side_of (color (taga jd)) = i.
        { by rewrite Hcoljd. }
        have Himmeq : @swcast _ (word_size mt) jimm' = @swcast _ (word_size mt) jimm.
        { have Hoff' := Hoff offt. rewrite HsideJd in Hoff'.
          have Hoe := Hoff' Hofft. rewrite Hzt addw0 in Hoe. exact Hoe. }
        (* build the strong-side step *)
        eexists. exists None.
        apply/Exec.stepP.
        eapply step_jal.
        * exact: (Symbolic.state_eta s).
        * exact Hd.
        * exact HRAs'.
        * exact Hjs.
        * exact Holds.
        * exact CLEARs.
        * (* discharge NEXT via the localised transfer + do_updates helpers (no giant cbv zeta) *)
          have Hg3 : belong (match td with {| color := c |} => c end) (Some (taga jd))
            by rewrite rb_color_match; apply: rb_belong_color_eq; rewrite Hcd Hcoljd.
          have HtrS := rb_jal_transfer_silent l ei Hiscode Hg1 Hg2 Hg3.
          rewrite /next_state_updates_and_pc /next_state Htgts Hevi.
          rewrite rb_obindSome HtrS rb_obindSome.
          cbn -[next_state_do_updates updm].
          rewrite (jal_do_updates_result (vv := vret') (a4 := old' @ told3) HRAs' Holds CLEARs).
          rewrite /next_state_do_update /updm Holds /=.
          by [].
    - (* Syscall *) admit.
  Admitted.

End RBScratch_Jal.

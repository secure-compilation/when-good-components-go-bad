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

Module RBScratch_Binop (S : RecompositionContext).

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

  (* [updm] succeeds (and equals a [setm]) on any in-domain key. *)
  Lemma rb_updm_some {St : Type} (m : {fmap reg mt -> St}) k a v :
    m k = Some a -> updm m k v = Some (setm m k v).
  Proof. by rewrite /updm => ->. Qed.

  (* From a successful merged BINOP transfer, the two source-operand tags pass the [is_other]
     gates.  Mirror [merged_transfer_iscode]: peel gate1 (is_code ti), gate2 (BINOP not
     STORE/LOAD ⟹ Some tt), then LRC.instr_rules's [current==current'] gate, then the two
     [is_other] obinds. *)
  Lemma rb_binop_is_other : forall b tpc ti (t1 t2 told : tag_type lrc_tags R) tni i r,
    Merged.transfer (IVec (OP (BINOP b)) tpc ti [hseq t1; t2; told] tni) i = Some r ->
    is_other t1 = Some tt /\ is_other t2 = Some tt.
  Proof.
    move=> b tpc ti t1 t2 told tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules] => H.
    apply obind_inv in H; destruct H as [out [Hir _]].
    (* peel gate1: is_code ti *)
    apply obind_inv in Hir; destruct Hir as [u1 [_ Hir]].
    (* peel gate2: BINOP ⟹ Some tt *)
    apply obind_inv in Hir; destruct Hir as [u2 [_ Hir]].
    (* now Hir : (do! out <- LRC.instr_rules ... ; ...) = Some out *)
    apply obind_inv in Hir; destruct Hir as [lout [Hlrc _]].
    move: Hlrc; clear r out u1 u2; rewrite /LRC.instr_rules.
    move: lout; case: ti => vti cti eti icti; case: tpc => lpc cpc => lout; cbv zeta.
    case: (cti == cpc) => //=.
    move=> Hg.
    apply obind_inv in Hg; destruct Hg as [v1 [Ho1 Hg]].
    apply obind_inv in Hg; destruct Hg as [v2 [Ho2 _]].
    by rewrite Ho1 Ho2; move: Ho1 Ho2; case: v1 => _; case: v2 => _.
  Qed.

  (* From a successful merged [next_state_updates_and_pc] (BINOP form), the two source operand
     tags pass [is_other].  Mirrors [nsu_transfer_iscode]. *)
  Lemma nsu_binop_is_other : forall (s : @Symbolic.state mt lrc_tags unit) b tpc ti
      (t1 t2 told : tag_type lrc_tags R) updts pc' res,
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
      (IVec (OP (BINOP b)) tpc ti [hseq t1; t2; told]) updts pc' = Some res ->
    is_other t1 = Some tt /\ is_other t2 = Some tt.
  Proof.
    move=> s b tpc ti t1 t2 told updts pc' res.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi s) => [evinp|] //=.
    case Hm: (mem s pc') => [ni|] /= H.
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_binop_is_other Htr).
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_binop_is_other Htr).
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
    - (* Binop *)
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Binop op r1 r2 r3).
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
      have R2W3' : regs s3 r2 = Some (w2 @ t2) by rewrite ST3 /=.
      have OLD3' : regs s3 r3 = Some (old3 @ told3) by rewrite ST3 /=.
      have [w1' Hr1] := reg_reflect Hrm R1W3'. cbn [taga] in Hr1.
      have [w2' Hr2] := reg_reflect Hrm R2W3'. cbn [taga] in Hr2.
      have [old' Hr3] := reg_reflect Hrm OLD3'. cbn [taga] in Hr3.
      have [Hot1 Hot2] := nsu_binop_is_other NEXT3.
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /next_state_updates /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite rb_color_ofE.
      exists (@State mt lrc_tags unit (mem s)
                (setm (setm (setm (regs s) r1 (w1' @ t1))
                            r2 (w2' @ t2))
                      r3 ((binop_denote op w1' w2') @ Other))
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_binop.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hr1.
      + exact Hr2.
      + exact Hr3.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        rewrite Hot1 Hot2 /=.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s Hmems} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /=.
        (* resolve read 1 (r1) and its updm via Hr1 *)
        rewrite Hr1 /= (rb_updm_some _ Hr1) /=.
        (* read 2 (r2) on [setm (regs s) r1 (w1'@t1)]: only the read VALUE can alias r1 *)
        case: (r2 =P r1) => [Hr21|Hr21].
        { (* r2 = r1: re-read of r1's freshly-written value forces w1' = w2' *)
          have Hw12 : w1' = w2'.
          { by move: Hr2; rewrite Hr21 Hr1 => -[] ->. }
          rewrite Hr21.
          rewrite [setm (regs s) r1 _ r1]setmE eqxx /=.
          rewrite (rb_updm_some _ (a := w1' @ t1)); last by rewrite setmE eqxx.
          rewrite /=.
          have [b3 Hb3] : exists b3,
              setm (setm (regs s) r1 (w1' @ t1)) r1 (w1' @ t2) r3 = Some b3.
          { rewrite !setmE; case: (r3 == r1); first by eauto.
            by rewrite Hr3; eauto. }
          rewrite (rb_updm_some _ Hb3) /=. by rewrite Hw12. }
        (* r2 <> r1: read r2 gives [regs s r2] = w2'@t2 *)
        rewrite setmE; move: Hr21 => /eqP/negbTE Hr21; rewrite Hr21 Hr2 /=.
        rewrite (rb_updm_some _ (a := w2' @ t2)); last by rewrite setmE Hr21 Hr2.
        rewrite /=.
        have [b3 Hb3] : exists b3,
            setm (setm (regs s) r1 (w1' @ t1)) r2 (w2' @ t2) r3 = Some b3.
        { rewrite !setmE; case: (r3 == r2); first by eauto.
          case: (r3 == r1); first by eauto. by rewrite Hr3; eauto. }
        by rewrite (rb_updm_some _ Hb3) /=.
    - (* Load *) admit.
    - (* Store *) admit.
    - (* Jump *) admit.
    - (* Bnz *) admit.
    - (* Jal *) admit.
    - (* Syscall *) admit.
  Admitted.

End RBScratch_Binop.

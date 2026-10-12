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

Module RBScratch_Syscall (S : RecompositionContext).

  Module RB := RecBackward S.
  Import RB.

  (* keep the kernel from re-normalising the word-op-laden allocator body in the Syscall case
     (the documented 42min->24s syscall fix); harmless for the Nop/Const/Mov bullets. *)
  Opaque andw shlw as_word word_of_nat.
  Opaque mask component_memory_prefix.
  Opaque unionm setm mkfmap mkfmapfp.

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
    - (* Jump *) admit.
    - (* Bnz *) admit.
    - (* Jal *) admit.
    - (* Syscall *)
      have Hpc3 : vala (pc s3) = pc3 by rewrite ST3 /=.
      have Hmem3none : mem s3 (vala (pc s3)) = None by rewrite ST3 /= PC3.
      have Hmemsnone : mem s (vala (pc s)) = None.
      { have [off Hoff0] := get_offset_some Hrel.
        have Hz0 := get_offset_zero Hrel Hoff0.
        inversion Hsp as [u u' Hpe Hnone | u u' v off' Hcell Hoff Hpce].
        - exact Hnone.
        - exfalso.
          have Hoffeq : off' = off by move: Hoff; rewrite Hoff0 => -[->].
          subst off'.
          have Hpcs3 : vala (pc s3) = vala (pc s) by rewrite Hpce Hz0 addw0.
          have Hmem3none' : mem s3 (vala (pc s)) = None by rewrite -Hpcs3.
          move: Hcell; case: v => vv tv Hcell.
          case Hcolv: (color tv == color_of s).
          + move: Hcolv => /eqP Hcolv.
            case Hcodv: (is_code tv).
            * have [v' [_ Hmems3]] :=
                proj1 (Hcc (vala (pc s)) vv tv off (color_of s) Hrel Hoff Hcodv Hcolv) Hcell.
              by rewrite Hz0 addw0 Hmem3none' in Hmems3.
            * have Hnc : ~ is_code (taga (vv @ tv)) by rewrite /= Hcodv.
              have Hrelv : is_relevant_comp i (color (taga (vv @ tv))) by rewrite /= Hcolv.
              have [d' [_ Hmems3]] := proj2 (Hmm (vala (pc s)) (vv @ tv) Hnc Hrelv) Hcell.
              by rewrite Hmem3none' in Hmems3.
          + (* NON-running colour pc cell: the documented backward belong corner.  Ruled out at
               runtime by code-region contiguity (the pc only ever addresses running-coloured cells),
               an invariant not available as a state predicate here.  This is the single isolated
               gap of the syscall reflection, dual to the [Jump]/[Bnz] belong corner. *)
            admit. }
      have Hpceq : vala (pc s) = pc3.
      { rewrite (same_pc_eq Hsp Hside Hval) Hpc3 //. }
      have GETCALLs : Instance.table (NC := NC) (vala (pc s)) = Some sc.
      { rewrite Hpceq; exact: GETCALL3. }
      have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
      { move: GETCALL3. Local Transparent mkfmap.
        rewrite /Instance.table /Merged.table mkfmapE /=.
        case: ifP => [_ [= <-] // | _]. by move=> [=]. }
      Local Opaque mkfmap.
      have Halloc3 : alloc_fun (NC := NC) s3 = Some s3' := run_syscall_alloc GETCALL3 CALL3.
      have [s' Hallocs] : exists s', alloc_fun (NC := NC) s = Some s'.
      { move: Halloc3. rewrite {1}/alloc_fun => H3.
        case: (obind_inv H3) => ra_val [Hra3 {}H3].
        case: (obind_inv H3) => u1 [Hjmp3 {}H3].
        case: (obind_inv H3) => reta3 [Hreta3 {}H3].
        case: (obind_inv H3) => ureta3 [Hretchk3 {}H3].
        move: Hretchk3; case: ifP => Hretcol3 Hretchk3; last by []; clear ureta3 Hretchk3.
        case: (obind_inv H3) => sz [Hsz3 {}H3].
        case: (obind_inv H3) => u2 [Hoth3 {}H3].
        case: (obind_inv H3) => len [Hlen3 {}H3].
        case: (obind_inv H3) => uchk3 [Hszchk3 {}H3].
        have Hszbnd : leq (len + 1) (expn 2 (word_size mt - NC)) = true.
        { case E: (leq (len + 1) (expn 2 (word_size mt - NC))) => //.
          rewrite E /= in Hszchk3; discriminate Hszchk3. }
        move: H3; case: ifP => // Hchk3 H3.
        case: (obind_inv H3) => addr3 [Haddr3 {}H3].
        move: H3; rewrite /updm.
        case Hret3 : (regs s3 syscall_ret) => [retv|] //= _.
        (* reflect the three register reads onto [s] (same tag via [data_match]) *)
        have [v_ra Hra_s] := reg_reflect Hrm Hra3.
        have [v_sz Hsz_s] := reg_reflect Hrm Hsz3.
        have [v_ret Hret_s] := reg_reflect Hrm Hret3.
        have E_rat : taga ra_val = InternalJump
          by move: Hjmp3; rewrite /is_jump; case: (taga ra_val).
        have E_sat : taga sz = Other
          by move: Hoth3; rewrite /is_other; case: (taga sz).
        (* running-colour facts for [s], [s3] (shared via [Hcoleq]) *)
        have Hccs : match taga (pc s) with Level _ c => c end = color_of s
          by rewrite -rb_color_ofE.
        have Hcc3 : match taga (pc s3) with Level _ c => c end = color_of s
          by rewrite -rb_color_ofE Hcoleq.
        (* the merged return-cell check forces [reta3] to be running CODE *)
        move: Hretcol3; rewrite Hcc3 => /andP [Hic3 /eqP Hcol3].
        (* the [ra] value is offset-mapped (InternalJump); offset 0 ⇒ same address on [s] *)
        have [off Hoff0] := get_offset_some Hrel.
        have Hz0 := get_offset_zero Hrel Hoff0.
        have [d_ra [Hdm_ra Hra_s2]] := proj1 (Hrm ra ra_val) Hra3.
        have Hvalra : vala d_ra = vala ra_val.
        { have Hdm := Hdm_ra. have Ert := E_rat.
          move: Hdm Ert; case: d_ra {Hdm_ra Hra_s2} => dv dt;
            case: ra_val {Hra3 Hreta3 Hjmp3 Hra_s E_rat}
            => rv rt /= -[Het Hop] Hrt; subst dt rt.
          move: Hop; rewrite /= Hoff0 /= => Hb. by rewrite Hb Hz0 addw0. }
        have Hra_s'' : regs s ra = Some (v_ra @ InternalJump).
        { rewrite E_rat in Hra_s; exact Hra_s. }
        (* reflect the return-address code cell from [s3] to [s] (same address, same tag) *)
        have Hreta3' : mem s3 (vala ra_val) = Some ((vala reta3) @ (taga reta3))
          by rewrite Hreta3; case: (reta3) => ? ? /=.
        have [vr_s Hreta_s] := succ_code_reflect Hcc Hrel Hic3 Hcol3 Hreta3'.
        (* the value of [ra] read on [s] is [v_ra] = [vala d_ra] = [vala ra_val] *)
        have Hdra_eq : v_ra @ InternalJump = d_ra.
        { move: Hra_s2; rewrite Hra_s'' => -[Hde]; exact Hde. }
        have Hvra_eq : v_ra = vala ra_val by rewrite -Hvalra -Hdra_eq.
        have Hretmem_s : mem s v_ra = Some (vr_s @ (taga reta3)) by rewrite Hvra_eq.
        have Hretchk_s : (is_code (taga reta3) && (color (taga reta3) == color_of s)) = true
          by rewrite Hcol3 eqxx andbT; exact Hic3.
        have Hck_s : (if is_code (taga (vr_s @ (taga reta3)))
                         && (color (taga (vr_s @ (taga reta3))) == color_of s)
                      then Some tt else None) = Some tt by rewrite /= Hretchk_s.
        (* size: [Other] tag preserved, value preserved *)
        have Hsz_s'' : regs s syscall_arg1 = Some (v_sz @ Other).
        { rewrite E_sat in Hsz_s; exact Hsz_s. }
        have E_dsv : v_sz = vala sz.
        { have [d_sz [Hdm_sz Hsz_s2]] := proj1 (Hrm syscall_arg1 sz) Hsz3.
          have E_dsat : taga d_sz = Other by rewrite (data_match_taga Hdm_sz).
          have Hv := data_match_other_val (cc := color_of s) (m := M) (i := i) E_dsat Hdm_sz.
          have Hde : Some (v_sz @ Other) = Some d_sz by rewrite -Hsz_s'' Hsz_s2.
          move: Hv Hde; case: d_sz {Hdm_sz Hsz_s2 E_dsat} => dv dt /= Hv [Hd1 Hd2].
          by rewrite Hd1 Hv. }
        (* prefix filter coincides on [s]/[s3] ⇒ same [max_addr] ⇒ same bound check + head block *)
        have Hmpcs : memory_prefix_condition' (mem s) by case: Hgmcs => _ [H _].
        have Hmpcs3 : memory_prefix_condition' (mem s3) by case: Hgmc3 => _ [H _].
        have Hdomm :
          List.filter
            (fun mw : word (word_size mt) => andw mw (@mask mt NC) ==
               @component_memory_prefix mt NC (ssrint.Posz (1 + color_of s))) (domm (mem s))
        = List.filter
            (fun mw : word (word_size mt) => andw mw (@mask mt NC) ==
               @component_memory_prefix mt NC (ssrint.Posz (1 + color_of s))) (domm (mem s3))
          by apply: (match_mem_pref_condition_filter_eq Hrel Hmm Hmpcs Hmpcs3).
        (* convert the s3 bound check + head into s-side via the running colour and filter eq *)
        rewrite Hcc3 -Hdomm in Hchk3 Haddr3.
        (* rebuild [alloc_fun s] *)
        rewrite /alloc_fun Hccs.
        rewrite Hra_s'' obindE; cbn beta.
        rewrite is_jumpE obindE; cbn beta.
        rewrite Hretmem_s obindE; cbn beta.
        rewrite Hck_s obindE; cbn beta.
        rewrite Hsz_s'' obindE; cbn beta.
        rewrite is_otherE obindE; cbn beta.
        rewrite /= E_dsv Hlen3 obindE; cbn beta.
        have Htt : (if leq (len + 1) (expn 2 (word_size mt - NC)) then Some tt else None) = Some tt
          by rewrite Hszbnd.
        rewrite Htt obindE; cbn beta.
        rewrite Hchk3.
        rewrite Haddr3 obindE; cbn beta.
        have Hupd_s : updm (regs s) syscall_ret (addr3 @ Other)
                    = Some (setm (regs s) syscall_ret (addr3 @ Other))
          by rewrite /updm Hret_s.
        rewrite Hupd_s obindE; cbn beta.
        by eexists. }
      (* run_syscall sc s = Some (s', None): [evi s] succeeds (its [rcom] read reflects from [s3]),
         the SERVICE transfer is unconditionally [Some], and [sem sc s = alloc_fun s = Some s']. *)
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: CALL3; rewrite /run_syscall /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 |]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hrun : @run_syscall mt ops lrc_tags Merged.transfer unit sc s = Some (s', None).
      { rewrite /run_syscall Hevi obindE /=.
        rewrite Hsem Hallocs obindE /=.
        by []. }
      exists s', None.
      apply/Exec.stepP.
      eapply step_syscall.
      + exact: (Symbolic.state_eta s).
      + exact Hmemsnone.
      + exact GETCALLs.
      + exact Hrun.
  Admitted.

End RBScratch_Syscall.

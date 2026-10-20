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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.micromega.Lia.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Exec.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.Padding.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.PaddingCorrect.
Require Import MicroPolicies.Recomposition.PaddingSim.
Import PaddingSim.
Require Import MicroPolicies.Recomposition.PaddingFwdJal.
Require Import MicroPolicies.Recomposition.PaddingFwdSys.

Section CodeShiftFwd.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).
Local Notation sizes := (pad_block_sizes (code q) (code q')).
Local Notation lpf c :=
  (fun (l d : nat) =>
     match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) c with
     | Some m => pc0 + m | None => if l == alloc_label then l else d end).

Hypothesis word_of_nat_inj : forall a b,
    a < 2 ^ (word_size mt) -> b < 2 ^ (word_size mt) ->
    @word_of_nat (word_size mt) a = word_of_nat b -> a = b.
Hypothesis Hcount  : size (proc_split (code q)) = size (proc_split (code q')).
Hypothesis Hbound  : pc0 + size (code q) < alloc_label.
Hypothesis Hbound' : pc0 + size padc < alloc_label.
Hypothesis code_tags_wf_q    : forall w a, encode_code (code q) pc0 w = Some a -> is_code (taga a).
Hypothesis code_tags_wf_padc : forall w a, encode_code padc pc0 w = Some a -> is_code (taga a).
Hypothesis fallthrough_aligned : forall n i t,
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  shift_pos sizes (n.+1) = (shift_pos sizes n).+1.
Hypothesis code_last_term : forall n i t,
  n.+1 = size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = true.
Hypothesis bnz_labels_resolved : forall n r l t,
  nth_error (code q) n = Some (MrBnz r l, t) ->
  exists m, findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m.

Variable NC : nat.

Hypothesis alloc_label_lt_NC : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis code_colors_bounded : forall w a,
  encode_code (code q) pc0 w = Some a -> 1 + color (taga a) < 2 ^ NC.

Local Notation st := (@Symbolic.state mt lrc_tags unit).

Local Notation match_pad  := (@PaddingSim.match_pad q q').
Local Notation pad_valid  := (@PaddingSim.pad_valid q q').
Local Notation phia       := (@PaddingSim.phia q q').
Local Notation rel_v      := (@PaddingSim.rel_v q q').
Local Notation addr_ok    := (@PaddingSim.addr_ok q q').
Local Notation memwk      := (@PaddingSim.memwk q q').
Local Notation memwk_bwd  := (@PaddingSim.memwk_bwd q q').
Local Notation wregs      := (@PaddingSim.wregs q q').

Local Notation code_cell_q      := (PaddingSim.code_cell_q Hcount Hbound Hbound').
Local Notation phia_addr_code   := (PaddingSim.phia_addr_code Hcount Hbound Hbound').
Local Notation pc_succ_corr     := (PaddingSim.pc_succ_corr Hcount Hbound Hbound' fallthrough_aligned).
Local Notation jal_corr         := (PaddingSim.jal_corr Hcount Hbound Hbound').
Local Notation bnz_corr         := (PaddingSim.bnz_corr Hcount Hbound Hbound').
Local Notation size_code_le_padc := (PaddingSim.size_code_le_padc Hcount).
Local Notation code_cell_padc   := (PaddingSim.code_cell_padc word_of_nat_inj Hcount Hbound Hbound').
Local Notation jump_target_corr := (PaddingSim.jump_target_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation jump_belong_corr := (PaddingSim.jump_belong_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation encode_code_dom  := (PaddingSim.encode_code_dom word_of_nat_inj).
Local Notation nonterm_succ_lt  := (PaddingSim.nonterm_succ_lt code_last_term).
Local Notation pad_step_fwd_jal := (@PaddingFwdJal.pad_step_fwd_jal q q' word_of_nat_inj Hcount Hbound Hbound'
                                      code_tags_wf_q fallthrough_aligned code_last_term NC).
Local Notation pad_step_fwd_sys := (@PaddingFwdSys.pad_step_fwd_sys q q' word_of_nat_inj Hcount Hbound Hbound'
                                      code_tags_wf_q NC alloc_label_lt_NC code_colors_bounded).

Local Opaque PaddingSim.rel_v.

Lemma pad_step_fwd (s1 s2 s1' : st) (ev : option event) :
  match_pad s1 s2 -> pad_valid s1 -> step_me (NC := NC) s1 s1' ev ->
  exists s2', step_me (NC := NC) s2 s2' ev /\ match_pad s1' s2'.
Proof.
  move=> Hm Hvalid Hstep. inversion Hstep; subst.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [n [im [tm [Hnlt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt Hnlt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hnlt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (n.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hn1.
    have [n' [im' [t' [Hn'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have En' : n.+1 = n'.
    { have Hb1 : n.+1 + pc0 < 2 ^ word_size mt by move: Hn1 Hbw; lia.
      have Hb2 : n' + pc0 < 2 ^ word_size mt by move: Hn'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hn'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes n + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hnlt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + n) = Nop mt.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes n) = Nop mt
      by apply: instr_nop_indep; exact: Hmmq.
    have Hnop2 : decode_instr (vala v2) = Some (Nop mt) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (n.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hn1 Hnth Hterm). exact: (phia_addr_code Hn1). }
      rewrite En'. exact: (Hc2' _ _ Henc2n). }
    have [Hs1' [Hev [Hcur [Hbel [ei1 Hevi1]]]]] := merged_nop_inv Hic Hm1n NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2) (Symbolic.regs s2)
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    -
      eapply step_nop.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hnop2.
      + exact: (merged_nop_intro Hic2 Hm2n Hcur2 Hbel2 Hevi2).
    -
      split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hn1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split; first exact: Hreg.
      split; first exact: Hc1.
      split; first exact: Hc1'.
      split; first exact: Hc2.
      split; first exact: Hc2'.
      split; first exact: Hnc1.
      exact: Hnc2.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Const n r.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Const n r
      by apply: instr_const_indep; exact: Hmmq.
    have Hdec2c : decode_instr (vala v2) = Some (Const n r) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have [vold2 OLD2] := reg_some Hreg OLD.
    have [Hs1' [Hev [Hcur [Hbel [ei1 Hevi1]]]]] := merged_const_inv Hic Hm1n OLD NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
              (setm (Symbolic.regs s2) r ((swcast n) @ Other))
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_const.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: OLD2.
      + apply: merged_const_intro;
          [exact: Hic2 | exact: Hm2n | exact: OLD2 | exact: Hcur2 | exact: Hbel2 | exact: Hevi2].
    - split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split.
      { move=> r0; rewrite !setmE; case E: (r0 == r);
          [ eexists; split; [reflexivity | move=> _; rewrite taga_at vala_at; symmetry; exact: rel_v_Other]
          | exact: (Hreg r0) ]. }
      split; first exact: Hc1.
      split; first exact: Hc1'.
      split; first exact: Hc2.
      split; first exact: Hc2'.
      split; first exact: Hnc1.
      exact: Hnc2.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Mov r1 r2.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Mov r1 r2
      by apply: instr_mov_indep; exact: Hmmq.
    have Hdec2c : decode_instr (vala v2) = Some (Mov r1 r2) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have [Hs1' [Hev [Hcur [Hbel [ei1 Hevi1]]]]]
      := merged_mov_inv Hic Hm1n R1W OLD NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    have [v1r [HR1s Hv1r]] := reg_get Hreg R1W.
    have [vold2 HR2s] := reg_some Hreg OLD.
    exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
              (setm (setm (Symbolic.regs s2) r1 (v1r @ (if is_address t1 then Invalidated else Other)))
                    r2 (v1r @ t1))
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_mov.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: HR1s.
      + exact: HR2s.
      + exact: (merged_mov_intro Hic2 Hm2n HR1s HR2s Hcur2 Hbel2 Hevi2).
    - split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split.
      { move=> r0; rewrite !setmE.
        case E2: (r0 == r2).
        - eexists; split;
            [ reflexivity
            | move=> Hni; rewrite taga_at in Hni; rewrite taga_at vala_at; exact: (Hv1r Hni) ].
        - case E1: (r0 == r1).
          + eexists; split;
              [ reflexivity
              | move=> Hni; rewrite taga_at vala_at; move: Hni; rewrite taga_at;
                case Ea: (is_address t1);
                  [ move=> Hni; by case: (Hni erefl)
                  | move=> _; have Et1 := is_addrF_Other Ea;
                    rewrite Et1 in Hv1r; apply: Hv1r; discriminate ] ].
          + exact: (Hreg r0). }
      split; first exact: Hc1.
      split; first exact: Hc1'.
      split; first exact: Hc2.
      split; first exact: Hc2'.
      split; first exact: Hnc1.
      exact: Hnc2.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Binop op0 r1 r2 r3.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Binop op0 r1 r2 r3
      by apply: instr_binop_indep; exact: Hmmq.
    have Hdec2c : decode_instr (vala v2) = Some (Binop op0 r1 r2 r3) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have [Hs1' [Hev [Ht1 [Ht2 [Hcur [Hbel [ei1 Hevi1]]]]]]]
      := merged_binop_inv Hic Hm1n R1W R2W OLD NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    have HR1s : Symbolic.regs s2 r1 = Some (w1 @ Other).
    { exact: (reg_otherE Hreg R1W Ht1). }
    have HR2s : Symbolic.regs s2 r2 = Some (w2 @ Other).
    { exact: (reg_otherE Hreg R2W Ht2). }
    have [vold3 HR3s] := reg_some Hreg OLD.
    exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
              (setm (Symbolic.regs s2) r3 ((binop_denote op0 w1 w2) @ Other))
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_binop.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: HR1s.
      + exact: HR2s.
      + exact: HR3s.
      + exact: (merged_binop_intro op0 Hic2 Hm2n HR1s HR2s HR3s Hcur2 Hbel2 Hevi2).
    - split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split.
      { move=> r0; rewrite !setmE; case E: (r0 == r3);
          [ eexists; split; [reflexivity | move=> _; rewrite taga_at vala_at; symmetry; exact: rel_v_Other]
          | exact: (Hreg r0) ]. }
      split; first exact: Hc1.
      split; first exact: Hc1'.
      split; first exact: Hc2.
      split; first exact: Hc2'.
      split; first exact: Hnc1.
      exact: Hnc2.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Load r1 r2.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Load r1 r2
      by apply: instr_load_indep; exact: Hmmq.
    have Hdec2c : decode_instr (vala v2) = Some (Load r1 r2) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have [Hs1' [Hev [Ht1 [Hct2 [Hbelt2c [Hcur [Hbel [ei1 Hevi1]]]]]]]]
      := merged_load_inv Hic Hm1n R1W MEM1 OLD NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    have Hbelt2c2 : color (taga v2) == color t2 by rewrite Htag2 -Htm; exact: Hbelt2c.
    have HR1s : Symbolic.regs s2 r1 = Some (w1 @ Other).
    { exact: (reg_otherE Hreg R1W Ht1). }
    have [vm [HMEMs Hvm]] := mem_get Hnc1 MEM1 Hct2.
    have [vold2 HR2s] := reg_some Hreg OLD.
    have Hcq_none : encode_code (code q) pc0 w1 = None
      := encode_none_noncode code_tags_wf_q Hc1' MEM1 Hct2.
    have Hpadc_none : encode_code padc pc0 w1 = None
      := encode_none_noncode code_tags_wf_padc Hc2' HMEMs Hct2.
    exists (@Symbolic.State mt lrc_tags unit
              (setm (Symbolic.mem s2) w1
                 (vm @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1))
              (setm (Symbolic.regs s2) r2 (vm @ (vtag t2)))
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_load.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: HR1s.
      + exact: HMEMs.
      + exact: HR2s.
      + exact: (merged_load_intro Hic2 Hct2 Hm2n HR1s HMEMs HR2s Hcur2 Hbel2 Hbelt2c2 Hevi2).
    - split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split.
      { move=> r0; rewrite !setmE; case E: (r0 == r2);
          [ eexists; split;
              [ reflexivity
              | move=> Hni; rewrite taga_at in Hni; rewrite taga_at vala_at; exact: (Hvm Hni) ]
          | exact: (Hreg r0) ]. }
      split. { apply: (code_fwd_setm Hc1). by rewrite taga_at switch_val_iscode. }
      split. { exact: (code_bwd_setm Hc1' Hcq_none). }
      split. { apply: (code_fwd_setm Hc2). by rewrite taga_at switch_val_iscode. }
      split. { exact: (code_bwd_setm Hc2' Hpadc_none). }
      split.
      { apply: (memrel_fwd Hnc1); first by rewrite !taga_at.
        move=> Hni; rewrite !vala_at taga_at switch_val_vtag; move: Hni;
          rewrite taga_at switch_val_vtag; case Ea: (is_address (vtag t2));
          [ move=> Hni; by case: (Hni erefl)
          | move=> _; have Et2 := is_addrF_Other Ea; rewrite Et2 in Hvm; apply: Hvm; discriminate ]. }
      { apply: (memrel_bwd Hnc2); first by rewrite !taga_at.
        move=> Hni; rewrite !vala_at taga_at switch_val_vtag; move: Hni;
          rewrite taga_at switch_val_vtag; case Ea: (is_address (vtag t2));
          [ move=> Hni; by case: (Hni erefl)
          | move=> _; have Et2 := is_addrF_Other Ea; rewrite Et2 in Hvm; apply: Hvm; discriminate ]. }
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hterm : is_term im = false.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H.
      by destruct im; simpl in H; try discriminate H. }
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Store r1 r2.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Store r1 r2
      by apply: instr_store_indep; exact: Hmmq.
    have Hdec2c : decode_instr (vala v2) = Some (Store r1 r2) by rewrite Hdec2 Hmmp.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n.
    { rewrite Hpw1. exact: (Hc1' _ _ Henc1n). }
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have [Hs1' [Hev [Ht1 [Hctold [Hbelt [Hcur [Hbel [ei1 Hevi1]]]]]]]]
      := merged_store_inv Hic Hm1n R1W R2W OLD NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hbel2 : color (taga v2) == color (taga v2n).
    { rewrite Htag2 -Htm Hvn. exact: Hbel. }
    have Hbelt2 : color (taga v2) == color told by rewrite Htag2 -Htm; exact: Hbelt.
    have HR1s : Symbolic.regs s2 r1 = Some (w1 @ Other).
    { exact: (reg_otherE Hreg R1W Ht1). }
    have [v2r [HR2s Hv2r]] := reg_get Hreg R2W.
    have [vm [HMEMs Hvm]] := mem_get Hnc1 OLD Hctold.
    have Hncq : encode_code (code q) pc0 w1 = None.
    { case E: (encode_code (code q) pc0 w1) => [a|]; last by [].
      exfalso. have Hm := Hc1' _ _ E. move: Hm; rewrite OLD => -[Ha].
      have Hcd := code_tags_wf_q E. rewrite -Ha taga_at Hctold in Hcd. by []. }
    have Hncpadc : encode_code padc pc0 w1 = None.
    { case E: (encode_code padc pc0 w1) => [a|]; last by [].
      exfalso. have Hm := Hc2' _ _ E. move: Hm; rewrite HMEMs => -[Ha].
      have Hcd := code_tags_wf_padc E. rewrite -Ha taga_at Hctold in Hcd. by []. }
    exists (@Symbolic.State mt lrc_tags unit
              (setm (Symbolic.mem s2) w1 (v2r @ (switch_val told t2).1))
              (setm (Symbolic.regs s2) r2 (v2r @ (if is_address t2 then Invalidated else Other)))
              ((vala (Symbolic.pc s2) + 1)%w @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_store.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: HR1s.
      + exact: HR2s.
      + exact: HMEMs.
      + exact: (merged_store_intro Hic2 Hctold Hm2n HR1s HR2s HMEMs Hcur2 Hbel2 Hbelt2 Hevi2).
    - split.
      { rewrite /= Hpcv.
        have Hpcc := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in Hpcc. exact: Hpcc. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split.
      { move=> r0; rewrite !setmE; case E: (r0 == r2);
          [ eexists; split;
              [ reflexivity
              | move=> Hni; rewrite taga_at vala_at; move: Hni; rewrite taga_at;
                case Ea: (is_address t2);
                  [ move=> Hni; by case: (Hni erefl)
                  | move=> _; have Et2 := is_addrF_Other Ea; rewrite Et2 in Hv2r; apply: Hv2r; discriminate ] ]
          | exact: (Hreg r0) ]. }
      split. { apply: (code_fwd_setm Hc1). by rewrite taga_at switch_val_iscode. }
      split. { exact: (code_bwd_setm Hc1' Hncq). }
      split. { apply: (code_fwd_setm Hc2). by rewrite taga_at switch_val_iscode. }
      split. { exact: (code_bwd_setm Hc2' Hncpadc). }
      split.
      { apply: (memrel_fwd Hnc1); first by rewrite !taga_at.
        move=> Hni; rewrite !vala_at taga_at switch_val_vtag; move: Hni;
          rewrite taga_at switch_val_vtag; exact: Hv2r. }
      { apply: (memrel_bwd Hnc2); first by rewrite !taga_at.
        move=> Hni; rewrite !vala_at taga_at switch_val_vtag; move: Hni;
          rewrite taga_at switch_val_vtag; exact: Hv2r. }
  -
    rename pc0 into pcw; rename ti0 into ti.
    have Hmp := Hm.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Jump r.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have Hmmp : instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes k) = Jump r
      by apply: instr_jump_indep; exact: Hmmq.
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hdec2c : decode_instr (vala v2) = Some (Jump r) by rewrite Hdec2 Hmmp.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1. exfalso.
      move: NEXT. by rewrite /next_state_updates_and_pc /next_state /Symbolic.evi E /=. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have [l2 Hl2] : exists l2, Symbolic.reg_clear_list (Symbolic.regs s2) t1 = Some l2.
    { apply: reg_clear_list_aux_total => e He.
      have [a Ha] := reg_clear_list_aux_dom CLEAR He.
      have [b Hb] := reg_some Hreg Ha. by exists (b @ (taga a)). }
    have [v2r [HRs2 Hv2r]] := reg_get Hreg RW.
    have [rav2 HRas2] := reg_some Hreg RA.
    have Hevi1 : Symbolic.evi (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra)
               = Some {| rcom_value := convert (int_of_word (vala a1)) |} by rewrite /Symbolic.evi Ha1.
    rewrite /mvec in NEXT.
    destruct tpc0 as [level ctpc].
    have [Hcolor Hdisj] := jump_step_inv Hic RW RA CLEAR NEXT.
    have Hcoltv2 : color (taga v2) = color ti by rewrite Htag2 -Htm.
    have Hpct' : taga (Symbolic.pc s2) = Level level ctpc by rewrite Hpct.
    case: Hdisj => [[Hbel1 Ht1] | [n0 [celltgt [rcv [Hmw0 [Hbel1 [Ht1 [Hlvl Hrcom]]]]]]]].
    +
      have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   (@Symbolic.State mt lrc_tags unit mem0 reg
                      (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
                   (IVec (OP JUMP) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti (HSeqCons rat l))
                   [:: RegRead ra, RegRead r & reg_clear_read] w
                 = Some (@Symbolic.State mt lrc_tags unit mem0 reg
                           (w@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra, None).
      { apply: jump_internal_nsuap.
        - exact: Hic.
        - by rewrite -Ht1; exact: RW.
        - exact: RA.
        - by rewrite -Ht1; exact: CLEAR.
        - exact: Hbel1.
        - by rewrite /= Hcolor.
        - exact: Hevi1. }
      rewrite HN1 in NEXT; move: NEXT => [= <- <-].
      have Hok : addr_ok mem0 w.
      { have [Hval1 _] := Hvalid. apply: (Hval1 _ _ _ RW). by rewrite Ht1. }
      have Hne1 : t1 <> Invalidated by rewrite Ht1.
      have Ev2r : v2r = phia w.
      { rewrite (Hv2r Hne1) Ht1. exact: rel_v_InternalJump. }
      have HRs2' : Symbolic.regs s2 r = Some ((phia w) @ InternalJump).
      { by rewrite HRs2 Ht1 Ev2r. }
      exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2) (Symbolic.regs s2)
                ((phia w) @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
      split.
      * eapply step_jump.
        - exact: (Symbolic.state_eta s2).
        - rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
        - exact: Hdec2c.
        - exact: HRs2'.
        - exact: HRas2.
        - by rewrite -Ht1; exact: Hl2.
        - apply: jump_internal_nsuap.
          + exact: Hic2.
          + exact: HRs2'.
          + exact: HRas2.
          + by rewrite -Ht1; exact: Hl2.
          + rewrite Hcoltv2. exact: (jump_belong_corr Hmp Hok Hbel1).
          + rewrite Hpct' Hcoltv2. exact: Hcolor.
          + exact: Hevi2.
      * split; first reflexivity.
        split; first exact: Hpct'.
        split; first exact: Hint.
        split; first exact: Hreg.
        split; first exact: Hc1.
        split; first exact: Hc1'.
        split; first exact: Hc2.
        split; first exact: Hc2'.
        split; first exact: Hnc1.
        exact: Hnc2.
    +
      have Ht1' : t1 = Ret level.-1 by rewrite Ht1 Hlvl.
      have Hlv0 : 0 < level by rewrite Hlvl.
      have Hbelne : color ti != color (taga celltgt) by move: Hbel1; rewrite belong_someE.
      have Hrne : r != rcom.
      { apply/eqP => E. move: Hrcom; rewrite -E RW Ht1. by move=> [=]. }
      have Harne : ra != rcom by [].
      have Hwreg : wregs reg (Symbolic.regs s2) := Hreg.
      have [sd1 [sd2 [Hsd1 [Hsd2 [Hwsd [Hmsd1 [Hmsd2 [Hpsd1 [Hpsd2 [Hisd1 Hisd2]]]]]]]]]]
        := return_clear (s1 := @Symbolic.State mt lrc_tags unit mem0 reg
                                  (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
             (s2 := s2) Hwreg RA RW Hrcom Hrne Harne CLEAR.
      have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   (@Symbolic.State mt lrc_tags unit mem0 reg
                      (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
                   (IVec (OP JUMP) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti (HSeqCons rat l))
                   [:: RegRead ra, RegRead r & reg_clear_read] w
                 = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd1) (Symbolic.regs sd1)
                           (w@(build_tpc level.-1 (color (taga celltgt)))) (Symbolic.internal sd1),
                         Some (ERet (color ti) (convert (int_of_word (vala a1))) (color (taga celltgt)))).
      { apply: (@jump_return_nsuap _ sd1 ti r w rav rcv level ctpc rat l celltgt
                  {| Symbolic.rcom_value := convert (int_of_word (vala a1)) |}).
        - exact: Hic.
        - by [].
        - exact: Hcolor.
        - exact: Hmw0.
        - exact: Hbelne.
        - by rewrite -Ht1'; exact: RW.
        - exact: Hrcom.
        - exact: Hlv0.
        - by rewrite -Ht1'; exact: CLEAR.
        - exact: Hevi1.
        - exact: Hsd1. }
      move: NEXT; rewrite HN1 => -[= Hs1eq Heveq].
      have [celltgt2 [Hm2tgt Htceq]] := jump_target_corr Hc1 Hc1' Hc2' Hnc1 Hmw0.
      have Hrcom2 : Symbolic.regs s2 rcom = Some (rcv @ Other) := reg_otherE Hreg Hrcom erefl.
      have Ha1v : vala a1 = rcv.
      { move: Ha1; rewrite Hrcom => -[= <-]. by rewrite vala_at. }
      have Hevi2v : Symbolic.evi s2 = Some {| Symbolic.rcom_value := convert (int_of_word rcv) |}.
      { by rewrite /Symbolic.evi Hrcom2 /=. }
      have Hne1 : t1 <> Invalidated by rewrite Ht1.
      have Ev2r : v2r = phia w by rewrite (Hv2r Hne1) Ht1; exact: rel_v_Ret.
      have HRs2r : Symbolic.regs s2 r = Some ((phia w) @ (Ret level.-1)).
      { by rewrite HRs2 Ev2r Ht1'. }
      have Hbelne2 : color (taga v2) != color (taga celltgt2) by rewrite Hcoltv2 Htceq.
      have HN2 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   s2 (IVec (OP JUMP) (taga (Symbolic.pc s2)) (taga v2) (HSeqCons rat l2))
                   [:: RegRead ra, RegRead r & reg_clear_read] (phia w)
                 = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd2) (Symbolic.regs sd2)
                           ((phia w)@(build_tpc level.-1 (color (taga celltgt2)))) (Symbolic.internal sd2),
                         Some (ERet (color (taga v2)) (convert (int_of_word rcv)) (color (taga celltgt2)))).
      { apply: (@jump_return_nsuap _ sd2 (taga v2) r (phia w) rav2 rcv level ctpc rat l2 celltgt2
                  {| Symbolic.rcom_value := convert (int_of_word rcv) |}).
        - exact: Hic2.
        - exact: Hpct'.
        - by rewrite Hcoltv2.
        - exact: Hm2tgt.
        - exact: Hbelne2.
        - exact: HRs2r.
        - exact: Hrcom2.
        - exact: Hlv0.
        - by rewrite -Ht1'; exact: Hl2.
        - exact: Hevi2v.
        - exact: Hsd2. }
      have Em1 : Symbolic.mem s1' = mem0 by rewrite -Hs1eq; exact: Hmsd1.
      have Er1 : Symbolic.regs s1' = Symbolic.regs sd1 by rewrite -Hs1eq.
      have Epc1 : Symbolic.pc s1' = (w @ (build_tpc level.-1 (color (taga celltgt)))) by rewrite -Hs1eq.
      have Ei1 : Symbolic.internal s1' = Symbolic.internal sd1 by rewrite -Hs1eq.
      set s2w := @Symbolic.State mt lrc_tags unit (Symbolic.mem sd2) (Symbolic.regs sd2)
                   ((phia w)@(build_tpc level.-1 (color (taga celltgt2)))) (Symbolic.internal sd2).
      have Em2 : Symbolic.mem s2w = Symbolic.mem s2 := Hmsd2.
      exists s2w.
      split.
      *
        rewrite -Heveq.
        eapply step_jump.
        - exact: (Symbolic.state_eta s2).
        - rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
        - exact: Hdec2c.
        - exact: HRs2r.
        - exact: HRas2.
        - by rewrite -Ht1'; exact: Hl2.
        - by rewrite HN2 Hcoltv2 Ha1v -Htceq.
      *
        split; first (rewrite Epc1 /s2w !vala_at; reflexivity).
        split; first by rewrite Epc1 /s2w !taga_at Htceq.
        split; first by rewrite Ei1 /s2w Hisd2 Hisd1 Hint.
        split; first by rewrite Er1 /s2w; exact: Hwsd.
        split; first by move=> w0 a; rewrite Em1; exact: (Hc1 w0 a).
        split; first by move=> w0 a; rewrite Em1; exact: (Hc1' w0 a).
        split; first by move=> w0 a; rewrite Em2; exact: (Hc2 w0 a).
        split; first by move=> w0 a; rewrite Em2; exact: (Hc2' w0 a).
        split; first by rewrite Em1 Em2; exact: Hnc1.
        by rewrite Em1 Em2; exact: Hnc2.
  -
    rename pc0 into pcw; rename ti0 into ti.
    move: Hm => [Hpcv [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates, next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Bnz r n.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have HimB : exists r0 l0, im = MrBnz r0 l0.
    { have H := Hmmq.
      destruct im as [ | l0 | i0 r0 | mr1 mr2 | bo b1 b2 b3 | lr1 lr2 | sr1 sr2 | jr | bzr bzl | jl | ];
        simpl in H; try discriminate H. by exists bzr, bzl. }
    move: HimB => [r0 [l0 Him]]; subst im.
    have Hn : n = word_of_nat (lpf (code q) l0 (pc0 + k) - (pc0 + k)).
    { have H := Hmmq. move: H => /= [= _ H2]. by rewrite H2. }
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    pose OFFp := @word_of_nat (imm_size mt)
                   (lpf padc l0 (pc0 + shift_pos sizes k) - (pc0 + shift_pos sizes k)).
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hdec2c : decode_instr (vala v2) = Some (Bnz r OFFp).
    { rewrite Hdec2. have H := Hmmq. move: H => /= [= <- _]. by []. }
    have Hterm : is_term (MrBnz r0 l0) = false by [].
    have Hk1 : k.+1 < size (code q) by apply: (nonterm_succ_lt Hklt Hnth Hterm).
    have Hpw1 : (pcw + 1)%w = word_of_nat (k.+1 + pc0).
    { rewrite Hpweq [X in X = _] word_of_nat_succ. congr word_of_nat. by lia. }
    have [v1n Henc1n] := encode_code_dom Hbw Hk1.
    have [k' [im' [t' [Hk'lt [Hpw' [Hnth' [Htm' Hdec']]]]]]] := code_cell_q Henc1n.
    have Ek' : k.+1 = k'.
    { have Hb1 : k.+1 + pc0 < 2 ^ word_size mt by move: Hk1 Hbw; lia.
      have Hb2 : k' + pc0 < 2 ^ word_size mt by move: Hk'lt Hbw; lia.
      have := word_of_nat_inj Hb1 Hb2 Hpw'. by lia. }
    have [v2n [Henc2n [Htag2n _]]] := code_cell_padc Hk'lt Hnth'.
    have Hm1n : mem0 (pcw + 1)%w = Some v1n by rewrite Hpw1; exact: (Hc1' _ _ Henc1n).
    have Hm2n : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some v2n.
    { rewrite Hpcv.
      have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have Hvn : taga v2n = taga v1n by rewrite Htag2n Htm'.
    have Hpcc : (phia pcw + 1)%w = phia (pcw + 1)%w.
    { have H := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in H. exact: H. }
    have [celln [celln2 [Hmem0pc' [Hmem2pc' [Hcol Hpccorr]]]]] :
      exists celln celln2,
        mem0 (pcw + (if w == 0%w then 1%w else swcast n))%w = Some celln /\
        Symbolic.mem s2 (vala (Symbolic.pc s2) + (if w == 0%w then 1%w else swcast OFFp))%w = Some celln2 /\
        color (taga celln2) = color (taga celln) /\
        (vala (Symbolic.pc s2) + (if w == 0%w then 1%w else swcast OFFp))%w
          = phia (pcw + (if w == 0%w then 1%w else swcast n))%w.
    { destruct (w == 0%w) eqn:Hw0.
      -
        exists v1n, v2n.
        split; first exact: Hm1n.
        split; first exact: Hm2n.
        split; first by rewrite Hvn.
        rewrite Hpcv. exact: Hpcc.
      -
        have [mtgt Hfind] := bnz_labels_resolved Hnth.
        have Hmlt : mtgt < size (code q) by exact: (findopt_lt Hfind).
        have Hlpfq : lpf (code q) l0 (pc0 + k) = pc0 + mtgt by rewrite Hfind.
        have Hbk : mtgt - k < alloc_label by lia.
        have Hjtgt : k + (mtgt - k) < size (code q) by lia.
        have Hpc'q : (pcw + swcast n)%w = word_of_nat ((k + (mtgt - k)) + pc0).
        { rewrite Hpweq Hn Hlpfq.
          have -> : (pc0 + mtgt) - (pc0 + k) = mtgt - k by lia.
          rewrite (addw_word_of_nat_swcast' (k + pc0) Hbk). congr word_of_nat. by lia. }
        have [v1tgt Henc1t] := encode_code_dom Hbw Hjtgt.
        have Hmem0t : mem0 (pcw + swcast n)%w = Some v1tgt
          by rewrite Hpc'q; exact: (Hc1' _ _ Henc1t).
        have [jt [imt [tmt [Hjtlt [Hpwt [Hntht [Htmt Hdect]]]]]]] := code_cell_q Henc1t.
        have Ejt : k + (mtgt - k) = jt.
        { have Hb1 : (k + (mtgt - k)) + pc0 < 2 ^ word_size mt by lia.
          have Hb2 : jt + pc0 < 2 ^ word_size mt by lia.
          have := word_of_nat_inj Hb1 Hb2 Hpwt. by lia. }
        have [v2tgt [Henc2t [Htag2t _]]] := code_cell_padc Hjtlt Hntht.
        have Hpccorr_t : (vala (Symbolic.pc s2) + swcast OFFp)%w = phia (pcw + swcast n)%w.
        { have HB := bnz_corr Hklt Hfind.
          have Hvp : vala (Symbolic.pc s2) = word_of_nat (pc0 + shift_pos sizes k).
          { rewrite Hpcv Hpweq (phia_addr_code Hklt). congr word_of_nat. by lia. }
          have Hpcwk : pcw = word_of_nat (pc0 + k) by rewrite Hpweq; congr word_of_nat; lia.
          rewrite Hvp Hpcwk Hn. exact: HB. }
        have Hmem2t : Symbolic.mem s2 (vala (Symbolic.pc s2) + swcast OFFp)%w = Some v2tgt.
        { rewrite Hpccorr_t Hpc'q (phia_addr_code Hjtgt) Ejt. exact: (Hc2' _ _ Henc2t). }
        exists v1tgt, v2tgt.
        split; first exact: Hmem0t.
        split; first exact: Hmem2t.
        split; first by rewrite Htag2t -Htmt.
        exact: Hpccorr_t. }
    have [Hs1' [Hev [Ht1 [Hcur [Hbel [ei1 Hevi1]]]]]] := merged_bnz_inv Hic RW Hmem0pc' NEXT.
    subst s1' ev.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      move: Hevi1; rewrite /Symbolic.evi E /=. by move=> []. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have HRs : Symbolic.regs s2 r = Some (w @ Other).
    { exact: (reg_otherE Hreg RW Ht1). }
    have Hcur2 : color (taga v2) == match taga (Symbolic.pc s2) with Level _ c => c end.
    { rewrite Htag2 -Htm Hpct. exact: Hcur. }
    have Hbel2 : color (taga v2) == color (taga celln2).
    { rewrite Htag2 -Htm Hcol. exact: Hbel. }
    exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2) (Symbolic.regs s2)
              ((vala (Symbolic.pc s2) + (if w == 0%w then 1%w else swcast OFFp))%w
               @ (taga (Symbolic.pc s2))) (Symbolic.internal s2)).
    split.
    - eapply step_bnz.
      + exact: (Symbolic.state_eta s2).
      + rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
      + exact: Hdec2c.
      + exact: HRs.
      + exact: (merged_bnz_intro Hic2 HRs Hmem2pc' Hcur2 Hbel2 Hevi2).
    - split.
      { rewrite /=. exact: Hpccorr. }
      split; first exact: Hpct.
      split; first exact: Hint.
      split; first exact: Hreg.
      split; first exact: Hc1.
      split; first exact: Hc1'.
      split; first exact: Hc2.
      split; first exact: Hc2'.
      split; first exact: Hnc1.
      exact: Hnc2.
  -
    exact: (pad_step_fwd_jal Hm Hvalid PC RA INST OLD CLEAR NEXT).
  -
    exact: (pad_step_fwd_sys Hm Hvalid PC GETCALL CALL).
Qed.

End CodeShiftFwd.

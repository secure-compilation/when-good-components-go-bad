(* ===== JAL bullet of the forward single-step padding simulation, split into its own file so each
   compile stays within the per-file budget.  Re-opens the [CodeShift] section context (same
   Variables/Hypotheses/notations as PaddingFwd.v) and proves the standalone JAL-case lemma
   [pad_step_fwd_jal], which PaddingFwd.v's [pad_step_fwd] dispatches to. ===== *)
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

Section CodeShiftFwdJal.

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

Local Notation st := (@Symbolic.state mt lrc_tags unit).

(* re-expose the q/q'-parametrized definitions proved in PaddingSim *)
Local Notation match_pad  := (@PaddingSim.match_pad q q').
Local Notation pad_valid  := (@PaddingSim.pad_valid q q').
Local Notation phia       := (@PaddingSim.phia q q').
Local Notation rel_v      := (@PaddingSim.rel_v q q').
Local Notation addr_ok    := (@PaddingSim.addr_ok q q').
Local Notation memwk      := (@PaddingSim.memwk q q').
Local Notation memwk_bwd  := (@PaddingSim.memwk_bwd q q').
Local Notation wregs      := (@PaddingSim.wregs q q').

(* re-expose the q/q'-parametrized helper lemmas — [q]/[q'] are implicit (inferred from args), so
   only the well-formedness hypotheses are pre-applied; the lemma-own args stay implicit. *)
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

Local Opaque PaddingSim.rel_v.

(* forward [reg_clear_list_aux] cons step.  Stated with the tail list [l'] ABSTRACT, so the
   [obind _ (Some _)]/= reductions never unfold the (concrete) recursive call — then applied to the
   concrete [reg_list] tail. *)
Local Lemma rcla_cons_some (e : nat) (l' : seq nat)
   (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
   (t : Symbolic.tag_type lrc_tags Symbolic.R)
   (a : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R))
   (ll : hseq (Symbolic.tag_type lrc_tags) (nseq (S (size l')) Symbolic.R)) :
   rs (as_word (ssrint.Posz e)) = Some a ->
   Symbolic.reg_clear_list_aux l' rs (taga a) = Some ll ->
   Symbolic.reg_clear_list_aux (e :: l') rs t = Some (HSeqCons t ll).
Proof.
  move=> Hr Hll.
  by rewrite reg_clear_list_aux_cons Hr [obind _ (Some a)]/= Hll [obind _ (Some ll)]/=.
Qed.

Lemma pad_step_fwd_jal :
  forall mem0 reg pcw i imm tpc0 ti old told extra l vret tret (s2 s1' : st) (ev : option event),
  match_pad (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) s2 ->
  pad_valid (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) ->
  mem0 pcw = Some (i @ ti) ->
  mem0 (pcw + 1)%w = Some (vret @ tret) ->
  decode_instr i = Some (Jal imm) ->
  reg ra = Some (old @ told) ->
  Symbolic.reg_clear_list reg told = Some l ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra)
     (IVec (OP JAL) tpc0 ti (HSeqCons tret l))
     [:: MemRead (pcw + 1)%w, RegWrite ra (pcw + 1)%w & reg_clear_read] (swcast imm)
   = Some (s1', ev) ->
  exists s2', step_me (NC := NC) s2 s2' ev /\ match_pad s1' s2'.
Proof.
  move=> mem0 reg pcw i imm tpc0 ti old told extra l vret tret s2 s1' ev Hm Hvalid PC RA INST OLD CLEAR NEXT.
    have Hmp := Hm.
    move: Hm => [Hpcv0 [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]].
    have Hpcv : vala (Symbolic.pc s2) = phia pcw. { rewrite Hpcv0. reflexivity. }
    have Hic : is_code ti.
    { case Eic: (is_code ti) => //. exfalso. have NX := NEXT.
      unfold next_state_updates_and_pc, next_state in NX.
      move: NX; case: (mem0 _) => [nn0|]; case: (evi _) => [ei|] /=;
        rewrite ?/Merged.transfer ?/Merged.instr_rules ?Eic /=; by move=> NX2; discriminate NX2. }
    have Henc1 : encode_code (code q) pc0 pcw = Some (i@ti).
    { apply: (Hc1 pcw (i@ti)); [exact: PC | exact: Hic]. }
    have [k [im [tm [Hklt [Hpweq [Hnth [Htm Hdecq]]]]]]] := code_cell_q Henc1.
    have Hmmq : instr_merged_to_mp im (lpf (code q)) (pc0 + k) = Jal imm.
    { have H := Hdecq. have Hvi : vala (i@ti) = i by []. rewrite Hvi INST in H. congruence. }
    have HimJ : exists l0, im = MrJal l0.
    { have H := Hmmq.
      destruct im as [ | l0 | i0 r0 | mr1 mr2 | bo b1 b2 b3 | lr1 lr2 | sr1 sr2 | jr | bzr bzl | jl | ];
        simpl in H; try discriminate H. by exists jl. }
    move: HimJ => [l0 Him]; subst im.
    have Himm : imm = word_of_nat (lpf (code q) l0 (pc0 + k)).
    { have H := Hmmq. by move: H => /= [= H1]. }
    have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have [v2 [Henc2 [Htag2 Hdec2]]] := code_cell_padc Hklt Hnth.
    pose OFFj := @word_of_nat (imm_size mt) (lpf padc l0 (pc0 + shift_pos sizes k)).
    have Hm2pc : Symbolic.mem s2 (phia pcw) = Some ((vala v2) @ (taga v2)).
    { rewrite atom_etaE.
      have -> : phia pcw = word_of_nat (shift_pos sizes k + pc0).
      { rewrite Hpweq. exact: (phia_addr_code Hklt). }
      exact: (Hc2' _ _ Henc2). }
    have Hic2 : is_code (taga v2) by rewrite Htag2 -Htm.
    have Hdec2c : decode_instr (vala v2) = Some (Jal OFFj) by rewrite Hdec2.
    have Hjc : swcast OFFj = phia (swcast imm).
    { rewrite /OFFj Himm. exact: (jal_corr l0 Hklt). }
    have Hok : addr_ok mem0 (swcast imm).
    { rewrite Himm /addr_ok.
      case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q)) => [m|].
      - have Hmlt : m < size (code q) by exact: (findopt_lt Hfo).
        have Hb : pc0 + m < alloc_label by move: Hmlt Hbound; lia.
        rewrite (swcast_word_of_nat_id Hb).
        have [v Hv] := encode_code_dom Hbw Hmlt.
        have -> : @word_of_nat (word_size mt) (pc0 + m) = word_of_nat (m + pc0) by congr word_of_nat; lia.
        left. exists v. exact: (Hc1' _ _ Hv).
      - case Hal: (l0 == alloc_label).
        + move/eqP: Hal => Hal. rewrite Hal swcast_alloc.
          right; left. rewrite (val_word_of_nat alloc_label_lt_word). move: Hbound'; lia.
        + have Hb : pc0 + k < alloc_label by move: Hklt Hbound; lia.
          rewrite (swcast_word_of_nat_id Hb).
          have [v Hv] := encode_code_dom Hbw Hklt.
          have -> : @word_of_nat (word_size mt) (pc0 + k) = word_of_nat (k + pc0) by congr word_of_nat; lia.
          left. exists v. exact: (Hc1' _ _ Hv). }
    have Hterm : is_term (MrJal l0) = false by [].
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
    have Htretn : v1n = vret @ tret.
    { move: RA. rewrite Hm1n. by move=> [= ->]. }
    have Hm2n : Symbolic.mem s2 (phia pcw + 1)%w = Some v2n.
    { have -> : (phia pcw + 1)%w = word_of_nat (shift_pos sizes (k.+1) + pc0).
      { rewrite Hpweq (pc_succ_corr Hk1 Hnth Hterm). exact: (phia_addr_code Hk1). }
      rewrite Ek'. exact: (Hc2' _ _ Henc2n). }
    have Htretn2 : taga v2n = tret.
    { rewrite Htag2n -Htm' Htretn. by rewrite taga_at. }
    have Hm2nt : Symbolic.mem s2 (phia pcw + 1)%w = Some ((vala v2n) @ tret).
    { rewrite Hm2n; congr (Some _); rewrite -Htretn2; exact: (esym (atom_etaE v2n)). }
    have Hretphi : (phia pcw + 1)%w = phia (pcw + 1)%w.
    { have H := pc_succ_corr Hk1 Hnth Hterm. rewrite -Hpweq -Hpw1 in H. exact: H. }
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1. exfalso.
      move: NEXT. by rewrite /next_state_updates_and_pc /next_state /Symbolic.evi E /=. }
    have [ei2 Hevi2] : exists ei, Symbolic.evi s2 = Some ei.
    { have [vrc Hrc] := reg_some Hreg Ha1. rewrite /Symbolic.evi Hrc /=. by eexists. }
    have Hevi1 : Symbolic.evi (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra)
               = Some {| rcom_value := convert (int_of_word (vala a1)) |} by rewrite /Symbolic.evi Ha1.
    have [lh1 Hlh1] : exists lh1, Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) = Some lh1.
    { apply: reg_clear_list_aux_total => e He.
      apply: (reg_clear_list_aux_dom CLEAR). by rewrite in_cons He orbT. }
    have Ha1' : reg (as_word (ssrint.Posz 1)) = Some a1 by exact: Ha1.
    have Hcl1 : Symbolic.reg_clear_list reg told = Some (HSeqCons told lh1).
    { rewrite /Symbolic.reg_clear_list /Symbolic.reg_list.
      exact: (@rcla_cons_some 1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg told a1 lh1 Ha1' Hlh1). }
    have Hleq : l = HSeqCons told lh1 by move: CLEAR; rewrite Hcl1 => -[= <-].
    have [vrc Hrc2] := reg_some Hreg Ha1.
    have [lh2 Hlh2] : exists lh2, Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s2) (taga a1) = Some lh2.
    { apply: reg_clear_list_aux_total => e He.
      have [a Ha] := reg_clear_list_aux_dom Hlh1 He.
      have [b Hb] := reg_some Hreg Ha. by exists (b @ (taga a)). }
    have Hrc2' : Symbolic.regs s2 (as_word (ssrint.Posz 1)) = Some (vrc @ (taga a1)) by exact: Hrc2.
    have HCL2 : Symbolic.reg_clear_list (Symbolic.regs s2) told = Some (HSeqCons told lh2).
    { rewrite /Symbolic.reg_clear_list /Symbolic.reg_list.
      exact: (@rcla_cons_some 1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s2) told (vrc @ (taga a1)) lh2 Hrc2' Hlh2). }
    destruct tpc0 as [level ctpc].
    have [Hcolor [Hcret Hdisj]] := jal_step_inv Hic RA OLD CLEAR NEXT.
    have Hcoltv2 : color (taga v2) = color ti by rewrite Htag2 -Htm.
    have Hpct' : taga (Symbolic.pc s2) = Level level ctpc by rewrite Hpct.
    have [o2 HRa2] : exists o2, Symbolic.regs s2 ra = Some (o2 @ told).
    { have [v2a [HRa2 _]] := reg_get Hreg OLD. by exists v2a. }
    rewrite Hleq in NEXT.
    case: Hdisj => [Hbel1 | [celltgt [rcv [Hmw0 [Hbel1 [Hrcom [u Hentry]]]]]]].
    + (* internal JAL *)
      have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   (@Symbolic.State mt lrc_tags unit mem0 reg
                      (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
                   (IVec (OP JAL) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti
                      (HSeqCons tret (HSeqCons told lh1)))
                   [:: MemRead (pcw + 1)%w, RegWrite ra (pcw + 1)%w & reg_clear_read] (swcast imm)
                 = Some (@Symbolic.State mt lrc_tags unit mem0
                           (setm reg ra ((pcw + 1)%w @ InternalJump))
                           ((swcast imm)@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra, None).
      { apply: jal_internal_nsuap.
        - exact: Hic.
        - exact: RA.
        - exact: OLD.
        - exact: Ha1.
        - exact: Hlh1.
        - exact: Hbel1.
        - by rewrite /= Hcolor.
        - by rewrite /= Hcret.
        - exact: Hevi1. }
      rewrite HN1 in NEXT; move: NEXT => [= <- <-].
      have Hbelphi : belong (color (taga v2))
                       (match Symbolic.mem s2 (swcast OFFj) with Some ni => Some (taga ni) | None => None end).
      { rewrite Hcoltv2 Hjc. exact: (jump_belong_corr Hmp Hok Hbel1). }
      have Hphi : (vala (Symbolic.pc s2) + 1)%w = phia (pcw + 1)%w by rewrite Hpcv; exact: Hretphi.
      have HN2 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   s2
                   (IVec (OP JAL) (taga (Symbolic.pc s2)) (taga v2)
                      (HSeqCons tret (HSeqCons told lh2)))
                   [:: MemRead (vala (Symbolic.pc s2) + 1)%w,
                       RegWrite ra (vala (Symbolic.pc s2) + 1)%w & reg_clear_read]
                   (swcast OFFj)
                 = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
                           (setm (Symbolic.regs s2) ra ((vala (Symbolic.pc s2) + 1)%w @ InternalJump))
                           ((swcast OFFj)@(taga (Symbolic.pc s2))) (Symbolic.internal s2), None).
      { apply: jal_internal_nsuap.
        - exact: Hic2.
        - rewrite Hpcv Hm2nt; reflexivity.
        - exact: HRa2.
        - exact: Hrc2.
        - rewrite taga_at; exact: Hlh2.
        - exact: Hbelphi.
        - rewrite Hcoltv2; move: Hpct'; case: (taga (Symbolic.pc s2)) => lvl c0 [= _ ->]; exact: Hcolor.
        - rewrite Hcoltv2; exact: Hcret.
        - exact: Hevi2. }
      exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
                (setm (Symbolic.regs s2) ra ((vala (Symbolic.pc s2) + 1)%w @ InternalJump))
                ((swcast OFFj)@(taga (Symbolic.pc s2))) (Symbolic.internal s2)).
      split.
      * eapply step_jal.
        - exact: (Symbolic.state_eta s2).
        - rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
        - rewrite /Symbolic.pcv Hpcv Hm2nt; reflexivity.
        - exact: Hdec2c.
        - exact: HRa2.
        - exact: HCL2.
        - exact: HN2.
      * split; first exact: Hjc.
        split; first exact: Hpct'.
        split; first exact: Hint.
        split; first exact: (wregs_setm_ij Hreg Hphi).
        split; first exact: Hc1.
        split; first exact: Hc1'.
        split; first exact: Hc2.
        split; first exact: Hc2'.
        split; first exact: Hnc1.
        exact: Hnc2.
    + (* cross-component CALL *)
      have Hbelne : color ti != color (taga celltgt) by move: Hbel1; rewrite belong_someE.
      have Hentry' : check_entry (color ti) (Some (taga celltgt)) = Some tt by move: Hentry; case: u.
      have [p Hpname] : exists p, get_proc_name (Some (taga celltgt)) = Some p.
      { move: Hentry; rewrite /check_entry /get_proc_name.
        case: (taga celltgt) => [vt cc0 ee ic].
        case: ee => [[pp el]|] /= H; last by [].
        by exists pp. }
      have Ea1 : a1 = rcv @ Other by move: Ha1; rewrite Hrcom => -[= <-].
      have Hta1 : taga a1 = Other by rewrite Ea1 taga_at.
      have Hva1 : vala a1 = rcv by rewrite Ea1 vala_at.
      have Hdom : forall kk, kk \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
                    exists a, reg (as_word (ssrint.Posz kk)) = Some a.
      { move=> kk Hkk; exact: (reg_clear_list_aux_dom Hlh1 Hkk). }
      have [a0 Ha0] : exists a, reg (as_word (ssrint.Posz 0)) = Some a by apply: Hdom.
      (* expose s1's clear tail [cc] : lh1 = HSeqCons Other cc *)
      have [cc Hcc] : exists cc, Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a0) = Some cc.
      { apply: reg_clear_list_aux_total => kk Hkk. apply: Hdom. by rewrite in_cons Hkk orbT. }
      have Hlh1' : lh1 = HSeqCons (taga a1) cc.
      { have H := @rcla_cons_some 0 [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) a0 cc Ha0 Hcc.
        by move: Hlh1; rewrite H => -[= <-]. }
      rewrite Hlh1' Hta1 in NEXT.
      (* expose s2's clear tail [cc2] : lh2 = HSeqCons Other cc2 *)
      have [b0 Hb0] := reg_some Hreg Ha0.
      have [cc2 Hcc2] : exists cc2, Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s2) (taga (b0 @ (taga a0))) = Some cc2.
      { apply: reg_clear_list_aux_total => kk Hkk.
        have Hkk0 : kk \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N by rewrite in_cons Hkk orbT.
        have [a Ha] := Hdom kk Hkk0.
        have [b Hb] := reg_some Hreg Ha. by exists (b @ (taga a)). }
      have Hlh2' : lh2 = HSeqCons (taga a1) cc2.
      { have H := @rcla_cons_some 0 [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s2) (taga a1) (b0 @ (taga a0)) cc2 Hb0 Hcc2.
        by move: Hlh2; rewrite H => -[= <-]. }
      have HCL2c : Symbolic.reg_clear_list (Symbolic.regs s2) told = Some (HSeqCons told (HSeqCons Other cc2)).
      { by rewrite HCL2 Hlh2' Hta1. }
      have Hras2 : Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some ((vala v2n) @ tret) by rewrite Hpcv Hm2nt.
      have Hphi : (vala (Symbolic.pc s2) + 1)%w = phia (pcw + 1)%w by rewrite Hpcv; exact: Hretphi.
      have [sd1 [sd2 [Hsd1 [Hsd2 [Hwsd [Hmsd1 [Hmsd2 [Hpsd1 [Hpsd2 [Hisd1 Hisd2]]]]]]]]]]
        := jal_call_clear (s1 := @Symbolic.State mt lrc_tags unit mem0 reg
                                   (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
             (s2 := s2) level Hreg OLD HRa2 Hrcom RA Hras2 Hphi Hdom.
      have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   (@Symbolic.State mt lrc_tags unit mem0 reg
                      (pcw@((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) extra)
                   (IVec (OP JAL) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti
                      (HSeqCons tret (HSeqCons told (HSeqCons Other cc))))
                   [:: MemRead (pcw + 1)%w, RegWrite ra (pcw + 1)%w & reg_clear_read] (swcast imm)
                 = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd1) (Symbolic.regs sd1)
                           ((swcast imm)@(build_tpc (level.+1) (color (taga celltgt)))) (Symbolic.internal sd1),
                         Some (ECall (color ti) p (convert (int_of_word (vala a1))) (color (taga celltgt)))).
      { apply: (@jal_call_nsuap _ sd1 ti (swcast imm) tret told level ctpc p cc celltgt
                  {| Symbolic.rcom_value := convert (int_of_word (vala a1)) |}).
        - exact: Hic.
        - by [].
        - exact: Hcolor.
        - exact: Hcret.
        - exact: Hmw0.
        - exact: Hbelne.
        - exact: Hpname.
        - exact: Hentry'.
        - exact: Hevi1.
        - exact: Hsd1. }
      move: NEXT; rewrite HN1 => -[= Hs1eq Heveq].
      have [celltgt2 [Hm2tgt Htceq]] := jump_target_corr Hc1 Hc1' Hc2' Hnc1 Hmw0.
      have Hm2tgt' : Symbolic.mem s2 (swcast OFFj) = Some celltgt2 by rewrite Hjc.
      have Hbelne2 : color (taga v2) != color (taga celltgt2) by rewrite Hcoltv2 Htceq.
      have Hrcom2 : Symbolic.regs s2 rcom = Some (rcv @ Other) := reg_otherE Hreg Hrcom erefl.
      have Hevi2v : Symbolic.evi s2 = Some {| Symbolic.rcom_value := convert (int_of_word rcv) |}.
      { by rewrite /Symbolic.evi Hrcom2. }
      have HN2 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                   s2 (IVec (OP JAL) (taga (Symbolic.pc s2)) (taga v2)
                          (HSeqCons tret (HSeqCons told (HSeqCons Other cc2))))
                   [:: MemRead (vala (Symbolic.pc s2) + 1)%w, RegWrite ra (vala (Symbolic.pc s2) + 1)%w & reg_clear_read]
                   (swcast OFFj)
                 = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd2) (Symbolic.regs sd2)
                           ((swcast OFFj)@(build_tpc (level.+1) (color (taga celltgt2)))) (Symbolic.internal sd2),
                         Some (ECall (color (taga v2)) p (convert (int_of_word rcv)) (color (taga celltgt2)))).
      { apply: (@jal_call_nsuap _ sd2 (taga v2) (swcast OFFj) tret told level ctpc p cc2 celltgt2
                  {| Symbolic.rcom_value := convert (int_of_word rcv) |}).
        - exact: Hic2.
        - exact: Hpct'.
        - by rewrite Hcoltv2.
        - by rewrite Hcoltv2.
        - exact: Hm2tgt'.
        - exact: Hbelne2.
        - by rewrite Htceq.
        - by rewrite Hcoltv2 Htceq.
        - exact: Hevi2v.
        - exact: Hsd2. }
      have Em1 : Symbolic.mem s1' = mem0 by rewrite -Hs1eq; exact: Hmsd1.
      have Er1 : Symbolic.regs s1' = Symbolic.regs sd1 by rewrite -Hs1eq.
      have Epc1 : Symbolic.pc s1' = ((swcast imm) @ (build_tpc (level.+1) (color (taga celltgt)))) by rewrite -Hs1eq.
      have Ei1 : Symbolic.internal s1' = Symbolic.internal sd1 by rewrite -Hs1eq.
      set s2w := @Symbolic.State mt lrc_tags unit (Symbolic.mem sd2) (Symbolic.regs sd2)
                   ((swcast OFFj)@(build_tpc (level.+1) (color (taga celltgt2)))) (Symbolic.internal sd2).
      have Em2 : Symbolic.mem s2w = Symbolic.mem s2 := Hmsd2.
      exists s2w.
      split.
      * rewrite -Heveq.
        eapply step_jal.
        - exact: (Symbolic.state_eta s2).
        - rewrite /Symbolic.pcv Hpcv. exact: Hm2pc.
        - rewrite /Symbolic.pcv Hpcv Hm2nt; reflexivity.
        - exact: Hdec2c.
        - exact: HRa2.
        - exact: HCL2c.
        - by rewrite HN2 Hcoltv2 Hva1 -Htceq.
      * split; first (rewrite Epc1 /s2w !vala_at; exact: Hjc).
        split; first by rewrite Epc1 /s2w !taga_at Htceq.
        split; first by rewrite Ei1 /s2w Hisd2 Hisd1 Hint.
        split; first by rewrite Er1 /s2w; exact: Hwsd.
        split; first by move=> w0 a; rewrite Em1; exact: (Hc1 w0 a).
        split; first by move=> w0 a; rewrite Em1; exact: (Hc1' w0 a).
        split; first by move=> w0 a; rewrite Em2; exact: (Hc2 w0 a).
        split; first by move=> w0 a; rewrite Em2; exact: (Hc2' w0 a).
        split; first by rewrite Em1 Em2; exact: Hnc1.
        by rewrite Em1 Em2; exact: Hnc2.
Qed.

End CodeShiftFwdJal.

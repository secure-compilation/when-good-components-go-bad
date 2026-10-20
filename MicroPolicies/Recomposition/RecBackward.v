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

Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.Definitions.
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceWF(nsuap_event_inv).
Import TraceBracket(jal_do_updates_result).
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.RecompositionInit.
Require Import MicroPolicies.Recomposition.PcColor.

Module RecBackward (S: RecompositionContext) (A: AlignmentFacts S).

  Module PC := RecPcColor S A.
  Include PC.
  Import PCCM.

  Lemma common_combined_left  : forall m s1 s2 s3, common_equiv m s1 s2 s3 -> combined_codes Left  s1 s3.
  Proof. move=> m s1 s2 s3 H; destruct H; assumption. Qed.
  Lemma common_combined_right : forall m s1 s2 s3, common_equiv m s1 s2 s3 -> combined_codes Right s2 s3.
  Proof. move=> m s1 s2 s3 H; destruct H; assumption. Qed.
  Lemma common_color_valid1 : forall m s1 s2 s3,
    common_equiv m s1 s2 s3 -> (color_of s1 \in domm ip) || (color_of s1 \in domm ic).
  Proof.
    move=> m s1 s2 s3 H.
    destruct H as [? sa sb sc ? cc Htag1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hval ? ?].
    rewrite (color_of_pc_tag sa) Htag1; exact Hval.
  Qed.
  Lemma common_color_valid2 : forall m s1 s2 s3,
    common_equiv m s1 s2 s3 -> (color_of s2 \in domm ip) || (color_of s2 \in domm ic).
  Proof.
    move=> m s1 s2 s3 H.
    destruct H as [? sa sb sc ? cc Htag1 Htag2 ? ? ? ? ? ? ? ? ? ? ? ? ? Hval ? ?].
    rewrite (color_of_pc_tag sb) Htag2; exact Hval.
  Qed.
  Lemma common_color_eq12 : forall m s1 s2 s3, common_equiv m s1 s2 s3 -> color_of s1 = color_of s2.
  Proof.
    move=> m s1 s2 s3 H.
    destruct H as [? sa sb sc n0 cc Htag1 Htag2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
    by rewrite (color_of_pc_tag sa) (color_of_pc_tag sb) Htag1 Htag2.
  Qed.
  Lemma common_gmc1 : forall m s1 s2 s3,
    common_equiv m s1 s2 s3 -> general_memory_correctness (mem s1).
  Proof. move=> m s1 s2 s3 H; destruct H as [? ? ? ? ? ? ? ? ? ? ? ? ? Hg ? ? ? ? ? ? ? ? ?]; exact Hg. Qed.
  Lemma common_gmc2 : forall m s1 s2 s3,
    common_equiv m s1 s2 s3 -> general_memory_correctness (mem s2).
  Proof. move=> m s1 s2 s3 H; destruct H as [? ? ? ? ? ? ? ? ? ? ? ? ? ? Hg ? ? ? ? ? ? ? ?]; exact Hg. Qed.
  Lemma common_gmc3 : forall m s1 s2 s3,
    common_equiv m s1 s2 s3 -> general_memory_correctness (mem s3).
  Proof. move=> m s1 s2 s3 H; destruct H as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hg ? ? ? ? ? ? ?]; exact Hg. Qed.
  Lemma strong_same_pc : forall i m s s', strong_equiv i m s s' -> same_pc i s s'.
  Proof. move=> i m s s' H; destruct H; assumption. Qed.
  Lemma strong_side : forall i m s s', strong_equiv i m s s' -> side_of (color_of s) = i.
  Proof. move=> i m s s' H; destruct H; assumption. Qed.
  Lemma strong_color_eq : forall i m s s', strong_equiv i m s s' -> color_of s = color_of s'.
  Proof. move=> i m s s' H; destruct H; assumption. Qed.

  Lemma final_me_cell : forall s,
    final_state_me s ->
    exists d, mem s (vala (pc s)) = Some d /\ decode_instr (vala d) = Some (Halt _) /\ is_code (taga d).
  Proof.
    move=> [m r [pcv tp] int]; rewrite /final_state_me /=.
    case E: (m pcv) => [[v t]|] // [Hd Hc]. by exists (v @ t).
  Qed.
  Lemma final_me_intro : forall (s : state) (d : atom (mword mt) mem_tag),
    mem s (vala (pc s)) = Some d -> decode_instr (vala d) = Some (Halt _) ->
    is_code (taga d) -> final_state_me s.
  Proof.
    move=> [m r [pcv tp] int] [v t] /= Hmem Hd Hc.
    rewrite /final_state_me /= Hmem /=. by split.
  Qed.
  Lemma final_rUB_intro : forall (s : state) (d : atom (mword mt) mem_tag),
    mem s (vala (pc s)) = Some d -> decode_instr (vala d) = Some (Halt _) ->
    is_code (taga d) -> final_state_rUB s.
  Proof.
    move=> [m r [pcv tp] int] [v t] /= Hmem Hd Hc.
    rewrite /final_state_rUB /= Hmem /=. by split; [ | move=> _ ].
  Qed.

  Lemma get_offset_some : forall i c, is_relevant_comp i c -> exists off, get_offset i c = Some off.
  Proof.
    move=> [] c Hrel /=.
    - have : c \in domm offset1 by rewrite offset1_domm.
      by rewrite mem_domm; case: (offset1 c) => [o|] // _; exists o.
    - have : c \in domm offset2 by rewrite offset2_domm.
      by rewrite mem_domm; case: (offset2 c) => [o|] // _; exists o.
  Qed.

  Lemma same_pc_cases : forall i (s s3 : state),
    same_pc i s s3 ->
    (exists v off, (mem s (vala (pc s)) = Some v /\ is_code (taga v))
       /\ get_offset i (color_of s) = Some off
       /\ vala (pc s3) = addw (vala (pc s)) (as_word off))
    \/ (vala (pc s) = vala (pc s3) /\ mem s (vala (pc s)) = None /\ mem s3 (vala (pc s3)) = None).
  Proof.
    move=> i s s3 Hsp.
    inversion Hsp as [u u' Hpe Hnone | u u' v off Hcell Hoff Hpc3]; subst.
    - right. split; [exact Hpe | exact Hnone].
    - left. exists v, off. split; [exact Hcell | split; [exact Hoff | exact Hpc3]].
  Qed.

  Lemma final_reflect_strong : forall (i : side) (s s3 : state),
    combined_codes i s s3 -> same_pc i s s3 -> color_of s = color_of s3 ->
    side_of (color_of s) = i -> (color_of s \in domm ip) || (color_of s \in domm ic) ->
    pc_color_inv s3 -> final_state_me s3 ->
    exists d, mem s (vala (pc s)) = Some d /\ decode_instr (vala d) = Some (Halt _) /\ is_code (taga d).
  Proof.
    move=> i s s3 Hcc Hsp Hcoleq Hside Hval Hpci Hf3.
    have [d3 [Hd3 [Hdec3 Hcode3]]] := final_me_cell Hf3.
    have Hrel : is_relevant_comp i (color_of s) by apply: is_relevant_comp_of_side.
    have Hcolor : color (taga d3) = color_of s by rewrite (Hpci d3 Hd3) Hcoleq.
    move: Hd3 Hdec3 Hcode3 Hcolor; case: d3 => vd td; cbn [vala taga] => Hd3 Hdec3 Hcode3 Hcolor.
    inversion Hsp as [u u' Hpe Hnone | u u' v off Hcell Hoff Hpc3]; subst.
    -
      exfalso.
      by rewrite (proj2 Hnone) in Hd3.
    -
      have Hd3' : mem s3 (addw (vala (pc s)) (as_word off)) = Some (vd @ td)
        by rewrite -Hpc3.
      have [v' [Hdm Hmems]] :=
        proj2 (Hcc (vala (pc s)) vd td off (color_of s) Hrel Hoff Hcode3 Hcolor) Hd3'.
      have Hv' : v' = vd.
      { inversion Hdm as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld];
          subst => //.
        - by move: Ha2; rewrite Hdec3.
        - by move: Hj2; rewrite Hdec3. }
      exists (v' @ td); split; [ exact Hmems | ].
      rewrite Hv' /=. by split.
  Qed.

  Lemma notfinal_reflect : forall M s1 s2 s3,
    match_states M s1 s2 s3 -> pc_color_inv s3 ->
    ~ final_state_rUB s1 -> ~ final_state_me s2 -> ~ final_state_me s3.
  Proof.
    move=> M s1 s2 s3 Hms Hpci Hnf1 Hnf2 Hf3.
    inversion Hms as [M0 sa sb sc Hcom HstrL HwkR | M0 sa sb sc Hcom HwkL HstrR]; subst.
    - have [d [Hcell [Hdec Hcode]]] := final_reflect_strong
        (common_combined_left Hcom) (strong_same_pc HstrL) (strong_color_eq HstrL)
        (strong_side HstrL) (common_color_valid1 Hcom) Hpci Hf3.
      exact: (Hnf1 (final_rUB_intro Hcell Hdec Hcode)).
    - have [d [Hcell [Hdec Hcode]]] := final_reflect_strong
        (common_combined_right Hcom) (strong_same_pc HstrR) (strong_color_eq HstrR)
        (strong_side HstrR) (common_color_valid2 Hcom) Hpci Hf3.
      exact: (Hnf2 (final_me_intro Hcell Hdec Hcode)).
  Qed.

  Lemma strong_registers_match : forall i m s s', strong_equiv i m s s' -> registers_match i m s s'.
  Proof. move=> i m s s' H; destruct H; assumption. Qed.
  Lemma strong_memory_match : forall i m s s', strong_equiv i m s s' -> memory_match i m s s'.
  Proof. move=> i m s s' H; destruct H; assumption. Qed.

  Lemma valid_of_relevant : forall i c,
    is_relevant_comp i c -> (c \in domm ip) || (c \in domm ic).
  Proof. move=> [] c H /=; by rewrite H ?orbT. Qed.

  Lemma pc_cell_reflect : forall (i : side) (s s3 : state) d3,
    combined_codes i s s3 -> same_pc i s s3 -> color_of s = color_of s3 ->
    side_of (color_of s) = i -> (color_of s \in domm ip) || (color_of s \in domm ic) ->
    pc_color_inv s3 -> mem s3 (vala (pc s3)) = Some d3 -> is_code (taga d3) ->
    exists d, mem s (vala (pc s)) = Some d /\
              decode_match i (mem s) (mem s3) (vala d) (vala d3) /\ taga d = taga d3.
  Proof.
    move=> i s s3 d3 Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
    have Hrel : is_relevant_comp i (color_of s) by apply: is_relevant_comp_of_side.
    have Hcolor : color (taga d3) = color_of s by rewrite (Hpci d3 Hd3) Hcoleq.
    move: Hd3 Hcode3 Hcolor; case: d3 => vd td; cbn [vala taga] => Hd3 Hcode3 Hcolor.
    inversion Hsp as [u u' Hpe Hnone | u u' v off Hcell Hoff Hpc3]; subst.
    - exfalso.
      by rewrite (proj2 Hnone) in Hd3.
    - have Hd3' : mem s3 (addw (vala (pc s)) (as_word off)) = Some (vd @ td)
        by rewrite -Hpc3.
      have [v' [Hdm Hmems]] :=
        proj2 (Hcc (vala (pc s)) vd td off (color_of s) Hrel Hoff Hcode3 Hcolor) Hd3'.
      exists (v' @ td); cbn [vala taga]; split; [ exact Hmems | by split ].
  Qed.

  Lemma merged_transfer_iscode : forall (op : opcode) tpc ti ts tni i r,
    Merged.transfer (IVec (OP op) tpc ti ts tni) i = Some r -> is_code ti = true.
  Proof.
    move=> op tpc ti ts tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules] => H.
    apply obind_inv in H; destruct H as [out [Hir _]].
    apply obind_inv in Hir; destruct Hir as [u1 [Hg1 _]].
    move: Hg1; case: (is_code ti) => Hg1; [ done | discriminate Hg1 ].
  Qed.

  Lemma nsu_transfer_iscode : forall (s : state) (op : opcode) tpc ti
      (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' res,
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
      (IVec (OP op) tpc ti ts) updts pc' = Some res -> is_code ti = true.
  Proof.
    move=> s op tpc ti ts updts pc' res.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi s) => [evinp|] //=.
    case Hm: (mem s pc') => [ni|] /= H.
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (merged_transfer_iscode Htr).
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (merged_transfer_iscode Htr).
  Qed.

  Lemma merged_silent_next_pc_belong :
    forall (st s' : state) op tpc ti (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc',
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st
        (IVec (OP op) tpc ti ts) updts pc' = Some (s', None) ->
      pc s' = pc'@tpc /\
      belong (match tpc with Level _ c => c end)
             (match mem st pc' with Some ni => Some (taga ni) | None => None end).
  Proof.
    move=> st s' op tpc ti ts updts pc' H.
    exact: (silent_next_pc_belong (nsu_and_pc_bridge H)).
  Qed.

  Lemma succ_code_reflect : forall (i : side) (s s3 : state) (w0 : mword mt) off v3 t3,
    combined_codes i s s3 ->
    is_relevant_comp i (color_of s) ->
    get_offset i (color_of s) = Some off ->
    is_code t3 -> color t3 = color_of s ->
    mem s3 (addw w0 (as_word off)) = Some (v3 @ t3) ->
    exists v', mem s w0 = Some (v' @ t3).
  Proof.
    move=> i s s3 w0 off v3 t3 Hcc Hrel Hoff Hcode Hcolor Hmem3.
    have [v' [Hdm Hmems]] :=
      proj2 (Hcc w0 v3 t3 off (color_of s) Hrel Hoff Hcode Hcolor) Hmem3.
    by exists v'.
  Qed.

  Lemma reg_reflect : forall i M s s3 r d3,
    registers_match i M s s3 ->
    regs s3 r = Some d3 ->
    exists v', regs s r = Some (v' @ (taga d3)).
  Proof.
    move=> i M s s3 r d3 Hrm Hr3.
    have [d' [Hdm Hr]] := proj1 (Hrm r d3) Hr3.
    move: Hdm Hr. case: d' => v' t'. case: d3 Hr3 => v3 t3 Hr3 /=.
    move=> [Htt _] Hr. subst t'. by exists v'.
  Qed.

  Definition code_present (codemem : memory) (s : state) : Prop :=
    forall w v0, codemem w = Some v0 -> exists v, mem s w = Some v /\ is_code (taga v).

  Lemma rb_belong_someE : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
    belong c (Some t) = (c == color t).
  Proof. by move=> c [vt ct et ict]. Qed.

  Lemma rb_evi_reflect : forall i M s s3,
    registers_match i M s s3 -> (exists a3, regs s3 rcom = Some a3) -> exists ei, evi s = Some ei.
  Proof.
    move=> i M s s3 Hrm [a3 Hrcom3].
    have [a' Ha'] := reg_reflect Hrm Hrcom3.
    rewrite /evi Ha'. by eexists.
  Qed.

  Lemma nsuap_evi_reflect : forall i M (s s3 : state) iv updts pc' res,
    registers_match i M s s3 ->
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s3 iv updts pc' = Some res ->
    exists ei, evi s = Some ei.
  Proof.
    move=> i M s s3 iv updts pc' res Hrm NEXT3.
    apply: (rb_evi_reflect Hrm).
    move: NEXT3; rewrite /next_state_updates_and_pc /next_state /evi.
    by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ].
  Qed.

  Lemma strong_reg_addr2 : forall i m s s',
    strong_equiv i m s s' -> register_address_correctness i s'.
  Proof. by move=> i m s s' [? ? ? ? ? ? ? H ? ?]. Qed.

  Lemma rb_updm_some {St : Type} (m : {fmap reg mt -> St}) k a v :
    m k = Some a -> updm m k v = Some (setm m k v).
  Proof. by rewrite /updm => ->. Qed.

  Lemma rb_binop_is_other : forall b tpc ti (t1 t2 told : tag_type lrc_tags R) tni i r,
    Merged.transfer (IVec (OP (BINOP b)) tpc ti [hseq t1; t2; told] tni) i = Some r ->
    is_other t1 = Some tt /\ is_other t2 = Some tt.
  Proof.
    move=> b tpc ti t1 t2 told tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules] => H.
    apply obind_inv in H; destruct H as [out [Hir _]].
    apply obind_inv in Hir; destruct Hir as [u1 [_ Hir]].
    apply obind_inv in Hir; destruct Hir as [u2 [_ Hir]].
    apply obind_inv in Hir; destruct Hir as [lout [Hlrc _]].
    move: Hlrc; clear r out u1 u2; rewrite /LRC.instr_rules.
    move: lout; case: ti => vti cti eti icti; case: tpc => lpc cpc => lout; cbv zeta.
    case: (cti == cpc) => //=.
    move=> Hg.
    apply obind_inv in Hg; destruct Hg as [v1 [Ho1 Hg]].
    apply obind_inv in Hg; destruct Hg as [v2 [Ho2 _]].
    by rewrite Ho1 Ho2; move: Ho1 Ho2; case: v1 => _; case: v2 => _.
  Qed.

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

  Lemma rb_is_other_eq : forall t : value_tag, is_other t = Some tt -> t = Other.
  Proof. by case. Qed.

  Lemma rb_store_gates : forall tpc ti (t1 t2 : tag_type lrc_tags R)
      (told : tag_type lrc_tags M) tni i r,
    Merged.transfer (IVec (OP STORE) tpc ti [hseq t1; t2; told] tni) i = Some r ->
    is_other t1 = Some tt /\ is_code told = false /\ color ti = color told.
  Proof.
    move=> tpc ti t1 t2 told tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules] => H.
    apply obind_inv in H; destruct H as [out [Hir _]].
    apply obind_inv in Hir; destruct Hir as [u1 [_ Hir]].
    apply obind_inv in Hir; destruct Hir as [u2 [Hg2 Hir]].
    have Hicfalse : is_code told = false.
    { by move: Hg2; case: (is_code told). }
    apply obind_inv in Hir; destruct Hir as [lout [Hlrc _]].
    move: Hlrc; clear r out u1 u2 Hg2; rewrite /LRC.instr_rules.
    move: lout Hicfalse; case: ti => vti cti eti icti; case: tpc => lpc cpc => lout Hicfalse;
      cbv zeta.
    case: (cti == cpc) => //=.
    move=> Hg.
    apply obind_inv in Hg; destruct Hg as [v1 [Ho1 Hg]].
    apply obind_inv in Hg; destruct Hg as [v2 [_ Hg]].
    apply obind_inv in Hg; destruct Hg as [v3 [Hbel _]].
    move: Hbel Hicfalse; rewrite /check_belong /belong.
    case: told => vtd ctd etd ictd /=.
    case Hbe: (cti == ctd) => //= _ Hicfalse.
    split; last (split; [exact Hicfalse | exact/eqP]).
    by move: Ho1; case: t1 => //=.
  Qed.

  Lemma nsu_store_gates : forall (s : @Symbolic.state mt lrc_tags unit) tpc ti
      (t1 t2 : tag_type lrc_tags R) (told : tag_type lrc_tags M) updts pc' res,
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
      (IVec (OP STORE) tpc ti [hseq t1; t2; told]) updts pc' = Some res ->
    is_other t1 = Some tt /\ is_code told = false /\ color ti = color told.
  Proof.
    move=> s tpc ti t1 t2 told updts pc' res.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi s) => [evinp|] //=.
    case Hm: (mem s pc') => [ni|] /= H.
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_store_gates Htr).
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_store_gates Htr).
  Qed.

  Lemma rb_bnz_is_other : forall tpc ti (t1 : tag_type lrc_tags R) tni i r,
    Merged.transfer (IVec (OP BNZ) tpc ti [hseq t1] tni) i = Some r ->
    is_other t1 = Some tt.
  Proof.
    move=> tpc ti t1 tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules] => H.
    apply obind_inv in H; destruct H as [out [Hir _]].
    apply obind_inv in Hir; destruct Hir as [u1 [_ Hir]].
    apply obind_inv in Hir; destruct Hir as [u2 [_ Hir]].
    apply obind_inv in Hir; destruct Hir as [lout [Hlrc _]].
    move: Hlrc; clear r out u1 u2; rewrite /LRC.instr_rules.
    move: lout; case: ti => vti cti eti icti; case: tpc => lpc cpc => lout; cbv zeta.
    case: (cti == cpc) => //=.
    move=> Hg.
    apply obind_inv in Hg; destruct Hg as [v1 [Ho1 _]].
    by rewrite Ho1; move: Ho1; case: v1 => _.
  Qed.

  Lemma nsu_bnz_is_other : forall (s : @Symbolic.state mt lrc_tags unit) tpc ti
      (t1 : tag_type lrc_tags R) updts pc' res,
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
      (IVec (OP BNZ) tpc ti [hseq t1]) updts pc' = Some res ->
    is_other t1 = Some tt.
  Proof.
    move=> s tpc ti t1 updts pc' res.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi s) => [evinp|] //=.
    case Hm: (mem s pc') => [ni|] /= H.
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_bnz_is_other Htr).
    - case: (obind_inv H) => ov_ev [Htr _]. exact: (rb_bnz_is_other Htr).
  Qed.

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

  Lemma rb_reg_ijump_reflect : forall (i : side) M s s3 r w off,
    registers_match i M s s3 -> is_relevant_comp i (color_of s) ->
    get_offset i (color_of s) = Some off ->
    regs s3 r = Some (w @ InternalJump) ->
    exists w', regs s r = Some (w' @ InternalJump) /\ w = addw w' (as_word off).
  Proof.
    move=> i M s s3 r w off Hrm Hrel Hoff Hr3.
    have [d' [Hdm Hr]] := proj1 (Hrm r (w @ InternalJump)) Hr3.
    move: Hdm Hr; case: d' => v' t' /=.
    move=> [Ht Hv] Hr; subst t'.
    move: Hv; rewrite Hoff /= => Hweq.
    by exists v'; split.
  Qed.

  Lemma rb_jump_silent_isjump :
    forall tpc ti (tra tp trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) tni evi (ov : ovec lrc_tags JUMP),
      LRC.instr_rules evi JUMP tpc ti (tra :: tp :: trcom :: next)%hseq tni
        = Some (ov, None) ->
      is_jump tp = Some tt.
  Proof.
    move=> [level current'] ti tra tp trcom next tni evi ov.
    rewrite /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest; last first.
    -
      exfalso.
      case: (obind_inv Hrest) => ? [_ {}Hrest]; case: (obind_inv Hrest) => ? [_ {}Hrest].
      by case: (obind_inv Hrest) => ? [_ Hf]; move: Hf => [= _].
    -
      move: Hrest; case Hij: (is_jump tp) => [u'|] //= _. by case: u' Hij.
  Qed.

  Lemma rb_is_jump_eq : forall t : value_tag, is_jump t = Some tt -> t = InternalJump.
  Proof. by case. Qed.

  Lemma rb_merged_transfer_strict :
    forall op tpc ti ts tni i (r : vovec lrc_tags (OP op) * option event),
      Merged.transfer (IVec (OP op) tpc ti ts tni) i = Some r ->
      exists ov', LRC.instr_rules i op tpc ti ts tni = Some (ov', snd r).
  Proof.
    move=> op tpc ti ts tni [rc] r.
    cbn [Merged.transfer Merged.instr_rules].
    move=> H. apply obind_inv in H. destruct H as [out [Hir Hr]].
    apply obind_inv in Hir. destruct Hir as [u1 [_ Hir]].
    apply obind_inv in Hir. destruct Hir as [u2 [_ Hir]].
    apply obind_inv in Hir. destruct Hir as [o [Hlrc Ho]].
    case: o Hlrc Ho => ov0 ev0 Hlrc Ho.
    case: ov0 Hlrc Ho => t' r' Hlrc Ho.
    move: Ho => /= [= Hout]; subst out.
    move: Hr => /= [= Hr]; subst r.
    eexists. exact: Hlrc.
  Qed.

  Lemma rb_merged_jump_isjump :
    forall (st s' : state) tpc ti (rat : tag_type lrc_tags R)
           (l : hseq (tag_type lrc_tags) (nseq 12 R)) updts (w : mword mt),
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st
        (IVec JUMP tpc ti (HSeqCons rat l)) updts w = Some (s', None) ->
      is_jump (hshead l) = Some tt.
  Proof.
    move=> st s' tpc ti rat l updts w H.
    move: H; rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       case: (rb_merged_transfer_strict Htr) => ov' Hs;
       exact: (rb_jump_silent_isjump Hs)).
  Qed.

  Lemma rb_target_belong : forall (i : side) (s s3 : state) (w : mword mt) off d3,
    combined_codes i s s3 ->
    is_relevant_comp i (color_of s) ->
    get_offset i (color_of s) = Some off ->
    mem s3 (addw w (as_word off)) = Some d3 ->
    is_code (taga d3) ->
    belong (color_of s) (Some (taga d3)) ->
    belong (color_of s) (match mem s w with Some ni => Some (taga ni) | None => None end).
  Proof.
    move=> i s s3 w off d3 Hcc Hrel Hoff Hm3 Hcode3 Hbel3.
    move: Hm3 Hcode3 Hbel3; case: d3 => v3 t3 /= Hm3 Hcode3 Hbel3.
    have Hcolc3 : color t3 = color_of s
      by have H := belong_some_eq Hbel3; exact: (esym H).
    have [v' Hsw] := succ_code_reflect Hcc Hrel Hoff Hcode3 Hcolc3 Hm3.
    rewrite Hsw /belong /=. clear Hm3 Hsw Hcode3 Hbel3.
    by case: t3 Hcolc3 => vt ct et ict /= ->; rewrite eqxx.
  Qed.

  Lemma rb_color_match : forall (t : tag_type lrc_tags Symbolic.M),
    match t with {| color := c |} => c end = color t.
  Proof. by case. Qed.

  Lemma rb_obindSome : forall (A B : Type) (f : A -> option B) (x : A),
    obind f (Some x) = f x.
  Proof. by []. Qed.

  Lemma rb_belong_color_eq : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
    c = color t -> belong c (Some t).
  Proof. by move=> c [vt ct et bt] /= ->; rewrite eqxx. Qed.

  Lemma rb_reg_clear_aux_reflect_jal : forall i M s s3 (ll : seq nat) (top : tag_type lrc_tags R) res,
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

  Lemma jal_silent_head_belong :
    forall tpc ti tret (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R)) tni evi
           (ov : ovec lrc_tags JAL),
      LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evi = Some (ov, None) ->
      belong (match ti with {| color := c |} => c end) (Some tret).
  Proof.
    move=> [level current'] [vti cti eti bti] tret l tni evi ov.
    rewrite /LRC.transfer /LRC.instr_rules_mp. cbv zeta.
    rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
    move=> H. case: (obind_inv H) => u0 [_ {}H].
    case: (obind_inv H) => ucb [Hcb {}H].
    move: Hcb; rewrite /check_belong /belong. clear H.
    by case: tret => vt ct et bt /=; case: (cti == ct).
  Qed.

  Lemma rb_reg_ret_reflect : forall (i : side) M s s3 r w n,
    registers_match i M s s3 ->
    regs s3 r = Some (w @ (Ret n)) ->
    exists w', regs s r = Some (w' @ (Ret n)).
  Proof.
    move=> i M s s3 r w n Hrm Hr3.
    have [v' Hr] := reg_reflect Hrm Hr3. by exists v'.
  Qed.

  Lemma rb_check_ret_eq : forall level (t : tag_type lrc_tags R),
    check_ret level t = Some tt -> exists n', t = Ret n' /\ level = S n'.
  Proof.
    move=> level [n' | | |] //=; case: ifP => // /eqP Hl _.
    by exists n'.
  Qed.

  Lemma rb_jump_event_inv :
    forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (tra tp trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evi : ev_inputs) (ov : ovec lrc_tags JUMP) (e : event),
      LRC.instr_rules evi JUMP tpc ti (tra :: tp :: trcom :: next)%hseq tni
        = Some (ov, Some e) ->
      belong (match ti with {| color := c |} => c end) tni = false /\
      is_other trcom = Some tt /\
      (exists c', get_tni_color tni = Some c' /\
                  e = ERet (match ti with {| color := c |} => c end) (rcom_value evi) c') /\
      (exists n', tp = Ret n' /\ (match tpc with Level level _ => level end) = S n') /\
      (match ti with {| color := c |} => c end) = (match tpc with Level _ c' => c' end).
  Proof.
    move=> [level current'] ti tra tp trcom next tni evi ov e.
    rewrite /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    have Hcur : (match ti with {| color := c |} => c end) = current' by apply/eqP.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest.
    -
      exfalso. case: (obind_inv Hrest) => u' [_ {}Hrest]. by move: Hrest => [= _].
    -
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

  Lemma rb_merged_jump_event :
    forall (st s' : state) (tpc : tag_type lrc_tags P) ti (rat : tag_type lrc_tags R)
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
    move: H; rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       case: (rb_merged_transfer_strict Htr) => ov' Hs;
       have [Hbel [Hother [[c' [Hc' _]] [Hret _]]]] := rb_jump_event_inv Hs;
       (split; [ exact Hbel |]); (split; [ exact Hother |]);
       (split; [ exists c'; exact Hc' | exact Hret ])).
  Qed.

  Lemma rb_jal_event_inv :
    forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (tnext : tag_type lrc_tags Symbolic.M) (tra trcom : tag_type lrc_tags R)
           (next : hseq (tag_type lrc_tags) (nseq 10 R)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evi : ev_inputs) (ov : ovec lrc_tags JAL) (e : event),
      LRC.instr_rules evi JAL tpc ti (tnext :: tra :: trcom :: next)%hseq tni
        = Some (ov, Some e) ->
      check_belong (match ti with {| color := c |} => c end) (Some tnext) = Some tt /\
      belong (match ti with {| color := c |} => c end) tni = false /\
      is_other trcom = Some tt /\
      (exists c', get_tni_color tni = Some c') /\
      (exists p, get_proc_name tni = Some p) /\
      check_entry (match ti with {| color := c |} => c end) tni = Some tt.
  Proof.
    move=> [level current'] ti tnext tra trcom next tni evi ov e.
    rewrite /LRC.instr_rules; cbv zeta.
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr.
    move: Hg; case Heq: (_ == current') => // _.
    case: (obind_inv Hrest) => ucb [Hcb {}Hrest]. case: ucb Hcb => Hcb.
    move: Hrest; cbn -[check_belong belong is_other is_jump get_tni_color check_ret get_proc_name check_entry].
    case Hb: (belong (match ti with {| color := c |} => c end) tni) => Hrest.
    -
      exfalso. by move: Hrest => [= _].
    -
      case: (obind_inv Hrest) => uo [Hother {}Hrest]. case: uo Hother => Hother.
      case: (obind_inv Hrest) => c' [Hc' {}Hrest].
      case: (obind_inv Hrest) => uent [Hent Hfin]. case: uent Hent => Hent.
      move: Hfin => [= Hov Hev].
      have Hpn : exists p, get_proc_name tni = Some p.
      { move: Hev; case Hp: (get_proc_name tni) => [p|] //= _. by exists p. }
      split; [ exact Hcb |]. split; [ by [] |]. split; [ exact Hother |].
      split; [ by exists c' | ]. split; [ exact Hpn | exact Hent ].
  Qed.

  Lemma rb_merged_jal_event :
    forall (st s' : state) (tpc : tag_type lrc_tags P) ti (tret : tag_type lrc_tags Symbolic.M)
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
    move: H; rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [ei|] //=.
    have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
    { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
    case Hm : (mem st w) => [ni|] /= Hgoal; move: Hgoal; rewrite El /= => Hgoal;
      (case: (obind_inv Hgoal) => -[ov ev] [Htr Hk];
       move: Hk => /= Hk; case: (obind_inv Hk) => st0 [_ Hfin];
       move: Hfin => [= _ Hev]; subst ev;
       case: (rb_merged_transfer_strict Htr) => ov' Hs;
       have [Hcb [Hbel [Hother [[c' Hc'] [[p Hp] Hent]]]]] := rb_jal_event_inv Hs;
       (split; [ exact Hcb |]); (split; [ exact Hbel |]); (split; [ exact Hother |]);
       (split; [ by exists c' |]); (split; [ by exists p | exact Hent ])).
  Qed.

  Lemma wf_stack_in_pts :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack),
      wf_stack m1 m2 m3 cn M ->
      forall a b c col, In (a, b, c, col) M ->
        points_to_comp_code' Right (side_of col) m1 (vala a) col /\
        points_to_comp_code m2 (vala b) col /\
        points_to_comp_code m3 (vala c) col.
  Proof.
    move=> m1 m2 m3 cn M H.
    induction H as [
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH ].
    - by move=> a b c col [].
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        by split; [exact P1 | split; [exact P2 | exact P3]].
      + exact: IH a b c col Hin.
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        by split; [exact P1 | split; [exact P2 | exact P3]].
      + exact: IH a b c col Hin.
  Qed.

  Lemma wf_stack_in_color_left :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack) a b c col,
      wf_stack m1 m2 m3 cn M -> In (a, b, c, col) M ->
      exists d, m1 (vala a) = Some d /\ color (taga d) = col.
  Proof.
    move=> m1 m2 m3 cn M a b c col Hwf Hin.
    have [P1 _] := wf_stack_in_pts Hwf Hin.
    move: P1; rewrite /points_to_comp_code'.
    case E: (m1 (vala a)) => [d|] //= [Hcol _]. by exists d.
  Qed.

  Lemma wf_stack_in_color_mid :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack) a b c col,
      wf_stack m1 m2 m3 cn M -> In (a, b, c, col) M ->
      exists d, m2 (vala b) = Some d /\ color (taga d) = col.
  Proof.
    move=> m1 m2 m3 cn M a b c col Hwf Hin.
    have [_ [P2 _]] := wf_stack_in_pts Hwf Hin.
    move: P2; rewrite /points_to_comp_code.
    case E: (m2 (vala b)) => [d|] //= [Hcol _]. by exists d.
  Qed.

  Lemma wf_stack_in_color_right :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack) a b c col,
      wf_stack m1 m2 m3 cn M -> In (a, b, c, col) M ->
      exists d, m3 (vala c) = Some d /\ color (taga d) = col.
  Proof.
    move=> m1 m2 m3 cn M a b c col Hwf Hin.
    have [_ [_ P3]] := wf_stack_in_pts Hwf Hin.
    move: P3; rewrite /points_to_comp_code.
    case E: (m3 (vala c)) => [d|] //= [Hcol _]. by exists d.
  Qed.

  Lemma ret_frame_colors :
    forall (i : side) (M : stack) (mrun mwk m3 : memory)
           (n0 lvl : nat) (w' w : mword mt) (cs : Component.id),
      wf_stack (if i is Left then mrun else mwk) (if i is Left then mwk else mrun) m3 lvl M ->
      data_match i cs M (w' @ (Ret n0)) (w @ (Ret n0)) ->
      exists col d ds3,
        mrun w' = Some d /\ color (taga d) = col /\
        m3 w = Some ds3 /\ color (taga ds3) = col.
  Proof.
    move=> i M mrun mwk m3 n0 lvl w' w cs Hwf Hdm.
    move: Hdm; rewrite /data_match /=.
    case: i Hwf => Hwf [_ Hin].
    -
      move: Hin => [sv' [comp' Hin]].
      have [d  [Hd  Hcol ]] := wf_stack_in_color_left  Hwf Hin.
      have [ds [Hds Hcols]] := wf_stack_in_color_right Hwf Hin.
      exists comp', d, ds. rewrite /= in Hd Hds.
      by split; [exact Hd | split; [exact Hcol | split; [exact Hds | exact Hcols]]].
    -
      move: Hin => [sv' [comp' Hin]].
      have [d  [Hd  Hcol ]] := wf_stack_in_color_mid   Hwf Hin.
      have [ds [Hds Hcols]] := wf_stack_in_color_right Hwf Hin.
      exists comp', d, ds. rewrite /= in Hd Hds.
      by split; [exact Hd | split; [exact Hcol | split; [exact Hds | exact Hcols]]].
  Qed.

  Lemma reg_clear_list_aux_mem :
    forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)})
           (top : tag_type lrc_tags R) res,
      reg_clear_list_aux l rs top = Some res ->
      forall n, n \in l -> exists a, rs (as_word (ssrint.Posz n)) = Some a.
  Proof.
    elim => [|e l' IH] rs top res //= H n.
    move: H; case He : (rs (as_word (ssrint.Posz e))) => [ve|] //=.
    case Hrec : (reg_clear_list_aux l' rs (taga ve)) => [l''|] //= _.
    rewrite in_cons => /orP[/eqP -> | Hn]; first by exists ve.
    exact: (IH rs (taga ve) l'' Hrec n Hn).
  Qed.

  Local Opaque next_state_do_updates next_state_do_update.
  Lemma reg_clear_read_aux_some :
    forall (l : seq nat) (tags : hseq (tag_type lrc_tags) (nseq (size l) R))
           (st : state) (top : tag_type lrc_tags R) res,
      reg_clear_list_aux l (regs st) top = Some res ->
      exists st', next_state_do_updates st tags
        [seq RegRead (as_word (ssrint.Posz n)) | n <- l] = Some st'
        /\ domm (regs st') = domm (regs st).
  Proof.
    elim => [|e l' IH] tags st top res.
    - Local Transparent next_state_do_updates.
      by move=> /= _; exists st. Local Opaque next_state_do_updates.
    - rewrite reg_clear_list_aux_cons.
      case He : (regs st (as_word (ssrint.Posz e))) => [ve|] //=.
      case Hrec : (reg_clear_list_aux l' (regs st) (taga ve)) => [l''|] //= _.
      move: tags; rewrite [size _]/= => tags.
      have Hstep : exists st1,
          next_state_do_update st (hshead tags : tag_type lrc_tags R)
            (RegRead (as_word (ssrint.Posz e))) = Some st1
          /\ domm (regs st1) = domm (regs st) /\ regs st1 = setm (regs st) (as_word (ssrint.Posz e)) ((vala ve)@(hshead tags)).
      { Local Transparent next_state_do_update.
        rewrite /next_state_do_update /= He /= /updm He /=.
        eexists; (split; [reflexivity |]); split;
          [ by rewrite (updm_domm_eq (m := regs st) (k := as_word (ssrint.Posz e)) (v := (vala ve)@(hshead tags)) _) // /updm He | by [] ].
        Local Opaque next_state_do_update. }
      have [st1 [Hst1 [Hdom1 Hregs1]]] := Hstep.
      rewrite (hseq_eta tags) ndsu_cons Hst1 /=.
      have Hrec1 : exists l1, reg_clear_list_aux l' (regs st1) (taga ve) = Some l1.
      { apply: (reg_clear_list_aux_total (rs := regs st1) (l := l') (taga ve)).
        move=> n Hn. have [a0 Ha0] := reg_clear_list_aux_mem Hrec Hn.
        have Hin : (as_word (ssrint.Posz n) : reg mt) \in domm (regs st1)
          by rewrite Hdom1 mem_domm Ha0.
        move: Hin; rewrite mem_domm.
        by case E: (regs st1 (as_word (ssrint.Posz n))) => [a1|] // _; exists a1. }
      have [l1 Hl1] := Hrec1.
      have [st' [Hst' Hdom']] := IH (hsbehead tags) st1 (taga ve) l1 Hl1.
      exists st'. split; [exact Hst' | by rewrite Hdom' Hdom1].
  Qed.
  Local Transparent next_state_do_updates next_state_do_update.

  Lemma ndsu_ret_event_some :
    forall (st : state) (ra0 r0 : reg mt) (top : tag_type lrc_tags R) l a b
           (t0 t1 : tag_type lrc_tags R)
           (tags : hseq (tag_type lrc_tags) (nseq (size reg_list) R)),
      regs st ra0 = Some a ->
      regs st r0 = Some b ->
      reg_clear_list_aux reg_list (regs st) top = Some l ->
      exists st', next_state_do_updates st (HSeqCons t0 (HSeqCons t1 tags)
          : hseq (tag_type lrc_tags) (R :: R :: nseq (size reg_list) R))
        (RegRead ra0 :: RegRead r0 :: reg_clear_read) = Some st'.
  Proof.
    Local Opaque next_state_do_updates.
    move=> st ra0 r0 top l a b t0 t1 tags Hra0 Hr0 Hcl.
    have Hua : exists st1, next_state_do_update st (t0 : tag_type lrc_tags R) (RegRead ra0) = Some st1
                        /\ domm (regs st1) = domm (regs st)
                        /\ regs st1 = setm (regs st) ra0 ((vala a)@t0).
    { rewrite /next_state_do_update /= Hra0 /= /updm Hra0 /=.
      eexists; (split; [reflexivity |]); split;
        [ by rewrite (updm_domm_eq (m := regs st) (k := ra0) (v := (vala a)@t0) _) // /updm Hra0 | by [] ]. }
    have [st1 [Hu1 [Hdom1 Hr1]]] := Hua.
    rewrite ndsu_cons Hu1 /=.
    have Hr0' : exists c, regs st1 r0 = Some c.
    { rewrite Hr1 setmE; case: eqP => [_|_]; [by eexists | by exists b]. }
    have [c0 Hc0] := Hr0'.
    have Hub : exists st2, next_state_do_update st1 (t1 : tag_type lrc_tags R) (RegRead r0) = Some st2
                        /\ domm (regs st2) = domm (regs st1).
    { rewrite /next_state_do_update /= Hc0 /= /updm Hc0 /=.
      eexists; (split; [reflexivity |]).
      by rewrite (updm_domm_eq (m := regs st1) (k := r0) (v := (vala c0)@t1) _) // /updm Hc0. }
    have [st2 [Hu2 Hdom2]] := Hub.
    rewrite ndsu_cons Hu2 /=.
    have Hcl2 : exists l2, reg_clear_list_aux reg_list (regs st2) top = Some l2.
    { apply: (reg_clear_list_aux_total (rs := regs st2) (l := reg_list) top).
      move=> n Hn. have [c Hc] := reg_clear_list_aux_mem Hcl Hn.
      have Hin : (as_word (ssrint.Posz n) : reg mt) \in domm (regs st2)
        by rewrite Hdom2 Hdom1 mem_domm Hc.
      move: Hin; rewrite mem_domm.
      by case E: (regs st2 (as_word (ssrint.Posz n))) => [a1|] // _; exists a1. }
    have [l2 Hl2] := Hcl2.
    have [st' [Hst' _]] := reg_clear_read_aux_some (l := reg_list) tags Hl2.
    by exists st'; rewrite /reg_clear_read Hst'.
    Local Transparent next_state_do_updates.
  Qed.

  Lemma ndsu_call_event_some :
    forall (st : state) (pcw : mword mt) (top : tag_type lrc_tags R) l a vret
           (tret : tag_type lrc_tags Symbolic.M) (t1 : tag_type lrc_tags R)
           (tags : hseq (tag_type lrc_tags) (nseq (size reg_list) R)),
      mem st (pcw + 1)%w = Some (vret @ tret) ->
      regs st ra = Some a ->
      reg_clear_list_aux reg_list (regs st) top = Some l ->
      exists st', next_state_do_updates st
          (HSeqCons tret (HSeqCons t1 tags)
             : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
          (MemRead (pcw + 1)%w :: RegWrite ra (pcw + 1)%w :: reg_clear_read) = Some st'.
  Proof.
    move=> st pcw top l a vret tret t1 tags Hmem Hra0 Hcl.
    Local Opaque next_state_do_updates.
    rewrite ndsu_cons.
    Local Transparent next_state_do_update.
    rewrite (mem_read_update_id Hmem).
    Local Opaque next_state_do_update.
    rewrite [obind _ (Some st)]/= ndsu_cons.
    have Hrw : exists st1, next_state_do_update st (t1 : tag_type lrc_tags R)
                  (RegWrite ra (pcw + 1)%w) = Some st1 /\ domm (regs st1) = domm (regs st).
    { Local Transparent next_state_do_update.
      rewrite /next_state_do_update /= /updm Hra0 /=.
      eexists; (split; [reflexivity |]).
      by rewrite (updm_domm_eq (m := regs st) (k := ra) (v := (pcw + 1)%w@t1) _) // /updm Hra0.
      Local Opaque next_state_do_update. }
    have [st1 [Hst1 Hdom1]] := Hrw.
    rewrite Hst1 [obind _ (Some st1)]/=.
    have Hcl1 : exists l1, reg_clear_list_aux reg_list (regs st1) top = Some l1.
    { apply: (reg_clear_list_aux_total (rs := regs st1) (l := reg_list) top).
      move=> n Hn. have [c Hc] := reg_clear_list_aux_mem Hcl Hn.
      have Hin : (as_word (ssrint.Posz n) : reg mt) \in domm (regs st1)
        by rewrite Hdom1 mem_domm Hc.
      move: Hin; rewrite mem_domm.
      by case E: (regs st1 (as_word (ssrint.Posz n))) => [a1|] // _; exists a1. }
    have [l1 Hl1] := Hcl1.
    have [st' [Hst' _]] := reg_clear_read_aux_some (l := reg_list) tags Hl1.
    by exists st'; rewrite /reg_clear_read Hst'.
    Local Transparent next_state_do_updates next_state_do_update.
  Qed.

  Lemma ce_wf_stack :
    forall (i : side) M s sweak s3,
      common_equiv M (if i is Left then s else sweak) (if i is Left then sweak else s) s3 ->
      exists lvl, wf_stack (if i is Left then mem s else mem sweak)
                           (if i is Left then mem sweak else mem s) (mem s3) lvl M.
  Proof.
    move=> i M s sweak s3.
    case: i => /= Hce;
      inversion Hce as [M0 s1 s2 s3' n c Htg1 Htg2 Htg3 Hwf]; subst;
      by exists n.
  Qed.

  Lemma ce_pc_level :
    forall (i : side) M s sweak s3,
      common_equiv M (if i is Left then s else sweak) (if i is Left then sweak else s) s3 ->
      (match pct s with Level level _ => level end) = (match pct s3 with Level level _ => level end).
  Proof.
    move=> i M s sweak s3.
    case: i => /= Hce;
      inversion Hce as [M0 s1 s2 s3' n c Htg1 Htg2 Htg3]; subst;
      rewrite /pct.
    - by rewrite Htg1 Htg3.
    - by rewrite Htg2 Htg3.
  Qed.

  Lemma seq_step_pre : forall (i : side) (s s3 s3' : state) op (tpc3 : tag_type lrc_tags P)
      (ts : hseq (tag_type lrc_tags) (inputs op)) (updts : seq update) i3 (ti3 : tag_type lrc_tags M),
    combined_codes i s s3 -> same_pc i s s3 -> color_of s = color_of s3 ->
    side_of (color_of s) = i -> (color_of s \in domm ip) || (color_of s \in domm ic) ->
    pc_color_inv s3 -> is_relevant_comp i (color_of s) ->
    mem s3 (vala (pc s3)) = Some (i3 @ ti3) -> is_code ti3 ->
    (exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s)) ->
    match tpc3 with Level _ c => c end = color_of s ->
    @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s3
      (IVec (OP op) tpc3 ti3 ts) updts (addw (vala (pc s3)) onew) = Some (s3', None) ->
    exists vd td v3s t3s v',
      mem s (vala (pc s)) = Some (vd @ td) /\ decode_match i (mem s) (mem s3) vd i3 /\
      td = ti3 /\ color td = color_of s /\
      mem s3 (addw (vala (pc s3)) onew) = Some (v3s @ t3s) /\ is_code t3s /\
      color t3s = color_of s /\ mem s (addw (vala (pc s)) onew) = Some (v' @ t3s).
  Proof.
    move=> i s s3 s3' op tpc3 ts updts i3 ti3 Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3
           [d3s [Hd3s Hcode3s]] Htpc3 NEXT3.
    have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
    move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
    have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
    have [_ Hbel] := merged_silent_next_pc_belong NEXT3.
    move: Hd3s Hcode3s; case: d3s => v3s t3s; cbn [vala taga] => Hd3s Hcode3s.
    have Hcolc : color t3s = color_of s.
    { move: Hbel; rewrite Hd3s Htpc3 => /belong_some_eq H. by rewrite H. }
    have Hpcnorm : exists v0 offr, (mem s (vala (pc s)) = Some v0 /\ is_code (taga v0))
          /\ get_offset i (color_of s) = Some offr
          /\ vala (pc s3) = addw (vala (pc s)) (as_word offr).
    { case: (same_pc_cases Hsp) => [H|[_ [_ Hn]]]; [exact H | by rewrite Hn in Hd3]. }
    have [v0x [offr [Hpcell0 [Hoffr Hpcoff]]]] := Hpcnorm.
    have Hshift : addw (vala (pc s3)) onew = addw (addw (vala (pc s)) onew) (as_word offr).
    { rewrite -> Hpcoff. exact (addw_rotate (vala (pc s)) (as_word offr) onew). }
    have Hd3s' : mem s3 (addw (addw (vala (pc s)) onew) (as_word offr)) = Some (v3s @ t3s)
      by rewrite <- Hshift.
    have [v' Hmems'] := succ_code_reflect Hcc Hrel Hoffr Hcode3s Hcolc Hd3s'.
    exists vd, td, v3s, t3s, v'.
    split; [exact Hd | split; [exact Hdec | split; [exact Htag | split; [exact Hcd |
      split; [exact Hd3s | split; [exact Hcode3s | split; [exact Hcolc | exact Hmems']]]]]]].
  Qed.

  Lemma stepf_reflect : forall (i : side) M s sweak s3 s3' ev,
    combined_codes i s s3 -> strong_equiv i M s s3 -> pc_color_inv s3 -> pc_color_inv s ->
    general_memory_correctness (mem s) -> general_memory_correctness (mem s3) ->
    is_relevant_comp i (color_of s) ->
    common_equiv M (if i is Left then s else sweak) (if i is Left then sweak else s) s3 ->
    step_me (NC := NC) s3 s3' ev -> exists s' ev', step_me (NC := NC) s s' ev'.
  Proof.
    move=> i M s sweak s3 s3' ev Hcc Hstr Hpci Hpcis Hgmcs Hgmc3 Hrel Hce Hstep.
    have Hval := valid_of_relevant Hrel.
    have Hsp := strong_same_pc Hstr.
    have Hrm := strong_registers_match Hstr.
    have Hmm := strong_memory_match Hstr.
    have Hcoleq := strong_color_eq Hstr.
    have Hside := strong_side Hstr.
    have Hpccase := same_pc_cases Hsp.
    have Hpcnorm : forall d3x, mem s3 (vala (pc s3)) = Some d3x ->
        exists v0 offr, (mem s (vala (pc s)) = Some v0 /\ is_code (taga v0))
          /\ get_offset i (color_of s) = Some offr
          /\ vala (pc s3) = addw (vala (pc s)) (as_word offr).
    { move=> d3x Hd3x. case: Hpccase => [H|[_ [_ Hn]]]; [exact H | by rewrite Hn in Hd3x]. }
    have Hend3 : end_condition (mem s3) by case: Hgmc3 => _ [_ [_ [_ [_ [H _]]]]]; exact H.
    have Hallocs_pro : mem s (word_of_nat alloc_label) = None
      by case: Hgmcs => _ [_ [_ [H _]]]; exact H.
    have [lvl Hwf] := ce_wf_stack Hce.
    suff [s' [ev' Hf]] : exists s' ev', step_eval_me (NC := NC) s = Some (s', ev').
    { exists s', ev'. by apply/Exec.stepP. }
    case: ev Hstep => [e|] Hstep.
    {
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
      all: try (rewrite /next_state_updates in NEXT3; unfold mv3 in NEXT3;
                have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT3);
                by case: (transfer_event_jumpjal Htr) => E; discriminate).
      -
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
        have RW3' : regs s3 r = Some (w @ t1) by rewrite ST3 /=.
        have RA3' : regs s3 ra = Some (rav @ rat) by rewrite ST3 /=.
        have [rav' Hra] := reg_reflect Hrm RA3'. cbn [taga] in Hra.
        have Hclear3 : reg_clear_list_aux reg_list (regs s3) t1 = Some l
          by rewrite ST3 /=; exact CLEAR3.
        have Hclears : reg_clear_list_aux reg_list (regs s) t1 = Some l
          := rb_reg_clear_aux_reflect Hrm Hclear3.
        have Hheadl : hshead l = t1.
        { move: Hclear3; rewrite /reg_list /=.
          case: (regs s3 (word.as_word (ssrint.Posz 1))) => [v1|] //= Hco.
          case: (obind_inv Hco) => l2 [_ ]; move=> [= Hl]. by rewrite -Hl. }
        have [Hbel3 [Hother3 [[c' Hc'3] [n' [Hheadret Hlevel]]]]] := rb_merged_jump_event NEXT3.
        rewrite Hheadl in Hheadret.
        have RW3'' : regs s3 r = Some (w @ (Ret n')) by rewrite RW3' Hheadret.
        have [w' Hrw] := rb_reg_ret_reflect Hrm RW3''.
        have Hclears' : reg_clear_list_aux reg_list (regs s) (Ret n') = Some l
          by rewrite -Hheadret.
        have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
        have Hiscode : is_code td by rewrite Htag.
        have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
        have Hdm : data_match i (color_of s) M (w' @ (Ret n')) (w @ (Ret n')).
        { have [d' [Hdm Hr]] := proj1 (Hrm r (w @ (Ret n'))) RW3''.
          have Heqd : d' = (w' @ (Ret n')) by rewrite Hr in Hrw; case: Hrw.
          by rewrite -Heqd. }
        have [col [ds [ds3 [Hsw' [Hcolds [Hs3w Hcolds3]]]]]] := ret_frame_colors Hwf Hdm.
        have Hbels : ((match td with {| color := c |} => c end) == color (taga ds)) = false.
        { have Hcolti3 : color ti3 = color_of s by rewrite (Hpci (i3 @ ti3) Hd3) Hcoleq.
          have Hbel3' : belong (color ti3) (Some (taga ds3)) = false
            by move: Hbel3; rewrite Hs3w.
          rewrite rb_belong_someE in Hbel3'.
          have Htdne : color td <> col.
          { rewrite Hcd -Hcolti3 -Hcolds3. by apply/eqP; rewrite Hbel3'. }
          apply/eqP => Heq; apply: Htdne. by rewrite -Hcolds. }
        have Hlvls := ce_pc_level Hce.
        have [st' Hupd] := @ndsu_ret_event_some s ra r _ _ _ _
          Invalidated Invalidated (Other :: reg_invalidate_hseq)%hseq
          Hra Hrw Hclears'.
        exists (@Symbolic.State mt lrc_tags unit (mem st') (regs st') w'@(build_tpc n' (color (taga ds))) (internal st')).
        exists (Some (ERet (color_of s) (rcom_value ei) (color (taga ds)))).
        apply/Exec.stepP.
        eapply step_jump.
        + exact: (Symbolic.state_eta s).
        + exact Hd.
        + exact Hdecs.
        + exact Hrw.
        + exact Hra.
        + rewrite /reg_clear_list. exact Hclears'.
        +
          have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
          { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
          have Htpc3 : pct s3 = tpc3 by rewrite ST3.
          have Hcols : color_of s = (match td with {| color := c |} => c end) by rewrite -Hcd.
          rewrite Hcols.
          Local Opaque next_state_do_updates.
          rewrite /next_state_updates_and_pc /next_state Hevi Hsw' /=.
          rewrite /Merged.transfer /Merged.instr_rules Hiscode /=.
          rewrite El /LRC.instr_rules; cbv zeta.
          move: Hlvls Hbels Hupd; case Epc : (pct s) => [lvl0 cur0] /= Hlvls Hbels Hupd.
          have Hcc' : (match td with {| color := c |} => c end) == cur0.
          { rewrite -Hcols; move: Hpccol; rewrite Epc /= => ->; exact: eqxx. }
          rewrite (eqP Hcc') eqxx /=.
          have Hbel0 : (match taga ds with {| color := c' |} => cur0 == c' end) = false.
          { move: Hbels; rewrite (eqP Hcc'). by case: (taga ds). }
          rewrite Hbel0.
          have Hhd : hshead l = Ret n' by rewrite Hheadl Hheadret.
          rewrite Hhd Hother3 /=.
          have Hckret : lvl0 == (S n') by rewrite Hlvls Htpc3; apply/eqP; exact Hlevel.
          rewrite /get_tni_color /check_ret (eqP Hckret) eqxx /=.
          rewrite -(eqP Hcc').
          case Etds : (taga ds) => [vt2 c2 e2 ic2] /=.
          rewrite Hupd /=.
          reflexivity.
          Local Transparent next_state_do_updates.
      -
        unfold mv3 in NEXT.
        have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv (nsu_and_pc_bridge NEXT).
        by case: (transfer_event_jumpjal Htr) => E; discriminate.
      -
        have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
        have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT).
        have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
        move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
        have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
        have Hbel3pre : belong (color ti3)
             (match mem s3 (swcast imm) with Some ni => Some (taga ni) | None => None end) = false
          by have [_ [H _]] := rb_merged_jal_event NEXT; exact H.
        have [imm' [Hdecs [dd [dd' [Hdd [Hdd' Htagd]]]]]] :
            exists imm', decode_instr vd = Some (Jal imm') /\
              exists dd dd', mem s (swcast imm') = Some dd /\ mem s3 (swcast imm) = Some dd'
                          /\ taga dd = taga dd'.
        { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm2 imm2' dd0 dd0' Hj Hj2 Hmd Hmd' Hicd Htagd0 Hreld].
          - exfalso. rewrite Heq in Hnj. by move: (Hnj imm); rewrite INST3.
          -
            exfalso. move: Hbel3pre. rewrite INST3 in Ha2.
            have [= Himm] := Ha2. rewrite Himm.
            have Halloc3 : mem s3 (word_of_nat alloc_label) = None
              by case: Hgmc3 => _ [_ [_ [H _]]]; exact H.
            by rewrite swcast_word_of_nat_alloc_label Halloc3.
          -
            move: Hj Hj2; rewrite INST3 => Hj [= Himm2']; subst imm2'.
            exists imm2. split; [exact Hj |].
            by exists dd0, dd0'; rewrite Hmd Hmd'. }
        have OLD3' : regs s3 ra = Some (old3 @ told3) by rewrite ST3 /=.
        have [old' Hold] := reg_reflect Hrm OLD3'. cbn [taga] in Hold.
        have Hclear3 : reg_clear_list_aux reg_list (regs s3) told3 = Some l
          by rewrite ST3 /=; exact CLEAR3.
        have Hclears : reg_clear_list_aux reg_list (regs s) told3 = Some l
          := rb_reg_clear_aux_reflect Hrm Hclear3.
        have Hra3cell : mem s3 (addw (vala (pc s3)) onew) = Some (vret @ tret).
        { rewrite ST3 /=. move: RA3. by []. }
        have Hcode_ret : is_code tret.
        { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | [v3 [Hv3 Hcv3]]].
          - exfalso. by move: Hhalt; cbn [vala]; rewrite INST3.
          - have Heqv : v3 = (vret @ tret) by congruence.
            move: Hcv3; rewrite Heqv /=. by apply. }
        have [Hcb3 [Hbel3 [Hother3 [[c' Hc'3] [[pn Hpn3] Hent3]]]]] := rb_merged_jal_event NEXT.
        have Hcolti3 : color ti3 = color_of s by rewrite (Hpci (i3 @ ti3) Hd3) Hcoleq.
        have Hcolret : color tret = color_of s.
        { have Hbel : belong (color ti3) (Some tret).
          { move: Hcb3; rewrite /check_belong. by case: (belong (color ti3) (Some tret)). }
          by rewrite -Hcolti3 -(belong_some_eq Hbel). }
        have [v0 [offr [Hpcell0 [Hoffr Hpcoff]]]] := Hpcnorm _ Hd3.
        have Hshift : addw (vala (pc s3)) onew = addw (addw (vala (pc s)) onew) (as_word offr).
        { rewrite -> Hpcoff. exact (addw_rotate (vala (pc s)) (as_word offr) onew). }
        have Hra3cell' : mem s3 (addw (addw (vala (pc s)) onew) (as_word offr)) = Some (vret @ tret)
          by rewrite <- Hshift.
        have [vret' Hretcell'] := succ_code_reflect Hcc Hrel Hoffr Hcode_ret Hcolret Hra3cell'.
        clear Hshift Hra3cell' Hpcoff Hoffr Hpcell0.
        have [ei Hevi] := nsuap_evi_reflect Hrm NEXT.
        have Hiscode : is_code td by rewrite Htag.
        have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
        have Htni3 : (match mem s3 (swcast imm) with Some ni => Some (taga ni) | None => None end)
                   = Some (taga dd') by rewrite Hdd'.
        rewrite Htni3 in Hbel3 Hc'3 Hpn3 Hent3.
        have Hcols : color_of s = (match td with {| color := c |} => c end) by rewrite -Hcd.
        have Hcbs : check_belong (match td with {| color := c |} => c end) (Some tret) = Some tt.
        { rewrite /check_belong rb_belong_someE.
          have -> : (match td with {| color := c |} => c end) = color tret by rewrite -Hcols Hcolret.
          by rewrite eqxx. }
        have [st' Hupd] := @ndsu_call_event_some s (vala (pc s)) told3 l (old' @ told3) vret'
          tret (Ret (match pct s with Level lvl _ => lvl end)) (Other :: reg_invalidate_hseq)%hseq
          Hretcell' Hold Hclears.
        exists (@Symbolic.State mt lrc_tags unit (mem st') (regs st')
                  (swcast imm')@(build_tpc (match pct s with Level lvl _ => lvl end).+1 c') (internal st')).
        exists (Some (ECall (color_of s) pn (rcom_value ei) c')).
        apply/Exec.stepP.
        eapply step_jal.
        + exact: (Symbolic.state_eta s).
        + exact Hd.
        + exact Hretcell'.
        + exact Hdecs.
        + exact Hold.
        + rewrite /reg_clear_list. exact Hclears.
        +
          rewrite Hcols.
          have Htpc3 : pct s3 = tpc3 by rewrite ST3.
          have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
          { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
          Local Opaque next_state_do_updates.
          rewrite /next_state_updates_and_pc /next_state Hevi Hdd /=.
          rewrite /Merged.transfer /Merged.instr_rules Hiscode /=.
          rewrite El /LRC.instr_rules; cbv zeta.
          move: Hupd; case Epc : (pct s) => [lvl0 cur0] /= Hupd.
          have Hcc' : (match td with {| color := c |} => c end) == cur0.
          { rewrite -Hcols; move: Hpccol; rewrite Epc /= => ->; exact: eqxx. }
          rewrite (eqP Hcc') eqxx /=.
          have HcbsE : check_belong cur0 (Some tret) = Some tt
            by rewrite -(eqP Hcc'); exact Hcbs.
          rewrite HcbsE /=.
          have Hcurti3 : cur0 = color ti3
            by rewrite -(eqP Hcc') -Hcols Hcolti3.
          rewrite Htagd.
          have Hbel0 : (match taga dd' with {| color := c' |} => cur0 == c' end) = false.
          { move: Hbel3; rewrite rb_belong_someE Hcurti3. by case: (taga dd'). }
          rewrite Hbel0.
          rewrite Hother3 /=.
          move: Hc'3; rewrite /get_tni_color => Hc'3; rewrite Hc'3 /=.
          move: Hent3 Hpn3; rewrite /check_entry /get_proc_name Hcurti3.
          case: (taga dd') => vt2 c2 [[p2 le2]|] ic2 //=.
          case: ifP => // _ _ [= Hp2].
          subst pn.
          cbn -[next_state_do_updates reg_clear_read build_tpc reg_invalidate_hseq].
          rewrite /pcv Hupd /=.
          reflexivity.
          Local Transparent next_state_do_updates.
      -
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
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Nop _).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s
        by rewrite color_ofE.
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
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        by rewrite Hcd Hpccol Hcolc eqxx /=.
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Const n3 r3).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have OLD3' : regs s3 r3 = Some (old3 @ told3) by rewrite ST3 /=.
      have [old' Hold] := reg_reflect Hrm OLD3'.
      cbn [taga] in Hold.
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
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
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /= /updm Hold /=.
        by [].
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Mov r1 r2).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have R1W3' : regs s3 r1 = Some (w1 @ t1) by rewrite ST3 /=.
      have OLD3' : regs s3 r2 = Some (old3 @ told3) by rewrite ST3 /=.
      have [w1' Hr1] := reg_reflect Hrm R1W3'. cbn [taga] in Hr1.
      have [old' Hr2] := reg_reflect Hrm OLD3'. cbn [taga] in Hr2.
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      exists (@State mt lrc_tags unit (mem s)
                (setm (setm (regs s) r1 (w1' @ (moved_tag t1)))
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
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /= /updm Hr1 /= setmE.
        by case: (r2 =P r1) => Hr21 /=; rewrite ?Hr2 //=.
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Binop op r1 r2 r3).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have R1W3' : regs s3 r1 = Some (w1 @ t1) by rewrite ST3 /=.
      have R2W3' : regs s3 r2 = Some (w2 @ t2) by rewrite ST3 /=.
      have OLD3' : regs s3 r3 = Some (old3 @ told3) by rewrite ST3 /=.
      have [w1' Hr1] := reg_reflect Hrm R1W3'. cbn [taga] in Hr1.
      have [w2' Hr2] := reg_reflect Hrm R2W3'. cbn [taga] in Hr2.
      have [old' Hr3] := reg_reflect Hrm OLD3'. cbn [taga] in Hr3.
      have [Hot1 Hot2] := nsu_binop_is_other NEXT3.
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
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
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /=.
        rewrite Hr1 /= (rb_updm_some _ Hr1) /=.
        case: (r2 =P r1) => [Hr21|Hr21].
        {
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
        rewrite setmE; move: Hr21 => /eqP/negbTE Hr21; rewrite Hr21 Hr2 /=.
        rewrite (rb_updm_some _ (a := w2' @ t2)); last by rewrite setmE Hr21 Hr2.
        rewrite /=.
        have [b3 Hb3] : exists b3,
            setm (setm (regs s) r1 (w1' @ t1)) r2 (w2' @ t2) r3 = Some b3.
        { rewrite !setmE; case: (r3 == r2); first by eauto.
          case: (r3 == r1); first by eauto. by rewrite Hr3; eauto. }
        by rewrite (rb_updm_some _ Hb3) /=.
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Load r1 r2).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Honew : (vala (pc s3) + 1)%w = addw (vala (pc s3)) onew by [].
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT3; rewrite /mv3 /next_state_updates /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [ei3 Hevi3] : exists ei3, evi s3 = Some ei3.
      { rewrite /evi Hrcom3. by eexists. }
      have Hti3col : color ti3 = color_of s by rewrite (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have Htpc3col : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      rewrite /mv3 in NEXT3. clear mv3.
      have Htpcgen : forall p : tag_type lrc_tags P,
          match p with Level n c' => (n, c') end
          = (match p with Level n _ => n end, match p with Level _ c => c end)
        by case.
      have Htpcpair : match tpc3 with Level n c' => (n, c') end
                      = (match tpc3 with Level n _ => n end, color_of s).
      { by rewrite (Htpcgen tpc3) Htpc3col. }
      have Hcurpass : (match ti3 with {| color := c |} => c end == color_of s) = true.
      { by rewrite -[match ti3 with {| color := c |} => c end]/(color ti3) Hti3col eqxx. }
      have [Hc2 [Ht1 Hbelt2]] :
        is_code t2 = false /\ t1 = Other /\ belong (color ti3) (Some t2).
      { move: NEXT3.
        rewrite /next_state_updates /next_state_updates_and_pc /next_state Honew Hd3s /= Hevi3 /=.
        rewrite /Merged.transfer /Merged.instr_rules Hcode3 /= /LRC.instr_rules.
        cbv zeta. rewrite Htpcpair /=.
        case Hc2 : (is_code t2) => /=; first by [].
        rewrite Hcurpass /=.
        case Ht1 : t1 => [ | | | ] /=; try by [].
        have Hbelgen : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
            (c == color t) -> check_belong c (Some t) = Some tt
          by move=> c [vt ct et ict] /= H; rewrite /check_belong /belong /= H.
        have Hbelt3s : check_belong (color ti3) (Some t3s) = Some tt
          by apply: Hbelgen; rewrite Hti3col -Hcolc eqxx.
        rewrite Hbelt3s /= orbF.
        move: Hc2; case: t2 MEM13 => vt2 ct2 et2 ict2 /= MEM13 Hc2.
        case Hbelt2 : (match ti3 with {| color := c |} => c end == ct2) => /=.
        - move=> _. split; [ by [] | split; by [] ].
        - by []. }
      clear NEXT3.
      have Hbelt2' : color t2 = color_of s.
      { move: Hbelt2; rewrite /belong; case: t2 {Hc2 MEM13} => vt2 ct2 et2 ict2 /=.
        move/eqP => <-. by rewrite Hti3col. }
      have R1W3' : regs s3 r1 = Some (w1 @ t1) by rewrite ST3 /=.
      have HR1 : regs s r1 = Some (w1 @ Other).
      { have [d' [Hdm Hr1]] := proj1 (Hrm r1 (w1 @ t1)) R1W3'.
        move: Hdm Hr1; rewrite Ht1; case: d' => vd1 td1 /= [Htt Hveq] Hr1.
        subst td1 vd1. exact Hr1. }
      have OLD3' : regs s3 r2 = Some (old3 @ told3) by rewrite ST3 /=.
      have [old' Hr2] := reg_reflect Hrm OLD3'. cbn [taga] in Hr2.
      have MEM13' : mem s3 w1 = Some (w2 @ t2) by rewrite ST3 /=.
      have Hncode2 : ~ is_code (taga (w2 @ t2)) by rewrite /= Hc2.
      have Hrel2 : is_relevant_comp i (color (taga (w2 @ t2))).
      { rewrite /= Hbelt2'. exact Hrel. }
      have [d' [Hdm' Hms1]] := proj1 (Hmm w1 (w2 @ t2) Hncode2 Hrel2) MEM13'.
      move: Hdm'; case: d' Hms1 => vload tload Hms1 /=.
      rewrite /data_match' /= => -[Htloadeq _].
      subst tload.
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      case Esw : (switch_val t2 (moved_tag (vtag t2)))
        => [ts' td'].
      have [mem' Hmem'] : exists mem', updm (mem s) w1 (vload @ ts') = Some mem'.
      { rewrite /updm Hms1. by eexists. }
      exists (@State mt lrc_tags unit mem'
                (setm (setm (regs s) r1 (w1 @ Other)) r2 (vload @ td'))
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_load.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact HR1.
      + exact Hms1.
      + exact Hr2.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= Hc2 /= /LRC.instr_rules.
        cbv zeta.
        have Hpcpair : match pct s with Level n c' => (n, c') end
                       = (match pct s with Level n _ => n end, color_of s)
          by rewrite (Htpcgen (pct s)) Hpccol.
        rewrite Hpcpair /=.
        have Hcurpass' : (match td with {| color := c |} => c end == color_of s) = true
          by rewrite -[match td with {| color := c |} => c end]/(color td) Hcd eqxx.
        rewrite Hcurpass' /=.
        have Hbelt3sS : check_belong (color td) (Some t3s) = Some tt.
        { rewrite /check_belong /belong.
          move: Hcolc; case: t3s {Hd3s Hcode3s Hmems'} => vt3 ct3 et3 ict3 /= ->.
          by rewrite Hcd eqxx. }
        rewrite Hbelt3sS /=.
        have Hbelgen2 : forall (c : Component.id) (t : tag_type lrc_tags Symbolic.M),
            (c == color t) -> belong c (Some t) = true
          by move=> c [vt ct et ict] /= H; rewrite /belong /= H.
        have Hbelt2S : belong (color td) (Some t2) = true
          by apply: Hbelgen2; rewrite Hcd -Hbelt2' eqxx.
        rewrite -/(belong (color td) (Some t2)) Hbelt2S /=.
        rewrite Esw /=.
        rewrite /updm HR1 /= Hms1 /= setmE.
        have Hmemeq : mem' = setm (mem s) w1 (vload @ ts')
          by move: Hmem'; rewrite /updm Hms1 /= => -[<-].
        rewrite Hmemeq.
        by case Hr21 : (r2 == r1) => /=; rewrite ?Hr2 //=.
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT3).
      have Hnext3 : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have [vd [td [v3s [t3s [v' [Hd [Hdec [Htag [Hcd [Hd3s [Hcode3s [Hcolc Hmems']]]]]]]]]]]] :=
        seq_step_pre Hcc Hsp Hcoleq Hside Hval Hpci Hrel Hd3 Hcode3 Hnext3 Htpc3 NEXT3.
      have Hdecs : decode_instr vd = Some (Store r1 r2).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have R1W3' : regs s3 r1 = Some (w1 @ t1) by rewrite ST3 /=.
      have R2W3' : regs s3 r2 = Some (w2 @ t2) by rewrite ST3 /=.
      have OLD3' : mem s3 w1 = Some (old3 @ told3) by rewrite ST3 /=.
      have [Hot1 [Hictold3 Hbelold3]] := nsu_store_gates NEXT3.
      have Ht1 : t1 = Other := rb_is_other_eq Hot1.
      have Hr1 : regs s r1 = Some (w1 @ Other).
      { have [d' [Hdm Hr]] := proj1 (Hrm r1 (w1 @ t1)) R1W3'.
        move: Hdm Hr; case: d' => va' ta'; rewrite Ht1 /= => -[] -> Hv Hr.
        by rewrite Hr Hv. }
      have [w2' Hr2] := reg_reflect Hrm R2W3'. cbn [taga] in Hr2.
      have Hcoltold3 : color told3 = color_of s.
      { rewrite -Hbelold3. by rewrite (Hpci (i3 @ ti3) Hd3) Hcoleq. }
      have [old' Hold] : exists old', mem s w1 = Some (old' @ told3).
      { have Hnc : ~~ is_code (taga (old3 @ told3)) by rewrite /= Hictold3.
        have Hrl : is_relevant_comp i (color (taga (old3 @ told3))).
        { rewrite /= Hcoltold3; exact Hrel. }
        have [d' [Hdm Hr]] := proj1 (Hmm w1 (old3 @ told3) (negP Hnc) Hrl) OLD3'.
        move: Hdm Hr; case: d' => vo' to'; rewrite /data_match' /= => -[] -> _ Hr.
        by exists vo'; rewrite Hr. }
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      exists (@State mt lrc_tags unit
                (setm (mem s) w1 (w2' @ (switch_val told3 t2).1))
                (setm (setm (regs s) r1 (w1 @ t1))
                      r2 (w2' @ (moved_tag t2)))
                ((vala (pc s) + 1)%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_store.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hr1.
      + exact Hr2.
      + exact Hold.
      + rewrite /next_state_updates /next_state_updates_and_pc /next_state Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        rewrite Ht1 /= Hictold3 /=.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        case: told3 Hold Hcoltold3 Hictold3 {OLD3' Hbelold3 OLD3 NEXT3 mv3} => vto cto eto icto /= Hold Hcoltold3 Hictold3.
        rewrite Hcd Hpccol Hcolc Hcoltold3 !eqxx /=.
        rewrite /updm Hr1 /=.
        rewrite setmE.
        case: (r2 =P r1) => [Hr21|Hr21] /=.
        {
          have Hww : w1 = w2' /\ t1 = t2.
          { move: Hr2; rewrite Hr21 Hr1 Ht1 => -[] -> ->. by split. }
          case: Hww => Hww _; rewrite -Hww /=.
          rewrite Hold /=.
          by rewrite -Hr21. }
        rewrite Hr2 /=.
        by rewrite Hold /=.
    -
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
      have RW3' : regs s3 r = Some (w @ t1) by rewrite ST3 /=.
      have RA3' : regs s3 ra = Some (rav @ rat) by rewrite ST3 /=.
      have [rav' Hra] := reg_reflect Hrm RA3'. cbn [taga] in Hra.
      have Hclear3 : reg_clear_list_aux reg_list (regs s3) t1 = Some l
        by rewrite ST3 /=; exact CLEAR3.
      have Hclears : reg_clear_list_aux reg_list (regs s) t1 = Some l
        := rb_reg_clear_aux_reflect Hrm Hclear3.
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
      have [v0x [offr [Hpcell0 [Hoffr Hpcoff]]]] := Hpcnorm _ Hd3.
      have [w' [Hrw Hweq]] := rb_reg_ijump_reflect Hrm Hrel Hoffr RW3''.
      have Htpc3c : match tpc3 with Level _ c => c end = color_of s.
      { by rewrite Hcoleq ST3 /=. }
      have [dj [Hdj Hdjimp]] : exists dj, mem s3 w = Some dj
          /\ (is_relevant_comp i (color (taga dj)) -> is_code (taga dj)).
      { have Hac := strong_reg_addr2 Hstr RW3''.
        move: Hac; rewrite /address_correctness /= => -[v [Hv Himp]]. by exists v. }
      have Hbeldj : belong (color_of s) (Some (taga dj)).
      { by move: Hbel; rewrite Htpc3c Hdj. }
      have Hdjcol : color (taga dj) = color_of s
        by have H := belong_some_eq Hbeldj; exact (esym H).
      have Hdjc : is_code (taga dj).
      { apply: Hdjimp. rewrite Hdjcol. exact Hrel. }
      have Hdj' : mem s3 (addw w' (as_word offr)) = Some dj by rewrite <- Hweq.
      have Hbelw : belong (color_of s)
                     (match mem s w' with Some ni => Some (taga ni) | None => None end)
        := rb_target_belong Hcc Hrel Hoffr Hdj' Hdjc Hbeldj.
      clear Hweq Hdj' Hpcoff Hoffr Hpcell0 Hdjimp.
      have [ei Hevi] := nsuap_evi_reflect Hrm NEXT3.
      have Hiscode : is_code td by rewrite Htag.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      have Hcdpc : color td = match pct s with Level _ c => c end by rewrite Hcd Hpccol.
      exists (@State mt lrc_tags unit (mem s) (regs s) (w' @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_jump.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hrw.
      + exact Hra.
      + rewrite /reg_clear_list. exact Hclears'.
      +
        Local Opaque next_state_do_updates.
        have Hupd : next_state_do_updates s
                      (HSeqCons rat l : hseq (tag_type lrc_tags) (R :: nseq (size reg_list).+1 R))
                      (RegRead ra :: RegRead r :: reg_clear_read) = Some s.
        { rewrite ndsu_cons.
          have Hra' : taga (rav' @ rat) = rat by [].
          rewrite -Hra' (reg_read_update_id Hra) /obind /oapp.
          have Hcl : reg_clear_list_aux reg_list (regs s) (taga (w' @ InternalJump)) = Some l
            by exact Hclears'.
          rewrite /reg_clear_read.
          exact: (reg_clear_do_updates_id (l := reg_list) (st := s) (k0 := r)
                    (a0 := w' @ InternalJump) Hrw Hcl). }
        rewrite /next_state_updates_and_pc /next_state Hevi /=.
        have Hhij : hshead l = InternalJump by rewrite Hheadl Ht1.
        have El : l = (hshead l :: hshead (hsbehead l) :: hsbehead (hsbehead l))%hseq.
        { rewrite [in LHS](hseq_eta l) [in hsbehead l](hseq_eta (hsbehead l)). by []. }
        have Hcurc : (match td with {| color := c |} => c end) = color_of s by exact Hcd.
        have Hfold : forall ni : atom (mword mt) (tag_type lrc_tags Symbolic.M),
                     belong (color_of s) (Some (taga ni))
                     -> (match taga ni with {| color := c' |} =>
                          (match td with {| color := c |} => c end) == c' end) = true.
        { move=> ni0; rewrite /belong Hcurc. by case: (taga ni0) => v0 c0 e0 b0 /=. }
        case Hmsw : (mem s w') => [ni|] /=;
          rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules;
          cbv zeta;
          rewrite {1}El /=;
          (move: Hpccol; case: (pct s) => lpc cpc /= Hpccol);
          ( rewrite (_ : (match td with {| color := c |} => c end == cpc) = true);
            last by (apply/eqP; rewrite Hcurc Hpccol) );
          rewrite /=.
        *
          rewrite (Hfold ni); last by (move: Hbelw; rewrite Hmsw /=).
          rewrite -El Hhij /is_jump /=.
          by rewrite Hupd.
        *
          rewrite -El Hhij /is_jump /=.
          by rewrite Hupd.
    Local Transparent next_state_do_updates.
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hdecs : decode_instr vd = Some (Bnz r n).
      { inversion Hdec as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
        - rewrite Heq; exact INST3.
        - rewrite INST3 in Ha2; discriminate Ha2.
        - rewrite INST3 in Hj2; discriminate Hj2. }
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have RW3' : regs s3 r = Some (w @ t1) by rewrite ST3 /=.
      have Hot1 := nsu_bnz_is_other NEXT.
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT; rewrite /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a3|] /=; [exists a3 | ]. }
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT.
      clear mv3 NEXT.
      move: Hot1 RW3 RW3'; rewrite /is_other; case: t1 => //= _ RW3 RW3'.
      have Hr : regs s r = Some (w @ Other).
      { have [d' [Hdm Hrs]] := proj1 (Hrm r (w @ Other)) RW3'.
        move: Hdm; case: d' Hrs => vv tt0 Hrs /= [Htt0 Hvv]; subst tt0 vv.
        by rewrite Hrs. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      have Hiscode : is_code td by rewrite Htag.
      have Htpc3 : match tpc3 with Level _ c => c end = color_of s by rewrite Hcoleq ST3 /=.
      have Hzero : exists d3s, mem s3 (addw (vala (pc s3)) onew) = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Hnz : exists d3s, mem s3 (addw (vala (pc s3)) (swcast n)) = Some d3s /\ is_code (taga d3s).
      { have Hbnz3 : BNZ_correctness (mem s3)
          by case: Hgmc3 => _ [_ [_ [_ [Hb _]]]]; exact Hb.
        have := Hbnz3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3.
        cbn [vala]; rewrite INST3 => [[v' [Hv' Hcv']]]. by exists v'. }
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (addw (vala (pc s3)) (if w == 0%w then onew else swcast n)) = Some d3s
                      /\ is_code (taga d3s)
        by case: (w == 0%w); [exact Hzero | exact Hnz].
      move: Hd3s Hcode3s; case: d3s => v3s t3s; cbn [vala taga] => Hd3s Hcode3s.
      have Hpc3val : vala (pc s3) = pc3 by rewrite ST3.
      have Hcolc : color t3s = color_of s.
      { move: Hbel; rewrite /NEXT3 -Hpc3val Hd3s Htpc3 => /belong_some_eq H. by rewrite H. }
      have [v0x [offr [Hpcell0 [Hoffr Hpcoff]]]] := Hpcnorm _ Hd3.
      have Hshift : addw (vala (pc s3)) (if w == 0%w then onew else swcast n)
                  = addw (addw (vala (pc s)) (if w == 0%w then onew else swcast n)) (as_word offr).
      { rewrite -> Hpcoff.
        exact (addw_rotate (vala (pc s)) (as_word offr) (if w == 0%w then onew else swcast n)). }
      have Hd3s' : mem s3 (addw (addw (vala (pc s)) (if w == 0%w then onew else swcast n)) (as_word offr))
                   = Some (v3s @ t3s)
        by rewrite <- Hshift.
      have [v' Hmems'] := succ_code_reflect Hcc Hrel Hoffr Hcode3s Hcolc Hd3s'.
      clear Hshift Hd3s' Hpcoff Hoffr Hpcell0.
      have Hpceq : (vala (pc s) + (if w == 0%w then 1%w else swcast n))%w
                 = addw (vala (pc s)) (if w == 0%w then onew else swcast n)
        by case: (w == 0%w).
      exists (@State mt lrc_tags unit (mem s)
                (setm (regs s) r (w @ Other))
                ((vala (pc s) + (if w == 0%w then 1%w else swcast n))%w @ (pct s)) (internal s)), None.
      apply/Exec.stepP.
      eapply step_bnz.
      + exact: (Symbolic.state_eta s).
      + exact Hd.
      + exact Hdecs.
      + exact Hr.
      + rewrite /next_state_updates_and_pc /next_state Hpceq Hmems' /= Hevi /=.
        rewrite /Merged.transfer /Merged.instr_rules Hiscode /= /LRC.instr_rules /check_belong /belong.
        cbv zeta.
        rewrite (_ : is_other Other = Some tt) //=.
        case: td Hcd {Hiscode Htag Hd Hdec} => vtd ctd etd ictd /= Hcd.
        case: (pct s) Hpccol => ltpc ctpc /= Hpccol.
        case: t3s Hcolc {Hcode3s Hmems' Hd3s} => vt3 ct3 et3 ic3 /= Hcolc.
        rewrite Hcd Hpccol Hcolc eqxx /= /updm Hr /=.
        by [].
    -
      have Hd3 : mem s3 (vala (pc s3)) = Some (i3 @ ti3) by rewrite ST3 /=.
      have Hcode3 : is_code ti3 by apply: (nsu_transfer_iscode NEXT).
      have [d [Hd [Hdec Htag]]] := pc_cell_reflect Hcc Hsp Hcoleq Hside Hval Hpci Hd3 Hcode3.
      move: Hd Hdec Htag; case: d => vd td; cbn [vala taga] => Hd Hdec Htag.
      have Hcd : color td = color_of s by rewrite Htag (Hpci (i3 @ ti3) Hd3) Hcoleq.
      have Hpccol : match pct s with Level _ c => c end = color_of s by rewrite color_ofE.
      have HRA3 : mem s3 (vala (pc s3) + 1)%w = Some (vret @ tret) by rewrite ST3 /=.
      have [d3s [Hd3s Hcode3s]] :
          exists d3s, mem s3 (vala (pc s3) + 1)%w = Some d3s /\ is_code (taga d3s).
      { case: (Hend3 (vala (pc s3)) (i3 @ ti3) Hd3 Hcode3) => [Hhalt | H]; last exact H.
        by move: Hhalt; cbn [vala]; rewrite INST3. }
      have Htretcode : is_code tret.
      { move: Hd3s; rewrite HRA3 => -[Hd3eq]. by rewrite -Hd3eq in Hcode3s; move: Hcode3s; cbn [taga]. }
      have [Hpc3' Hbel] := merged_silent_next_pc_belong NEXT.
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
      { have HtretEq := belong_some_eq HtretBel. by rewrite -HtretEq -Hcolti3. }
      have [v0x [offr [Hpcell0 [Hoffr Hpcoff]]]] := Hpcnorm _ Hd3.
      have Hshift : addw (vala (pc s3)) onew = addw (addw (vala (pc s)) onew) (as_word offr).
      { rewrite -> Hpcoff. exact (addw_rotate (vala (pc s)) (as_word offr) onew). }
      have HRA3' : mem s3 (addw (addw (vala (pc s)) onew) (as_word offr)) = Some (vret @ tret)
        by rewrite <- Hshift.
      have [vret' HRAs'] := succ_code_reflect Hcc Hrel Hoffr Htretcode Hcoltret HRA3'.
      clear Hshift HRA3' Hpcell0.
      have OLD3' : regs s3 ra = Some (old3 @ told3) by rewrite ST3 /=.
      have [old' Holds] := reg_reflect Hrm OLD3'. cbn [taga] in Holds.
      have CLEAR3' : reg_clear_list (regs s3) told3 = Some l by rewrite ST3 /=.
      have CLEARs : reg_clear_list (regs s) told3 = Some l
        by apply: (rb_reg_clear_aux_reflect_jal Hrm CLEAR3').
      have [a3 Hrcom3] : exists a3, regs s3 rcom = Some a3.
      { move: NEXT; rewrite /next_state_updates_and_pc /next_state /evi.
        by case: (regs s3 rcom) => [a4|] /=; [exists a4 | ]. }
      have [ei Hevi] := rb_evi_reflect Hrm (ex_intro _ a3 Hrcom3).
      have Hiscode : is_code td by rewrite Htag.
      have Hg1 : (match td with {| color := c |} => c end)
                 == (match pct s with Level _ c' => c' end)
        by rewrite !rb_color_match Hcd Hpccol eqxx.
      have Hg2 : belong (match td with {| color := c |} => c end) (Some tret)
        by rewrite rb_color_match; apply: rb_belong_color_eq; rewrite Hcd Hcoltret.
      inversion Hdec as [Hnj Hnj' Heq | Halloc Halloc2 | jimm jimm' jd jd' Hjs Hj3 Htgts Htgt3 Hcodet Htagteq Hoff].
      +
        exfalso. by move: (Hnj' imm); rewrite INST3.
      +
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
      +
        have Himm3 : jimm' = imm by move: Hj3; rewrite INST3 => -[].
        have Htgt3' : mem s3 NEXT3 = Some jd'.
        { rewrite -[NEXT3]/(swcast imm) -Himm3. exact Htgt3. }
        have Hcoljd' : color (taga jd') = color_of s.
        { have Hbel' := Hbel. rewrite Htgt3' in Hbel'.
          have := belong_some_eq Hbel'. move=> Heq.
          have Htpc3c : match tpc3 with Level _ c => c end = color_of s
            by rewrite Hcoleq ST3 /=.
          by rewrite -Htpc3c -Heq. }
        have Hcoljd : color (taga jd) = color_of s by rewrite Htagteq.
        eexists. exists None.
        apply/Exec.stepP.
        eapply step_jal.
        * exact: (Symbolic.state_eta s).
        * exact Hd.
        * exact HRAs'.
        * exact Hjs.
        * exact Holds.
        * exact CLEARs.
        *
          have Hg3 : belong (match td with {| color := c |} => c end) (Some (taga jd))
            by rewrite rb_color_match; apply: rb_belong_color_eq; rewrite Hcd Hcoljd.
          have HtrS := rb_jal_transfer_silent l ei Hiscode Hg1 Hg2 Hg3.
          rewrite /next_state_updates_and_pc /next_state Htgts Hevi.
          rewrite rb_obindSome HtrS rb_obindSome.
          cbn -[next_state_do_updates updm].
          rewrite (jal_do_updates_result (vv := vret') (a4 := old' @ told3) HRAs' Holds CLEARs).
          rewrite /next_state_do_update /updm Holds /=.
          by [].
    -
      have Hpc3 : vala (pc s3) = pc3 by rewrite ST3 /=.
      have Hmem3none : mem s3 (vala (pc s3)) = None by rewrite ST3 /= PC3.
      have Hmemsnone : mem s (vala (pc s)) = None.
      { case: Hpccase => [[v0 [offr [Hpcell [Hoffr Hpcoff]]]] | [_ [Hn _]]]; last exact Hn.
        exfalso.
        case: Hpcell => Hcell Hcodev.
        move: Hcell Hcodev; case: v0 => vv tv /= Hcell Hcodev.
        have Hcolv : color tv = color_of s by exact: (Hpcis (vv @ tv) Hcell).
        have [v3' [_ Hm3]] :=
          proj1 (Hcc (vala (pc s)) vv tv offr (color_of s) Hrel Hoffr Hcodev Hcolv) Hcell.
        move: Hm3. rewrite <- Hpcoff. by rewrite Hmem3none. }
      have Hpceq : vala (pc s) = pc3.
      { case: Hpccase => [[v0 [offr [[Hcell _] _]]] | [Hpe _]];
          [ by rewrite Hmemsnone in Hcell | by rewrite Hpe Hpc3 ]. }
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
        have [v_ra Hra_s] := reg_reflect Hrm Hra3.
        have [v_sz Hsz_s] := reg_reflect Hrm Hsz3.
        have [v_ret Hret_s] := reg_reflect Hrm Hret3.
        have E_rat : taga ra_val = InternalJump
          by move: Hjmp3; rewrite /is_jump; case: (taga ra_val).
        have E_sat : taga sz = Other
          by move: Hoth3; rewrite /is_other; case: (taga sz).
        have Hccs : match taga (pc s) with Level _ c => c end = color_of s
          by rewrite -color_ofE.
        have Hcc3 : match taga (pc s3) with Level _ c => c end = color_of s
          by rewrite -color_ofE Hcoleq.
        move: Hretcol3; rewrite Hcc3 => /andP [Hic3 /eqP Hcol3].
        have [off Hoff0] := get_offset_some Hrel.
        have [d_ra [Hdm_ra Hra_s2]] := proj1 (Hrm ra ra_val) Hra3.
        have Hvalra : vala ra_val = addw (vala d_ra) (as_word off).
        { have Hdm := Hdm_ra. have Ert := E_rat.
          move: Hdm Ert; case: d_ra {Hdm_ra Hra_s2} => dv dt;
            case: ra_val {Hra3 Hreta3 Hjmp3 Hra_s E_rat}
            => rv rt /= -[Het Hop] Hrt; subst dt rt.
          move: Hop; rewrite /= Hoff0 /= => Hb. exact Hb. }
        have Hra_s'' : regs s ra = Some (v_ra @ InternalJump).
        { rewrite E_rat in Hra_s; exact Hra_s. }
        have Hreta3' : mem s3 (addw (vala d_ra) (as_word off)) = Some ((vala reta3) @ (taga reta3)).
        { rewrite <- Hvalra. by rewrite Hreta3; case: (reta3) => ? ? /=. }
        have [vr_s Hreta_s] := succ_code_reflect Hcc Hrel Hoff0 Hic3 Hcol3 Hreta3'.
        have Hdra_eq : v_ra @ InternalJump = d_ra.
        { move: Hra_s2; rewrite Hra_s'' => -[Hde]; exact Hde. }
        have Hvra_eq : v_ra = vala d_ra by rewrite -Hdra_eq.
        have Hretmem_s : mem s v_ra = Some (vr_s @ (taga reta3)) by rewrite Hvra_eq.
        have Hretchk_s : (is_code (taga reta3) && (color (taga reta3) == color_of s)) = true
          by rewrite Hcol3 eqxx andbT; exact Hic3.
        have Hck_s : (if is_code (taga (vr_s @ (taga reta3)))
                         && (color (taga (vr_s @ (taga reta3))) == color_of s)
                      then Some tt else None) = Some tt by rewrite /= Hretchk_s.
        have Hsz_s'' : regs s syscall_arg1 = Some (v_sz @ Other).
        { rewrite E_sat in Hsz_s; exact Hsz_s. }
        have E_dsv : v_sz = vala sz.
        { have [d_sz [Hdm_sz Hsz_s2]] := proj1 (Hrm syscall_arg1 sz) Hsz3.
          have E_dsat : taga d_sz = Other by rewrite (data_match_taga Hdm_sz).
          have Hv := data_match_other_val (cc := color_of s) (m := M) (i := i) E_dsat Hdm_sz.
          have Hde : Some (v_sz @ Other) = Some d_sz by rewrite -Hsz_s'' Hsz_s2.
          move: Hv Hde; case: d_sz {Hdm_sz Hsz_s2 E_dsat} => dv dt /= Hv [Hd1 Hd2].
          by rewrite Hd1 Hv. }
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
        rewrite Hcc3 -Hdomm in Hchk3 Haddr3.
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
  Qed.

  Lemma nostep_reflect : forall M s1 s2 s3,
    match_states M s1 s2 s3 -> pc_color_inv s3 -> pc_color_inv s1 -> pc_color_inv s2 ->
    Nostep sem s1 -> Nostep sem' s2 -> Nostep sem'' s3.
  Proof.
    move=> M s1 s2 s3 Hms Hpci Hpci1 Hpci2 Hns1 Hns2 t s3' Hstep.
    have [ev Hme3] : exists ev, step_me (NC := NC) s3 s3' ev.
    { move: Hstep => /=. destruct t as [|e [|? ?]];
        [ move=> H; by exists None | move=> H; by exists (Some e) | by case ]. }
    inversion Hms as [M0 sa sb sc Hcom HstrL HwkR | M0 sa sb sc Hcom HwkL HstrR]; subst.
    - have [s1' [ev1 Hme1]] := stepf_reflect (sweak := s2)
        (common_combined_left Hcom) HstrL Hpci Hpci1 (common_gmc1 Hcom) (common_gmc3 Hcom)
        (is_relevant_comp_of_side (common_color_valid1 Hcom) (strong_side HstrL)) Hcom Hme3.
      apply: (Hns1 (oapp (fun e => [:: e]) [::] ev1) s1'); simpl.
      apply: step_UB_disallowed.
      + by case: ev1 Hme1 => [e|] Hme1.
      + by case: ev1 Hme1 => [e|] Hme1; apply: step_me_mp.
    - have [s2' [ev2 Hme2]] := stepf_reflect (sweak := s1)
        (common_combined_right Hcom) HstrR Hpci Hpci2 (common_gmc2 Hcom) (common_gmc3 Hcom)
        (is_relevant_comp_of_side (common_color_valid2 Hcom) (strong_side HstrR)) Hcom Hme3.
      apply: (Hns2 (oapp (fun e => [:: e]) [::] ev2) s2'); simpl.
      by case: ev2 Hme2 => [e|] Hme2.
  Qed.

  Lemma nostep_reflect_left : forall M s1 s2 s3,
    common_equiv M s1 s2 s3 -> strong_equiv Left M s1 s3 -> pc_color_inv s3 -> pc_color_inv s1 ->
    Nostep sem s1 -> Nostep sem'' s3.
  Proof.
    move=> M s1 s2 s3 Hcom HstrL Hpci Hpci1 Hns1 t s3' Hstep.
    have [ev Hme3] : exists ev, step_me (NC := NC) s3 s3' ev.
    { move: Hstep => /=. destruct t as [|e [|? ?]];
        [ move=> H; by exists None | move=> H; by exists (Some e) | by case ]. }
    have [s1' [ev1 Hme1]] := stepf_reflect (sweak := s2)
      (common_combined_left Hcom) HstrL Hpci Hpci1 (common_gmc1 Hcom) (common_gmc3 Hcom)
      (is_relevant_comp_of_side (common_color_valid1 Hcom) (strong_side HstrL)) Hcom Hme3.
    apply: (Hns1 (oapp (fun e => [:: e]) [::] ev1) s1'); simpl.
    apply: step_UB_disallowed.
    + by case: ev1 Hme1 => [e|] Hme1.
    + by case: ev1 Hme1 => [e|] Hme1; apply: step_me_mp.
  Qed.

  Lemma notfinal_reflect_left : forall M s1 s2 s3,
    common_equiv M s1 s2 s3 -> strong_equiv Left M s1 s3 -> pc_color_inv s3 ->
    ~ final_state_rUB s1 -> ~ final_state_me s3.
  Proof.
    move=> M s1 s2 s3 Hcom HstrL Hpci Hnf1 Hf3.
    have [d [Hcell [Hdec Hcode]]] := final_reflect_strong
      (common_combined_left Hcom) (strong_same_pc HstrL) (strong_color_eq HstrL)
      (strong_side HstrL) (common_color_valid1 Hcom) Hpci Hf3.
    exact: (Hnf1 (final_rUB_intro Hcell Hdec Hcode)).
  Qed.

End RecBackward.

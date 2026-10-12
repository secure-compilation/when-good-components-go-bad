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
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Common.Traces.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import MicroPolicies.Recomposition.TraceInit.
Require Import MicroPolicies.Recomposition.BackTranslation.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Layout.
Require Import Backtranslation_ME_MP_Trace.
Require Import Backtranslation_ME_MP_Sim.
Require Import Backtranslation_ME_MP_Wf.
Require Import Backtranslation_ME_MP_Obs.

Lemma ret_comps (good : pred nat) (t : trace) pre C0 z C' suf :
  well_bracketed_trace stack_state0 t -> t = pre ++ ERet C0 z C' :: suf ->
  good Component.main ->
  (forall C1 P1 z1 C2, List.In (ECall C1 P1 z1 C2) t -> good C1 && good C2) ->
  good C0 && good C'.
Proof.
move=> Hwb Et Hm Hc.
have Hpre : forall e, e \in pre -> List.In e t.
{ move=> e He. rewrite Et. apply: in_catl. exact: mem_in_seq He. }
move: Hwb. rewrite Et well_bracketed_trace_cat => /andP [Hwp /= /andP [/eqP Hcur Hrest]].
have [Hcur' Hcal _] := pend_inv Hwp.
apply/andP; split.
- rewrite -Hcur Hcur' /topcomp.
  case E: (pend pre) => [|x st]; first exact: Hm.
  have Hx : x \in pend pre by rewrite E mem_head.
  have := pend_callee_called Hx. rewrite /calls_into => /hasP [e He].
  case: e He => [C1 P1 z1 C2|//] He /eqP <-.
  by case/andP: (Hc _ _ _ _ (Hpre _ He)).
- move: Hrest. rewrite Hcal.
  case E: (pend pre) => [|x st] //= /andP [/eqP Ex _].
  have Hx : x \in pend pre by rewrite E mem_head.
  have [P0 [z0 [Hlt Hn]]] := pend_entry_call (ERet 0 BinNums.Z0 0) Hx.
  have Hin : ECall (pcaller x) P0 z0 (pcallee x) \in pre.
  { rewrite -Hn. have := mem_nth (ERet 0 BinNums.Z0 0) Hlt.
    rewrite /rp_events mem_filter. by case/andP. }
  rewrite -Ex. by case/andP: (Hc _ _ _ _ (Hpre _ Hin)).
Qed.

Lemma rp_block_ok (PB : NMap {fmap Block.id -> nat + seq value}) X bm b :
  PB X = Some bm -> 0 < odflt 0 (omap bsize (bm b)) ->
  linearize_bufs PB (X, rp_block PB X, 0) <> None.
Proof.
move=> HX Hb.
have Hin : b \in [seq b0 <- domm bm | 0 < odflt 0 (omap bsize (bm b0))].
{ rewrite mem_filter Hb /=. move: Hb. case E: (bm b) => [v|] //= _.
  by apply/dommP; exists v. }
case Ef: [seq b0 <- domm bm | 0 < odflt 0 (omap bsize (bm b0))] Hin => [//|b' l] _.
have Hb' : b' \in [seq b0 <- domm bm | 0 < odflt 0 (omap bsize (bm b0))].
{ by rewrite Ef mem_head. }
rewrite mem_filter in Hb'. case/andP: Hb' => Hpos _.
rewrite /rp_block HX /= Ef /= linearize_bufsE HX.
case E: (bm b') Hpos => [blk|] //= Hpos.
rewrite /linearize_buf HX /= E /=.
case: blk E Hpos => [n|vs] _ /= Hpos.
- by case: n Hpos.
- by case: vs Hpos.
Qed.

Lemma shape_inl (B : NMap {fmap Block.id -> nat + seq value}) :
  bufs_shape (mapm (mapm (fun x => inl (bsize x) : nat + seq value)) B) = bufs_shape B.
Proof.
apply/eq_fmap => X. rewrite /bufs_shape !mapmE.
case: (B X) => [bm|] //=. congr Some. apply/eq_fmap => b. rewrite !mapmE.
by case: (bm b).
Qed.

Section Pkg.

Variables (L P C NC : nat) (p c : program) (m0 : finpref_behavior).

Local Notation Ip := (prog_interface p).
Local Notation Ic := (prog_interface c).
Local Notation Bp := (prog_buffers p).
Local Notation Bc := (prog_buffers c).
Local Notation PI := (unionm Ip Ic).
Local Notation PB := (unionm Bp Bc).
Local Notation t := (finpref_trace m0).
Local Notation W := (Definitions.program_link p c).
Local Notation bp := (rp_program L P C PI PB t Ip Bp).
Local Notation bc := (rp_program L P C PI PB t Ic Bc).

Hypothesis Hwfp : wf_mp L P C PI p.
Hypothesis Hwfc : wf_mp L P C PI c.
Hypothesis Hmerg : mergeable_interfaces Ip Ic.
Hypothesis Hclosed : closed_program W.
Hypothesis Hcb : forall x, (x \in domm Ip) || (x \in domm Ic) -> 1 + x < 2 ^ NC.
Hypothesis HNC : NC < word_size mt.
Hypothesis HKal : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis Hmem : size (linearize_bufs PB) + size (code p ++ code c) < alloc_label.
Hypothesis Hdp : does_prefix (rub_sem NC Ip Ic W) m0.
Hypothesis Hnw : not_wrong_finpref m0.

Hypothesis Hfl : forall X, (X \in domm Ip) || (X \in domm Ic) -> 4 + size (rp_events t X) <= L.
Hypothesis Hft : (size t).+4 < 2 ^ 14.
Hypothesis Hfc :
  size (linearize_bufs (unionm (prog_buffers bp) (prog_buffers bc)))
    + size (code bp ++ code bc) < alloc_label.
Hypothesis Hfc2 :
  size (linearize_bufs (unionm (prog_buffers p) (prog_buffers bc)))
    + size (code p ++ code bc) < alloc_label.

Lemma Hdis : fdisjoint (domm Ip) (domm Ic).
Proof. by case: Hmerg => [[_ Hd] _]. Qed.

Lemma mem_comps X : (X \in comps Ip Ic) = (X \in domm Ip) || (X \in domm Ic).
Proof. by rewrite /comps mem_cat. Qed.

Lemma PI_p X : X \in domm Ip -> PI X = Ip X.
Proof. rewrite unionmE. by case/dommP => v ->. Qed.

Lemma PI_c X : X \in domm Ic -> PI X = Ic X.
Proof.
move=> HX. have Hd : fdisjoint (domm Ic) (domm Ip) by rewrite fdisjointC; exact: Hdis.
have HnI : X \notin domm Ip := fdisjointP Hd X HX.
rewrite unionmE. by move/dommPn: HnI => ->.
Qed.

Lemma obs_run : exists cs',
  Star (mp_sem NC W) (Merged.initial_state (code W) (prog_buffers W) (prog_interface W)) t cs'.
Proof.
have [cs [cs' [Hi Hs]]] := rub_prefix_star Hdp Hnw.
have Ecs : cs = Merged.initial_state (code W) (prog_buffers W) (prog_interface W) := Hi.
exists cs'. rewrite -Ecs. exact: rub_star_mp Hs.
Qed.

Lemma code_W_in i tg : List.In (i, tg) (code W) ->
  List.In (i, tg) (code p) \/ List.In (i, tg) (code c).
Proof. exact: in_cat_or. Qed.

Lemma canon0 : entry_canon PI (mem (Merged.initial_state (code W) (prog_buffers W) (prog_interface W))).
Proof.
apply: initial_entry_canon => i tg e Hin He.
case: (code_W_in Hin) => H.
- exact: (wfmp_eh Hwfp H He).
- exact: (wfmp_eh Hwfc H He).
Qed.

Lemma binv0 : bracket_inv stack_state0
  (Merged.initial_state (code W) (prog_buffers W) (prog_interface W)).
Proof.
apply: initial_bracket_inv => i tg Hin n.
case: (code_W_in Hin) => H.
- have [_ Hv] := low_tags (wfmp_loww Hwfp) H. by rewrite Hv.
- have [_ Hv] := low_tags (wfmp_loww Hwfc) H. by rewrite Hv.
Qed.

Lemma Hwb_t : well_bracketed_trace stack_state0 t.
Proof. have [cs' Hs] := obs_run. by have [H _] := star_bracket Hs binv0. Qed.

Lemma Hobs e : List.In e t ->
  [/\ next_comp_of_event e <> cur_comp_of_event e,
      Z.le (Z.opp (Z.pow 2 31)) (zarg' e) /\ Z.lt (zarg' e) (Z.pow 2 31)
    & forall c0 p0 v c', e = ECall c0 p0 v c' ->
        exists lc, entry (Transitional.head_tag_gen PI c' p0) = Some (p0, lc) /\ c0 \in lc].
Proof. have [cs' Hs] := obs_run. exact: star_obs Hs canon0 e. Qed.

Lemma mem_domm_PI X : X \in domm PI -> X \in comps Ip Ic.
Proof. by rewrite domm_union in_fsetU mem_comps. Qed.

Lemma Hcalls_t C0 P0 z0 C' : List.In (ECall C0 P0 z0 C') t ->
  [/\ P0 \in rp_exports PI C', C0 <> C'
    & C0 \in odflt [::] (omap snd (entry (Transitional.head_tag_gen PI C' P0)))].
Proof.
move=> Hin. have [Hneq _ Hc] := Hobs Hin.
have [lc [Hent Hlc]] := Hc _ _ _ _ (erefl _).
have [i [i' [E1 E2 Hex _]]] := head_entry_facts Hent Hlc.
split.
- by rewrite /rp_exports E1 /=.
- move=> E. apply: Hneq. by rewrite /= E.
- by rewrite Hent /=.
Qed.

Lemma calls_comps C0 P0 z0 C' : List.In (ECall C0 P0 z0 C') t ->
  (C0 \in comps Ip Ic) && (C' \in comps Ip Ic).
Proof.
move=> Hin. have [_ _ Hc] := Hobs Hin.
have [lc [Hent Hlc]] := Hc _ _ _ _ (erefl _).
have [i [i' [E1 E2 _ _]]] := head_entry_facts Hent Hlc.
apply/andP; split; apply: mem_domm_PI; apply/dommP.
- exists i'. exact: E2.
- exists i. exact: E1.
Qed.

Lemma Hmain_c : Component.main \in comps Ip Ic.
Proof.
rewrite mem_comps.
have := cprog_main_existence Hclosed. rewrite /= => /orP [H|H].
- by rewrite (proj2 (wfprog_main_existence (wfmp_wf Hwfp)) H).
- by rewrite (proj2 (wfprog_main_existence (wfmp_wf Hwfc)) H) orbT.
Qed.

Lemma Hcev_t e : List.In e t ->
  (cur_comp_of_event e \in comps Ip Ic) && (next_comp_of_event e \in comps Ip Ic).
Proof.
case: e => [C0 P0 z0 C'|C0 z0 C'] Hin.
- exact: calls_comps Hin.
- have Hm : ERet C0 z0 C' \in t := in_mem_seq Hin.
  have [pre [suf Et]] : exists pre suf, t = pre ++ ERet C0 z0 C' :: suf.
  { have Hi : index (ERet C0 z0 C') t < size t by rewrite index_mem.
    exists (take (index (ERet C0 z0 C') t) t), (drop (index (ERet C0 z0 C') t).+1 t).
    by rewrite -{1}(cat_take_drop (index (ERet C0 z0 C') t) t)
               (drop_nth (ERet C0 z0 C') Hi) nth_index. }
  exact: (@ret_comps (fun X => X \in comps Ip Ic) _ pre C0 z0 C' suf Hwb_t Et Hmain_c
           (fun C1 P1 z1 C2 H => calls_comps H)).
Qed.

Lemma Hcok_c X : X \in comps Ip Ic -> comp_ok L P C PI t X.
Proof.
rewrite mem_comps => HX. split.
- case/orP: HX => H.
  + have Hx : iface_bounded C p := wfmp_ib Hwfp. exact: (Hx X H).
  + have Hx : iface_bounded C c := wfmp_ib Hwfc. exact: (Hx X H).
- apply: Hfl. exact: HX.
- move=> p0. case/orP: HX => H.
  + rewrite /rp_exports (PI_p H). case/dommP: H => CI E. rewrite E /= => Hp.
    have Heb : exports_bounded P p := wfmp_eb Hwfp.
    apply: (Heb X p0). exists CI. split; [exact: E | exact: Hp].
  + rewrite /rp_exports (PI_c H). case/dommP: H => CI E. rewrite E /= => Hp.
    have Heb : exports_bounded P c := wfmp_eb Hwfc.
    apply: (Heb X p0). exists CI. split; [exact: E | exact: Hp].
Qed.

Lemma Hstat_c X : X \in comps Ip Ic ->
  linearize_bufs PB (X, rp_block PB X, 0) <> None.
Proof.
rewrite mem_comps => /orP [H|H].
- have Hr := wfprog_well_formed_buffers (wfmp_wf Hwfp) (C := X).
  have HXb : X \in domm Bp by rewrite -(wfprog_defined_buffers (wfmp_wf Hwfp)).
  have [b Hb] : has_required_local_buffers p X.
  { apply: Hr. case/dommP: H => v E. by rewrite E. }
  case/dommP: HXb => bm Ebm.
  have EPB : PB X = Some bm by rewrite unionmE Ebm.
  apply: (rp_block_ok EPB (b := b)).
  move: Hb. rewrite Ebm /=. by case: (bm b) => [[n|vs]|].
- have Hr := wfprog_well_formed_buffers (wfmp_wf Hwfc) (C := X).
  have HXb : X \in domm Bc by rewrite -(wfprog_defined_buffers (wfmp_wf Hwfc)).
  have HnI : X \notin domm Bp.
  { rewrite -(wfprog_defined_buffers (wfmp_wf Hwfp)).
    have Hd : fdisjoint (domm Ic) (domm Ip) by rewrite fdisjointC; exact: Hdis.
    exact: fdisjointP Hd X H. }
  have [b Hb] : has_required_local_buffers c X.
  { apply: Hr. case/dommP: H => v E. by rewrite E. }
  case/dommP: HXb => bm Ebm.
  have EPB : PB X = Some bm by rewrite unionmE; move/dommPn: HnI => ->.
  apply: (rp_block_ok EPB (b := b)).
  move: Hb. rewrite Ebm /=. by case: (bm b) => [[n|vs]|].
Qed.

Lemma HbufsW_c :
  bufs_shape (unionm (prog_buffers bp) (prog_buffers bc)) = bufs_shape PB.
Proof.
apply/eq_fmap => X. rewrite /bufs_shape /= !mapmE !unionmE !mapmE.
case: (Bp X) => [bm|] /=.
- congr Some. apply/eq_fmap => b. rewrite !mapmE. by case: (bm b).
- case: (Bc X) => [bm|] //=. congr Some. apply/eq_fmap => b. rewrite !mapmE. by case: (bm b).
Qed.

Lemma Hdata_c : size (linearize_bufs PB) < 2 ^ 14.
Proof. apply: leq_ltn_trans _ Hmem. exact: leq_addr. Qed.

Lemma Hcs_c :
  size (initial_memory (mt := mt) (unionm (prog_buffers bp) (prog_buffers bc)))
    + size (code bp ++ code bc) < alloc_label.
Proof.
have Hb : size (linearize_bufs (unionm (prog_buffers bp) (prog_buffers bc))) < 2 ^ word_size mt.
{ apply: leq_ltn_trans _ (ltn_trans Hfc _); first exact: leq_addr.
  by rewrite word_size_mt /alloc_label ltn_exp2l. }
by rewrite (initial_memory_size_eq Hb).
Qed.

Lemma HKt_c : (size t).+4 <= 2 ^ (word_size mt - NC).
Proof. exact: leq_trans (ltnW Hft) (ltnW HKal). Qed.

Lemma Hcomp_c X : X \in comps Ip Ic -> 1 + X < 2 ^ NC.
Proof. rewrite mem_comps. exact: Hcb. Qed.

Lemma Hz_t e : List.In e t ->
  Z.le (Z.opp (Z.pow 2 31)) (zarg e) /\ Z.lt (zarg e) (Z.pow 2 31).
Proof. move=> Hin. by have [_ H _] := Hobs Hin. Qed.

Lemma Hrets_t C0 z0 C' : List.In (ERet C0 z0 C') t -> C0 <> C'.
Proof. move=> Hin E. have [H _ _] := Hobs Hin. apply: H. by rewrite /= E. Qed.

Lemma bt_run_c : does_prefix (me_sem NC (Definitions.program_link bp bc)) m0.
Proof.
exact: (@replay_prefix L P C NC Ip Ic Bp Bc t Hcomp_c (ltnW HNC) HKal HKt_c Hstat_c HbufsW_c
          Hdata_c Hdis Hcok_c Hcs_c Hwb_t Hcev_t Hft Hmain_c Hz_t Hcalls_t Hrets_t
          m0 (erefl _) Hnw).
Qed.

Lemma wfmp_bp : wf_mp L P C PI bp.
Proof.
apply: rp_wfmp.
- exact: PI_p.
- move=> X HX. apply: Hcok_c. by rewrite mem_comps HX.
- exact: Hcalls_t.
- exact: wfprog_interface_soundness (wfmp_wf Hwfp).
- exact: wfprog_defined_buffers (wfmp_wf Hwfp).
- exact: wfprog_well_formed_buffers (wfmp_wf Hwfp).
Qed.

Lemma wfmp_bc : wf_mp L P C PI bc.
Proof.
apply: rp_wfmp.
- exact: PI_c.
- move=> X HX. apply: Hcok_c. by rewrite mem_comps HX orbT.
- exact: Hcalls_t.
- exact: wfprog_interface_soundness (wfmp_wf Hwfc).
- exact: wfprog_defined_buffers (wfmp_wf Hwfc).
- exact: wfprog_well_formed_buffers (wfmp_wf Hwfc).
Qed.

Lemma closed_bt : closed_program (Definitions.program_link bp bc).
Proof.
split.
- exact: cprog_closed_interface Hclosed.
- have := Hmain_c. by rewrite mem_comps.
Qed.

Definition bt_pack : bt_me_package L P C NC p c m0.
Proof.
refine (@Build_bt_me_package L P C NC p c m0 bp bc wfmp_bp wfmp_bc erefl erefl closed_bt
          Hfc Hfc2 _ _ bt_run_c).
- rewrite /= shape_inl. exact: erefl.
- rewrite /= shape_inl. exact: erefl.
Defined.

End Pkg.

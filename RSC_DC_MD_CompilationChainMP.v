Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.
Require Import Common.Traces.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalEpsilon.

Require Import Source.Language.
Require Import Source.Definability.
Require Import Source.Blame.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.BackTranslation.
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import MicroPolicies.Recomposition.TraceInit.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.
Require T2M.MDefs.
Require Import T2M.MBnz.
Require Import T2M.MStatic2.
Require Import T2M.MBwdSrc.
Require Import T2M.MInstance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Types.

Section Generic.

  Variables (a : Intermediate.program) (c : program).

  Local Notation Ia := (Intermediate.prog_interface a).
  Local Notation Ic := (prog_interface c).
  Local Notation PI := (unionm Ia Ic).

  Definition bufsz_mp : NMap nat :=
    unionm (block0_sizes (Intermediate.prog_buffers a)) (block0_sizes (prog_buffers c)).

  Definition back_mp (t : trace) : Source.program :=
    Definability.program_of_trace PI bufsz_mp t.

  Definition btP_mp (t : trace) : Source.program :=
    Source.program_unlink (domm Ia) (back_mp t).

  Definition btC_mp (t : trace) : Source.program :=
    Source.program_unlink (domm Ic) (back_mp t).

  Lemma definability_mp (m : finpref_behavior) :
    linkable Ia Ic ->
    closed_interface PI ->
    PI Component.main ->
    well_formed_trace PI (finpref_trace m) ->
    not_wrong_finpref m ->
    Source.prog_interface (btP_mp (finpref_trace m)) = Ia /\
    Source.prog_interface (btC_mp (finpref_trace m)) = Ic /\
    Source.well_formed_program (btP_mp (finpref_trace m)) /\
    Source.well_formed_program (btC_mp (finpref_trace m)) /\
    Source.closed_program (Source.program_link (btP_mp (finpref_trace m))
                                                   (btC_mp (finpref_trace m))) /\
    does_prefix (S.CS.sem (Source.program_link (btP_mp (finpref_trace m))
                                                   (btC_mp (finpref_trace m)))) m /\
    (forall C, C \in domm Ia ->
           Source.prog_buffers (btP_mp (finpref_trace m)) C
           = Some (inr (nseq (Definability.buf_size bufsz_mp C) (Int 0)))) /\
    (forall C, C \in domm Ic ->
           Source.prog_buffers (btC_mp (finpref_trace m)) C
           = Some (inr (nseq (Definability.buf_size bufsz_mp C) (Int 0)))).
  Proof.
    move=> Hlinkable Hclosed_intf intf_main wf_m Hnot_wrong.
    set m' := finpref_trace m.
    have wf_events : all (well_formed_event PI) m' by case/andP: wf_m.
    have := @definability PI Hclosed_intf intf_main bufsz_mp m' wf_m.
    rewrite -/(back_mp m') => Hback.
    have wf_back : Source.well_formed_program (back_mp m')
      by exact: well_formed_events_well_formed_program.
    have Hclosed_back : Source.closed_program (back_mp m')
      by exact: closed_program_of_trace.
    have Hlink : Source.program_link (btP_mp m') (btC_mp m') = back_mp m'.
    { apply: Source.program_unlinkK; [ by [] | exact: wf_back | exact: Hlinkable ]. }
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - rewrite /btP_mp /= -[RHS](unionmK Ia Ic).
      by apply/eq_filterm=> ??; rewrite mem_domm.
    - rewrite /btC_mp /= unionmC; last by case: Hlinkable.
      rewrite -[RHS](unionmK Ic Ia).
      by apply/eq_filterm=> ??; rewrite mem_domm.
    - exact: Source.well_formed_program_unlink.
    - exact: Source.well_formed_program_unlink.
    - by rewrite Hlink.
    - rewrite Hlink. exists (Terminates m').
      split=> //.
      rewrite /m'; case: (m) Hnot_wrong => //= t _.
      by exists (Terminates nil); rewrite /= E0_right.
    - move=> C HC. rewrite /= filtermE /buffers_of_sizes mkfmapfE.
      have HCu : C \in domm PI by rewrite domm_union in_fsetU HC.
      by rewrite HCu HC.
    - move=> C HC. rewrite /= filtermE /buffers_of_sizes mkfmapfE.
      have HCu : C \in domm PI by rewrite domm_union in_fsetU HC orbT.
      by rewrite HCu HC.
  Qed.

End Generic.

Lemma prescribed_matches_canonical_gen
    (Ib : Program.interface) (Bb : NMap {fmap Block.id -> nat + seq value})
    (P' : Source.program) (bufsz : NMap nat) (ic' : Intermediate.program) :
  domm Ib = domm Bb ->
  bufs_shape Bb
  = mapm (fun n => mkfmap [:: (0 : Block.id, n); (1 : Block.id, 2)]) (block0_sizes Bb) ->
  (forall (C : Component.id) (n : nat), block0_sizes Bb C = Some n -> 0 < n) ->
  Source.well_formed_program P' ->
  compile_program P' = Some ic' ->
  Source.prog_interface P' = Ib ->
  (forall C, C \in domm Ib ->
     Source.prog_buffers P' C
     = Some (inr (nseq (Definability.buf_size bufsz C) (Int 0)))) ->
  (forall C, C \in domm Ib -> bufsz C = block0_sizes Bb C) ->
  bufs_shape (Intermediate.prog_buffers ic') = bufs_shape Bb.
Proof.
move=> Hdom Hcanon Hpos HwfP' Hic' Hif HbufsP' Hpres.
rewrite (compilation_buffers Hic') Hcanon.
apply/eq_fmap => C.
rewrite /bufs_shape /gen_buffers !mapmE.
case HC: (C \in domm Ib); last first.
- have /dommPn -> /= : C \notin domm (Source.prog_buffers P').
  { by rewrite -(Source.wfprog_defined_buffers HwfP') Hif HC. }
  have /dommPn HnB : C \notin domm Bb by rewrite -Hdom HC.
  by rewrite HnB.
- rewrite (HbufsP' C HC) /=.
  have HCb : C \in domm Bb by rewrite -Hdom HC.
  case/dommP: HCb => bm Hbm.
  rewrite Hbm /=.
  congr Some.
  have Hn : bufsz C = Some (odflt 1 (omap bsize (bm (0 : Block.id)))).
  { by rewrite (Hpres C HC) /block0_sizes mapmE Hbm. }
  have Hposn : 0 < odflt 1 (omap bsize (bm (0 : Block.id))).
  { apply: (Hpos C).
    by rewrite /block0_sizes mapmE Hbm. }
  apply/eq_fmap => blk.
  rewrite mapmE !setmE.
  case: (blk == 0 :> nat) => //=; last by case: (blk == 1 :> nat).
  congr Some.
  rewrite size_nseq /Definability.buf_size Hn /=.
  by lia.
Qed.

Lemma intermediate_closed_link (a b : Intermediate.program) :
  Intermediate.well_formed_program a ->
  Intermediate.well_formed_program b ->
  linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
  closed_interface (unionm (Intermediate.prog_interface a) (Intermediate.prog_interface b)) ->
  Component.main \in domm (unionm (Intermediate.prog_interface a)
                                  (Intermediate.prog_interface b)) ->
  Intermediate.closed_program (Intermediate.program_link a b).
Proof.
move=> Hwa Hwb [_ Hdis] Hcl Hmain.
constructor; first exact: Hcl.
move: Hmain; rewrite domm_union in_fsetU => /orP [Ha | Hb].
- have Hma : Intermediate.prog_main a by apply/(Intermediate.wfprog_main_component Hwa).
  have [procs [Hp Hin]] := Intermediate.wfprog_main_existence Hwa Hma.
  exists procs. split; first by rewrite /= Hma.
  by rewrite /= unionmE Hp.
- have Hmb : Intermediate.prog_main b by apply/(Intermediate.wfprog_main_component Hwb).
  have [procs [Hp Hin]] := Intermediate.wfprog_main_existence Hwb Hmb.
  exists procs. split; first by rewrite /= Hmb orbT.
  have HnA : Component.main \notin domm (Intermediate.prog_procedures a).
  { rewrite -(Intermediate.wfprog_defined_procedures Hwa).
    have Hdis' : fdisjoint (domm (Intermediate.prog_interface b))
                           (domm (Intermediate.prog_interface a)) by rewrite fdisjointC.
    exact: (fdisjointP Hdis' _ Hb). }
  by rewrite /= unionmE (dommPn HnA) Hp.
Qed.

Lemma rub_trace_wf_mp (L P C NC : nat) (p c : program) (m : finpref_behavior) :
  wf_mp L P C (unionm (prog_interface p) (prog_interface c)) p ->
  wf_mp L P C (unionm (prog_interface p) (prog_interface c)) c ->
  does_prefix (rub_sem NC (prog_interface p) (prog_interface c) (program_link p c)) m ->
  not_wrong_finpref m ->
  well_formed_trace (unionm (prog_interface p) (prog_interface c)) (finpref_trace m).
Proof.
move=> Hwfp Hwfc Hdp Hnw.
have [cs [cs' [Hi Hs]]] := rub_prefix_star Hdp Hnw.
have Ecs : cs = Merged.initial_state (code (program_link p c))
                  (prog_buffers (program_link p c)) (prog_interface (program_link p c)) := Hi.
apply: (star_well_formed_trace (rub_star_mp Hs)).
- rewrite Ecs. apply: initial_entry_sound => i t p0 lc c0 Hin Hent Hc.
  have Ht : t = Transitional.head_tag_gen (unionm (prog_interface p) (prog_interface c))
                  (color t) (p0, lc).1.
  { case: (List.in_app_or _ _ _ Hin) => H.
    - exact: (wfmp_eh Hwfp H Hent).
    - exact: (wfmp_eh Hwfc H Hent). }
  rewrite Ht in Hent.
  have [i' [Hgi [Himp HcI]]] := head_tag_entry_sound Hent Hc.
  by rewrite /imported_procedure_b Hgi.
- rewrite Ecs. apply: initial_bracket_inv => i tg Hin n.
  case: (List.in_app_or _ _ _ Hin) => H.
  + have [_ Hv] := low_tags (wfmp_loww Hwfp) H. by rewrite Hv.
  + have [_ Hv] := low_tags (wfmp_loww Hwfc) H. by rewrite Hv.
Qed.

Section Fits.

  Variables (L P C : nat) (a : Intermediate.program) (c : program).

  Record fit_pack_mp (t : trace) (ip' ic' : Intermediate.program) : Prop := {
    fm_cip  : compile_program (btP_mp a c t) = Some ip';
    fm_cic  : compile_program (btC_mp a c t) = Some ic';
    fm_lokp : BackTranslation.lin_ok_at L P C ip';
    fm_immp : MDefs.imm_fits ip';
    fm_lokc : BackTranslation.lin_ok_at L P C ic';
    fm_immc : MDefs.imm_fits ic';
    fm_lfp  : MDefs.link_fits L P C ip' ic';
    fm_lfa  : MDefs.link_fits L P C a ic';
    fm_rfp  : MDefs.run_fits (MDefs.cde ip' ic') (Intermediate.program_link ip' ic') t;
    fm_rfa  : MDefs.run_fits (MDefs.cde a ic') (Intermediate.program_link a ic') t
  }.

  Definition bt_fits_mp (t : trace) : Prop :=
    exists ip' ic', fit_pack_mp t ip' ic'.

End Fits.

Module Type ChainMPInput.

  Parameter p : Source.program.
  Parameter c : program.
  Parameter fm : finpref_behavior.
  Parameter L P C : nat.

  Parameter p_compiled : Intermediate.program.
  Axiom successful_compilation : compile_program p = Some p_compiled.

  Definition PB := unionm (Intermediate.prog_buffers p_compiled) (prog_buffers c).
  Definition PI := unionm (Intermediate.prog_interface p_compiled) (prog_interface c).
  Definition lin (q : Intermediate.program) : program := compiler L P C PB PI q.

  Axiom well_formed_p : Source.well_formed_program p.
  Axiom p_ok : MDefs.t2m_ok L P C p_compiled /\ canonical_bufs p_compiled.
  Axiom wfmp_c : wf_mp L P C PI c.
  Axiom canonical_c :
    bufs_shape (prog_buffers c)
    = mapm (fun n => mkfmap [:: (0 : Block.id, n); (1 : Block.id, 2)])
           (block0_sizes (prog_buffers c))
    /\ (forall (C : Component.id) (n : nat),
          block0_sizes (prog_buffers c) C = Some n -> 0 < n).
  Axiom mergeable :
    mergeable_interfaces (Intermediate.prog_interface p_compiled) (prog_interface c).
  Axiom closed : closed_program (program_link (lin p_compiled) c).
  Axiom comp_bound : forall x,
    (x \in domm (Intermediate.prog_interface p_compiled)) || (x \in domm (prog_interface c)) ->
    1 + x < 2 ^ MDefs.NC.
  Axiom size_fit :
    size (linearize_bufs (unionm (prog_buffers (lin p_compiled)) (prog_buffers c)))
      + size (code (lin p_compiled) ++ code c) < alloc_label.

  Axiom target_prefix :
    does_prefix (mp_sem MDefs.NC (program_link (lin p_compiled) c)) fm.
  Axiom safe_prefix : not_wrong_finpref fm.
  Axiom prefix_fits : forall t,
    trace_finpref_prefix t fm -> bt_fits_mp L P C p_compiled c t.

End ChainMPInput.

Lemma trace_prefix_refl (t : trace) : trace_prefix t t.
Proof. by exists E0; rewrite E0_right. Qed.

Definition behavior_improves_blame_mp (b : program_behavior)
           (m : finpref_behavior) (p : Source.program) :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m /\
             undef_in t (Source.prog_interface p).

Lemma trace_prefix_trans_mp : forall (a b c : trace),
  trace_prefix a b -> trace_prefix b c -> trace_prefix a c.
Proof.
  move=> a b c [x Hx] [y Hy].
  exists (x ** y). by rewrite Hy Hx Eapp_assoc.
Qed.

Lemma trace_prefix_antisym_mp : forall (a b : trace),
  trace_prefix a b -> trace_prefix b a -> a = b.
Proof.
  move=> a b [x Hx] [y Hy].
  have Ha' : a ** E0 = a ** (x ** y).
  { rewrite E0_right. by rewrite {1}Hy Hx Eapp_assoc. }
  have H0 : E0 = x ** y := List.app_inv_head _ _ _ Ha'.
  case: (Eapp_E0_inv _ _ (esym H0)) => Hx0 _.
  by rewrite Hx Hx0 E0_right.
Qed.

Lemma prefix_gw_mp : forall t (b : program_behavior),
  CompCertExtensions.prefix (FGoes_wrong t) b -> b = Goes_wrong t.
Proof.
  move=> t. case=> //= t2 ->. by [].
Qed.

Lemma behavior_prefix_gw_mp : forall t t3,
  behavior_prefix t (Goes_wrong t3) -> trace_prefix t t3.
Proof.
  move=> t t3 [b' Hb'].
  case: b' Hb' => [t2|t2|T2|t2] /= Hb'; try by [].
  case: Hb' => ->. by exists t2.
Qed.

Lemma improves_to_prefix_mp : forall (L : semantics) beh mfin,
  program_behaves L beh ->
  (CompCertExtensions.prefix mfin beh
   \/ behavior_improves_finpref beh mfin) ->
  does_prefix L mfin
  \/ exists t'', [/\ beh = Goes_wrong t'',
                    does_prefix L (FGoes_wrong t'')
                  & trace_finpref_prefix t'' mfin].
Proof.
  move=> L beh mfin Hb [Hp | [t'' [Eb Hpref]]].
  - left. by exists beh.
  - right. exists t''. split=> //.
    exists (Goes_wrong t''). split; first by rewrite -Eb.
    by [].
Qed.

Module ChainMP (In : ChainMPInput).

  Module I <: T2M_K_Input.
    Definition L := In.L.
    Definition P := In.P.
    Definition C := In.C.
    Definition PB := In.PB.
    Definition PI := In.PI.
  End I.

  Module K := K_T2M I.

  Local Notation Ia := (Intermediate.prog_interface In.p_compiled).
  Local Notation Ic := (prog_interface In.c).

  Lemma wf_p_compiled : Intermediate.well_formed_program In.p_compiled.
  Proof.
    exact: (Compiler.compilation_preserves_well_formedness
              In.well_formed_p In.successful_compilation).
  Qed.

  Lemma iface_p_compiled : Ia = Source.prog_interface In.p.
  Proof.
    exact: (Compiler.compilation_preserves_interface _ _ In.successful_compilation).
  Qed.

  Lemma linkable_pc : linkable Ia Ic.
  Proof. by case: In.mergeable. Qed.

  Lemma closed_iface_pc : closed_interface In.PI.
  Proof. by case: In.mergeable. Qed.

  Lemma disjoint_pc : fdisjoint (domm Ia) (domm Ic).
  Proof. by case: linkable_pc. Qed.

  Lemma main_in_PI : Component.main \in domm In.PI.
  Proof.
    have Hm : prog_main (In.lin In.p_compiled) || prog_main In.c
      := cprog_main_existence In.closed.
    have Ep : prog_main (In.lin In.p_compiled) = (Component.main \in domm Ia) by [].
    rewrite Ep in Hm.
    rewrite /In.PI domm_union in_fsetU.
    case/orP: Hm => [-> // | Hc].
    apply/orP; right.
    exact: (proj2 (wfprog_main_existence (wfmp_wf In.wfmp_c)) Hc).
  Qed.

  Lemma PI_main : In.PI Component.main.
  Proof. by rewrite -mem_domm main_in_PI. Qed.

  Module Lft <: MEtoMP_Left.
    Definition p : program := In.lin In.p_compiled.
    Definition c : program := In.c.
    Definition L := In.L.
    Definition P := In.P.
    Definition C := In.C.
    Definition NC := MDefs.NC.

    Lemma Hwfmp_p : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) p.
    Proof.
      case: In.p_ok => [[Hlok _ _] _].
      case: Hlok => Hne Hbuf HbL HbP HbC.
      apply: compiler_wf_mp.
      - exact: wf_p_compiled.
      - exact: HbL.
      - exact: HbP.
      - exact: HbC.
      - exact: Hne.
      - exact: Hbuf.
    Qed.

    Lemma Hwfmp_c : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) c.
    Proof. exact: In.wfmp_c. Qed.

    Lemma Hmergeable : mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof. exact: In.mergeable. Qed.

    Lemma Hclosed : closed_program (program_link p c).
    Proof. exact: In.closed. Qed.

    Lemma comps_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
    Proof. exact: In.comp_bound. Qed.

    Lemma NC_lt_word : NC < word_size mt.
    Proof. exact: K.NC_lt_word. Qed.

    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. exact: K.alloc_label_lt_word_NC. Qed.

    Lemma memory_size_pc :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: In.size_fit. Qed.
  End Lft.

  Definition ipc (t : trace) : Intermediate.program :=
    odflt In.p_compiled (compile_program (btP_mp In.p_compiled In.c t)).
  Definition icc (t : trace) : Intermediate.program :=
    odflt In.p_compiled (compile_program (btC_mp In.p_compiled In.c t)).

  Lemma canon (a b x : Intermediate.program) :
    memory_lengths (MDefs.PBw a b) = memory_lengths In.PB ->
    MDefs.PIw a b = In.PI ->
    In.lin x = compiler In.L In.P In.C (MDefs.PBw a b) (MDefs.PIw a b) x.
  Proof. exact: K.lin_canonical. Qed.

  Section Back.

    Variable m0 : finpref_behavior.
    Hypothesis Hrub : does_prefix (rub_sem Lft.NC (prog_interface Lft.p) (prog_interface Lft.c)
                                           (program_link Lft.p Lft.c)) m0.
    Hypothesis Hnw : not_wrong_finpref m0.
    Hypothesis Hfit : bt_fits_mp In.L In.P In.C In.p_compiled In.c (finpref_trace m0).

    Local Notation t := (finpref_trace m0).
    Local Notation P' := (btP_mp In.p_compiled In.c t).
    Local Notation Cs := (btC_mp In.p_compiled In.c t).
    Local Notation ip' := (ipc t).
    Local Notation ic' := (icc t).

    Lemma back_wft : well_formed_trace In.PI t.
    Proof. exact: (rub_trace_wf_mp Lft.Hwfmp_p Lft.Hwfmp_c Hrub Hnw). Qed.

    Definition back_def :=
      @definability_mp In.p_compiled In.c m0 linkable_pc closed_iface_pc PI_main back_wft Hnw.

    Lemma ifP' : Source.prog_interface P' = Ia.
    Proof. by case: back_def. Qed.
    Lemma ifCs : Source.prog_interface Cs = Ic.
    Proof. by case: back_def => _ []. Qed.
    Lemma wfP' : Source.well_formed_program P'.
    Proof. by case: back_def => _ [_ []]. Qed.
    Lemma wfCs : Source.well_formed_program Cs.
    Proof. by case: back_def => _ [_ [_ []]]. Qed.
    Lemma src_closed : Source.closed_program (Source.program_link P' Cs).
    Proof. by case: back_def => _ [_ [_ [_ []]]]. Qed.
    Lemma src_run : does_prefix (S.CS.sem (Source.program_link P' Cs)) m0.
    Proof. by case: back_def => _ [_ [_ [_ [_ []]]]]. Qed.
    Lemma bufP' : forall C, C \in domm Ia ->
      Source.prog_buffers P' C
      = Some (inr (nseq (Definability.buf_size (bufsz_mp In.p_compiled In.c) C) (Int 0))).
    Proof. by case: back_def => _ [_ [_ [_ [_ [_ []]]]]]. Qed.
    Lemma bufCs : forall C, C \in domm Ic ->
      Source.prog_buffers Cs C
      = Some (inr (nseq (Definability.buf_size (bufsz_mp In.p_compiled In.c) C) (Int 0))).
    Proof. by case: back_def => _ [_ [_ [_ [_ [_ [_ ]]]]]]. Qed.

    Lemma fit_ok : fit_pack_mp In.L In.P In.C In.p_compiled In.c t ip' ic'.
    Proof.
      case: Hfit => ip1 [ic1 H].
      by rewrite /ipc /icc (fm_cip H) (fm_cic H).
    Qed.

    Lemma comp_P' : compile_program P' = Some ip'.
    Proof. exact: (fm_cip fit_ok). Qed.
    Lemma comp_Cs : compile_program Cs = Some ic'.
    Proof. exact: (fm_cic fit_ok). Qed.

    Lemma wf_ip' : Intermediate.well_formed_program ip'.
    Proof. exact: (Compiler.compilation_preserves_well_formedness wfP' comp_P'). Qed.
    Lemma wf_ic' : Intermediate.well_formed_program ic'.
    Proof. exact: (Compiler.compilation_preserves_well_formedness wfCs comp_Cs). Qed.

    Lemma iface_ip' : Intermediate.prog_interface ip' = Ia.
    Proof. by rewrite (Compiler.compilation_preserves_interface _ _ comp_P') ifP'. Qed.
    Lemma iface_ic' : Intermediate.prog_interface ic' = Ic.
    Proof. by rewrite (Compiler.compilation_preserves_interface _ _ comp_Cs) ifCs. Qed.

    Lemma t2m_ip' : MDefs.t2m_ok In.L In.P In.C ip'.
    Proof.
      split.
      - exact: (fm_lokp fit_ok).
      - exact: (compiled_branches_forward comp_P').
      - exact: (fm_immp fit_ok).
    Qed.
    Lemma t2m_ic' : MDefs.t2m_ok In.L In.P In.C ic'.
    Proof.
      split.
      - exact: (fm_lokc fit_ok).
      - exact: (compiled_branches_forward comp_Cs).
      - exact: (fm_immc fit_ok).
    Qed.

    Lemma wfmp_lin (x : Intermediate.program) :
      Intermediate.well_formed_program x -> MDefs.t2m_ok In.L In.P In.C x ->
      wf_mp In.L In.P In.C In.PI (In.lin x).
    Proof.
      move=> Hwf [Hlok _ _].
      case: Hlok => Hne Hbuf HbL HbP HbC.
      apply: compiler_wf_mp.
      - exact: Hwf.
      - exact: HbL.
      - exact: HbP.
      - exact: HbC.
      - exact: Hne.
      - exact: Hbuf.
    Qed.

    Lemma pres_a : forall C, C \in domm Ia ->
      bufsz_mp In.p_compiled In.c C = block0_sizes (Intermediate.prog_buffers In.p_compiled) C.
    Proof.
      move=> C HC.
      rewrite /bufsz_mp unionmE.
      have: C \in domm (block0_sizes (Intermediate.prog_buffers In.p_compiled)).
      { rewrite /block0_sizes domm_map.
        by rewrite -(Intermediate.wfprog_defined_buffers wf_p_compiled). }
      rewrite mem_domm.
      by case: (block0_sizes (Intermediate.prog_buffers In.p_compiled) C).
    Qed.

    Lemma pres_c : forall C, C \in domm Ic ->
      bufsz_mp In.p_compiled In.c C = block0_sizes (prog_buffers In.c) C.
    Proof.
      move=> C HC.
      rewrite /bufsz_mp unionmE.
      have HnA : block0_sizes (Intermediate.prog_buffers In.p_compiled) C = None.
      { apply/dommPn.
        rewrite /block0_sizes domm_map.
        rewrite -(Intermediate.wfprog_defined_buffers wf_p_compiled).
        have Hd : fdisjoint (domm Ic) (domm Ia) by rewrite fdisjointC; exact: disjoint_pc.
        exact: (fdisjointP Hd _ HC). }
      by rewrite HnA.
    Qed.

    Lemma shape_p : bufs_shape (Intermediate.prog_buffers ip')
                    = bufs_shape (Intermediate.prog_buffers In.p_compiled).
    Proof.
      apply: (prescribed_matches_canonical wf_p_compiled (proj2 In.p_ok) wfP' comp_P'
                ifP' bufP').
      exact: pres_a.
    Qed.

    Lemma shape_c : bufs_shape (Intermediate.prog_buffers ic') = bufs_shape (prog_buffers In.c).
    Proof.
      apply: (prescribed_matches_canonical_gen _ (proj1 In.canonical_c) (proj2 In.canonical_c)
                wfCs comp_Cs ifCs bufCs).
      - exact: (wfprog_defined_buffers (wfmp_wf In.wfmp_c)).
      - exact: pres_c.
    Qed.

    Lemma Emsz' : memory_lengths (MDefs.PBw ip' ic') = memory_lengths In.PB.
    Proof.
      apply: memory_lengths_shape.
      rewrite /MDefs.PBw /In.PB (bufs_shape_unionm_l _ shape_p).
      by rewrite (bufs_shape_unionm_r _ shape_c).
    Qed.
    Lemma EPI' : MDefs.PIw ip' ic' = In.PI.
    Proof. by rewrite /MDefs.PIw iface_ip' iface_ic'. Qed.
    Lemma Emsza : memory_lengths (MDefs.PBw In.p_compiled ic') = memory_lengths In.PB.
    Proof.
      apply: memory_lengths_shape.
      rewrite /MDefs.PBw /In.PB.
      by rewrite (bufs_shape_unionm_r _ shape_c).
    Qed.
    Lemma EPIa : MDefs.PIw In.p_compiled ic' = In.PI.
    Proof. by rewrite /MDefs.PIw iface_ic'. Qed.

    Lemma closed_I : Intermediate.closed_program (Intermediate.program_link ip' ic').
    Proof.
      apply: intermediate_closed_link.
      - exact: wf_ip'.
      - exact: wf_ic'.
      - rewrite iface_ip' iface_ic'. exact: linkable_pc.
      - rewrite iface_ip' iface_ic'. exact: closed_iface_pc.
      - rewrite iface_ip' iface_ic'. exact: main_in_PI.
    Qed.

    Lemma closed_pI : Intermediate.closed_program (Intermediate.program_link In.p_compiled ic').
    Proof.
      apply: intermediate_closed_link.
      - exact: wf_p_compiled.
      - exact: wf_ic'.
      - rewrite iface_ic'. exact: linkable_pc.
      - rewrite iface_ic'. exact: closed_iface_pc.
      - rewrite iface_ic'. exact: main_in_PI.
    Qed.

    Lemma back_run : does_prefix (me_sem Lft.NC (program_link (In.lin ip') (In.lin ic'))) m0.
    Proof.
      have Hlink' : linkable (Intermediate.prog_interface ip') (Intermediate.prog_interface ic').
      { rewrite iface_ip' iface_ic'. exact: linkable_pc. }
      have Hprem' : MDefs.t2me_premises In.L In.P In.C ip' ic'.
      { split; [|split].
        - split.
          + by exists P'; split; [exact: wfP' | exact: comp_P'].
          + by exists Cs; split; [exact: wfCs | exact: comp_Cs].
          + exact: wf_ip'.
          + exact: wf_ic'.
          + exact: Hlink'.
        - exact: closed_I.
        - split.
          + exact: t2m_ip'.
          + exact: t2m_ic'.
          + exact: (fm_lfp fit_ok). }
      have Hme : does_prefix (MDefs.mesem In.L In.P In.C ip' ic') m0.
      { have [MM [HMM Hdsy0]] := @disch_dsy0 In.L In.P In.C ip' ic' Hprem'.
        exact: (t2me_bt_run wfP' wfCs src_closed comp_P' comp_Cs Hlink' closed_I
                  t2m_ip' t2m_ic' (fm_lfp fit_ok) HMM
                  (@disch_HcstT In.L In.P In.C ip' ic' Hprem')
                  (@disch_HuniqT In.L In.P In.C ip' ic' Hprem')
                  (Hdsy0 m0) src_run Hnw (fm_rfp fit_ok)). }
      move: Hme.
      by rewrite (canon ip' Emsz' EPI') (canon ic' Emsz' EPI').
    Qed.

    Lemma back_closed : closed_program (program_link (In.lin ip') (In.lin ic')).
    Proof.
      constructor.
      - have -> : prog_interface (program_link (In.lin ip') (In.lin ic'))
                  = unionm (Intermediate.prog_interface ip') (Intermediate.prog_interface ic')
          by [].
        rewrite iface_ip' iface_ic'. exact: closed_iface_pc.
      - have -> : prog_main (program_link (In.lin ip') (In.lin ic'))
                  = (Component.main \in domm (Intermediate.prog_interface ip'))
                    || (Component.main \in domm (Intermediate.prog_interface ic')) by [].
        rewrite iface_ip' iface_ic'.
        by move: main_in_PI; rewrite /In.PI domm_union in_fsetU.
    Qed.

    Lemma back_size' :
      size (linearize_bufs (unionm (prog_buffers (In.lin ip')) (prog_buffers (In.lin ic'))))
        + size (code (In.lin ip') ++ code (In.lin ic')) < alloc_label.
    Proof.
      have [Hsz _] := fm_lfp fit_ok.
      move: Hsz.
      by rewrite (canon ip' Emsz' EPI') (canon ic' Emsz' EPI').
    Qed.

    Lemma back_size'' :
      size (linearize_bufs (unionm (prog_buffers Lft.p) (prog_buffers (In.lin ic'))))
        + size (code Lft.p ++ code (In.lin ic')) < alloc_label.
    Proof.
      have [Hsz _] := fm_lfa fit_ok.
      move: Hsz.
      by rewrite /Lft.p (canon In.p_compiled Emsza EPIa) (canon ic' Emsza EPIa).
    Qed.

  End Back.

  Module BT <: H_bt_me Lft.

    Definition bt_fits (t : trace) : Prop :=
      forall t', trace_prefix t' t -> bt_fits_mp In.L In.P In.C In.p_compiled In.c t'.

    Lemma bt_fits_prefix : forall t1 t2, trace_prefix t1 t2 -> bt_fits t2 -> bt_fits t1.
    Proof.
      move=> t1 t2 [s E2] H t' [s' E1].
      apply: H. exists (s' ** s). by rewrite E2 E1 Eapp_assoc.
    Qed.

    Definition back (m0 : finpref_behavior)
        (Hrub : does_prefix (rub_sem Lft.NC (prog_interface Lft.p) (prog_interface Lft.c)
                                     (program_link Lft.p Lft.c)) m0)
        (Hnw : not_wrong_finpref m0)
        (Hf : bt_fits (finpref_trace m0)) :
        bt_me_package Lft.L Lft.P Lft.C Lft.NC Lft.p Lft.c m0 :=
      let Hfit := Hf (finpref_trace m0) (trace_prefix_refl _) in
      @Build_bt_me_package Lft.L Lft.P Lft.C Lft.NC Lft.p Lft.c m0
        (In.lin (ipc (finpref_trace m0))) (In.lin (icc (finpref_trace m0)))
        (wfmp_lin (wf_ip' Hrub Hnw Hfit) (t2m_ip' Hfit))
        (wfmp_lin (wf_ic' Hrub Hnw Hfit) (t2m_ic' Hfit))
        (esym (iface_ip' Hrub Hnw Hfit))
        (esym (iface_ic' Hrub Hnw Hfit))
        (back_closed Hrub Hnw Hfit)
        (back_size' Hrub Hnw Hfit)
        (back_size'' Hrub Hnw Hfit)
        (esym (shape_p Hrub Hnw Hfit))
        (esym (shape_c Hrub Hnw Hfit))
        (back_run Hrub Hnw Hfit).

  End BT.

  Module Obs <: ObservedRun Lft BT.
    Definition fm := In.fm.
    Definition observed := In.target_prefix.
    Definition safe := In.safe_prefix.
    Lemma fits : BT.bt_fits (finpref_trace fm).
    Proof.
      move=> t' Hpre. apply: In.prefix_fits.
      move: Hpre. rewrite /fm. by case: In.fm.
    Qed.
  End Obs.

  Module M := RSC_ME_MP_Faithful Lft BT Obs.

  Local Notation t0 := (finpref_trace M.M0).

  Lemma rub0 : does_prefix (rub_sem Lft.NC (prog_interface Lft.p) (prog_interface Lft.c)
                                    (program_link Lft.p Lft.c)) M.M0.
  Proof. by case: (proj2_sig M.mp_pack). Qed.

  Lemma nw0 : not_wrong_finpref M.M0.
  Proof. by case: (proj2_sig M.mp_pack). Qed.

  Lemma fit0 : bt_fits_mp In.L In.P In.C In.p_compiled In.c t0.
  Proof.
    have H : BT.bt_fits t0 := M.M0_fits.
    exact: (H t0 (trace_prefix_refl t0)).
  Qed.

  Lemma cc_pkg : bt_cc M.pkg = In.lin (icc t0).
  Proof. rewrite /M.pkg. by case: (proj2_sig M.mp_pack). Qed.

  Local Notation Cs := (btC_mp In.p_compiled In.c t0).
  Local Notation P' := (btP_mp In.p_compiled In.c t0).

  Lemma wf_Cs : Source.well_formed_program Cs.
  Proof. exact: (wfCs rub0 nw0). Qed.

  Lemma iface_Cs : Source.prog_interface Cs = Ic.
  Proof. exact: (ifCs rub0 nw0). Qed.

  Lemma iface_P'_p : Source.prog_interface P' = Source.prog_interface In.p.
  Proof. by rewrite (ifP' rub0 nw0) iface_p_compiled. Qed.

  Lemma linkable_p_Cs :
    linkable (Source.prog_interface In.p) (Source.prog_interface Cs).
  Proof. rewrite iface_Cs -iface_p_compiled. exact: linkable_pc. Qed.

  Lemma closed_p_Cs : Source.closed_program (Source.program_link In.p Cs).
  Proof.
    exact: (Source.interface_preserves_closedness_l (src_closed rub0 nw0) iface_P'_p
              (wfP' rub0 nw0) In.well_formed_p).
  Qed.

  Lemma comp_Cs0 : compile_program Cs = Some (icc t0).
  Proof. exact: (comp_Cs fit0). Qed.

  Lemma lin_ok_ic : K.lin_ok (icc t0).
  Proof.
    split.
    - exact: (t2m_ic' fit0).
    - exact: (compiled_canonical wf_Cs comp_Cs0).
  Qed.

  Lemma linkable_p_ic :
    linkable Ia (Intermediate.prog_interface (icc t0)).
  Proof. rewrite (iface_ic' rub0 nw0 fit0). exact: linkable_pc. Qed.

  Lemma run_ok0 : K.run_ok In.p_compiled (icc t0) t0.
  Proof.
    split.
    - exact: (fm_lfa (fit_ok fit0)).
    - exact: (fm_rfa (fit_ok fit0)).
    - exact: (Emsza rub0 nw0 fit0).
    - exact: (EPIa rub0 nw0 fit0).
  Qed.

  Lemma sem''_me : forall m,
    does_prefix M.Trec.sem'' m ->
    does_prefix (me_sem K.NC (program_link (K.lin In.p_compiled) (K.lin (icc t0)))) m.
  Proof.
    move=> m H.
    have H' : does_prefix (me_sem Lft.NC (program_link Lft.p (bt_cc M.pkg))) m := H.
    by rewrite cc_pkg in H'.
  Qed.

  Theorem RSC_DC_MD_CompilationChainMP :
    exists Cs beh,
      Source.prog_interface Cs = prog_interface In.c /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface In.p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link In.p Cs) /\
      program_behaves (S.CS.sem (Source.program_link In.p Cs)) beh /\
      (CompCertExtensions.prefix In.fm beh
       \/ behavior_improves_blame_mp beh In.fm In.p).
  Proof.
    have Hrun : does_prefix M.Trec.sem' M.M0 := bt_run M.pkg.
    case: (proj2_sig M.mp_pack) => HA HB Hcases.
    have HAr : does_prefix M.Trec.sem M.M0 := HA.
    have Hfinale : exists beh1,
        program_behaves (S.CS.sem (Source.program_link In.p Cs)) beh1
        /\ (CompCertExtensions.prefix In.fm beh1
            \/ behavior_improves_blame_mp beh1 In.fm In.p).
    { case: Hcases => [[Efm Hfull] | [t' [Em0 Hgw Hpref Hundef]]].
      - have Hsem'' : does_prefix M.Trec.sem'' In.fm.
        { apply: M.Trec.recomposition_blame.
          - exact: Hfull.
          - have Em : M.M0 = In.fm := Efm. rewrite -Em. exact: Hrun. }
        have Hruok : K.run_ok In.p_compiled (icc t0) (finpref_trace In.fm).
        { have Em : M.M0 = In.fm := Efm. rewrite -Em. exact: run_ok0. }
        have [beh1 [Hbeh1 Himp1]] := K.H_bwd_src In.well_formed_p wf_Cs closed_p_Cs
          In.successful_compilation comp_Cs0 In.p_ok lin_ok_ic
          linkable_p_ic (closed_pI rub0 nw0 fit0) (sem''_me Hsem'') Hruok.
        case: (improves_to_prefix_mp Hbeh1 Himp1)
          => [[beh2 [Hb2 Hp2]] | [t3 [Eb3 _ Ht3]]].
        + exists beh2. split; [exact: Hb2 | by left].
        + subst beh1.
          have Hsrc : does_prefix (S.CS.sem (Source.program_link P' Cs)) In.fm.
          { have Em : M.M0 = In.fm := Efm. rewrite -Em. exact: (src_run rub0 nw0). }
          case: (Blame.blame_program In.well_formed_p wf_Cs
                   linkable_p_Cs closed_p_Cs Hbeh1 (wfP' rub0 nw0)
                   iface_P'_p (src_closed rub0 nw0) Hsrc In.safe_prefix Ht3)
            => [Hpm | Hundef].
          * exists (Goes_wrong t3). split; [exact: Hbeh1 | by left].
          * exists (Goes_wrong t3). split; [exact: Hbeh1 |].
            right. exists t3.
            split; first by [].
            split; [exact: Ht3 | exact: Hundef].
      - have Em : M.M0 = FTbc t' := Em0.
        have Hsem'' : does_prefix M.Trec.sem'' (FGoes_wrong t').
        { apply: M.Trec.recomposition_blame'.
          - exact: Hgw.
          - rewrite -Em. exact: Hrun.
          - exact: Hundef. }
        have Hruok : K.run_ok In.p_compiled (icc t0) (finpref_trace (FGoes_wrong t')).
        { have -> : finpref_trace (FGoes_wrong t') = t0 by rewrite Em.
          exact: run_ok0. }
        have [beh1 [Hbeh1 Himp1]] := K.H_bwd_src In.well_formed_p wf_Cs closed_p_Cs
          In.successful_compilation comp_Cs0 In.p_ok lin_ok_ic
          linkable_p_ic (closed_pI rub0 nw0 fit0) (sem''_me Hsem'') Hruok.
        have [t3 [Eb3 Ht3t']] : exists t3,
            beh1 = Goes_wrong t3 /\ trace_prefix t3 t'.
        { case: Himp1 => [Hp1 | [t3 [Eb3 Hp3]]].
          - have Eb1 := prefix_gw_mp Hp1. exists t'. split.
            + exact: Eb1.
            + by exists E0; rewrite E0_right.
          - exists t3. by split. }
        subst beh1.
        have Ht3fm : trace_finpref_prefix t3 In.fm.
        { have Hpref' : trace_finpref_prefix t' In.fm := Hpref.
          move: Hpref'. case: In.fm => t0' /= H2; exact: (trace_prefix_trans_mp Ht3t' H2). }
        have Hsrc : does_prefix (S.CS.sem (Source.program_link P' Cs)) (FTbc t').
        { rewrite -Em. exact: (src_run rub0 nw0). }
        have HK : trace_finpref_prefix t3 (FTbc t') := Ht3t'.
        case: (Blame.blame_program In.well_formed_p wf_Cs
                 linkable_p_Cs closed_p_Cs Hbeh1 (wfP' rub0 nw0)
                 iface_P'_p (src_closed rub0 nw0) Hsrc I HK)
          => [Hpm | Hundef'].
        + have Ht't3 : trace_prefix t' t3 := behavior_prefix_gw_mp Hpm.
          have Et3 : t3 = t' := trace_prefix_antisym_mp Ht3t' Ht't3.
          subst t3.
          exists (Goes_wrong t'). split; [exact: Hbeh1 |].
          right. exists t'.
          split; first by [].
          split; first exact: Hpref.
          move: Hundef. by rewrite /undef_in /= iface_p_compiled.
        + exists (Goes_wrong t3). split; [exact: Hbeh1 |].
          right. exists t3.
          split; first by [].
          split; [exact: Ht3fm | exact: Hundef']. }
    case: Hfinale => beh1 [Hbeh1 Hor].
    exists Cs, beh1.
    split; [exact: iface_Cs |].
    split; [exact: wf_Cs |].
    split; [exact: linkable_p_Cs |].
    split; [exact: closed_p_Cs |].
    split; [exact: Hbeh1 |].
    exact: Hor.
  Qed.

  (* Print Assumptions RSC_DC_MD_CompilationChainMP. *)

End ChainMP.

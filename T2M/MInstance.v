Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Common.Linking.
Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.
Require Import Common.SmallstepUB.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RSCSigs.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.BackTranslation.
Require T2M.MDefs.
Require Import T2M.MBnz.
Require Import T2M.MStatic.
Require Import T2M.MStatic2.
Require Import T2M.MBwdSrc.

Import DoNotation.
Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Lemma elementsm_mapm (S S' : Type) (f : S -> S') (m : NMap S) :
  Maps.elementsm (mapm f m)
  = [seq (p.1, f p.2) | p <- Maps.elementsm m].
Proof. by []. Qed.

Lemma mapm_comp' (A B C : Type) (f : B -> C) (g : A -> B) (m : NMap A) :
  mapm f (mapm g m) = mapm (fun x => f (g x)) m.
Proof.
apply/eq_fmap => k. rewrite !mapmE. by case: (m k).
Qed.

Definition bimg (q : nat * (nat + seq value)) : nat * nat :=
  (q.1, bsize q.2).

Lemma flmb_shape (t1 t2 : seq (nat * (nat + seq value))) :
  map bimg t1 = map bimg t2 ->
  forall acc,
    fold_left_map_bis
      (fun acc' (a : nat * (nat + seq value)) =>
         match a.2 with
         | inl n => ((a.1, acc'), n + acc')
         | inr s => ((a.1, acc'), size s + acc')
         end) acc t1
    = fold_left_map_bis
        (fun acc' (a : nat * (nat + seq value)) =>
           match a.2 with
           | inl n => ((a.1, acc'), n + acc')
           | inr s => ((a.1, acc'), size s + acc')
           end) acc t2.
Proof.
elim: t1 t2 => [|[b1 v1] t1 IH] [|[b2 v2] t2] //=.
case=> Eb Ev Et acc.
subst b2.
have Ev' : match v1 with inl n => n | inr s => size s end
           = match v2 with inl n => n | inr s => size s end.
{ by move: Ev; rewrite /bsize; case: v1; case: v2. }
case: v1 Ev' {Ev} => [n1|s1]; case: v2 => [n2|s2] //= E;
  rewrite E (IH _ Et) //=;
  by case: (fold_left_map_bis _ _ t2).
Qed.

Lemma flm_shape (l1 l2 : seq (nat * seq (nat * (nat + seq value)))) :
  map (fun p => (p.1, map bimg p.2)) l1
  = map (fun p => (p.1, map bimg p.2)) l2 ->
  forall acc,
    fold_left_map
      (fun acc0 s =>
         let (flat0, count0) :=
           fold_left_map_bis
             (fun acc' (a : nat * (nat + seq value)) =>
                match a.2 with
                | inl n => ((a.1, acc'), n + acc')
                | inr s0 => ((a.1, acc'), size s0 + acc')
                end) acc0 s.2 in
         ((s.1, mkfmap flat0), count0)) acc l1
    = fold_left_map
        (fun acc0 s =>
           let (flat0, count0) :=
             fold_left_map_bis
               (fun acc' (a : nat * (nat + seq value)) =>
                  match a.2 with
                  | inl n => ((a.1, acc'), n + acc')
                  | inr s0 => ((a.1, acc'), size s0 + acc')
                  end) acc0 s.2 in
           ((s.1, mkfmap flat0), count0)) acc l2.
Proof.
elim: l1 l2 => [|[c1 bl1] l1 IH] [|[c2 bl2] l2] //=.
case=> Ec Ebl El acc.
subst c2.
rewrite (flmb_shape Ebl acc).
case E2 : (fold_left_map_bis _ acc bl2) => [flat count] /=.
congr cons.
exact: IH El count.
Qed.

Lemma elements_shape (PB : NMap {fmap Block.id -> nat + seq value}) :
  [seq (p.1, map bimg p.2) | p <- Maps.elementsm (mapm Maps.elementsm PB)]
  = Maps.elementsm (mapm Maps.elementsm (bufs_shape PB)).
Proof.
rewrite /bufs_shape mapm_comp' !elementsm_mapm.
rewrite -map_comp.
apply: eq_map => r /=.
by congr pair.
Qed.

Lemma memory_lengths_shape
    (PB1 PB2 : NMap {fmap Block.id -> nat + seq value}) :
  bufs_shape PB1 = bufs_shape PB2 ->
  memory_lengths PB1 = memory_lengths PB2.
Proof.
move=> Hsh.
have Hel : [seq (p.1, map bimg p.2)
           | p <- Maps.elementsm (mapm Maps.elementsm PB1)]
           = [seq (p.1, map bimg p.2)
             | p <- Maps.elementsm (mapm Maps.elementsm PB2)].
{ by rewrite !elements_shape Hsh. }
rewrite /memory_lengths.
congr mkfmap.
exact: flm_shape Hel 0.
Qed.

Lemma compiler_msz_eq (L P C : nat)
    (PB1 PB2 : NMap {fmap Block.id -> nat + seq value})
    (PI : Program.interface) (pr : Intermediate.program) :
  memory_lengths PB1 = memory_lengths PB2 ->
  compiler L P C PB1 PI pr = compiler L P C PB2 PI pr.
Proof.
move=> E.
rewrite /compiler /compiler_code /compiler_body /compiler_gen
        /transitional_to_merged_gen.
by rewrite E.
Qed.


Definition canonical_bufs (x : Intermediate.program) : Prop :=
  bufs_shape (Intermediate.prog_buffers x)
  = mapm (fun n => mkfmap [:: (0 : Block.id, n); (1 : Block.id, 2)])
         (block0_sizes (Intermediate.prog_buffers x))
  /\ (forall (C : Component.id) (n : nat),
        block0_sizes (Intermediate.prog_buffers x) C = Some n -> 0 < n).

Lemma compiled_canonical (P : Source.program) (x : Intermediate.program) :
  Source.well_formed_program P ->
  compile_program P = Some x ->
  canonical_bufs x.
Proof.
move=> Hwf Hc.
split.
- rewrite (compilation_buffers Hc).
  apply/eq_fmap => C.
  rewrite /bufs_shape /block0_sizes /gen_buffers !mapmE.
  case E: (Source.prog_buffers P C) => [buf|] //=.
  congr Some.
  apply/eq_fmap => blk.
  rewrite mapmE !setmE.
  case: (blk == 0 :> nat) => //=.
  by case: (blk == 1 :> nat).
- move=> C n.
  rewrite (compilation_buffers Hc) /block0_sizes /gen_buffers !mapmE.
  case E: (Source.prog_buffers P C) => [buf|] //=.
  move=> -[<-].
  have HiC : Source.prog_interface P C.
  { have: C \in domm (Source.prog_buffers P) by rewrite mem_domm E.
    by rewrite -(Source.wfprog_defined_buffers Hwf) mem_domm. }
  have [buf' Hbuf' Hcond] := Source.wfprog_well_formed_buffers Hwf HiC.
  rewrite E in Hbuf'. case: Hbuf' => ->.
  case: buf' Hcond => [k|l] /= Hk.
  + by lia.
  + rewrite -size_lengthE. by lia.
Qed.

Lemma prescribed_matches_canonical
    (b : Intermediate.program) (P' : Source.program)
    (bufsz : NMap nat) (ic' : Intermediate.program) :
  Intermediate.well_formed_program b ->
  canonical_bufs b ->
  Source.well_formed_program P' ->
  compile_program P' = Some ic' ->
  Source.prog_interface P' = Intermediate.prog_interface b ->
  (forall C, C \in domm (Intermediate.prog_interface b) ->
     Source.prog_buffers P' C
     = Some (inr (nseq (Definability.buf_size bufsz C) (Int 0)))) ->
  (forall C, C \in domm (Intermediate.prog_interface b) ->
     bufsz C = block0_sizes (Intermediate.prog_buffers b) C) ->
  bufs_shape (Intermediate.prog_buffers ic')
  = bufs_shape (Intermediate.prog_buffers b).
Proof.
move=> Hwb [Hcanon Hpos] HwfP' Hic' Hif HbufsP' Hpres.
rewrite (compilation_buffers Hic') Hcanon.
apply/eq_fmap => C.
rewrite /bufs_shape /gen_buffers !mapmE.
case HC: (C \in domm (Intermediate.prog_interface b)); last first.
- have /dommPn -> /= : C \notin domm (Source.prog_buffers P').
  { by rewrite -(Source.wfprog_defined_buffers HwfP') Hif HC. }
  have /dommPn HnB : C \notin domm (Intermediate.prog_buffers b).
  { by rewrite -(Intermediate.wfprog_defined_buffers Hwb) HC. }
  by rewrite HnB.
- rewrite (HbufsP' C HC) /=.
  have HCb : C \in domm (Intermediate.prog_buffers b).
  { by rewrite -(Intermediate.wfprog_defined_buffers Hwb) HC. }
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


Module Type T2M_K_Input.
  Parameter L P C : nat.
  Parameter PB : NMap {fmap Block.id -> nat + seq value}.
  Parameter PI : Program.interface.
End T2M_K_Input.

Record bt_fit_pack (L P C : nat) (PBW : NMap {fmap Block.id -> nat + seq value})
    (PIW : Program.interface) (a b : Intermediate.program) (t : Events.trace)
    (ip' ic' : Intermediate.program) : Prop := {
  bfp_cip  : compile_program (bt_P'c a b t) = Some ip';
  bfp_cic  : compile_program (bt_Csc a b t) = Some ic';
  bfp_lokp : BackTranslation.lin_ok_at L P C ip';
  bfp_immp : MDefs.imm_fits ip';
  bfp_lokc : BackTranslation.lin_ok_at L P C ic';
  bfp_immc : MDefs.imm_fits ic';
  bfp_lfp  : MDefs.link_fits L P C ip' ic';
  bfp_lfa  : MDefs.link_fits L P C a ic';
  bfp_rfp  : MDefs.run_fits (MDefs.cde ip' ic')
               (Intermediate.program_link ip' ic') t;
  bfp_rfa  : MDefs.run_fits (MDefs.cde a ic')
               (Intermediate.program_link a ic') t;
  bfp_msz  : memory_lengths (MDefs.PBw a b) = memory_lengths PBW;
  bfp_piw  : MDefs.PIw a b = PIW
}.

Definition t2m_bt_fits (L P C : nat) (PBW : NMap {fmap Block.id -> nat + seq value})
    (PIW : Program.interface) (a b : Intermediate.program) (t : Events.trace) : Prop :=
  exists ip' ic', bt_fit_pack L P C PBW PIW a b t ip' ic'.

Module K_T2M (I : T2M_K_Input) <: MPCompilerSig.

  Definition NC : nat := MDefs.NC.

  Lemma NC_lt_word : NC < word_size mt.
  Proof. by rewrite /NC /MDefs.NC Int32.word_size_mt. Qed.

  Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
  Proof.
    rewrite /alloc_label /NC /MDefs.NC Int32.word_size_mt.
    by rewrite ltn_exp2l.
  Qed.

  Definition PBW := I.PB.
  Definition PIW := I.PI.

  Definition lin (pr : Intermediate.program) : program :=
    compiler I.L I.P I.C PBW PIW pr.

  Definition lin_ok (pr : Intermediate.program) : Prop :=
    MDefs.t2m_ok I.L I.P I.C pr /\ canonical_bufs pr.

  Lemma lin_interface : forall a,
    prog_interface (lin a) = Intermediate.prog_interface a.
  Proof. by []. Qed.

  Lemma lin_buffers : forall a,
    prog_buffers (lin a) = Intermediate.prog_buffers a.
  Proof. by []. Qed.

  Lemma lin_main : forall a,
    prog_main (lin a)
    = (Component.main \in domm (Intermediate.prog_interface a)).
  Proof. by []. Qed.

  Lemma lin_wf : forall a,
    Intermediate.well_formed_program a -> lin_ok a ->
    well_formed_program (lin a).
  Proof.
    move=> a Hwf [[Hlin _ _] _].
    case: Hlin => Hne Hbuf _ _ _.
    apply: compiler_wf.
    - exact: Hwf.
    - exact: Hne.
    - exact: Hbuf.
  Qed.

  Lemma lin_out_wf : forall a,
    Intermediate.well_formed_program a -> lin_output_wf (lin a).
  Proof.
    move=> a Hwf.
    apply: compiler_output_wf. exact: Hwf.
  Qed.

  Lemma lin_labels_disjoint : forall a b,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    lin_ok a -> lin_ok b ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    forall l, findopt (is_label_def l) (code (lin a)) <> None ->
              findopt (is_label_def l) (code (lin b)) = None.
  Proof.
    move=> a b Hwa Hwb [[Hla _ _] _] [[Hlb _ _] _] Hdis l Hdef.
    case: Hla => _ _ HbLa HbPa HbCa.
    case: Hlb => _ _ HbLb HbPb HbCb.
    exact: (@LinearizeMerged.lin_labels_disjoint I.L I.P I.C PBW PIW a b
              Hwa Hwb HbLa HbPa HbCa HbLb HbPb HbCb Hdis l Hdef).
  Qed.

  Lemma lin_jal_cross : forall a b b',
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    Intermediate.well_formed_program b' ->
    lin_ok a -> lin_ok b -> lin_ok b' ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    closed_interface (unionm (Intermediate.prog_interface a)
                             (Intermediate.prog_interface b)) ->
    Intermediate.prog_interface b = Intermediate.prog_interface b' ->
    forall n l t,
      nth_error (code (lin a)) n = Some (@MrJal mt l, t) ->
      l <> alloc_label ->
      findopt (is_label_def l) (code (lin a)) = None ->
      exists mb mb' (i i' : @Merged.instr mt) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code (lin b)) = Some mb,
            findopt (is_label_def l) (code (lin b')) = Some mb',
            nth_error (code (lin b)) mb = Some (i, tc)
            /\ nth_error (code (lin b')) mb' = Some (i', tc)
          & is_code tc /\ color tc \in domm (Intermediate.prog_interface b)].
  Proof.
    move=> a b b' Hwa Hwb Hwb' [[Hla _ _] _] [[Hlb _ _] _] [[Hlb' _ _] _]
           Hdis Hclosed Eiface n l t Hnth Halloc Hnone.
    case: Hla => _ _ HbLa HbPa HbCa.
    case: Hlb => _ _ HbLb HbPb HbCb.
    case: Hlb' => _ _ HbLb' HbPb' HbCb'.
    have Hdis' : fdisjoint (domm (Intermediate.prog_interface a))
                           (domm (Intermediate.prog_interface b')).
    { by rewrite -Eiface. }
    have Hclosed' : closed_interface
        (unionm (Intermediate.prog_interface a)
                (Intermediate.prog_interface b')).
    { by rewrite -Eiface. }
    have [m1 [C1 [P1 [Hf1 Hn1 Hl1 Hd1 [HC1 HP1]]]]] :=
      @lin_jal_foreign I.L I.P I.C PBW PIW a b
        Hwa Hwb HbLb HbPb HbCb n l t
        Hclosed Hnth Halloc Hnone.
    have [m2 [C2 [P2 [Hf2 Hn2 Hl2 Hd2 [HC2 HP2]]]]] :=
      @lin_jal_foreign I.L I.P I.C PBW PIW a b'
        Hwa Hwb' HbLb' HbPb' HbCb' n l t
        Hclosed' Hnth Halloc Hnone.
    have [EC EP] := mk_entry_inj HP2 HP1 (etrans (esym Hl2) Hl1).
    subst C2 P2.
    exists m1, m2, (@MrLabel mt l), (@MrLabel mt l),
           (Transitional.head_tag_gen PIW C1 P1).
    split.
    - exact: Hf1.
    - exact: Hf2.
    - split.
      + exact: Hn1.
      + exact: Hn2.
    - split.
      + exact: erefl.
      + exact: Hd1.
  Qed.

  Definition run_ok (a b : Intermediate.program)
      (t : Events.trace) : Prop :=
    [/\ MDefs.link_fits I.L I.P I.C a b,
        MDefs.run_fits (MDefs.cde a b) (Intermediate.program_link a b) t,
        memory_lengths (MDefs.PBw a b) = memory_lengths PBW
      & MDefs.PIw a b = PIW].

  Lemma lin_canonical (a b : Intermediate.program) (x : Intermediate.program) :
    memory_lengths (MDefs.PBw a b) = memory_lengths PBW ->
    MDefs.PIw a b = PIW ->
    lin x = compiler I.L I.P I.C (MDefs.PBw a b) (MDefs.PIw a b) x.
  Proof.
    move=> Emsz EPI.
    rewrite /lin -EPI.
    exact: (compiler_msz_eq I.L I.P I.C (MDefs.PIw a b) x (esym Emsz)).
  Qed.

  Lemma H_bwd_src : forall (sa sb : Source.program)
      (a b : Intermediate.program) m,
    Source.well_formed_program sa ->
    Source.well_formed_program sb ->
    Source.closed_program (Source.program_link sa sb) ->
    compile_program sa = Some a ->
    compile_program sb = Some b ->
    lin_ok a -> lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (me_sem NC (program_link (lin a) (lin b))) m ->
    run_ok a b (finpref_trace m) ->
    exists beh,
      program_behaves (S.CS.sem (Source.program_link sa sb)) beh
      /\ (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).
  Proof.
    move=> sa sb a b m Hwsa Hwsb HclS Hca Hcb [Hoka _] [Hokb _] Hlink Hcl
           Hdp [Hlf Hrf Emsz EPI].
    have Hdp' : does_prefix (MDefs.mesem I.L I.P I.C a b) m.
    { move: Hdp.
      by rewrite (lin_canonical a Emsz EPI) (lin_canonical b Emsz EPI). }
    have Hwia : Intermediate.well_formed_program a
      := compilation_preserves_well_formedness Hwsa Hca.
    have Hwib : Intermediate.well_formed_program b
      := compilation_preserves_well_formedness Hwsb Hcb.
    have Hprem : MDefs.t2me_premises I.L I.P I.C a b.
    { split; [|split].
      - split.
        + by exists sa; split.
        + by exists sb; split.
        + exact: Hwia.
        + exact: Hwib.
        + exact: Hlink.
      - exact: Hcl.
      - split.
        + exact: Hoka.
        + exact: Hokb.
        + exact: Hlf. }
    have [MM [HMM Hdsy0]] := @disch_dsy0 I.L I.P I.C a b Hprem.
    exact: (t2me_H_bwd_src Hwsa Hwsb HclS Hca Hcb
              Hlink Hcl Hoka Hokb Hlf HMM
              (@disch_HcstT I.L I.P I.C a b Hprem)
              (@disch_HuniqT I.L I.P I.C a b Hprem)
              (Hdsy0 m) Hdp' Hrf).
  Qed.

  Definition bt_fits (a b : Intermediate.program)
      (t : Events.trace) : Prop :=
    t2m_bt_fits I.L I.P I.C PBW PIW a b t.

  Lemma H_bt : forall a b (m0 : finpref_behavior),
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    lin_ok a -> lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (rub_sem NC (Intermediate.prog_interface a)
                            (Intermediate.prog_interface b)
                            (program_link (lin a) (lin b)))
                m0 ->
    not_wrong_finpref m0 ->
    bt_fits a b (finpref_trace m0) ->
    bt_package NC lin lin_ok run_ok a b m0.
  Proof.
    move=> a b m0 Hwa Hwb Hoka Hokb Hlink Hcl Hrub Hnw Hfits.
    have [ip' Hfits1] := constructive_indefinite_description _ Hfits.
    have [ic' Hfit] := constructive_indefinite_description _ Hfits1.
    have Hcip := bfp_cip Hfit.
    have Hcic := bfp_cic Hfit.
    have Hlfp := bfp_lfp Hfit.
    have Hlfa := bfp_lfa Hfit.
    have Hrfp := bfp_rfp Hfit.
    have Hrfa := bfp_rfa Hfit.
    have Emsz := bfp_msz Hfit.
    have EPI := bfp_piw Hfit.
    have Hrub' : does_prefix
        (rub_sem NC (Intermediate.prog_interface a)
                    (Intermediate.prog_interface b)
                    (program_link
                       (compiler I.L I.P I.C (MDefs.PBw a b)
                          (MDefs.PIw a b) a)
                       (compiler I.L I.P I.C (MDefs.PBw a b)
                          (MDefs.PIw a b) b)))
        m0.
    { move: Hrub.
      by rewrite (lin_canonical a Emsz EPI) (lin_canonical b Emsz EPI). }
    have Hsrc := @bt_source_half_shapes I.L I.P I.C a b Hwa Hwb Hlink Hcl
                   NC m0 Hrub' Hnw.
    have [P' HbtA] := constructive_indefinite_description _ Hsrc.
    have [Cs HbtB] := constructive_indefinite_description _ HbtA.
    have [ip1 HbtC] := constructive_indefinite_description _ HbtB.
    have [ic1 Hpack] := constructive_indefinite_description _ HbtC.
    have Eip : ip1 = ip'.
    { have H := btsp_compP Hpack.
      rewrite (btsp_eqP Hpack) Hcip in H.
      by move: H => [->]. }
    have Eic : ic1 = ic'.
    { have H := btsp_compCs Hpack.
      rewrite (btsp_eqCs Hpack) Hcic in H.
      by move: H => [->]. }
    subst ip1 ic1.
    have HwfP' := btsp_wfP Hpack.
    have HwfCs := btsp_wfCs Hpack.
    have EifP := btsp_ifP Hpack.
    have EifCs := btsp_ifCs Hpack.
    have Hscl := btsp_closed Hpack.
    have HmmP := btsp_mmP Hpack.
    have HmmC := btsp_mmCs Hpack.
    have Hsrun := btsp_run Hpack.
    have Hcp' := btsp_compP Hpack.
    have Hcc' := btsp_compCs Hpack.
    have Hwip := btsp_wfip Hpack.
    have Hwic := btsp_wfic Hpack.
    have Eifp := btsp_ifip Hpack.
    have Eifc := btsp_ific Hpack.
    have HbufP := btsp_bufP Hpack.
    have HbufC := btsp_bufCs Hpack.
    have Hokip : lin_ok ip'.
    { split; last exact: (compiled_canonical HwfP' Hcp').
      split.
      - exact: (bfp_lokp Hfit).
      - exact: (compiled_branches_forward Hcp').
      - exact: (bfp_immp Hfit). }
    have Hokic : lin_ok ic'.
    { split; last exact: (compiled_canonical HwfCs Hcc').
      split.
      - exact: (bfp_lokc Hfit).
      - exact: (compiled_branches_forward Hcc').
      - exact: (bfp_immc Hfit). }
    have Hcana : canonical_bufs a.
    { by case: Hoka. }
    have Hcanb : canonical_bufs b.
    { by case: Hokb. }
    have Hdis_ab : fdisjoint (domm (Intermediate.prog_interface a))
                             (domm (Intermediate.prog_interface b)).
    { by case: Hlink. }
    have Hpres_a : forall C,
        C \in domm (Intermediate.prog_interface a) ->
        bt_bufsz a b C = block0_sizes (Intermediate.prog_buffers a) C.
    { move=> C HC.
      rewrite /bt_bufsz unionmE.
      have: C \in domm (block0_sizes (Intermediate.prog_buffers a)).
      { rewrite /block0_sizes domm_map.
        by rewrite -(Intermediate.wfprog_defined_buffers Hwa). }
      rewrite mem_domm.
      by case: (block0_sizes (Intermediate.prog_buffers a) C). }
    have Hpres_b : forall C,
        C \in domm (Intermediate.prog_interface b) ->
        bt_bufsz a b C = block0_sizes (Intermediate.prog_buffers b) C.
    { move=> C HC.
      rewrite /bt_bufsz unionmE.
      have HnA : block0_sizes (Intermediate.prog_buffers a) C = None.
      { apply/dommPn.
        rewrite /block0_sizes domm_map.
        rewrite -(Intermediate.wfprog_defined_buffers Hwa).
        move: Hdis_ab. rewrite fdisjointC => /fdisjointP HD.
        exact: HD HC. }
      by rewrite HnA. }
    have Hshp : bufs_shape (Intermediate.prog_buffers ip')
                = bufs_shape (Intermediate.prog_buffers a).
    { apply: (prescribed_matches_canonical Hwa Hcana HwfP' Hcp'
                EifP HbufP).
      move=> C HC. exact: (Hpres_a C HC). }
    have Hshc : bufs_shape (Intermediate.prog_buffers ic')
                = bufs_shape (Intermediate.prog_buffers b).
    { apply: (prescribed_matches_canonical Hwb Hcanb HwfCs Hcc'
                EifCs HbufC).
      move=> C HC. exact: (Hpres_b C HC). }
    have Hlink' : linkable (Intermediate.prog_interface ip')
                           (Intermediate.prog_interface ic').
    { by rewrite Eifp Eifc. }
    have Hmm_b_ic : Intermediate.matching_mains b ic'
      := matching_mains_equiv _ _ _ HmmC
           (compilation_has_matching_mains HwfCs Hcc').
    have Hmm_a_ip : Intermediate.matching_mains a ip'
      := matching_mains_equiv _ _ _ HmmP
           (compilation_has_matching_mains HwfP' Hcp').
    have Hmains_ab : Intermediate.linkable_mains a b
      := Intermediate.linkable_implies_linkable_mains Hwa Hwb Hlink.
    have Hlink_a_ic : linkable (Intermediate.prog_interface a)
                               (Intermediate.prog_interface ic').
    { by rewrite Eifc. }
    have Hcl_a_ic : Intermediate.closed_program
                      (Intermediate.program_link a ic').
    { exact: (Intermediate.interface_preserves_closedness_r Hwa Hwic
                (esym Eifc) Hlink Hcl Hmains_ab Hmm_b_ic). }
    have Hcl_ic_a : Intermediate.closed_program
                      (Intermediate.program_link ic' a).
    { rewrite -(Intermediate.program_linkC Hwa Hwic Hlink_a_ic).
      exact: Hcl_a_ic. }
    have Hmains_ic_a : Intermediate.linkable_mains ic' a
      := Intermediate.linkable_implies_linkable_mains Hwic Hwa
           (linkable_sym Hlink_a_ic).
    have Hcl_ic_ip : Intermediate.closed_program
                       (Intermediate.program_link ic' ip').
    { exact: (Intermediate.interface_preserves_closedness_r Hwic Hwip
                (esym Eifp) (linkable_sym Hlink_a_ic) Hcl_ic_a
                Hmains_ic_a Hmm_a_ip). }
    have HclI : Intermediate.closed_program
                  (Intermediate.program_link ip' ic').
    { rewrite (Intermediate.program_linkC Hwip Hwic Hlink').
      exact: Hcl_ic_ip. }
    have Ht2ip : MDefs.t2m_ok I.L I.P I.C ip'.
    { by case: Hokip. }
    have Ht2ic : MDefs.t2m_ok I.L I.P I.C ic'.
    { by case: Hokic. }
    have Hprem' : MDefs.t2me_premises I.L I.P I.C ip' ic'.
    { split; [|split].
      - split.
        + by exists P'; split.
        + by exists Cs; split.
        + exact: Hwip.
        + exact: Hwic.
        + exact: Hlink'.
      - exact: HclI.
      - split.
        + exact: Ht2ip.
        + exact: Ht2ic.
        + exact: Hlfp. }
    have Hme : does_prefix (MDefs.mesem I.L I.P I.C ip' ic') m0.
    { have [MM [HMM Hdsy0]] := @disch_dsy0 I.L I.P I.C ip' ic' Hprem'.
      exact: (t2me_bt_run HwfP' HwfCs Hscl
                Hcp' Hcc' Hlink' HclI Ht2ip Ht2ic Hlfp HMM
                (@disch_HcstT I.L I.P I.C ip' ic' Hprem')
                (@disch_HuniqT I.L I.P I.C ip' ic' Hprem')
                (Hdsy0 m0) Hsrun Hnw Hrfp). }
    have Emsz' : memory_lengths (MDefs.PBw ip' ic') = memory_lengths PBW.
    { rewrite -Emsz.
      apply: memory_lengths_shape.
      rewrite /MDefs.PBw.
      rewrite (bufs_shape_unionm_l _ Hshp).
      by rewrite (bufs_shape_unionm_r _ Hshc). }
    have EPI' : MDefs.PIw ip' ic' = PIW.
    { by rewrite /MDefs.PIw Eifp Eifc -EPI. }
    have Hme' : does_prefix
        (me_sem NC (program_link (lin ip') (lin ic'))) m0.
    { move: Hme.
      by rewrite (lin_canonical ip' Emsz' EPI')
                 (lin_canonical ic' Emsz' EPI'). }
    have Emsza : memory_lengths (MDefs.PBw a ic') = memory_lengths PBW.
    { rewrite -Emsz.
      apply: memory_lengths_shape.
      rewrite /MDefs.PBw.
      by rewrite (bufs_shape_unionm_r _ Hshc). }
    have EPIa : MDefs.PIw a ic' = PIW.
    { by rewrite /MDefs.PIw Eifc -EPI. }
    have Hsz' : size (linearize_bufs (unionm (prog_buffers (lin ip'))
                                             (prog_buffers (lin ic'))))
                  + size (code (lin ip') ++ code (lin ic')) < alloc_label.
    { have [Hsz _] := Hlfp.
      move: Hsz.
      by rewrite (lin_canonical ip' Emsz' EPI')
                 (lin_canonical ic' Emsz' EPI'). }
    have Hsz'' : size (linearize_bufs (unionm (prog_buffers (lin a))
                                              (prog_buffers (lin ic'))))
                  + size (code (lin a) ++ code (lin ic')) < alloc_label.
    { have [Hsz _] := Hlfa.
      move: Hsz.
      by rewrite (lin_canonical a Emsza EPIa)
                 (lin_canonical ic' Emsza EPIa). }
    unshelve refine {| bt_Cs := Cs; bt_P' := P';
                       bt_ip' := ip'; bt_ic' := ic' |}.
    - exact: HwfCs.
    - exact: HwfP'.
    - exact: EifCs.
    - exact: EifP.
    - exact: Hcp'.
    - exact: Hcc'.
    - exact: Hokip.
    - exact: Hokic.
    - exact: Hshp.
    - exact: Hshc.
    - exact: HmmC.
    - exact: Hscl.
    - exact: Hsrun.
    - exact: Hme'.
    - split.
      + exact: Hlfa.
      + exact: Hrfa.
      + exact: Emsza.
      + exact: EPIa.
    - exact: Hsz'.
    - exact: Hsz''.
  Qed.

End K_T2M.


Require Import MicroPolicies.RSC_MD_MP.

Module RSC_MP_T2M (I : T2M_K_Input).
  Module K := K_T2M I.
  Module Make (X : RSC_MP_Input K) := RSC_MP K X.
End RSC_MP_T2M.

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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Intermediate.Machine.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RecompositionTop.
Require Import MicroPolicies.Recomposition.RSC_ME_MP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Types.


Section Discipline.
  Variables L P C : nat.

  Definition labels_in_scheme (q : program) : Prop :=
    forall n l t,
      nth_error (code q) n = Some (@MrLabel mt l, t) ->
      (exists cid j,
          [/\ cid \in domm (prog_interface q), cid < C, j < L
            & l = mk_body L cid j])
      \/ (exists cid Pid,
          [/\ cid \in domm (prog_interface q), cid < C, Pid < P
            & l = mk_entry L P C cid Pid]).

  Definition foreign_jal_entry (q : program) : Prop :=
    forall n l t,
      nth_error (code q) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code q) = None ->
      exists cid Pid,
        [/\ l = mk_entry L P C cid Pid,
            imported_procedure (prog_interface q) (color t) cid Pid
          & color t <> cid].

  Definition entries_present (q : program) : Prop :=
    forall cid Pid,
      exported_procedure (prog_interface q) cid Pid ->
      findopt (is_label_def (mk_entry L P C cid Pid)) (code q) <> None.

  Definition entry_tag_canonical (PIW : Program.interface) (q : program)
      : Prop :=
    forall cid Pid m i t,
      cid < C -> Pid < P ->
      findopt (is_label_def (mk_entry L P C cid Pid)) (code q) = Some m ->
      nth_error (code q) m = Some (i, t) ->
      t = Transitional.head_tag_gen PIW cid Pid.

  Definition iface_bounded (q : program) : Prop :=
    forall cid, cid \in domm (prog_interface q) -> cid < C.

  Definition exports_bounded (q : program) : Prop :=
    forall cid Pid, exported_procedure (prog_interface q) cid Pid -> Pid < P.

  Definition entry_heads (PIW : Program.interface) (q : program) : Prop :=
    forall i t e, List.In (i, t) (code q) -> entry t = Some e ->
      t = Transitional.head_tag_gen PIW (color t) e.1.

  Record wf_mp (PIW : Program.interface) (q : program) : Prop := {
    wfmp_wf     : well_formed_program q;
    wfmp_loww   : lin_output_wf q;
    wfmp_scheme : labels_in_scheme q;
    wfmp_fje    : foreign_jal_entry q;
    wfmp_ep     : entries_present q;
    wfmp_etc    : entry_tag_canonical PIW q;
    wfmp_ib     : iface_bounded q;
    wfmp_eb     : exports_bounded q;
    wfmp_eh     : entry_heads PIW q
  }.

  Lemma wfmp_labels_disjoint (PIWa PIWb : Program.interface)
      (qa qb : program) :
    wf_mp PIWa qa -> wf_mp PIWb qb ->
    fdisjoint (domm (prog_interface qa)) (domm (prog_interface qb)) ->
    forall l, findopt (is_label_def l) (code qa) <> None ->
              findopt (is_label_def l) (code qb) = None.
  Proof.
    move=> Ha Hb Hdis l H1.
    case E1: (findopt (is_label_def l) (code qa)) H1 => [m1|]; last by [].
    move=> _.
    have [[i1 t1] [Hnth1 Hp1]] := findopt_nth E1.
    case: i1 Hnth1 Hp1 => // l1 Hnth1 Hp1.
    move: Hp1. rewrite /is_label_def /= => /eqP El. subst l1.
    apply: findopt_notIn_None => -[i2 t2] HIn2.
    rewrite /is_label_def /=.
    case: i2 HIn2 => // l2 HIn2.
    apply: negbTE. apply/negP => /eqP El2. subst l2.
    have [n2 Hnth2] := List.In_nth_error _ _ HIn2.
    case: (wfmp_scheme Ha Hnth1)
      => [[cid1 [l01 [Hd1 HC1 HL1 Hl1]]]|[cid1 [p01 [Hd1 HC1 HP1 Hl1]]]];
    case: (wfmp_scheme Hb Hnth2)
      => [[cid2 [l02 [Hd2 HC2 HL2 Hl2]]]|[cid2 [p02 [Hd2 HC2 HP2 Hl2]]]].
    - have [Ec _] := mk_body_inj HL1 HL2 (etrans (esym Hl1) Hl2).
      move: (fdisjointP Hdis _ Hd1). by rewrite Ec Hd2.
    - exact: (mk_body_entry_disjoint HC1 HL1 (etrans (esym Hl1) Hl2)).
    - exact: (mk_body_entry_disjoint HC2 HL2 (etrans (esym Hl2) Hl1)).
    - have [Ec _] := mk_entry_inj HP1 HP2 (etrans (esym Hl1) Hl2).
      move: (fdisjointP Hdis _ Hd1). by rewrite Ec Hd2.
  Qed.

  Lemma wfmp_jal_cross (PIWa PIWb : Program.interface)
      (qa qb qb' : program) :
    wf_mp PIWa qa -> wf_mp PIWb qb -> wf_mp PIWb qb' ->
    fdisjoint (domm (prog_interface qa)) (domm (prog_interface qb)) ->
    closed_interface (unionm (prog_interface qa) (prog_interface qb)) ->
    prog_interface qb = prog_interface qb' ->
    forall n l t,
      nth_error (code qa) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code qa) = None ->
      exists mb mb' (i i' : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code qb) = Some mb,
            findopt (is_label_def l) (code qb') = Some mb',
            nth_error (code qb) mb = Some (i, tc) /\ nth_error (code qb') mb' = Some (i', tc)
          & is_code tc /\ color tc \in domm (prog_interface qb)].
  Proof.
    move=> Ha Hb Hb' Hdis Hclosed Eiface n l t Hnth Halloc Hnone.
    have [cid [Pid [Hl Himp Hneq]]] := wfmp_fje Ha Hnth Halloc Hnone.
    have Himp_u : imported_procedure
        (unionm (prog_interface qa) (prog_interface qb)) (color t) cid Pid.
    { case: Himp => CI [HCI Him]. exists CI. split=> //.
      by rewrite /Program.has_component unionmE HCI. }
    case: (Hclosed _ _ _ Himp_u) => CI [HCIu Hexpo].
    case Ea: (prog_interface qa cid) => [CIa|].
    -
      have ECIa : CIa = CI.
      { move: HCIu. rewrite /Program.has_component unionmE Ea.
        by move=> [->]. }
      have Hexpa : exported_procedure (prog_interface qa) cid Pid.
      { exists CIa. split; [exact: Ea | rewrite ECIa; exact: Hexpo]. }
      have Hcon := wfmp_ep Ha Hexpa.
      rewrite -Hl in Hcon.
      by case: (Hcon Hnone).
    -
      have HCIb : prog_interface qb cid = Some CI.
      { move: HCIu. by rewrite /Program.has_component unionmE Ea. }
      have Hdomb : cid \in domm (prog_interface qb)
        by apply/dommP; exists CI.
      have Hexpb : exported_procedure (prog_interface qb) cid Pid.
      { by exists CI. }
      have Hexpb' : exported_procedure (prog_interface qb') cid Pid.
      { exists CI. split; last exact: Hexpo.
        rewrite /Program.has_component -Eiface. exact: HCIb. }
      have HC : cid < C := wfmp_ib Hb Hdomb.
      have HP : Pid < P := wfmp_eb Hb Hexpb.
      have Hep1 := wfmp_ep Hb Hexpb.
      case E1: (findopt (is_label_def (mk_entry L P C cid Pid)) (code qb))
        Hep1 => [mb|]; last by move=> Hcon; case: (Hcon (erefl _)).
      move=> _.
      have Hep2 := wfmp_ep Hb' Hexpb'.
      case E2: (findopt (is_label_def (mk_entry L P C cid Pid)) (code qb'))
        Hep2 => [mb'|]; last by move=> Hcon; case: (Hcon (erefl _)).
      move=> _.
      have [[i1 t1] [Hn1 _]] := findopt_nth E1.
      have [[i2 t2] [Hn2 _]] := findopt_nth E2.
      have Et1 : t1 = Transitional.head_tag_gen PIWb cid Pid
        := wfmp_etc Hb HC HP E1 Hn1.
      have Et2 : t2 = Transitional.head_tag_gen PIWb cid Pid
        := wfmp_etc Hb' HC HP E2 Hn2.
      exists mb, mb', i1, i2, (Transitional.head_tag_gen PIWb cid Pid).
      split.
      + rewrite Hl. exact: E1.
      + rewrite Hl. exact: E2.
      + split.
        * rewrite -Et1. exact: Hn1.
        * rewrite -Et2. exact: Hn2.
      + split.
        * exact: erefl.
        * exact: Hdomb.
  Qed.

  Lemma compiler_wf_mp (PB : NMap {fmap Block.id -> nat + seq value})
      (PI : Program.interface) (pr : Intermediate.program) :
    Intermediate.well_formed_program pr ->
    (forall cid Cprocs Pid Pcode l0,
       Intermediate.prog_procedures pr cid = Some Cprocs ->
       Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L) ->
    (forall cid Cprocs Pid,
       Intermediate.prog_procedures pr cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P) ->
    (forall cid, cid \in domm (Intermediate.prog_interface pr) -> cid < C) ->
    (forall cid Cprocs, Intermediate.prog_procedures pr cid = Some Cprocs -> exists Pid, Pid \in domm Cprocs) ->
    (forall C0, Intermediate.prog_interface pr C0 -> has_required_local_buffers (compiler L P C PB PI pr) C0) ->
    wf_mp PI (compiler L P C PB PI pr).
  Proof.
    move=> Hwf HbL HbP HbC Hne Hbuf.
    constructor.
    -
      apply: compiler_wf.
      + exact: Hwf.
      + exact: Hne.
      + exact: Hbuf.
    -
      apply: compiler_output_wf. exact: Hwf.
    -
      move=> n l t Hnth.
      have HIn := List.nth_error_In _ _ Hnth.
      case: (lin_label_cases Hwf HbL HbP HbC HIn)
        => [[cid [j [H1 H2 H3 H4]]]|[cid [p0 [H1 H2 H3 H4 _]]]].
      + left. exists cid, j.
        split; [exact: H1 | exact: H2 | exact: H3 | exact: H4].
      + right. exists cid, p0.
        split; [exact: H1 | exact: H2 | exact: H3 | exact: H4].
    -
      move=> n l t Hnth Halloc Hnone.
      have HIn := List.nth_error_In _ _ Hnth.
      case: (lin_jal_cases Hwf HIn)
        => [Ea|[Hloc|[C0 [P0 [Hl Himp Hneq]]]]].
      + by case: (Halloc Ea).
      + case: Hloc => m Hm. by rewrite Hnone in Hm.
      + exists C0, P0.
        split; [exact: Hl | exact: Himp | exact: Hneq].
    -
      move=> cid Pid [CI [HCI Hexp]] Hfind.
      have [Cprocs [Pcode [Hproc Epc]]]
        := Intermediate.wfprog_exported_procedures_existence Hwf HCI Hexp.
      have HPd : Pid \in domm Cprocs by apply/dommP; exists Pcode.
      have HInc := compiler_body_sub (lin_entry_In L P C PB PI Hproc HPd).
      have [m Hm] : exists m,
          findopt (is_label_def (mk_entry L P C cid Pid))
            (compiler_code L P C PB PI pr) = Some m.
      { apply: (findopt_In_ex HInc). by rewrite /is_label_def /= eqxx. }
      by rewrite Hm in Hfind.
    -
      move=> cid Pid m i t HC HP Hfind Hnth.
      have [[i0 t0] [Hn0 Hp0]] := findopt_nth Hfind.
      rewrite Hnth in Hn0. case: Hn0 => Ei Et. subst i0 t0.
      case: i Hnth Hp0 => // l0 Hnth Hp0.
      move: Hp0. rewrite /is_label_def /= => /eqP El0.
      have HIn := List.nth_error_In _ _ Hnth.
      case: (lin_label_cases Hwf HbL HbP HbC HIn)
        => [[cid2 [l02 [_ HC2 HL2 Hl2]]]|[cid2 [p02 [_ _ HP2 Hl2 Ht2]]]].
      + by case: (mk_body_entry_disjoint HC2 HL2
                    (etrans (esym Hl2) (esym El0))).
      + have [Ec Ep] := mk_entry_inj HP2 HP (etrans (esym Hl2) (esym El0)).
        subst cid2 p02. exact: Ht2.
    -
      move=> cid Hdom. exact: HbC Hdom.
    -
      move=> cid Pid [CI [HCI Hexp]].
      have [Cprocs [Pcode [Hproc Epc]]]
        := Intermediate.wfprog_exported_procedures_existence Hwf HCI Hexp.
      have HPd : Pid \in domm Cprocs by apply/dommP; exists Pcode.
      exact: HbP Hproc HPd.
    -
      move=> i t e HIn He. exact: (lin_entry_head HIn He).
  Qed.

End Discipline.


Record bt_me_package (L P C NC : nat) (p c : program) (m0 : finpref_behavior) : Type := {
  bt_pp : program;
  bt_cc : program;

  bt_wfmp_pp : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) bt_pp;
  bt_wfmp_cc : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) bt_cc;

  bt_ifacep : prog_interface p = prog_interface bt_pp;
  bt_ifacec : prog_interface c = prog_interface bt_cc;

  bt_closed' : closed_program (program_link bt_pp bt_cc);

  bt_memory_size' :
    size (linearize_bufs (unionm (prog_buffers bt_pp) (prog_buffers bt_cc)))
      + size (code bt_pp ++ code bt_cc) < alloc_label;
  bt_memory_size'' :
    size (linearize_bufs (unionm (prog_buffers p) (prog_buffers bt_cc)))
      + size (code p ++ code bt_cc) < alloc_label;
  bt_bufs_shape_pp : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers bt_pp);
  bt_bufs_shape_cc : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers bt_cc);

  bt_run : does_prefix (me_sem NC (program_link bt_pp bt_cc)) m0
}.

Module Type MEtoMP_Left.
  Parameter p c : program.
  Parameter L P C : nat.
  Parameter NC : nat.

  Axiom Hwfmp_p : wf_mp L P C
    (unionm (prog_interface p) (prog_interface c)) p.
  Axiom Hwfmp_c : wf_mp L P C
    (unionm (prog_interface p) (prog_interface c)) c.

  Axiom Hmergeable : mergeable_interfaces (prog_interface p) (prog_interface c).
  Axiom Hclosed : closed_program (program_link p c).
  Axiom comps_bounded : forall x,
    (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
  Axiom NC_lt_word : NC < word_size mt.
  Axiom alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
  Axiom memory_size_pc :
    size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
      + size (code p ++ code c) < alloc_label.
End MEtoMP_Left.

Module Type H_bt_me (Lft : MEtoMP_Left).
  Parameter bt_fits : trace -> Prop.
  Axiom bt_fits_prefix : forall t1 t2, trace_prefix t1 t2 -> bt_fits t2 -> bt_fits t1.
  Parameter back : forall (m0 : finpref_behavior),
    does_prefix (rub_sem Lft.NC (prog_interface Lft.p) (prog_interface Lft.c)
                   (program_link Lft.p Lft.c)) m0 ->
    not_wrong_finpref m0 ->
    bt_fits (finpref_trace m0) ->
    bt_me_package Lft.L Lft.P Lft.C Lft.NC Lft.p Lft.c m0.
End H_bt_me.

Module Type ObservedRun (Lft : MEtoMP_Left) (BT : H_bt_me Lft).
  Parameter fm : finpref_behavior.
  Axiom observed : does_prefix (mp_sem Lft.NC (program_link Lft.p Lft.c)) fm.
  Axiom safe : not_wrong_finpref fm.
  Axiom fits : BT.bt_fits (finpref_trace fm).
End ObservedRun.


Module RSC_ME_MP_Faithful
    (Lft : MEtoMP_Left) (BT : H_bt_me Lft) (Obs : ObservedRun Lft BT).

  Lemma disjoint_pc :
    fdisjoint (domm (prog_interface Lft.p)) (domm (prog_interface Lft.c)).
  Proof. by case: Lft.Hmergeable => [[_ Hd] _]. Qed.
  Lemma closed_pc :
    closed_interface (unionm (prog_interface Lft.p) (prog_interface Lft.c)).
  Proof. by case: Lft.Hmergeable => _ Hc. Qed.
  Lemma disjoint_cp :
    fdisjoint (domm (prog_interface Lft.c)) (domm (prog_interface Lft.p)).
  Proof. rewrite fdisjointC. exact: disjoint_pc. Qed.
  Lemma closed_cp :
    closed_interface (unionm (prog_interface Lft.c) (prog_interface Lft.p)).
  Proof. rewrite unionmC; [exact: closed_pc | rewrite fdisjointC; exact: disjoint_pc]. Qed.

  Module Sd <: RecompositionContext.
    Definition p  : program := Lft.p.
    Definition c  : program := Lft.c.
    Definition p' : program := Lft.p.
    Definition c' : program := Lft.c.
    Definition NC : nat := Lft.NC.

    Lemma Hwfp  : well_formed_program p.  Proof. exact: (wfmp_wf Lft.Hwfmp_p). Qed.
    Lemma Hwfc  : well_formed_program c.  Proof. exact: (wfmp_wf Lft.Hwfmp_c). Qed.
    Lemma Hwfp' : well_formed_program p'. Proof. exact: (wfmp_wf Lft.Hwfmp_p). Qed.
    Lemma Hwfc' : well_formed_program c'. Proof. exact: (wfmp_wf Lft.Hwfmp_c). Qed.
    Lemma Hmergeable_ifaces :
      mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof. exact: Lft.Hmergeable. Qed.
    Lemma Hifacep : prog_interface p = prog_interface p'. Proof. by []. Qed.
    Lemma Hifacec : prog_interface c = prog_interface c'. Proof. by []. Qed.
    Lemma Hprog_is_closed  : closed_program (program_link p c).  Proof. exact: Lft.Hclosed. Qed.
    Lemma Hprog_is_closed' : closed_program (program_link p' c'). Proof. exact: Lft.Hclosed. Qed.
    Lemma colors_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
    Proof. exact: Lft.comps_bounded. Qed.
    Lemma NC_lt_word : NC < word_size mt. Proof. exact: Lft.NC_lt_word. Qed.
    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. exact: Lft.alloc_label_lt_word_NC. Qed.
  End Sd.

  Module Ad <: LinearizerFacts Sd.
    Module D := RecompositionDefinitions Sd.
    Import D.

    Lemma lin_wf_p  : lin_output_wf p.  Proof. exact: (wfmp_loww Lft.Hwfmp_p). Qed.
    Lemma lin_wf_c  : lin_output_wf c.  Proof. exact: (wfmp_loww Lft.Hwfmp_c). Qed.
    Lemma lin_wf_p' : lin_output_wf p'. Proof. exact: (wfmp_loww Lft.Hwfmp_p). Qed.
    Lemma lin_wf_c' : lin_output_wf c'. Proof. exact: (wfmp_loww Lft.Hwfmp_c). Qed.

    Lemma labels_disjoint_prefix : forall l,
      findopt (is_label_def l) (code p) <> None ->
      findopt (is_label_def l) (code c) = None /\ findopt (is_label_def l) (code c') = None.
    Proof.
      move=> l H.
      split; exact: (wfmp_labels_disjoint Lft.Hwfmp_p Lft.Hwfmp_c disjoint_pc H).
    Qed.
    Lemma labels_disjoint_suffix : forall l,
      findopt (is_label_def l) (code c') <> None ->
      findopt (is_label_def l) (code p) = None /\ findopt (is_label_def l) (code p') = None.
    Proof.
      move=> l H.
      split; exact: (wfmp_labels_disjoint Lft.Hwfmp_c Lft.Hwfmp_p disjoint_cp H).
    Qed.
    Lemma jal_cross_p : forall n l t,
      nth_error (code p) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p) = None ->
      exists mc mc' (ic_ i_ : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code c) = Some mc,
            findopt (is_label_def l) (code c') = Some mc',
            nth_error (code c) mc = Some (ic_, tc) /\ nth_error (code c') mc' = Some (i_, tc)
          & is_code tc /\ color tc \in domm (prog_interface c)].
    Proof.
      move=> n l t H1 H2 H3.
      exact: (wfmp_jal_cross Lft.Hwfmp_p Lft.Hwfmp_c Lft.Hwfmp_c disjoint_pc closed_pc (erefl _) H1 H2 H3).
    Qed.
    Lemma jal_cross_c' : forall n l t,
      nth_error (code c') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c') = None ->
      exists mp' mp (ip_ i_ : Merged.instr) (tp : mem_tag),
        [/\ findopt (is_label_def l) (code p') = Some mp',
            findopt (is_label_def l) (code p) = Some mp,
            nth_error (code p') mp' = Some (ip_, tp) /\ nth_error (code p) mp = Some (i_, tp)
          & is_code tp /\ color tp \in domm (prog_interface p)].
    Proof.
      move=> n l t H1 H2 H3.
      have [mb [mb' [i [i' [tc [F1 F2 [F3 F4] F5]]]]]] :=
        wfmp_jal_cross Lft.Hwfmp_c Lft.Hwfmp_p Lft.Hwfmp_p disjoint_cp closed_cp (erefl _) H1 H2 H3.
      exists mb', mb, i', i, tc. by split; [| | split |].
    Qed.
    Lemma jal_cross_p'one : forall n l t,
      nth_error (code p') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p') = None ->
      exists m, findopt (is_label_def l) (code c') = Some m.
    Proof.
      move=> n l t H1 H2 H3.
      have [mb [mb' [i [i' [tc [F1 _ _ _]]]]]] :=
        wfmp_jal_cross Lft.Hwfmp_p Lft.Hwfmp_c Lft.Hwfmp_c disjoint_pc closed_pc (erefl _) H1 H2 H3.
      by exists mb.
    Qed.
    Lemma jal_cross_cone : forall n l t,
      nth_error (code c) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c) = None ->
      exists m, findopt (is_label_def l) (code p) = Some m.
    Proof.
      move=> n l t H1 H2 H3.
      have [mb [mb' [i [i' [tc [F1 _ _ _]]]]]] :=
        wfmp_jal_cross Lft.Hwfmp_c Lft.Hwfmp_p Lft.Hwfmp_p disjoint_cp closed_cp (erefl _) H1 H2 H3.
      by exists mb.
    Qed.

    Lemma memory_size_lin :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: Lft.memory_size_pc. Qed.
    Lemma memory_size_lin' :
      size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c')))
        + size (code p' ++ code c') < alloc_label.
    Proof. exact: Lft.memory_size_pc. Qed.
    Lemma memory_size_lin'' :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c')))
        + size (code p ++ code c') < alloc_label.
    Proof. exact: Lft.memory_size_pc. Qed.

    Lemma bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p').
    Proof. by []. Qed.
    Lemma bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c').
    Proof. by []. Qed.
  End Ad.

  Module Mdiag := RSC_ME_MP Sd Ad.

  Lemma bt_input :
    exists m0 : finpref_behavior,
      [/\ does_prefix Mdiag.T.sem m0,
          not_wrong_finpref m0
        & (m0 = Obs.fm /\ does_prefix Mdiag.T.sem Obs.fm)
          \/ (exists t', [/\ m0 = FTbc t',
                            does_prefix Mdiag.T.sem (FGoes_wrong t'),
                            trace_finpref_prefix t' Obs.fm
                          & undef_in t' (prog_interface Lft.p)])].
  Proof.
    case: (Mdiag.maximum_prefix Obs.observed Obs.safe) => [Hfull | [t' [Hgw Hpre Hundef]]].
    - exists Obs.fm. split; [exact: Hfull | exact: Obs.safe | left; by split].
    - exists (FTbc t'). split.
      + exact: (Mdiag.fgw_to_ftbc Hgw).
      + by [].
      + right. exists t'. by split.
  Qed.

  Definition mp_pack := constructive_indefinite_description _ bt_input.
  Definition M0 : finpref_behavior := proj1_sig mp_pack.

  Lemma M0_fits : BT.bt_fits (finpref_trace M0).
  Proof.
    rewrite /M0.
    case: (proj2_sig mp_pack) => _ _ [[-> _]|[t' [-> _ Hpre _]]].
    - exact: Obs.fits.
    - apply: (BT.bt_fits_prefix _ Obs.fits). move: Hpre.
      by case: Obs.fm.
  Qed.

  Definition pkg : bt_me_package Lft.L Lft.P Lft.C Lft.NC Lft.p Lft.c M0 :=
    match proj2_sig mp_pack with
    | And3 HA HB _ => BT.back HA HB M0_fits
    end.

  Definition wfmp_pp : wf_mp Lft.L Lft.P Lft.C
      (unionm (prog_interface Lft.p) (prog_interface Lft.c)) (bt_pp pkg) :=
    bt_wfmp_pp pkg.
  Definition wfmp_cc : wf_mp Lft.L Lft.P Lft.C
      (unionm (prog_interface Lft.p) (prog_interface Lft.c)) (bt_cc pkg) :=
    bt_wfmp_cc pkg.
  Definition wfmp_pp0 := wfmp_pp.
  Definition wfmp_cc0 := wfmp_cc.

  Module Srec <: RecompositionContext.
    Definition p  : program := Lft.p.
    Definition c  : program := Lft.c.
    Definition p' : program := bt_pp pkg.
    Definition c' : program := bt_cc pkg.
    Definition NC : nat := Lft.NC.

    Lemma Hwfp  : well_formed_program p.  Proof. exact: (wfmp_wf Lft.Hwfmp_p). Qed.
    Lemma Hwfc  : well_formed_program c.  Proof. exact: (wfmp_wf Lft.Hwfmp_c). Qed.
    Lemma Hwfp' : well_formed_program p'. Proof. exact: (wfmp_wf wfmp_pp). Qed.
    Lemma Hwfc' : well_formed_program c'. Proof. exact: (wfmp_wf wfmp_cc). Qed.
    Lemma Hmergeable_ifaces :
      mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof. exact: Lft.Hmergeable. Qed.
    Lemma Hifacep : prog_interface p = prog_interface p'. Proof. exact: (bt_ifacep pkg). Qed.
    Lemma Hifacec : prog_interface c = prog_interface c'. Proof. exact: (bt_ifacec pkg). Qed.
    Lemma Hprog_is_closed  : closed_program (program_link p c).  Proof. exact: Lft.Hclosed. Qed.
    Lemma Hprog_is_closed' : closed_program (program_link p' c'). Proof. exact: (bt_closed' pkg). Qed.
    Lemma colors_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
    Proof. exact: Lft.comps_bounded. Qed.
    Lemma NC_lt_word : NC < word_size mt. Proof. exact: Lft.NC_lt_word. Qed.
    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. exact: Lft.alloc_label_lt_word_NC. Qed.
  End Srec.

  Module Arec <: LinearizerFacts Srec.
    Module D := RecompositionDefinitions Srec.
    Import D.

    Lemma iface_pp : prog_interface (bt_pp pkg) = prog_interface Lft.p.
    Proof. exact: (esym (bt_ifacep pkg)). Qed.
    Lemma iface_cc : prog_interface (bt_cc pkg) = prog_interface Lft.c.
    Proof. exact: (esym (bt_ifacec pkg)). Qed.

    Lemma lin_wf_p  : lin_output_wf p.  Proof. exact: (wfmp_loww Lft.Hwfmp_p). Qed.
    Lemma lin_wf_c  : lin_output_wf c.  Proof. exact: (wfmp_loww Lft.Hwfmp_c). Qed.
    Lemma lin_wf_p' : lin_output_wf p'. Proof. exact: (wfmp_loww wfmp_pp). Qed.
    Lemma lin_wf_c' : lin_output_wf c'. Proof. exact: (wfmp_loww wfmp_cc). Qed.

    Lemma labels_disjoint_prefix : forall l,
      findopt (is_label_def l) (code p) <> None ->
      findopt (is_label_def l) (code c) = None /\ findopt (is_label_def l) (code c') = None.
    Proof.
      move=> l H. split.
      - exact: (wfmp_labels_disjoint Lft.Hwfmp_p Lft.Hwfmp_c disjoint_pc H).
      - have Hd : fdisjoint (domm (prog_interface Lft.p)) (domm (prog_interface (bt_cc pkg))).
        { rewrite iface_cc. exact: disjoint_pc. }
        exact: (wfmp_labels_disjoint Lft.Hwfmp_p wfmp_cc Hd H).
    Qed.
    Lemma labels_disjoint_suffix : forall l,
      findopt (is_label_def l) (code c') <> None ->
      findopt (is_label_def l) (code p) = None /\ findopt (is_label_def l) (code p') = None.
    Proof.
      move=> l H.
      have Hd : fdisjoint (domm (prog_interface (bt_cc pkg))) (domm (prog_interface Lft.p)).
      { rewrite iface_cc. exact: disjoint_cp. }
      have Hd' : fdisjoint (domm (prog_interface (bt_cc pkg))) (domm (prog_interface (bt_pp pkg))).
      { rewrite iface_cc iface_pp. exact: disjoint_cp. }
      split.
      - exact: (wfmp_labels_disjoint wfmp_cc Lft.Hwfmp_p Hd H).
      - exact: (wfmp_labels_disjoint wfmp_cc wfmp_pp Hd' H).
    Qed.

    Lemma jal_cross_p : forall n l t,
      nth_error (code p) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p) = None ->
      exists mc mc' (ic_ i_ : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code c) = Some mc,
            findopt (is_label_def l) (code c') = Some mc',
            nth_error (code c) mc = Some (ic_, tc) /\ nth_error (code c') mc' = Some (i_, tc)
          & is_code tc /\ color tc \in domm (prog_interface c)].
    Proof.
      move=> n l t H1 H2 H3.
      exact: (wfmp_jal_cross Lft.Hwfmp_p Lft.Hwfmp_c wfmp_cc0 disjoint_pc closed_pc
                (esym iface_cc) H1 H2 H3).
    Qed.
    Lemma jal_cross_c' : forall n l t,
      nth_error (code c') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c') = None ->
      exists mp' mp (ip_ i_ : Merged.instr) (tp : mem_tag),
        [/\ findopt (is_label_def l) (code p') = Some mp',
            findopt (is_label_def l) (code p) = Some mp,
            nth_error (code p') mp' = Some (ip_, tp) /\ nth_error (code p) mp = Some (i_, tp)
          & is_code tp /\ color tp \in domm (prog_interface p)].
    Proof.
      move=> n l t H1 H2 H3.
      have Hd : fdisjoint (domm (prog_interface (bt_cc pkg))) (domm (prog_interface Lft.p)).
      { rewrite iface_cc. exact: disjoint_cp. }
      have Hc : closed_interface (unionm (prog_interface (bt_cc pkg)) (prog_interface Lft.p)).
      { rewrite iface_cc. exact: closed_cp. }
      have [mb [mb' [i [i' [tc [F1 F2 [F3 F4] F5]]]]]] :=
        wfmp_jal_cross wfmp_cc Lft.Hwfmp_p wfmp_pp0 Hd Hc (esym iface_pp) H1 H2 H3.
      exists mb', mb, i', i, tc.
      split; [exact: F2 | exact: F1 | by split |].
      case: F5 => Hcode Hcol. by split.
    Qed.
    Lemma jal_cross_p'one : forall n l t,
      nth_error (code p') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p') = None ->
      exists m, findopt (is_label_def l) (code c') = Some m.
    Proof.
      move=> n l t H1 H2 H3.
      have Hd : fdisjoint (domm (prog_interface (bt_pp pkg))) (domm (prog_interface (bt_cc pkg))).
      { rewrite iface_pp iface_cc. exact: disjoint_pc. }
      have Hc : closed_interface (unionm (prog_interface (bt_pp pkg)) (prog_interface (bt_cc pkg))).
      { rewrite iface_pp iface_cc. exact: closed_pc. }
      have [mb [mb' [i [i' [tc [F1 _ _ _]]]]]] :=
        wfmp_jal_cross wfmp_pp wfmp_cc wfmp_cc Hd Hc (erefl _) H1 H2 H3.
      by exists mb.
    Qed.
    Lemma jal_cross_cone : forall n l t,
      nth_error (code c) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c) = None ->
      exists m, findopt (is_label_def l) (code p) = Some m.
    Proof.
      move=> n l t H1 H2 H3.
      have [mb [mb' [i [i' [tc [F1 _ _ _]]]]]] :=
        wfmp_jal_cross Lft.Hwfmp_c Lft.Hwfmp_p Lft.Hwfmp_p disjoint_cp closed_cp (erefl _) H1 H2 H3.
      by exists mb.
    Qed.

    Lemma memory_size_lin :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: Lft.memory_size_pc. Qed.
    Lemma memory_size_lin' :
      size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c')))
        + size (code p' ++ code c') < alloc_label.
    Proof. exact: (bt_memory_size' pkg). Qed.
    Lemma memory_size_lin'' :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c')))
        + size (code p ++ code c') < alloc_label.
    Proof. exact: (bt_memory_size'' pkg). Qed.

    Lemma bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p').
    Proof. exact: (bt_bufs_shape_pp pkg). Qed.
    Lemma bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c').
    Proof. exact: (bt_bufs_shape_cc pkg). Qed.
  End Arec.

  Module Trec := RecTop Srec Arec.

  Theorem rsc_dc_md_me_mp_faithful :
    does_prefix Trec.sem'' Obs.fm
    \/ (exists m', does_prefix Trec.sem'' (FGoes_wrong m')
                   /\ trace_finpref_prefix m' Obs.fm
                   /\ undef_in m' (prog_interface Lft.p)).
  Proof.
    have Hrun : does_prefix Trec.sem' M0 := bt_run pkg.
    case: (proj2_sig mp_pack) => HA HB Hcases.
    have HAr : does_prefix Trec.sem M0 := HA.
    case: Hcases => [[Efm _] | [t' [Em0 Hgw Hpref Hundef]]].
    - left. rewrite -Efm. exact: (Trec.recomposition_blame HAr Hrun).
    - right. exists t'.
      have Hgwr : does_prefix Trec.sem (FGoes_wrong t') := Hgw.
      have Hrun' : does_prefix Trec.sem' (FTbc t'). { by rewrite -Em0. }
      split; first exact: (Trec.recomposition_blame' Hgwr Hrun' Hundef).
      split; [ exact: Hpref | exact: Hundef ].
  Qed.

End RSC_ME_MP_Faithful.

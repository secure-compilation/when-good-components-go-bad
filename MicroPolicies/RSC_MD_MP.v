(* RSC^DC_MD for the micro-policy machine backend: [RSC_MP (K) (X)] proves the
   RSC^DC_MD conclusion for a model [K : MPCompilerSig] of the linearizer
   correctness and an instance [X : RSC_MP_Input K] of the theorem premises. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Source.Language.
Require Import Source.Blame.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RSCSigs.
Require Import MicroPolicies.Recomposition.RecompositionTop.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalEpsilon.

Import DoNotation.
Import Types.

(* the blame-refined improvement (as in RSC_DC_MD.v) *)
Definition behavior_improves_blame (b : program_behavior)
           (m : finpref_behavior) (p : Source.program) :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m /\
             undef_in t (Source.prog_interface p).

Module RSC_MP (K : MPCompilerSig) (X : RSC_MP_Input K).

  (* ==================== derived static facts ==================== *)

  Lemma wf_p_compiled : Intermediate.well_formed_program X.p_compiled.
  Proof.
    exact: (Compiler.compilation_preserves_well_formedness
              X.well_formed_p X.successful_compilation).
  Qed.

  Lemma iface_p_compiled :
    Intermediate.prog_interface X.p_compiled = Source.prog_interface X.p.
  Proof.
    exact: (Compiler.compilation_preserves_interface _ _
              X.successful_compilation).
  Qed.

  Lemma linkability_pc :
    linkable (Intermediate.prog_interface X.p_compiled)
             (Intermediate.prog_interface X.Ct).
  Proof.
    rewrite iface_p_compiled. exact: X.linkability.
  Qed.

  Lemma disjoint_pc :
    fdisjoint (domm (Intermediate.prog_interface X.p_compiled))
              (domm (Intermediate.prog_interface X.Ct)).
  Proof.
    by case: linkability_pc.
  Qed.

  Lemma closed_iface_pc :
    closed_interface (unionm (Intermediate.prog_interface X.p_compiled)
                             (Intermediate.prog_interface X.Ct)).
  Proof.
    exact: (Intermediate.cprog_closed_interface X.closedness).
  Qed.

  Lemma wf_link_pc :
    Intermediate.well_formed_program
      (Intermediate.program_link X.p_compiled X.Ct).
  Proof.
    exact: (Intermediate.linking_well_formedness wf_p_compiled
              X.well_formed_Ct linkability_pc).
  Qed.

  Lemma main_in_link :
    Component.main \in domm (unionm (Intermediate.prog_interface X.p_compiled)
                                    (Intermediate.prog_interface X.Ct)).
  Proof.
    have [main_procs [Hmain [Hget _]]] :=
      Intermediate.cprog_main_existence X.closedness.
    have Hdomm : Component.main
                 \in domm (Intermediate.prog_procedures
                             (Intermediate.program_link X.p_compiled X.Ct)).
    { by rewrite mem_domm Hget. }
    move: Hdomm.
    by rewrite -(Intermediate.wfprog_defined_procedures wf_link_pc).
  Qed.

  (* ==================== the diagonal recomposition instance ====================
     (p' := p, c' := c): run-local machinery (colour-trace correspondence,
     memory invariants, initial-state facts) for the maximum-prefix argument,
     which only concerns the left run. *)

  Module SDiag <: RecompositionContext.
    Definition p  : program := K.lin X.p_compiled.
    Definition c  : program := K.lin X.Ct.
    Definition p' : program := K.lin X.p_compiled.
    Definition c' : program := K.lin X.Ct.

    Definition NC : nat := K.NC.

    Lemma Hwfp : well_formed_program p.
    Proof. exact: (K.lin_wf wf_p_compiled X.p_ok). Qed.
    Lemma Hwfc : well_formed_program c.
    Proof. exact: (K.lin_wf X.well_formed_Ct X.Ct_ok). Qed.
    Lemma Hwfp' : well_formed_program p'.
    Proof. exact: Hwfp. Qed.
    Lemma Hwfc' : well_formed_program c'.
    Proof. exact: Hwfc. Qed.

    Lemma Hmergeable_ifaces :
      mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof.
      rewrite /p /c !K.lin_interface. split.
      - exact: linkability_pc.
      - exact: closed_iface_pc.
    Qed.

    Lemma Hifacep : prog_interface p = prog_interface p'.
    Proof. by []. Qed.
    Lemma Hifacec : prog_interface c = prog_interface c'.
    Proof. by []. Qed.

    Lemma Hprog_is_closed : closed_program (program_link p c).
    Proof.
      constructor.
      - rewrite /program_link /= /p /c !K.lin_interface.
        exact: closed_iface_pc.
      - rewrite /program_link /= /p /c !K.lin_main.
        move: main_in_link. by rewrite domm_union in_fsetU.
    Qed.

    Lemma Hprog_is_closed' : closed_program (program_link p' c').
    Proof. exact: Hprog_is_closed. Qed.

    Lemma colors_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) ->
      1 + x < 2 ^ NC.
    Proof.
      move=> x. rewrite /p /c !K.lin_interface. exact: X.comp_bound.
    Qed.

    Lemma NC_lt_word : NC < word_size mt.
    Proof. exact: K.NC_lt_word. Qed.

    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. exact: K.alloc_label_lt_word_NC. Qed.
  End SDiag.

  Module LDiag <: LinearizerFacts SDiag.
    Module D := RecompositionDefinitions SDiag.
    Import D.

    Lemma lin_wf_p : lin_output_wf p.
    Proof. exact: (K.lin_out_wf wf_p_compiled). Qed.
    Lemma lin_wf_c : lin_output_wf c.
    Proof. exact: (K.lin_out_wf X.well_formed_Ct). Qed.
    Lemma lin_wf_p' : lin_output_wf p'.
    Proof. exact: lin_wf_p. Qed.
    Lemma lin_wf_c' : lin_output_wf c'.
    Proof. exact: lin_wf_c. Qed.

    Lemma labels_disjoint_prefix : forall l,
      findopt (is_label_def l) (code p) <> None ->
      findopt (is_label_def l) (code c) = None
      /\ findopt (is_label_def l) (code c') = None.
    Proof.
      move=> l H. split;
        exact: (K.lin_labels_disjoint wf_p_compiled X.well_formed_Ct
                  X.p_ok X.Ct_ok disjoint_pc H).
    Qed.

    Lemma labels_disjoint_suffix : forall l,
      findopt (is_label_def l) (code c') <> None ->
      findopt (is_label_def l) (code p) = None
      /\ findopt (is_label_def l) (code p') = None.
    Proof.
      move=> l H.
      have Hd : fdisjoint (domm (Intermediate.prog_interface X.Ct))
                          (domm (Intermediate.prog_interface X.p_compiled)).
      { rewrite fdisjointC. exact: disjoint_pc. }
      split;
        exact: (K.lin_labels_disjoint X.well_formed_Ct wf_p_compiled X.Ct_ok X.p_ok Hd H).
    Qed.

    Lemma jal_cross_p : forall n l t,
      nth_error (code p) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p) = None ->
      exists mc mc' (ic_ i_ : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code c) = Some mc,
            findopt (is_label_def l) (code c') = Some mc',
            nth_error (code c) mc = Some (ic_, tc)
            /\ nth_error (code c') mc' = Some (i_, tc)
          & is_code tc /\ color tc \in domm (prog_interface c)].
    Proof.
      move=> n l t Hn Hne Hnf.
      have := K.lin_jal_cross wf_p_compiled X.well_formed_Ct X.well_formed_Ct
                X.p_ok X.Ct_ok X.Ct_ok
                disjoint_pc closed_iface_pc erefl Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 F2 [F3 F4] [F5 F6]]]]]]].
      exists mb, mb', i, i', tc.
      split.
      - exact: F1.
      - exact: F2.
      - by split.
      - split; first exact: F5.
        by rewrite /c K.lin_interface.
    Qed.

    Lemma jal_cross_c' : forall n l t,
      nth_error (code c') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c') = None ->
      exists mp' mp (ip_ i_ : Merged.instr) (tp : mem_tag),
        [/\ findopt (is_label_def l) (code p') = Some mp',
            findopt (is_label_def l) (code p) = Some mp,
            nth_error (code p') mp' = Some (ip_, tp)
            /\ nth_error (code p) mp = Some (i_, tp)
          & is_code tp /\ color tp \in domm (prog_interface p)].
    Proof.
      move=> n l t Hn Hne Hnf.
      have Hd : fdisjoint (domm (Intermediate.prog_interface X.Ct))
                          (domm (Intermediate.prog_interface X.p_compiled)).
      { rewrite fdisjointC. exact: disjoint_pc. }
      have Hc : closed_interface
                  (unionm (Intermediate.prog_interface X.Ct)
                          (Intermediate.prog_interface X.p_compiled)).
      { rewrite unionmC; first exact: closed_iface_pc.
        exact: Hd. }
      have := K.lin_jal_cross X.well_formed_Ct wf_p_compiled wf_p_compiled
                X.Ct_ok X.p_ok X.p_ok Hd Hc erefl Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 F2 [F3 F4] [F5 F6]]]]]]].
      exists mb, mb', i, i', tc.
      split.
      - exact: F1.
      - exact: F2.
      - by split.
      - split; first exact: F5.
        by rewrite /p K.lin_interface.
    Qed.

    Lemma jal_cross_p'one : forall n l t,
      nth_error (code p') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p') = None ->
      exists m, findopt (is_label_def l) (code c') = Some m.
    Proof.
      move=> n l t Hn Hne Hnf.
      have [mc [mc' [? [? [? [F1 _ _ _]]]]]] := jal_cross_p Hn Hne Hnf.
      by exists mc.
    Qed.

    Lemma jal_cross_cone : forall n l t,
      nth_error (code c) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c) = None ->
      exists m, findopt (is_label_def l) (code p) = Some m.
    Proof.
      move=> n l t Hn Hne Hnf.
      have [mp' [mp [? [? [? [_ F2 _ _]]]]]] := jal_cross_c' Hn Hne Hnf.
      by exists mp.
    Qed.

    Lemma memory_size_lin :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: X.size_fit. Qed.
    Lemma memory_size_lin' :
      size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c')))
        + size (code p' ++ code c') < alloc_label.
    Proof. exact: X.size_fit. Qed.
    Lemma memory_size_lin'' :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c')))
        + size (code p ++ code c') < alloc_label.
    Proof. exact: X.size_fit. Qed.

    Lemma bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p').
    Proof. by []. Qed.
    Lemma bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c').
    Proof. by []. Qed.
  End LDiag.

  Module TDiag := RecTop SDiag LDiag.

  (* ==================== the maximum prefix lemma ==================== *)

  Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).
  Local Notation Wprog := (program_link (K.lin X.p_compiled) (K.lin X.Ct)).
  Local Notation ipL := (prog_interface (K.lin X.p_compiled)).
  Local Notation icL := (prog_interface (K.lin X.Ct)).
  Local Open Scope word_scope.

  (* a state halted on a decoded [Halt] takes no machine step *)
  Lemma halt_no_step_mp :
    forall (s s' : state) ev i tg,
      step_mp (NC := K.NC) s s' ev ->
      mem s (vala (pc s)) = Some (i @ tg) ->
      decode_instr i = Some (Halt mt) -> False.
  Proof.
    move=> s s' ev i tg Hstep Hm Hd.
    inversion Hstep; subst; simpl in Hm;
      try (rewrite Hm in PC; case: PC => E1 _; subst;
           rewrite Hd in INST; discriminate INST).
    by rewrite Hm in PC.
  Qed.

  (* functionality of the machine step *)
  Lemma step_mp_functional : forall (s s' s'' : state) ev ev',
    step_mp (NC := K.NC) s s' ev -> step_mp (NC := K.NC) s s'' ev' ->
    s' = s'' /\ ev = ev'.
  Proof.
    move=> s s' s'' ev ev' H1 H2.
    setoid_rewrite <- Exec.stepP in H1.
    setoid_rewrite <- Exec.stepP in H2.
    rewrite H1 in H2. by case: H2 => <- <-.
  Qed.

  (* inverting a UB-restricted step *)
  Lemma rub_step_inv : forall (s : state) t (s' : state),
    Step TDiag.sem s t s' ->
    (TDiag.step2 tt s t s' /\ TDiag.allowed_UB s)
    \/ (TDiag.step1 tt s t s' /\ TDiag.step2 tt s t s').
  Proof.
    move=> s t s' Hst. simpl in Hst.
    case: Hst => [s0 t0 s0' HT HA | s0 t0 s0' HS HT].
    - by left.
    - by right.
  Qed.

  (* event steps leave the memory untouched: JUMP touches only registers,
     JAL's MemRead re-tag is the identity, syscalls never emit *)
  Lemma event_step_mem : forall (s s' : state) e,
    step_mp (NC := K.NC) s s' (Some e) -> mem s' = mem s.
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] :=
        TDiag.nsuap_event_inv NEXT.
      rewrite Hmem.
      apply: TDiag.ndsu_mem_noM Hdsu.
      + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TDiag.no_mw_reg_clear_read Hin))).
      + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TDiag.no_mr_reg_clear_read Hin))).
    -
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] :=
        TDiag.nsuap_event_inv NEXT.
      have Hmemcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hhead := TDiag.jal_head_tret Htr.
      rewrite Hmem.
      apply: (@TDiag.mem_unchanged_jal s st0 (pc0+1)%w vret tret (nseq 12 R)
                (tr ov0) (RegWrite ra (pc0+1)%w :: reg_clear_read)
                Hmemcell Hhead _ _ Hdsu).
      + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TDiag.no_mw_reg_clear_read Hin))).
      + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TDiag.no_mr_reg_clear_read Hin))).
    -
      have Hev := TDiag.run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* an event step's target colour is the colour of an existing memory cell *)
  Lemma event_step_valid : forall (s s' : state) e,
    step_mp (NC := K.NC) s s' (Some e) ->
    TDiag.color_in_memory (mem s) ->
    (TDiag.color_of s' \in domm ipL) || (TDiag.color_of s' \in domm icL).
  Proof.
    move=> s s' e Hstep Hcim.
    have Hcol := TDiag.event_step_color Hstep.
    inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      have [tn [Htni Hnc]] := TDiag.event_nextcomp_and_some Htr.
      move: Htni. rewrite ST /=.
      case Hmw : (mem0 w) => [ni|] // [Etn]. subst tn.
      rewrite Hcol Hnc.
      have Hcell : mem s w = Some ni by rewrite ST.
      case: (Hcim _ _ Hcell) => HIn; apply/orP; [left | right];
        exact/Extra.In_in.
    -
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      case: (TDiag.transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TDiag.nsuap_event_inv NEXT.
      have [tn [Htni Hnc]] := TDiag.event_nextcomp_and_some Htr.
      move: Htni. rewrite ST /=.
      case Hmw : (mem0 (swcast imm)) => [ni|] // [Etn]. subst tn.
      rewrite Hcol Hnc.
      have Hcell : mem s (swcast imm) = Some ni by rewrite ST.
      case: (Hcim _ _ Hcell) => HIn; apply/orP; [left | right];
        exact/Extra.In_in.
    -
      have Hev := TDiag.run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* the run-local invariant of the machine run *)
  Definition Jinv (s : state) : Prop :=
    TDiag.general_memory_correctness (mem s)
    /\ ((TDiag.color_of s \in domm ipL) || (TDiag.color_of s \in domm icL)).

  Lemma step_mp_J : forall (s s' : state) ev,
    step_mp (NC := K.NC) s s' ev -> Jinv s -> Jinv s'.
  Proof.
    move=> s s' [e|] Hstep [Hgmc Hval].
    - have Hmm := event_step_mem Hstep.
      split.
      + by rewrite Hmm.
      + apply: event_step_valid Hstep _.
        by case: Hgmc => _ [_ [_ [_ [_ [_ [Hcim _]]]]]].
    - split.
      + exact: (TDiag.lrc_silent_gmc Hstep Hval Hgmc).
      + by rewrite (TDiag.PCCM.silent_step_color_preserved Hstep).
  Qed.

  (* the initial state: main's colour, and correct memory *)
  Lemma initial_color :
    TDiag.color_of (Merged.initial_state (code TDiag.prog)
                      (prog_buffers TDiag.prog) (prog_interface TDiag.prog))
    = Component.main.
  Proof. by []. Qed.

  Lemma initial_J :
    Jinv (Merged.initial_state (code TDiag.prog)
            (prog_buffers TDiag.prog) (prog_interface TDiag.prog)).
  Proof.
    split.
    - have props := TDiag.tsim_properties_match_states.
      have [s3 [Hi3 Hmatch]] :=
        tsim_match_initial_states props
          (Merged.initial_state (code TDiag.prog)
             (prog_buffers TDiag.prog) (prog_interface TDiag.prog))
          (Merged.initial_state (code TDiag.prog')
             (prog_buffers TDiag.prog') (prog_interface TDiag.prog'))
          (erefl _) (erefl _).
      case: Hmatch => M0 Hms.
      inversion Hms; subst;
        match goal with
        | H : TDiag.common_equiv _ _ _ _ |- _ =>
            exact: (TDiag.common_gmc1 H)
        end.
    - rewrite initial_color.
      have := main_in_link. rewrite domm_union in_fsetU => /orP [Hp | Hc];
        apply/orP; [left | right]; by rewrite K.lin_interface.
  Qed.

  (* splitting the machine run at the first program-side divergence *)
  Lemma star_rub_split : forall (s0 : state) t (s' : state),
    Star (mp_sem K.NC Wprog) s0 t s' ->
    Jinv s0 ->
    (Star TDiag.sem s0 t s' /\ Jinv s')
    \/ exists t1 t2 (s1 : state),
        [/\ Star TDiag.sem s0 t1 s1, Jinv s1,
            Nostep TDiag.sem s1 /\ ~ TDiag.final_state_rUB s1,
            TDiag.color_of s1 \in domm ipL
          & t = t1 ** t2].
  Proof.
    move=> s0 t s' Hstar.
    elim: Hstar => [s HJ | s1 t1 s2 t2 s3 tw Hstep Hstar IH Ht HJ].
    - left. split; [exact: star_refl | exact: HJ].
    - have Hraw : exists ev,
          step_mp (NC := K.NC) s1 s2 ev
          /\ t1 = match ev with None => E0 | Some e => [:: e] end.
      { move: Hstep. rewrite /= /prog_step_mp.
        case: (t1) => [|e [|? ?]] //= Hs.
        - by exists None.
        - by exists (Some e). }
      case: Hraw => ev [Hmp Hev].
      have HJ2 : Jinv s2 := step_mp_J Hmp HJ.
      case Hic: (TDiag.color_of s1 \in domm icL).
      +
        have HstepR : Step TDiag.sem s1 t1 s2.
        { apply: step_UB_allowed; last exact: Hic.
          move: Hstep. by rewrite /=. }
        case: (IH HJ2) => [[HstarR HJ'] | [ta [tb [sx [F1 F2 [F3 F4] F5 F6]]]]].
        * left. split; last exact: HJ'.
          eapply star_step; [exact: HstepR | exact: HstarR | exact: Ht].
        * right. exists (t1 ** ta), tb, sx.
          split.
          -- eapply star_step; [exact: HstepR | exact: F1 | by []].
          -- exact: F2.
          -- by split.
          -- exact: F5.
          -- by rewrite Ht F6 Eapp_assoc.
      +
        have Hip : TDiag.color_of s1 \in domm ipL.
        { case: HJ => _ /orP [|] //. by rewrite Hic. }
        case: (classic (exists (s2' : state) ev',
                          step_me (NC := K.NC) s1 s2' ev'))
          => [[s2' [ev' Hme]] | Hnome].
        *
          have Hmp' := TDiag.PCCM.step_me_mp Hme.
          have [E1 E2] := step_mp_functional Hmp' Hmp.
          subst s2' ev'.
          have HstepR : Step TDiag.sem s1 t1 s2.
          { apply: step_UB_disallowed.
            - rewrite /=. rewrite Hev.
              by case: (ev) Hme => [e|] Hme.
            - move: Hstep. by rewrite /=. }
          case: (IH HJ2)
            => [[HstarR HJ'] | [ta [tb [sx [F1 F2 [F3 F4] F5 F6]]]]].
          -- left. split; last exact: HJ'.
             eapply star_step; [exact: HstepR | exact: HstarR | exact: Ht].
          -- right. exists (t1 ** ta), tb, sx.
             split.
             ++ eapply star_step; [exact: HstepR | exact: F1 | by []].
             ++ exact: F2.
             ++ by split.
             ++ exact: F5.
             ++ by rewrite Ht F6 Eapp_assoc.
        *
          right. exists E0, tw, s1.
          split.
          -- exact: star_refl.
          -- exact: HJ.
          -- split.
             ++
                move=> t' s'' /rub_step_inv [[HmpT Hall] | [HmeS HmpT]].
                ** suff: TDiag.color_of s1 \in domm icL by rewrite Hic.
                   exact: Hall.
                ** move: HmeS. rewrite /TDiag.step1.
                   case: (t') => [|e [|? ?]] //= HmeS;
                     by apply: Hnome; eexists; eexists; exact: HmeS.
             ++
                move=> Hfin.
                destruct s1 as [m0 r0 [pcv tpc0] ex0].
                move: Hfin. rewrite /TDiag.final_state_rUB.
                case Hm0 : (m0 pcv) => [[iv tg]|] //= [Hd _].
                exact: (halt_no_step_mp Hmp Hm0 Hd).
          -- exact: Hip.
          -- by [].
  Qed.

  (* THE maximum prefix lemma: the machine run replays in the UB-restricting
     semantics, in full or up to a blamable program-side divergence *)
  Lemma maximum_prefix :
    does_prefix TDiag.sem X.fm
    \/ exists t', [/\ does_prefix TDiag.sem (FGoes_wrong t'),
                     trace_finpref_prefix t' X.fm
                   & undef_in t' (Intermediate.prog_interface X.p_compiled)].
  Proof.
    have DPE := does_prefix_equiv TDiag.det_sem.
    have Hdp := X.target_prefix.
    apply (does_prefix_equiv (det_mp_sem K.NC Wprog)) in Hdp.
    have Hnw := X.safe_prefix.
    have Hundef : forall (s1 : state) t1,
        Star TDiag.sem (Merged.initial_state (code TDiag.prog)
              (prog_buffers TDiag.prog) (prog_interface TDiag.prog)) t1 s1 ->
        TDiag.color_of s1 \in domm ipL ->
        undef_in t1 (Intermediate.prog_interface X.p_compiled).
    { move=> s1 t1 Hst Hip.
      rewrite /undef_in /last_comp.
      have -> : last Component.main [seq next_comp_of_event e | e <- t1]
                = TDiag.color_of s1.
      { by rewrite (TDiag.star_color_last Hst) initial_color. }
      move: Hip. by rewrite K.lin_interface. }
    case: X.fm Hdp Hnw => [t|t|t] Hdp Hnw //.
    -
      inversion Hdp as [| |s s' t0 Hini Hstar Hfin| |]; subst.
      move: Hini. rewrite /= /prog_initial => ?; subst s.
      case: (star_rub_split Hstar initial_J)
        => [[HstarR HJ'] | [ta [tb [sx [F1 F2 [F3 F4] F5 F6]]]]].
      + case: (classic (TDiag.final_state_rUB s')) => [HfinR | HnfinR].
        * left. apply/DPE.
          eapply does_FTerminates;
            [reflexivity | exact: HstarR | exact: HfinR].
        *
          right. exists t.
          have Hpci : TDiag.pc_color_inv s' :=
            TDiag.reachable_pc_color (erefl _) HstarR.
          destruct s' as [m0 r0 [pcv tpc0] ex0].
          move: Hfin HnfinR. rewrite /= /final_halt /TDiag.final_state_rUB.
          case Hm0 : (m0 pcv) => [[iv tg]|] //= Hd HnfinR.
          have Hnostep : Nostep TDiag.sem
                           {| Symbolic.mem := m0; Symbolic.regs := r0;
                              Symbolic.pc := pcv @ tpc0;
                              Symbolic.internal := ex0 |}.
          { move=> t' s'' /rub_step_inv [[HmpT _] | [_ HmpT]];
              move: HmpT; rewrite /TDiag.step2;
              case: (t') => [|e [|? ?]] //= HmpT;
              exact: (halt_no_step_mp HmpT Hm0 Hd). }
          have Hip' : TDiag.color_of
                        {| Symbolic.mem := m0; Symbolic.regs := r0;
                           Symbolic.pc := pcv @ tpc0;
                           Symbolic.internal := ex0 |} \in domm ipL.
          { have Hcol : color tg
                        = TDiag.color_of
                            {| Symbolic.mem := m0; Symbolic.regs := r0;
                               Symbolic.pc := pcv @ tpc0;
                               Symbolic.internal := ex0 |}.
            { exact: (Hpci _ Hm0). }
            case: (imply_to_and _ _ (fun HH => HnfinR (conj Hd HH)))
              => [Hin _].
            by rewrite -Hcol. }
          split.
          -- apply/DPE.
             eapply does_FGoes_wrong;
               [reflexivity | exact: HstarR | exact: Hnostep |].
             move=> HfinR. apply: HnfinR. move: HfinR.
             by rewrite /TDiag.final_state_rUB /= Hm0.
          -- exists E0. by rewrite E0_right.
          -- exact: (Hundef _ _ HstarR Hip').
      + right. exists ta.
        split.
        * apply/DPE.
          eapply does_FGoes_wrong;
            [reflexivity | exact: F1 | exact: F3 | exact: F4].
        * by exists tb; rewrite F6.
        * exact: (Hundef _ _ F1 F5).
    -
      inversion Hdp as [s s' t0 Hini Hstar| | | |Hnoinit]; subst; last first.
      + by have := Hnoinit _ (erefl _).
      + move: Hini. rewrite /= /prog_initial => ?; subst s.
        case: (star_rub_split Hstar initial_J)
          => [[HstarR HJ'] | [ta [tb [sx [F1 F2 [F3 F4] F5 F6]]]]].
        * left. apply/DPE.
          eapply does_FTbc; [reflexivity | exact: HstarR].
        * right. exists ta.
          split.
          -- apply/DPE.
             eapply does_FGoes_wrong;
               [reflexivity | exact: F1 | exact: F3 | exact: F4].
          -- by exists tb; rewrite F6.
          -- exact: (Hundef _ _ F1 F5).
  Qed.

  (* ==================== the recomposition quadruple ==================== *)

  Lemma rub_transport : forall Y,
    does_prefix TDiag.sem Y ->
    does_prefix (rub_sem K.NC (Intermediate.prog_interface X.p_compiled)
                   (Intermediate.prog_interface X.Ct) Wprog) Y.
  Proof.
    move=> Y HY.
    rewrite -(K.lin_interface X.p_compiled) -(K.lin_interface X.Ct).
    exact: HY.
  Qed.

  Lemma fgw_to_ftbc : forall t',
    does_prefix TDiag.sem (FGoes_wrong t') -> does_prefix TDiag.sem (FTbc t').
  Proof.
    move=> t' /(does_prefix_equiv TDiag.det_sem) H1.
    apply/(does_prefix_equiv TDiag.det_sem).
    inversion H1 as [|s s' t0 Hini Hstar Hnos Hnf| |Hnoinit|]; subst.
    - by eapply does_FTbc; [exact: Hini | exact: Hstar].
    - by have := Hnoinit _ (erefl _).
  Qed.

  Lemma bt_input :
    exists m0 : finpref_behavior,
      [/\ does_prefix (rub_sem K.NC (Intermediate.prog_interface X.p_compiled)
                        (Intermediate.prog_interface X.Ct) Wprog) m0,
          not_wrong_finpref m0
        & (m0 = X.fm /\ does_prefix TDiag.sem X.fm)
          \/ (exists t', [/\ m0 = FTbc t',
                            does_prefix TDiag.sem (FGoes_wrong t'),
                            trace_finpref_prefix t' X.fm
                          & undef_in t' (Intermediate.prog_interface
                                           X.p_compiled)])].
  Proof.
    case: maximum_prefix => [Hfull | [t' [H1 H2 H3]]].
    - exists X.fm. split.
      + exact: (rub_transport Hfull).
      + exact: X.safe_prefix.
      + left. by split.
    - exists (FTbc t'). split.
      + exact: (rub_transport (fgw_to_ftbc H1)).
      + by [].
      + right. exists t'. by split.
  Qed.

  Definition mp_pack := constructive_indefinite_description _ bt_input.
  Definition M0 : finpref_behavior := proj1_sig mp_pack.

  (* the extracted prefix's trace is a prefix of the observed one, so it
     fits the machine by [X.prefix_fits] *)
  Lemma M0_fits : K.bt_fits X.p_compiled X.Ct (finpref_trace M0).
  Proof.
    apply: X.prefix_fits.
    rewrite /M0. case: (proj2_sig mp_pack) => _ _ [[-> _]|[t' [-> _ Hpre _]]].
    - case: (X.fm) => t /=; by exists E0; rewrite E0_right.
    - exact: Hpre.
  Qed.

  Definition BT : bt_package K.NC K.lin K.lin_ok K.run_ok X.p_compiled X.Ct M0 :=
    match proj2_sig mp_pack with
    | And3 HA HB _ =>
        K.H_bt wf_p_compiled X.well_formed_Ct X.p_ok X.Ct_ok linkability_pc
               X.closedness HA HB M0_fits
    end.

  (* ---- derived facts about the back-translated sides ---- *)

  Lemma wf_ip' : Intermediate.well_formed_program (bt_ip' BT).
  Proof.
    exact: (Compiler.compilation_preserves_well_formedness
              (bt_P'_wf BT) (bt_compile_P' BT)).
  Qed.

  Lemma wf_ic' : Intermediate.well_formed_program (bt_ic' BT).
  Proof.
    exact: (Compiler.compilation_preserves_well_formedness
              (bt_Cs_wf BT) (bt_compile_Cs BT)).
  Qed.

  Lemma iface_ip' :
    Intermediate.prog_interface (bt_ip' BT)
    = Intermediate.prog_interface X.p_compiled.
  Proof.
    by rewrite (Compiler.compilation_preserves_interface _ _
                  (bt_compile_P' BT)) (bt_P'_iface BT).
  Qed.

  Lemma iface_ic' :
    Intermediate.prog_interface (bt_ic' BT)
    = Intermediate.prog_interface X.Ct.
  Proof.
    by rewrite (Compiler.compilation_preserves_interface _ _
                  (bt_compile_Cs BT)) (bt_Cs_iface BT).
  Qed.

  (* ---- the recomposition context with the back-translated sides ---- *)

  Module SRec <: RecompositionContext.
    Definition p  : program := K.lin X.p_compiled.
    Definition c  : program := K.lin X.Ct.
    Definition p' : program := K.lin (bt_ip' BT).
    Definition c' : program := K.lin (bt_ic' BT).

    Definition NC : nat := K.NC.

    Lemma Hwfp : well_formed_program p.
    Proof. exact: (K.lin_wf wf_p_compiled X.p_ok). Qed.
    Lemma Hwfc : well_formed_program c.
    Proof. exact: (K.lin_wf X.well_formed_Ct X.Ct_ok). Qed.
    Lemma Hwfp' : well_formed_program p'.
    Proof. exact: (K.lin_wf wf_ip' (bt_ip'_ok BT)). Qed.
    Lemma Hwfc' : well_formed_program c'.
    Proof. exact: (K.lin_wf wf_ic' (bt_ic'_ok BT)). Qed.

    Lemma Hmergeable_ifaces :
      mergeable_interfaces (prog_interface p) (prog_interface c).
    Proof.
      rewrite /p /c !K.lin_interface. split.
      - exact: linkability_pc.
      - exact: closed_iface_pc.
    Qed.

    Lemma Hifacep : prog_interface p = prog_interface p'.
    Proof. by rewrite /p /p' !K.lin_interface iface_ip'. Qed.
    Lemma Hifacec : prog_interface c = prog_interface c'.
    Proof. by rewrite /c /c' !K.lin_interface iface_ic'. Qed.

    Lemma Hprog_is_closed : closed_program (program_link p c).
    Proof.
      constructor.
      - rewrite /program_link /= /p /c !K.lin_interface.
        exact: closed_iface_pc.
      - rewrite /program_link /= /p /c !K.lin_main.
        move: main_in_link. by rewrite domm_union in_fsetU.
    Qed.

    Lemma Hprog_is_closed' : closed_program (program_link p' c').
    Proof.
      constructor.
      - rewrite /program_link /= /p' /c' !K.lin_interface iface_ip' iface_ic'.
        exact: closed_iface_pc.
      - rewrite /program_link /= /p' /c' !K.lin_main iface_ip' iface_ic'.
        move: main_in_link. by rewrite domm_union in_fsetU.
    Qed.

    Lemma colors_bounded : forall x,
      (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) ->
      1 + x < 2 ^ NC.
    Proof.
      move=> x. rewrite /p /c !K.lin_interface. exact: X.comp_bound.
    Qed.

    Lemma NC_lt_word : NC < word_size mt.
    Proof. exact: K.NC_lt_word. Qed.

    Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
    Proof. exact: K.alloc_label_lt_word_NC. Qed.
  End SRec.

  Module LRec <: LinearizerFacts SRec.
    Module D := RecompositionDefinitions SRec.
    Import D.

    Lemma lin_wf_p : lin_output_wf p.
    Proof. exact: (K.lin_out_wf wf_p_compiled). Qed.
    Lemma lin_wf_c : lin_output_wf c.
    Proof. exact: (K.lin_out_wf X.well_formed_Ct). Qed.
    Lemma lin_wf_p' : lin_output_wf p'.
    Proof. exact: (K.lin_out_wf wf_ip'). Qed.
    Lemma lin_wf_c' : lin_output_wf c'.
    Proof. exact: (K.lin_out_wf wf_ic'). Qed.

    Lemma labels_disjoint_prefix : forall l,
      findopt (is_label_def l) (code p) <> None ->
      findopt (is_label_def l) (code c) = None
      /\ findopt (is_label_def l) (code c') = None.
    Proof.
      move=> l H. split.
      - exact: (K.lin_labels_disjoint wf_p_compiled X.well_formed_Ct
                  X.p_ok X.Ct_ok disjoint_pc H).
      - have Hd : fdisjoint (domm (Intermediate.prog_interface X.p_compiled))
                            (domm (Intermediate.prog_interface (bt_ic' BT))).
        { rewrite iface_ic'. exact: disjoint_pc. }
        exact: (K.lin_labels_disjoint wf_p_compiled wf_ic' X.p_ok (bt_ic'_ok BT) Hd H).
    Qed.

    Lemma labels_disjoint_suffix : forall l,
      findopt (is_label_def l) (code c') <> None ->
      findopt (is_label_def l) (code p) = None
      /\ findopt (is_label_def l) (code p') = None.
    Proof.
      move=> l H.
      have Hd : fdisjoint (domm (Intermediate.prog_interface (bt_ic' BT)))
                          (domm (Intermediate.prog_interface X.p_compiled)).
      { rewrite iface_ic' fdisjointC. exact: disjoint_pc. }
      split.
      - exact: (K.lin_labels_disjoint wf_ic' wf_p_compiled (bt_ic'_ok BT) X.p_ok Hd H).
      - have Hd' : fdisjoint (domm (Intermediate.prog_interface (bt_ic' BT)))
                             (domm (Intermediate.prog_interface (bt_ip' BT))).
        { rewrite iface_ic' iface_ip' fdisjointC. exact: disjoint_pc. }
        exact: (K.lin_labels_disjoint wf_ic' wf_ip' (bt_ic'_ok BT) (bt_ip'_ok BT) Hd' H).
    Qed.

    Lemma jal_cross_p : forall n l t,
      nth_error (code p) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p) = None ->
      exists mc mc' (ic_ i_ : Merged.instr) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code c) = Some mc,
            findopt (is_label_def l) (code c') = Some mc',
            nth_error (code c) mc = Some (ic_, tc)
            /\ nth_error (code c') mc' = Some (i_, tc)
          & is_code tc /\ color tc \in domm (prog_interface c)].
    Proof.
      move=> n l t Hn Hne Hnf.
      have := K.lin_jal_cross wf_p_compiled X.well_formed_Ct wf_ic'
                X.p_ok X.Ct_ok (bt_ic'_ok BT)
                disjoint_pc closed_iface_pc (esym iface_ic') Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 F2 [F3 F4] [F5 F6]]]]]]].
      exists mb, mb', i, i', tc.
      split.
      - exact: F1.
      - exact: F2.
      - by split.
      - split; first exact: F5.
        by rewrite /c K.lin_interface.
    Qed.

    Lemma jal_cross_c' : forall n l t,
      nth_error (code c') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c') = None ->
      exists mp' mp (ip_ i_ : Merged.instr) (tp : mem_tag),
        [/\ findopt (is_label_def l) (code p') = Some mp',
            findopt (is_label_def l) (code p) = Some mp,
            nth_error (code p') mp' = Some (ip_, tp)
            /\ nth_error (code p) mp = Some (i_, tp)
          & is_code tp /\ color tp \in domm (prog_interface p)].
    Proof.
      move=> n l t Hn Hne Hnf.
      have Hd : fdisjoint (domm (Intermediate.prog_interface (bt_ic' BT)))
                          (domm (Intermediate.prog_interface X.p_compiled)).
      { rewrite iface_ic' fdisjointC. exact: disjoint_pc. }
      have Hc : closed_interface
                  (unionm (Intermediate.prog_interface (bt_ic' BT))
                          (Intermediate.prog_interface X.p_compiled)).
      { rewrite iface_ic' unionmC; first exact: closed_iface_pc.
        rewrite fdisjointC. exact: disjoint_pc. }
      have := K.lin_jal_cross wf_ic' wf_p_compiled wf_ip'
                (bt_ic'_ok BT) X.p_ok (bt_ip'_ok BT)
                Hd Hc (esym iface_ip') Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 F2 [F3 F4] [F5 F6]]]]]]].
      exists mb', mb, i', i, tc.
      split.
      - exact: F2.
      - exact: F1.
      - by split.
      - split; first exact: F5.
        by rewrite /p K.lin_interface.
    Qed.

    Lemma jal_cross_p'one : forall n l t,
      nth_error (code p') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code p') = None ->
      exists m, findopt (is_label_def l) (code c') = Some m.
    Proof.
      move=> n l t Hn Hne Hnf.
      have Hd : fdisjoint (domm (Intermediate.prog_interface (bt_ip' BT)))
                          (domm (Intermediate.prog_interface (bt_ic' BT))).
      { rewrite iface_ip' iface_ic'. exact: disjoint_pc. }
      have Hc : closed_interface
                  (unionm (Intermediate.prog_interface (bt_ip' BT))
                          (Intermediate.prog_interface (bt_ic' BT))).
      { rewrite iface_ip' iface_ic'. exact: closed_iface_pc. }
      have := K.lin_jal_cross wf_ip' wf_ic' wf_ic' (bt_ip'_ok BT) (bt_ic'_ok BT)
                (bt_ic'_ok BT) Hd Hc erefl Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 _ _ _]]]]]].
      by exists mb.
    Qed.

    Lemma jal_cross_cone : forall n l t,
      nth_error (code c) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      findopt (is_label_def l) (code c) = None ->
      exists m, findopt (is_label_def l) (code p) = Some m.
    Proof.
      move=> n l t Hn Hne Hnf.
      have Hd : fdisjoint (domm (Intermediate.prog_interface X.Ct))
                          (domm (Intermediate.prog_interface X.p_compiled)).
      { rewrite fdisjointC. exact: disjoint_pc. }
      have Hc : closed_interface
                  (unionm (Intermediate.prog_interface X.Ct)
                          (Intermediate.prog_interface X.p_compiled)).
      { rewrite unionmC; first exact: closed_iface_pc.
        exact: Hd. }
      have := K.lin_jal_cross X.well_formed_Ct wf_p_compiled wf_p_compiled
                X.Ct_ok X.p_ok X.p_ok Hd Hc erefl Hn Hne Hnf.
      move=> [mb [mb' [i [i' [tc [F1 _ _ _]]]]]].
      by exists mb.
    Qed.

    Lemma memory_size_lin :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
        + size (code p ++ code c) < alloc_label.
    Proof. exact: X.size_fit. Qed.
    Lemma memory_size_lin' :
      size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c')))
        + size (code p' ++ code c') < alloc_label.
    Proof. exact: (bt_size' BT). Qed.
    Lemma memory_size_lin'' :
      size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c')))
        + size (code p ++ code c') < alloc_label.
    Proof. exact: (bt_size'' BT). Qed.

    Lemma bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p').
    Proof.
      rewrite /p /p' !K.lin_buffers. exact: (esym (bt_ip'_buffers BT)).
    Qed.
    Lemma bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c').
    Proof.
      rewrite /c /c' !K.lin_buffers. exact: (esym (bt_ic'_buffers BT)).
    Qed.
  End LRec.

  Module TRec := RecTop SRec LRec.

  (* ==================== the assembly ==================== *)

  Lemma linkable_p_ic' :
    linkable (Intermediate.prog_interface X.p_compiled)
             (Intermediate.prog_interface (bt_ic' BT)).
  Proof. rewrite iface_ic'. exact: linkability_pc. Qed.

  Lemma closed_p_ic' :
    Intermediate.closed_program
      (Intermediate.program_link X.p_compiled (bt_ic' BT)).
  Proof.
    apply (Intermediate.interface_preserves_closedness_r
             wf_p_compiled wf_ic' (esym iface_ic') linkability_pc
             X.closedness X.mains).
    apply (matching_mains_equiv _ _ _ (bt_Cs_mmains BT)
             (Compiler.compilation_has_matching_mains (bt_Cs_wf BT)
                (bt_compile_Cs BT))).
  Qed.

  Lemma iface_P'_p :
    Source.prog_interface (bt_P' BT) = Source.prog_interface X.p.
  Proof. by rewrite (bt_P'_iface BT) iface_p_compiled. Qed.

  Lemma linkable_p_Cs :
    linkable (Source.prog_interface X.p) (Source.prog_interface (bt_Cs BT)).
  Proof.
    rewrite (bt_Cs_iface BT) -iface_p_compiled. exact: linkability_pc.
  Qed.

  Lemma closed_p_Cs :
    Source.closed_program (Source.program_link X.p (bt_Cs BT)).
  Proof.
    apply (Source.interface_preserves_closedness_l (bt_src_closed BT)
             iface_P'_p (bt_P'_wf BT) X.well_formed_p).
  Qed.

  (* ---- small prefix algebra ---- *)

  Lemma trace_prefix_trans : forall (a b c : trace),
    trace_prefix a b -> trace_prefix b c -> trace_prefix a c.
  Proof.
    move=> a b c [x Hx] [y Hy].
    exists (x ** y). by rewrite Hy Hx Eapp_assoc.
  Qed.

  Lemma trace_prefix_antisym : forall (a b : trace),
    trace_prefix a b -> trace_prefix b a -> a = b.
  Proof.
    move=> a b [x Hx] [y Hy].
    have Ha' : a ** E0 = a ** (x ** y).
    { rewrite E0_right. by rewrite {1}Hy Hx Eapp_assoc. }
    have H0 : E0 = x ** y := List.app_inv_head _ _ _ Ha'.
    case: (Eapp_E0_inv _ _ (esym H0)) => Hx0 _.
    by rewrite Hx Hx0 E0_right.
  Qed.

  Lemma prefix_gw : forall t (b : program_behavior),
    CompCertExtensions.prefix (FGoes_wrong t) b -> b = Goes_wrong t.
  Proof.
    move=> t. case=> //= t2 ->. by [].
  Qed.

  Lemma behavior_prefix_gw : forall t t3,
    behavior_prefix t (Goes_wrong t3) -> trace_prefix t t3.
  Proof.
    move=> t t3 [b' Hb'].
    case: b' Hb' => [t2|t2|T2|t2] /= Hb'; try by [].
    case: Hb' => ->. by exists t2.
  Qed.

  (* lifting one improvement layer to a prefix or a shorter Goes_wrong *)
  Lemma improves_to_prefix : forall (L : semantics) beh mfin,
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

  (* ==================== THE theorem ==================== *)

  Theorem RSC_DC_MD_MP :
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface X.Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface X.p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link X.p Cs) /\
      program_behaves (S.CS.sem (Source.program_link X.p Cs)) beh /\
      (CompCertExtensions.prefix X.fm beh
       \/ behavior_improves_blame beh X.fm X.p).
  Proof.
    case: (proj2_sig mp_pack) => HA HB Hcases.
    have Hfinale : exists beh1,
        program_behaves (S.CS.sem (Source.program_link X.p (bt_Cs BT)))
          beh1
        /\ (CompCertExtensions.prefix X.fm beh1
            \/ behavior_improves_blame beh1 X.fm X.p).
    { case: Hcases => [[Em Hfull] | [t' [Em H1 H2 H3]]].
      -
        have Hsem'' : does_prefix TRec.sem'' X.fm.
        { apply: TRec.recomposition_blame.
          - exact: Hfull.
          - rewrite -Em. exact: (bt_run BT). }
        have Hruok : K.run_ok X.p_compiled (bt_ic' BT)
                       (finpref_trace X.fm).
        { rewrite -Em. exact: (bt_runok'' BT). }
        have [beh1 [Hbeh1 Himp1]] := K.H_bwd_src X.well_formed_p
          (bt_Cs_wf BT) closed_p_Cs X.successful_compilation
          (bt_compile_Cs BT) X.p_ok (bt_ic'_ok BT)
          linkable_p_ic' closed_p_ic' Hsem'' Hruok.
        case: (improves_to_prefix Hbeh1 Himp1)
          => [[beh2 [Hb2 Hp2]] | [t3 [Eb3 _ Ht3]]].
        + exists beh2. split; [exact: Hb2 | by left].
        +
          subst beh1.
          have Hsrc : does_prefix (S.CS.sem (Source.program_link
                        (bt_P' BT) (bt_Cs BT))) X.fm.
          { rewrite -Em. exact: (bt_src_run BT). }
          case: (Blame.blame_program X.well_formed_p (bt_Cs_wf BT)
                   linkable_p_Cs closed_p_Cs Hbeh1 (bt_P'_wf BT)
                   iface_P'_p (bt_src_closed BT) Hsrc X.safe_prefix Ht3)
            => [Hpm | Hundef].
          * exists (Goes_wrong t3). split; [exact: Hbeh1 | by left].
          * exists (Goes_wrong t3). split; [exact: Hbeh1 |].
            right. exists t3.
            split; first by [].
            split; [exact: Ht3 | exact: Hundef].
      -
        have Hundef_mp : undef_in t' (prog_interface (K.lin X.p_compiled)).
        { move: H3. by rewrite /undef_in K.lin_interface. }
        have Hsem'' : does_prefix TRec.sem'' (FGoes_wrong t').
        { apply: TRec.recomposition_blame'.
          - exact: H1.
          - rewrite -Em. exact: (bt_run BT).
          - exact: Hundef_mp. }
        have Hruok : K.run_ok X.p_compiled (bt_ic' BT)
                       (finpref_trace (FTbc t')).
        { rewrite -Em. exact: (bt_runok'' BT). }
        have [beh1 [Hbeh1 Himp1]] := K.H_bwd_src X.well_formed_p
          (bt_Cs_wf BT) closed_p_Cs X.successful_compilation
          (bt_compile_Cs BT) X.p_ok (bt_ic'_ok BT)
          linkable_p_ic' closed_p_ic' Hsem'' Hruok.
        have [t3 [Eb3 Ht3t']] : exists t3,
            beh1 = Goes_wrong t3 /\ trace_prefix t3 t'.
        { case: Himp1 => [Hp1 | [t3 [Eb3 Hp3]]].
          - have Eb1 := prefix_gw Hp1. exists t'. split.
            + exact: Eb1.
            + by exists E0; rewrite E0_right.
          - exists t3. by split. }
        subst beh1.
        have Ht3fm : trace_finpref_prefix t3 X.fm.
        { case: X.fm H2 => t0 /= H2; exact: (trace_prefix_trans Ht3t' H2). }
        have Hsrc : does_prefix (S.CS.sem (Source.program_link
                      (bt_P' BT) (bt_Cs BT))) (FTbc t').
        { rewrite -Em. exact: (bt_src_run BT). }
        have HK : trace_finpref_prefix t3 (FTbc t') := Ht3t'.
        case: (Blame.blame_program X.well_formed_p (bt_Cs_wf BT)
                 linkable_p_Cs closed_p_Cs Hbeh1 (bt_P'_wf BT)
                 iface_P'_p (bt_src_closed BT) Hsrc I HK)
          => [Hpm | Hundef].
        +
          have Ht't3 : trace_prefix t' t3.
          { exact: (behavior_prefix_gw Hpm). }
          have Et3 : t3 = t' := trace_prefix_antisym Ht3t' Ht't3.
          subst t3.
          exists (Goes_wrong t'). split; [exact: Hbeh1 |].
          right. exists t'.
          split; first by [].
          split.
          * by case: (X.fm) H2 => t0 /= H2.
          * move: H3. by rewrite /undef_in -iface_p_compiled.
        + exists (Goes_wrong t3). split; [exact: Hbeh1 |].
          right. exists t3.
          split; first by [].
          split; [exact: Ht3fm | exact: Hundef]. }
    case: Hfinale => beh1 [Hbeh1 Hor].
    exists (bt_Cs BT), beh1.
    split; [exact: (bt_Cs_iface BT) |].
    split; [exact: (bt_Cs_wf BT) |].
    split; [exact: linkable_p_Cs |].
    split; [exact: closed_p_Cs |].
    split; [exact: Hbeh1 |].
    exact: Hor.
  Qed.

  (* Assumption-closure gate: only [K.*]/[X.*] axioms and classical principles. *)
  Print Assumptions RSC_DC_MD_MP.

End RSC_MP.

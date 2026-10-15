(* RSC_ME_MP : the paper's headline micro-policies theorem — RSC^DC_MD between the
   OVERLAY semantics ([me]) and the low-level micro-policy machine ([mp]) — as a
   STANDALONE theorem over an abstract recomposition-ready overlay quadruple
   [S : RecompositionContext] (+ its static [LinearizerFacts]).

   THE REDUCTION (three ingredients, two PROVEN + one assumed):
     1. MAX-PREFIX  [PROVEN HERE — [maximum_prefix], reproduced generically over [T]]:
        the observed [mp_sem] run of [p ⋈ c] replays on the UB-restricting/overlay side
        ([T.sem]), either in full (as [fm]) or up to a program-side divergence (a UB of
        [p] at a prefix [t']).
     2. BACK-TRANSLATION MP→ME  [THE assumption, "H_bt_me"]: an overlay run of the primed
        pair [p' ⋈ c'] ([T.sem']) realizes that same observed-side prefix.
     3. RECOMPOSITION  [PROVEN — RecompositionTop.recomposition_blame / _blame']:
        recombines (1) and (2) into an overlay run of [p ⋈ c'] ([T.sem'']).

   The conclusion is the paper's claim: the overlay context [c'] explains the observed
   prefix, or the overlay program [p] is BLAMED — and the blame closes OVERLAY-LOCALLY
   via [recomposition_blame'] (a [Goes_wrong] of [T.sem'']); no [H_bwd], no source [Blame].

   The max-prefix machinery below (halt_no_step_mp .. maximum_prefix) is the [RSC_MP]-local
   argument from RSC_MD_MP.v, reproduced generically over [T = RecTop S A] (it only uses
   [T]/[RecTop] members + the [mp] observation, never anything [lin]-specific). *)

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

Require Import Coq.Logic.Classical.
Require Import Lib.Extra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Exec.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RecompositionTop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Types.

Module RSC_ME_MP (S : RecompositionContext) (A : LinearizerFacts S).

  Module T := RecTop S A.

  Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).
  Local Notation W    := (program_link S.p S.c).
  Local Notation ipL  := (prog_interface S.p).
  Local Notation icL  := (prog_interface S.c).
  Local Open Scope word_scope.

  (* [Component.main] is in the linked interface (from closedness of [p ⋈ c]). *)
  Lemma main_in_link :
    Component.main \in domm (unionm (prog_interface S.p) (prog_interface S.c)).
  Proof.
    have Hm : prog_main S.p || prog_main S.c
      := cprog_main_existence S.Hprog_is_closed.
    rewrite domm_union in_fsetU; apply/orP.
    case/orP: Hm => [Hp | Hc].
    - left.  by case: (wfprog_main_existence S.Hwfp) => _ H2; apply: H2.
    - right. by case: (wfprog_main_existence S.Hwfc) => _ H2; apply: H2.
  Qed.

  (* a state halted on a decoded [Halt] takes no machine step *)
  Lemma halt_no_step_mp :
    forall (s s' : state) ev i tg,
      step_mp (NC := S.NC) s s' ev ->
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
    step_mp (NC := S.NC) s s' ev -> step_mp (NC := S.NC) s s'' ev' ->
    s' = s'' /\ ev = ev'.
  Proof.
    move=> s s' s'' ev ev' H1 H2.
    setoid_rewrite <- Exec.stepP in H1.
    setoid_rewrite <- Exec.stepP in H2.
    rewrite H1 in H2. by case: H2 => <- <-.
  Qed.

  (* inverting a UB-restricted step *)
  Lemma rub_step_inv : forall (s : state) t (s' : state),
    Step T.sem s t s' ->
    (T.step2 tt s t s' /\ T.allowed_UB s)
    \/ (T.step1 tt s t s' /\ T.step2 tt s t s').
  Proof.
    move=> s t s' Hst. simpl in Hst.
    case: Hst => [s0 t0 s0' HT HA | s0 t0 s0' HS HT].
    - by left.
    - by right.
  Qed.

  (* event steps leave the memory untouched *)
  Lemma event_step_mem : forall (s s' : state) e,
    step_mp (NC := S.NC) s s' (Some e) -> mem s' = mem s.
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - (* jump *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] :=
        TraceWF.nsuap_event_inv NEXT.
      rewrite Hmem.
      apply: TraceWF.ndsu_mem_noM Hdsu.
      + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TraceWF.no_mw_reg_clear_read Hin))).
      + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TraceWF.no_mr_reg_clear_read Hin))).
    - (* bnz *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - (* jal *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] :=
        TraceWF.nsuap_event_inv NEXT.
      have Hmemcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hhead := TraceWF.jal_head_tret Htr.
      rewrite Hmem.
      apply: (@TraceWF.mem_unchanged_jal s st0 (pc0+1)%w vret tret (nseq 12 R)
                (tr ov0) (RegWrite ra (pc0+1)%w :: reg_clear_read)
                Hmemcell Hhead _ _ Hdsu).
      + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TraceWF.no_mw_reg_clear_read Hin))).
      + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (TraceWF.no_mr_reg_clear_read Hin))).
    - (* syscall: no event *)
      have Hev := TraceWF.run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* an event step's target colour is the colour of an existing memory cell *)
  Lemma event_step_valid : forall (s s' : state) e,
    step_mp (NC := S.NC) s s' (Some e) ->
    T.color_in_memory (mem s) ->
    (T.color_of s' \in domm ipL) || (T.color_of s' \in domm icL).
  Proof.
    move=> s s' e Hstep Hcim.
    have Hcol := T.event_step_color Hstep.
    inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - (* jump: the target cell is [mem s w] *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      have [tn [Htni Hnc]] := T.event_nextcomp_and_some Htr.
      move: Htni. rewrite ST /=.
      case Hmw : (mem0 w) => [ni|] // [Etn]. subst tn.
      rewrite Hcol Hnc.
      have Hcell : mem s w = Some ni by rewrite ST.
      case: (Hcim _ _ Hcell) => HIn; apply/orP; [left | right];
        exact/Extra.In_in.
    - (* bnz *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      case: (T.transfer_event_jumpjal Htr) => E; discriminate.
    - (* jal: the target cell is [mem s (swcast imm)] *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := TraceWF.nsuap_event_inv NEXT.
      have [tn [Htni Hnc]] := T.event_nextcomp_and_some Htr.
      move: Htni. rewrite ST /=.
      case Hmw : (mem0 (swcast imm)) => [ni|] // [Etn]. subst tn.
      rewrite Hcol Hnc.
      have Hcell : mem s (swcast imm) = Some ni by rewrite ST.
      case: (Hcim _ _ Hcell) => HIn; apply/orP; [left | right];
        exact/Extra.In_in.
    - (* syscall *)
      have Hev := TraceWF.run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* the run-local invariant of the machine run *)
  Definition Jinv (s : state) : Prop :=
    T.general_memory_correctness (mem s)
    /\ ((T.color_of s \in domm ipL) || (T.color_of s \in domm icL)).

  Lemma step_mp_J : forall (s s' : state) ev,
    step_mp (NC := S.NC) s s' ev -> Jinv s -> Jinv s'.
  Proof.
    move=> s s' [e|] Hstep [Hgmc Hval].
    - have Hmm := event_step_mem Hstep.
      split.
      + by rewrite Hmm.
      + apply: event_step_valid Hstep _.
        by case: Hgmc => _ [_ [_ [_ [_ [_ [Hcim _]]]]]].
    - split.
      + exact: (T.lrc_silent_gmc Hstep Hval Hgmc).
      + by rewrite (T.PCCM.silent_step_color_preserved Hstep).
  Qed.

  (* the initial state: main's colour, and correct memory *)
  Lemma initial_color :
    T.color_of (Merged.initial_state (code T.prog)
                  (prog_buffers T.prog) (prog_interface T.prog))
    = Component.main.
  Proof. by []. Qed.

  Lemma initial_J :
    Jinv (Merged.initial_state (code T.prog)
            (prog_buffers T.prog) (prog_interface T.prog)).
  Proof.
    split.
    - have props := T.tsim_properties_match_states.
      have [s3 [Hi3 Hmatch]] :=
        tsim_match_initial_states props
          (Merged.initial_state (code T.prog)
             (prog_buffers T.prog) (prog_interface T.prog))
          (Merged.initial_state (code T.prog')
             (prog_buffers T.prog') (prog_interface T.prog'))
          (erefl _) (erefl _).
      case: Hmatch => M0 Hms.
      inversion Hms; subst;
        match goal with
        | H : T.common_equiv _ _ _ _ |- _ =>
            exact: (T.common_gmc1 H)
        end.
    - rewrite initial_color.
      have := main_in_link. rewrite domm_union in_fsetU => /orP [Hp | Hc];
        apply/orP; [left | right]; by [].
  Qed.

  (* splitting the machine run at the first program-side divergence *)
  Lemma star_rub_split : forall (s0 : state) t (s' : state),
    Star (mp_sem S.NC W) s0 t s' ->
    Jinv s0 ->
    (Star T.sem s0 t s' /\ Jinv s')
    \/ exists t1 t2 (s1 : state),
        [/\ Star T.sem s0 t1 s1, Jinv s1,
            Nostep T.sem s1 /\ ~ T.final_state_rUB s1,
            T.color_of s1 \in domm ipL
          & t = t1 ** t2].
  Proof.
    move=> s0 t s' Hstar.
    elim: Hstar => [s HJ | s1 t1 s2 t2 s3 tw Hstep Hstar IH Ht HJ].
    - left. split; [exact: star_refl | exact: HJ].
    - have Hraw : exists ev,
          step_mp (NC := S.NC) s1 s2 ev
          /\ t1 = match ev with None => E0 | Some e => [:: e] end.
      { move: Hstep. rewrite /= /prog_step_mp.
        case: (t1) => [|e [|? ?]] //= Hs.
        - by exists None.
        - by exists (Some e). }
      case: Hraw => ev [Hmp Hev].
      have HJ2 : Jinv s2 := step_mp_J Hmp HJ.
      case Hic: (T.color_of s1 \in domm icL).
      + (* context side: the raw machine step is allowed *)
        have HstepR : Step T.sem s1 t1 s2.
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
      + (* program side *)
        have Hip : T.color_of s1 \in domm ipL.
        { case: HJ => _ /orP [|] //. by rewrite Hic. }
        case: (classic (exists (s2' : state) ev',
                          step_me (NC := S.NC) s1 s2' ev'))
          => [[s2' [ev' Hme]] | Hnome].
        * (* the overlay agrees: functionality forces the same step *)
          have Hmp' := T.PCCM.step_me_mp Hme.
          have [E1 E2] := step_mp_functional Hmp' Hmp.
          subst s2' ev'.
          have HstepR : Step T.sem s1 t1 s2.
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
        * (* first divergence: an observational UB of the program *)
          right. exists E0, tw, s1.
          split.
          -- exact: star_refl.
          -- exact: HJ.
          -- split.
             ++ (* no UB-restricted step *)
                move=> t' s'' /rub_step_inv [[HmpT Hall] | [HmeS HmpT]].
                ** suff: T.color_of s1 \in domm icL by rewrite Hic.
                   exact: Hall.
                ** move: HmeS. rewrite /T.step1.
                   case: (t') => [|e [|? ?]] //= HmeS;
                     by apply: Hnome; eexists; eexists; exact: HmeS.
             ++ (* not an overlay-final state either *)
                move=> Hfin.
                destruct s1 as [m0 r0 [pcv tpc0] ex0].
                move: Hfin. rewrite /T.final_state_rUB.
                case Hm0 : (m0 pcv) => [[iv tg]|] //= [Hd _].
                exact: (halt_no_step_mp Hmp Hm0 Hd).
          -- exact: Hip.
          -- by [].
  Qed.

  (* THE maximum prefix lemma: the machine run replays in the UB-restricting
     semantics, in full or up to a blamable program-side divergence *)
  Lemma maximum_prefix : forall (fm : finpref_behavior),
    does_prefix (mp_sem S.NC W) fm ->
    not_wrong_finpref fm ->
    does_prefix T.sem fm
    \/ exists t', [/\ does_prefix T.sem (FGoes_wrong t'),
                     trace_finpref_prefix t' fm
                   & undef_in t' (prog_interface S.p)].
  Proof.
    move=> fm Hdp Hnw.
    have DPE := does_prefix_equiv T.det_sem.
    apply (does_prefix_equiv (det_mp_sem S.NC W)) in Hdp.
    have Hundef : forall (s1 : state) t1,
        Star T.sem (Merged.initial_state (code T.prog)
              (prog_buffers T.prog) (prog_interface T.prog)) t1 s1 ->
        T.color_of s1 \in domm ipL ->
        undef_in t1 (prog_interface S.p).
    { move=> s1 t1 Hst Hip.
      rewrite /undef_in /last_comp.
      have -> : last Component.main [seq next_comp_of_event e | e <- t1]
                = T.color_of s1.
      { by rewrite (T.star_color_last Hst) initial_color. }
      exact: Hip. }
    case: fm Hdp Hnw => [t|t|t] Hdp Hnw //.
    - (* FTerminates *)
      inversion Hdp as [| |s s' t0 Hini Hstar Hfin| |]; subst.
      move: Hini. rewrite /= /prog_initial => ?; subst s.
      case: (star_rub_split Hstar initial_J)
        => [[HstarR HJ'] | [ta [tb [sx [F1 F2 [F3 F4] F5 F6]]]]].
      + case: (classic (T.final_state_rUB s')) => [HfinR | HnfinR].
        * left. apply/DPE.
          eapply does_FTerminates;
            [reflexivity | exact: HstarR | exact: HfinR].
        * (* halted on program-coloured data: blame *)
          right. exists t.
          have Hpci : T.pc_color_inv s' :=
            T.reachable_pc_color (erefl _) HstarR.
          destruct s' as [m0 r0 [pcv tpc0] ex0].
          move: Hfin HnfinR. rewrite /= /final_halt /T.final_state_rUB.
          case Hm0 : (m0 pcv) => [[iv tg]|] //= Hd HnfinR.
          have Hnostep : Nostep T.sem
                           {| Symbolic.mem := m0; Symbolic.regs := r0;
                              Symbolic.pc := pcv @ tpc0;
                              Symbolic.internal := ex0 |}.
          { move=> t' s'' /rub_step_inv [[HmpT _] | [_ HmpT]];
              move: HmpT; rewrite /T.step2;
              case: (t') => [|e [|? ?]] //= HmpT;
              exact: (halt_no_step_mp HmpT Hm0 Hd). }
          have Hip' : T.color_of
                        {| Symbolic.mem := m0; Symbolic.regs := r0;
                           Symbolic.pc := pcv @ tpc0;
                           Symbolic.internal := ex0 |} \in domm ipL.
          { have Hcol : color tg
                        = T.color_of
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
             by rewrite /T.final_state_rUB /= Hm0.
          -- exists E0. by rewrite E0_right.
          -- exact: (Hundef _ _ HstarR Hip').
      + right. exists ta.
        split.
        * apply/DPE.
          eapply does_FGoes_wrong;
            [reflexivity | exact: F1 | exact: F3 | exact: F4].
        * by exists tb; rewrite F6.
        * exact: (Hundef _ _ F1 F5).
    - (* FTbc *)
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

  Lemma fgw_to_ftbc : forall t',
    does_prefix T.sem (FGoes_wrong t') -> does_prefix T.sem (FTbc t').
  Proof.
    move=> t' /(does_prefix_equiv T.det_sem) H1.
    apply/(does_prefix_equiv T.det_sem).
    inversion H1 as [|s s' t0 Hini Hstar Hnos Hnf| |Hnoinit|]; subst.
    - by eapply does_FTbc; [exact: Hini | exact: Hstar].
    - by have := Hnoinit _ (erefl _).
  Qed.

  (* ==================================================================== *)
  (* [me]/[mp] RSC^DC_MD.  From the observed [mp_sem] run of [p ⋈ c], the
     max-prefix (proven above) transfers it to the overlay side; the
     BACK-TRANSLATION MP→ME [Hbt] supplies the primed pair's overlay run;
     recomposition recombines them.  Conclusion (overlay-local): the
     overlay context [c'] explains the observed prefix [fm], or the overlay
     program [p] is BLAMED.  The "∃ overlay context" of RSC^DC_MD is
     discharged by the module parameter [S], which supplies [c']. *)
  Theorem rsc_dc_md_me_mp :
    forall (fm : finpref_behavior),
      does_prefix (mp_sem S.NC W) fm ->
      not_wrong_finpref fm ->
      (* BACK-TRANSLATION MP→ME ("H_bt_me"), as an oracle over the observed-side prefix *)
      (forall m0, does_prefix T.sem m0 -> not_wrong_finpref m0 -> does_prefix T.sem' m0) ->
      does_prefix T.sem'' fm
      \/ (exists m', does_prefix T.sem'' (FGoes_wrong m')
                     /\ trace_finpref_prefix m' fm
                     /\ undef_in m' (prog_interface S.p)).
  Proof.
    move=> fm Hobs Hsafe Hbt.
    case: (maximum_prefix Hobs Hsafe) => [Hfull | [t' [Hgw Hpref Hundef]]].
    - (* full replay: [c'] reproduces the whole observed prefix *)
      left. exact: (T.recomposition_blame Hfull (Hbt _ Hfull Hsafe)).
    - (* program-side UB: [p] is blamed, overlay-locally *)
      right. exists t'.
      have Hbt' : does_prefix T.sem' (FTbc t').
      { apply: Hbt; [ exact: (fgw_to_ftbc Hgw) | by [] ]. }
      split; first exact: (T.recomposition_blame' Hgw Hbt' Hundef).
      split; [ exact: Hpref | exact: Hundef ].
  Qed.

End RSC_ME_MP.

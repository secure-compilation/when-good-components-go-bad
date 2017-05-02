Require Import Common.
Require Import Events.
Require Import Machine.
Require Import LTT.
Require Import PLTT.
Require Import Smallstep.
Require Import Behavior.

Require Import Coq.Logic.Classical.

Module LTT_TO_PLTT.

Include AbstractMachine.

Section SIMULATION.
  Variable p : LTT.program.
  Variable pp : PLTT.program.
  Variable split : list Component.id.

  (* the split is well-formed w.r.t. to the program interface *)
  Hypothesis splitWF :
    forall C,
      In C split ->
    exists CI,
      In CI (LTT.prog_interface p) /\ Component.name CI = C.

  (* the partial program is obtained by "splitting" the original
     program w.r.t. to split *)
  Hypothesis p_transfto_pp :
    pp = PLTT.apply_split p split splitWF.

  (* build the global environments *)
  Let G := LTT.mkGlobalEnv (LTT.prog_interface p)
                           (LTT.prog_entrypoints p).
  Let G' := PLTT.mkGlobalEnv (LTT.prog_interface p)
                             (LTT.prog_entrypoints p)
                             split.

  Inductive match_states (split : list Component.id)
    : LTT.state -> PLTT.partial_state -> Prop :=
  | program_control:
      forall C s ps mem pmem regs pc,
        PLTT.is_program_component C split ->
        ps = PLTT.to_partial_stack s split ->
        PLTT.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PLTT.PC (C, ps, pmem, regs, pc))

  | context_control:
      forall C s ps mem pmem regs pc,
        PLTT.is_context_component C split ->
        ps = PLTT.to_partial_stack s split ->
        PLTT.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PLTT.CC (C, ps, pmem) PLTT.Normal)

  | context_went_wrong:
      forall C s ps mem pmem regs pc,
        PLTT.is_context_component C split ->
        ps = PLTT.to_partial_stack s split ->
        PLTT.maps_match_on split mem pmem ->
        (forall s' t, ~ LTT.step G (C,s,mem,regs,pc) t s') ->
        ~ LTT.final_state (C,s,mem,regs,pc) ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PLTT.CC (C, ps, pmem) PLTT.WentWrong).

  Hint Constructors match_states.

  Lemma initial_states_match:
    forall s,
      LTT.initial_state p s ->
    exists ps,
      PLTT.initial_state pp ps /\ match_states split s ps.
  Proof.
    intros s Hs_init.
    rewrite p_transfto_pp.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    destruct Hs_init
      as [C_is_0 [empty_stack [empty_regs main_proc]]].
    destruct (Util.mem 0 split) eqn:Hcontrol.
    - exists (PLTT.PC (0, [], mem, regs,
                       EntryPoint.get 0 0 (LTT.genv_entrypoints G))).
      split.
      + unfold PLTT.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply program_control; try auto.
        * unfold PLTT.is_program_component.
          apply Util.in_iff_mem_true. auto.
    - exists (PLTT.CC (0, [], mem) PLTT.Normal).
      split.
      + unfold PLTT.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply context_control; try auto.
        * unfold PLTT.is_context_component.
          apply Util.not_in_iff_mem_false. auto.
  Qed.

  Lemma final_states_match:
    forall s ps,
      match_states split s ps ->
      LTT.final_state s ->
      PLTT.final_state ps.
  Proof.
    intros s ps Hmatch_states Hs_final.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    unfold LTT.final_state in Hs_final.
    inversion Hmatch_states; subst;
      unfold PLTT.final_state; auto.
    - exfalso. apply H9. auto.
  Qed.

  Lemma lockstep_simulation:
    forall s t s',
      LTT.step G s t s' ->
      forall ps,
        match_states split s ps ->
      exists ps',
        PLTT.step G' ps t ps' /\ match_states split s' ps'.
  Proof.
    intros s t s'.
    intros Hstep ps Hmatch_states.

    (* extract the currently executing component memory *)
    destruct (LTT.step_implies_memory_existence G s t s' Hstep)
      as [Cmem HCmem].

    (* useful facts *)
    pose (LTT.prog_entrypoints p) as E.
    pose (LTT.prog_entrypoints_wf p) as EWF.
    assert (HG_unfolded:
              G = {|
                LTT.genv_interfaces := LTT.genv_interfaces G;
                LTT.genv_entrypoints := LTT.genv_entrypoints G
              |}). {
      destruct G. simpl. auto.
    } rewrite HG_unfolded in Hstep.

    (* case analysis on who has control and on the execution *)
    inversion Hmatch_states as
        [ C d pd mem pmem regs pc Hcontrol Hpstack Hmem
        | C d pd mem pmem regs pc Hcontrol Hpstack Hmem
        | C d pd mem pmem regs pc Hcontrol Hpstack Hmem
            Hno_step Hnot_final];
      subst;
      inversion Hstep; subst;

        (* try to extract the current component interface *)
        try (destruct (splitWF C Hcontrol)
              as [CI [C_in_I CI_name]]);
        (* simplify assumptions about memory *)
        simpl in HCmem;

        (* context epsilon steps (except store) *)
        try (eexists; split;
             [ apply PLTT.Context_Epsilon
             | apply context_control; auto
             ]);

        (* program epsilon steps (except store) *)
        try (eexists; split;
             [ eapply PLTT.Program_Epsilon;
               [ apply HCmem
               | apply HCmem
               | eauto
               | apply Hstep
               | apply Hmem; auto
               | apply HCmem
               ]
             | auto
            ]);

        (* the context goes wrong *)
        try (exfalso; eapply Hno_step; eauto).

    (* program store *)
    - exists (PLTT.PC (C, PLTT.to_partial_stack d split,
                       Memory.set pmem C
                                  (Register.get r1 regs)
                                  (Register.get r2 regs),
                       regs, pc+1)).
      split.
      (* step *)
      + remember (Memory.local_update
                    (Register.get r1 regs)
                    (Register.get r2 regs) Cmem)
          as updated_Cmem.
        eapply PLTT.Program_Epsilon with
            (s:=d) (cmem:=Cmem)
            (cmem':=updated_Cmem)
            (wmem':=M.add C updated_Cmem mem).
        * apply HCmem.
        * apply M.add_1. reflexivity.
        * unfold PLTT.maps_match_on.
          intros. split; intro; eassumption.
        * unfold Memory.set in Hstep.
          rewrite (M.find_1 HCmem) in Hstep.
          rewrite Hequpdated_Cmem.
          apply Hstep.
        * apply Hmem; assumption.
        * unfold Memory.set.
          apply Hmem in HCmem.
          rewrite (M.find_1 HCmem).
          rewrite Hequpdated_Cmem.
          apply M.add_1.
          ** reflexivity.
          ** assumption.
      (* states match *)
      + apply program_control; auto.
        * apply PLTT.update_related_memories with
              (C:=C) (mem1:=mem) (mem2:=pmem)
              (addr:=Register.get r1 regs)
              (val:=Register.get r2 regs);
            auto.

    (* program is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* internal call - step *)
      + apply PLTT.Program_Internal_Call; auto.
      (* internal call - states match *)
      + destruct (splitWF C' HC'origin)
          as [C'I [C'I_in_I C'I_name_is_C']].
        destruct (EWF C'I C' C'I_in_I C'I_name_is_C')
          as [C'_in_E' [addrs C'_mapsto_E']].
        rewrite EntryPoint.get_on_compatible_entrypoints with
            (E':=E) (addrs:=addrs).
        apply program_control; eauto.
        * simpl.
          apply Util.in_iff_mem_true in Hcontrol.
          rewrite Hcontrol.
          reflexivity.
        * eauto.
        * auto.
      (* external call - step *)
      + apply PLTT.Program_External_Call; auto.
      (* external call - states match *)
      + apply context_control; auto.
        * simpl.
          apply Util.in_iff_mem_true in Hcontrol.
          rewrite Hcontrol.
          reflexivity.

    (* program is returning *)
    - destruct (in_dec Nat.eq_dec C' split)
        as [ HC'origin | HC'origin ];
        eexists; split.
      (* internal return - step *)
      + apply PLTT.Program_Internal_Return; auto.
        * simpl.
          apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin. reflexivity.
      (* internal return - states match *)
      + eauto.
      (* external return - step *)
      + apply PLTT.Program_External_Return; auto.
        * simpl.
          apply Util.not_in_iff_mem_false in HC'origin.
          rewrite HC'origin. reflexivity.
      (* external return - states match *)
      + eauto.

    (* context store - states match *)
    - unfold PLTT.maps_match_on.
      intros C' C'mem HC'origin.
      split.
      + intro HC'map.
        apply Hmem; auto.
        * destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
          ** unfold Memory.set in HC'map.
             rewrite HCfind in HC'map.
             apply M.add_3 in HC'map; auto.
             *** unfold not. intros HeqCC'.
                 apply Hcontrol.
                 rewrite <- HeqCC' in HC'origin.
                 apply HC'origin.
          ** unfold Memory.set in HC'map.
             rewrite HCfind in HC'map.
             assumption.
      + intro HC'map.
        assert (HneqCC': C <> C').
        { intro HeqCC'. apply Hcontrol.
          rewrite <- HeqCC' in HC'origin. apply HC'origin. }
        unfold Memory.set.
        destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
        * assert (HC'mem: PLTT.M.MapsTo C' C'mem mem).
          { apply Hmem; assumption. }
          eapply M.add_2; assumption.
        * apply Hmem; auto.

    (* context call is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* external call - step *)
      + apply PLTT.Context_External_Call;
          try assumption.
        * apply PLTT.push_by_context_preserves_partial_stack; eauto.
      (* external call - states match *)
      + destruct (splitWF C' HC'origin)
          as [CI [CI_in_I CI_name_is_C']].
        destruct (EWF CI C' CI_in_I CI_name_is_C')
          as [C'_in_E' [addrs C'_mapsto_E']].
        rewrite EntryPoint.get_on_compatible_entrypoints with
            (E':=E) (addrs:=addrs).
        apply program_control; eauto.
        * eauto.
        * assumption.
      (* internal call - step *)
      + apply PLTT.Context_Internal_Call;
          try assumption.
        * apply PLTT.push_by_context_preserves_partial_stack; eauto.
      (* internal call - states match *)
      + eauto.

    (* context is returning *)
    - destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
        eexists; split.
      (* external return - step*)
      + apply PLTT.Context_External_Return; auto.
        * simpl. apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin.
          reflexivity.
      (* external return - states match *)
      + eauto.
      (* internal return - step *)
      + apply PLTT.Context_Internal_Return; auto.
        * apply PLTT.push_by_context_preserves_partial_stack; auto.
      (* internal return - states match *)
      + eauto.
  Qed.

  Theorem forward_simulation_between_LTT_and_PLTT:
    forward_simulation (LTT.semantics p) (PLTT.semantics pp).
  Proof.
    apply forward_simulation_step with (match_states split).
    - apply initial_states_match.
    - apply final_states_match.
    - rewrite p_transfto_pp.
      apply lockstep_simulation.
  Qed.

  Corollary not_wrong_behavior_preservation:
    forall beh,
      not_wrong beh ->
      program_behaves (LTT.semantics p) beh ->
      program_behaves (PLTT.semantics pp) beh.
  Proof.
    intros beh Hnotwrong Hprogbeh.
    eapply forward_simulation_same_safe_behavior; eauto.
    apply forward_simulation_between_LTT_and_PLTT.
  Qed.

  (* END OF STABLE PART *)

  (* We can prove something stronger, that is, PLTT 
     preserves exactly all behaviors. *)

  (* IDEA:
     when LTT goes wrong we might be in two cases:
     - the program is executing
       it means that PLTT must be stuck as well
     - the context is executing
       it means that the last step of our simulation
       must go into a WentWrong state
     by proving this two lemmas, we should be able to
     show that the trace produced when going wrong
     is exactly the same.
   *)

  Lemma nonfinal_preservation_for_program:
    forall s pstate,
      match_states split s (PLTT.PC pstate) ->
      ~ LTT.final_state s ->
      ~ PLTT.final_state (PLTT.PC pstate).
  Proof.
    intros s pstate Hmatch_states Hnot_final.
    unfold not, PLTT.final_state.
    destruct pstate. destruct p0. destruct p0. destruct p0.
    intro Hhalt.
    apply Hnot_final. unfold LTT.final_state.
    destruct s. destruct p0. destruct p0. destruct p0.
    inversion Hmatch_states; subst. auto.
  Qed.

  Lemma nostep_preservation_for_program:
    forall s pstate,
      match_states split s (PLTT.PC pstate) ->
      (forall t s', ~ LTT.step G s t s') -> 
      (forall t ps', ~ PLTT.step G' (PLTT.PC pstate) t ps'). 
  Proof.
    intros s pstate Hmatch_states Hnostep.
    intros t ps'. unfold not. intro contra.
    inversion Hmatch_states. subst.
    inversion contra; subst.
    apply Hnostep with (t:=E0) (s':=(C,s0,mem',regs,pc')).
    (* apply LTT weakening *)
    Admitted.

  (* 1st ATTEMPT *)
  
  Section FORWARD_SIMULATION.
    Context index order match_states
            (S: fsim_properties
                  (LTT.semantics p) (PLTT.semantics pp)
                  index order match_states).

    Lemma generic_match_implies_specific_match:
      forall i s pstate,
        match_states i s (PLTT.PC pstate) ->
        SIMULATION.match_states split s (PLTT.PC pstate).
    Proof.
      intros i s pstate Hmatch_states.
    Admitted.

    Lemma goes_wrong_preservation:
      forall i s ps t s',
        Star (LTT.semantics p) s t s' ->
        Nostep (LTT.semantics p) s' ->
        ~final_state (LTT.semantics p) s' ->
        match_states i s ps ->
      exists ps',
        Star (PLTT.semantics pp) ps t ps' /\
        Nostep (PLTT.semantics pp) ps' /\
        ~final_state (PLTT.semantics pp) ps'.
    Proof.
      intros i s ps t s'.
      intros HLTT_star HLTT_nostep HLTT_nofinal.
      intros Hmatch_states.
      destruct (simulation_star
                  S HLTT_star i ps Hmatch_states)
        as [i' [ps' [HPLTT_star Hmatch_states']]].
      destruct ps' as [pstate | cstate exec_state].
      (* the program got stuck *)
      - exists (PLTT.PC pstate). split; auto. split.
        (* we cannot step anymore *)
        + simpl. unfold nostep.
          rewrite p_transfto_pp.
          unfold PLTT.apply_split. simpl.
          eapply nostep_preservation_for_program;
            eauto.
          apply (generic_match_implies_specific_match i');
            auto.
        (* we are not in a final state *)
        + apply nonfinal_preservation_for_program with s';
            eauto.
          apply (generic_match_implies_specific_match i');
            auto.
      (* the context got stuck *)
      - exists (PLTT.CC cstate PLTT.WentWrong).
        split.
        * destruct exec_state.
          ** apply star_right with
                 t (PLTT.CC cstate PLTT.Normal) E0.
             *** apply HPLTT_star.
             *** destruct cstate. destruct p0.
                 apply PLTT.Context_GoesWrong.
             *** symmetry. apply E0_right.
          ** auto.
        * split.
          (* WentWrong doesn't step *)
          ** unfold nostep. intros.
             unfold not. intro contra. inversion contra.
          (* WentWrong is not final *)
          ** unfold not. intro.
             enough (Hnot_final:
                       ~ PLTT.final_state
                         (PLTT.CC cstate PLTT.WentWrong)).
             apply Hnot_final; auto.
             unfold not, PLTT.final_state.
             destruct cstate. destruct p0.
             intro contra. inversion contra.
    Qed.

    Theorem state_goes_wrong_preservation:
      forall i s ps t,
        match_states i s ps ->
        state_behaves (LTT.semantics p) s (Goes_wrong t) ->
        state_behaves (PLTT.semantics pp) ps (Goes_wrong t).
    Proof.
      intros i s ps t Hmatch_states Hstatebeh.
      inversion Hstatebeh.
      destruct (goes_wrong_preservation
             i s ps t s' H0 H1 H2 Hmatch_states)
        as [ps' [Hps_star [Hps_nostep Hps_notfinal]]].
      eapply state_goes_wrong; eauto.
    Qed.

    Theorem wrong_behavior_preservation:
      forall t,
        program_behaves (LTT.semantics p) (Goes_wrong t) ->
        program_behaves (PLTT.semantics pp) (Goes_wrong t).
    Proof.
      intros t Hprogbeh.
      inversion Hprogbeh as [ s beh Hs_init Hstatebeh
                            | Hnot_init ].
      (* goes wrong with non-empty trace *)
      - (* initial states *)
        destruct (fsim_match_initial_states S s Hs_init)
          as [i [ps [Hps_init Hmatch_states]]].
        (* simulation *)
        eapply program_runs; eauto.
        apply state_goes_wrong_preservation with i s; auto.
      (* goes intially wrong *)
      - assert (Hgoingwrong_state:
          exists ps,
            ps = (PLTT.CC (0%nat, [],
                           @M.empty (list nat))
                          PLTT.WentWrong) /\
            Nostep (PLTT.semantics pp) ps /\
            PLTT.initial_state pp ps /\
            ~PLTT.final_state ps). {
          exists (PLTT.CC (0%nat, [], @M.empty (list nat))
                          PLTT.WentWrong).
          split; auto.
          split.
          - unfold nostep. intros.
            unfold not. intro contra. inversion contra.
          - unfold PLTT.initial_state. split; auto.
            unfold PLTT.final_state.
            unfold not. intro contra. inversion contra.
        }
        destruct Hgoingwrong_state
          as [ps [Hps_state [Hps_nostep
                               [Hps_init Hps_notfinal]]]].
        apply program_runs with ps; eauto. subst.
        apply state_goes_wrong with
            (PLTT.CC (0%nat, [], M.empty (list nat))
                     PLTT.WentWrong).
        apply star_refl; auto.
        unfold nostep. intros t ps' contra.
        inversion contra.
        unfold not. intro contra.
        apply Hps_notfinal. auto.
    Qed.
  End FORWARD_SIMULATION.

  Corollary strong_behavior_preservation:
    forall beh,
      program_behaves (LTT.semantics p) beh ->
      program_behaves (PLTT.semantics pp) beh.
  Proof.
    intros beh Hprogbeh.
    destruct beh.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_LTT_and_PLTT.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_LTT_and_PLTT.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_LTT_and_PLTT.
      simpl. reflexivity.
    - destruct forward_simulation_between_LTT_and_PLTT.
      apply wrong_behavior_preservation with
          index order match_states0; auto.
  Qed.

  (* STUCK! We cannot prove the two lemmas about
     generic nostep and nonfinal preservation! *)

  (* 2nd ATTEMPT *)
  (* Let's try with a stronger notion of simulation *)

  Record fsim_properties'
         (L1 L2: semantics) (index: Type)
         (order: index -> index -> Prop)
         (match_states: index -> state L1 -> state L2 -> Prop)
    : Prop := {
      fsim_order_wf': well_founded order;
      fsim_match_initial_states':
        forall s1, initial_state L1 s1 ->
        exists i, exists s2,
            initial_state L2 s2 /\ match_states i s1 s2;
      fsim_match_final_states':
        forall i s1 s2,
          match_states i s1 s2 ->
          final_state L1 s1 -> final_state L2 s2;
      fsim_simulation':
        forall s1 t s1', Step L1 s1 t s1' ->
        forall i s2, match_states i s1 s2 ->
        exists i', exists s2',
          (Plus L2 s2 t s2' \/
           (Star L2 s2 t s2' /\ order i' i)) /\
          match_states i' s1' s2';
      fsim_match_stuck_states:
        forall i s1 s2,
          match_states i s1 s2 ->
          Nostep L1 s1 ->
          Nostep L2 s2;
      fsim_match_nonfinal_states:
        forall i s1 s2,
          match_states i s1 s2 ->
          ~ (final_state L1 s1) ->
          ~ (final_state L2 s2)
  }.

  Arguments fsim_properties': clear implicits.

  Inductive forward_simulation' (L1 L2: semantics) : Prop :=
    Forward_simulation' (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop)
                       (props: fsim_properties' L1 L2 index order match_states).

  Arguments Forward_simulation' {L1 L2 index} order match_states props.
  
  Lemma stronger_forward_LTT_PLTT:
    forward_simulation' (LTT.semantics p) (PLTT.semantics pp).
  Proof.
    destruct forward_simulation_between_LTT_and_PLTT.
    destruct props.
    econstructor.
    constructor; eauto.
    (* stuck states *)
    - admit.
    (* non final states *)
    - admit.
  Admitted.

  Require Import Coqlib.
  Require Import Classical.

  Section FORWARD_SIMULATION_2.
    Context index order match_states
            (S': fsim_properties'
                   (LTT.semantics p) (PLTT.semantics pp)
                   index order match_states).

    Let S := {|
              fsim_order_wf :=
                fsim_order_wf' _ _ _ _ _ S';
              fsim_match_initial_states :=
                fsim_match_initial_states' _ _ _ _ _ S';
              fsim_match_final_states :=
                fsim_match_final_states' _ _ _ _ _ S';
              fsim_simulation :=
                fsim_simulation' _ _ _ _ _ S' |}.

    Lemma forward_simulation_state_behaves:
      forall i s1 s2 beh,
        match_states i s1 s2 ->
        state_behaves (LTT.semantics p) s1 beh ->
        state_behaves (PLTT.semantics pp) s2 beh.
    Proof.
      intros. inv H0.
      - (* termination *)
        exploit simulation_star; eauto. intros [i' [s2' [A B]]].
        econstructor; eauto. eapply fsim_match_final_states; eauto.
      - (* silent divergence *)
        exploit simulation_star; eauto. intros [i' [s2' [A B]]].
        econstructor; eauto. eapply simulation_forever_silent; eauto.
      - (* reactive divergence *)
        econstructor. eapply simulation_forever_reactive; eauto.
      - (* going wrong *)
        exploit simulation_star; eauto. intros [i' [s2' [A B]]].
        econstructor; eauto.
        + apply (fsim_match_stuck_states _ _ _ _ _ S')
            with i' s'; eauto.
        + apply (fsim_match_nonfinal_states _ _ _ _ _ S')
            with i' s'; eauto.
    Qed.

    Theorem behavior_preservation:
      forall beh,
        program_behaves (LTT.semantics p) beh ->
        program_behaves (PLTT.semantics pp) beh.
    Proof.
      destruct stronger_forward_LTT_PLTT as [init ? ?].
      intros. inversion H.
      - (* initial state defined *)
        exploit (fsim_match_initial_states S); eauto.
        intros [i [s' [INIT MATCH]]].
        + econstructor; eauto.
          eapply forward_simulation_state_behaves; eauto.
      - (* initial state undefined *)
        assert (Hgoingwrong_state:
                  exists ps,
                    ps = (PLTT.CC (0%nat, [],
                                   @M.empty (list nat))
                                  PLTT.WentWrong) /\
                    Nostep (PLTT.semantics pp) ps /\
                    PLTT.initial_state pp ps /\
                    ~PLTT.final_state ps). {
          exists (PLTT.CC (0%nat, [], @M.empty (list nat))
                          PLTT.WentWrong).
          split; auto.
          split.
          - unfold nostep. intros.
            unfold not. intro contra. inversion contra.
          - unfold PLTT.initial_state. split; auto.
            unfold PLTT.final_state.
            unfold not. intro contra. inversion contra.
        }
        destruct Hgoingwrong_state
          as [ps [Hps_state [Hps_nostep [Hps_init Hps_notfinal]]]].
        apply program_runs with ps; eauto.
        subst.
        apply state_goes_wrong
          with (PLTT.CC (0%nat, [], M.empty (list nat))
                        PLTT.WentWrong).
        apply star_refl. auto.
        unfold not. intro contra. apply Hps_notfinal.
        auto.
    Qed.
  End FORWARD_SIMULATION_2.
  (* Stuck! Even here we have problems with the same lemmas! *)
End SIMULATION.
End LTT_TO_PLTT.
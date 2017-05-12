Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Events.
Require Import Common.Smallstep.
Require Import Common.Behavior.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import Intermediate.PS.

Require Import Coq.Logic.Classical.

Import IntermediateMachine.

Section CS_PS_SIMULATION.
  Variable p : CS.program.
  Variable pp : PS.program.
  Variable split : list Component.id.

  (* the split is well-formed w.r.t. to the program interface *)
  Hypothesis splitWF :
    forall C,
      In C split ->
    exists CI,
      In CI (CS.prog_interface p) /\ Component.name CI = C.

  (* the partial program is obtained by "splitting" the original
     program w.r.t. to split *)
  Hypothesis p_transfto_pp :
    pp = PS.apply_split p split splitWF.

  (* build the global environments *)
  Let G := CS.mkGlobalEnv (CS.prog_interface p)
                           (CS.prog_entrypoints p).
  Let G' := PS.mkGlobalEnv (CS.prog_interface p)
                             (CS.prog_entrypoints p)
                             split.

  Inductive match_states (split : list Component.id)
    : CS.state -> PS.partial_state -> Prop :=
  | program_control:
      forall C s ps mem pmem regs pc,
        PS.is_program_component C split ->
        ps = PS.to_partial_stack s split ->
        PS.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PS.PC (C, ps, pmem, regs, pc))

  | context_control:
      forall C s ps mem pmem regs pc,
        PS.is_context_component C split ->
        ps = PS.to_partial_stack s split ->
        PS.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PS.CC (C, ps, pmem) PS.Normal)

  | context_went_wrong:
      forall C s ps mem pmem regs pc,
        PS.is_context_component C split ->
        ps = PS.to_partial_stack s split ->
        PS.maps_match_on split mem pmem ->
        (forall s' t, ~ CS.step G (C,s,mem,regs,pc) t s') ->
        ~ CS.final_state (C,s,mem,regs,pc) ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PS.CC (C, ps, pmem) PS.WentWrong).

  Hint Constructors match_states.

  Lemma initial_states_match:
    forall s,
      CS.initial_state p s ->
    exists ps,
      PS.initial_state pp ps /\ match_states split s ps.
  Proof.
    intros s Hs_init.
    rewrite p_transfto_pp.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    destruct Hs_init
      as [C_is_0 [empty_stack [empty_regs main_proc]]].
    destruct (Util.mem 0 split) eqn:Hcontrol.
    - exists (PS.PC (0, [], mem, regs,
                       EntryPoint.get 0 0 (CS.genv_entrypoints G))).
      split.
      + unfold PS.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply program_control; auto.
        * unfold PS.is_program_component.
          apply Util.in_iff_mem_true. auto.
    - exists (PS.CC (0, [], mem) PS.Normal).
      split.
      + unfold PS.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply context_control; auto.
        * unfold PS.is_context_component.
          apply Util.not_in_iff_mem_false. auto.
  Qed.

  Lemma final_states_match:
    forall s ps,
      match_states split s ps ->
      CS.final_state s ->
      PS.final_state ps.
  Proof.
    intros s ps Hmatch_states Hs_final.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    unfold CS.final_state in Hs_final.
    inversion Hmatch_states; subst;
      unfold PS.final_state; auto.
    - exfalso. apply H9. auto.
  Qed.

  Lemma lockstep_simulation:
    forall s t s',
      CS.step G s t s' ->
      forall ps,
        match_states split s ps ->
      exists ps',
        PS.step G' ps t ps' /\ match_states split s' ps'.
  Proof.
    intros s t s'.
    intros Hstep ps Hmatch_states.

    (* extract the currently executing component memory *)
    destruct (CS.step_implies_memory_existence G s t s' Hstep)
      as [Cmem HCmem].

    (* useful facts *)
    pose (CS.prog_entrypoints p) as E.
    pose (CS.prog_entrypoints_wf p) as EWF.
    assert (HG_unfolded:
              G = {|
                CS.genv_interfaces := CS.genv_interfaces G;
                CS.genv_entrypoints := CS.genv_entrypoints G
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
        try (match goal with
             | HC: PS.is_context_component C split |- _ =>
               eexists; split;
               [ apply PS.Context_Epsilon
               | apply context_control; auto]
             end);

        (* program epsilon steps (except store) *)
        try (match goal with
             | HC: PS.is_program_component C split |- _ =>
               eexists; split;
               [ eapply PS.Program_Epsilon;
                 [ apply HCmem
                 | apply HCmem
                 | eauto
                 | apply Hstep
                 | apply Hmem; auto
                 | apply HCmem
                 ]
               | auto]
             end);

        (* the context goes wrong *)
        try (exfalso; eapply Hno_step; eauto).

    (* program store *)
    - destruct (Memory.set pmem C
                           (Register.get r1 regs)
                           (Register.get r2 regs))
        as [pmem'|] eqn:Hmemset.
      + exists (PS.PC (C, PS.to_partial_stack d split,pmem',regs, pc+1)).
        split.
        (* step *)
        * remember (Memory.local_update
                      (Register.get r1 regs)
                      (Register.get r2 regs) Cmem)
            as updated_Cmem.
          eapply PS.Program_Epsilon with
              (s:=d) (cmem:=Cmem)
              (cmem':=updated_Cmem)
              (wmem':=M.add C updated_Cmem mem).
          ** apply HCmem.
          ** apply M.add_1. reflexivity.
          ** unfold PS.maps_match_on.
             intros. split; intro; eassumption.
          ** unfold Memory.set in Hstep.
             unfold Memory.set in H9.
             rewrite (M.find_1 HCmem) in H9.
             inversion H9.
             rewrite H0 in Hstep.
             rewrite Hequpdated_Cmem.
             apply Hstep.
          ** apply Hmem; assumption.
          ** unfold Memory.set in H9, Hmemset.
             apply Hmem in HCmem. apply M.find_1 in HCmem.
             rewrite HCmem in Hmemset. inversion Hmemset. subst.
             apply M.add_1; auto. auto.
      (* states match *)
        * apply program_control; auto.
          ** apply PS.update_related_memories with
                 (C:=C) (mem1:=mem) (mem2:=pmem)
                 (addr:=Register.get r1 regs)
                 (val:=Register.get r2 regs);
               auto.
      + unfold Memory.set in Hmemset.
        apply Hmem in HCmem. apply M.find_1 in HCmem. rewrite HCmem in Hmemset.
        inversion Hmemset. auto.

    (* program is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* internal call - step *)
      + apply PS.Program_Internal_Call; auto.
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
      + apply PS.Program_External_Call; auto.
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
      + apply PS.Program_Internal_Return; auto.
        * simpl.
          apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin. reflexivity.
      (* internal return - states match *)
      + eauto.
      (* external return - step *)
      + apply PS.Program_External_Return; auto.
        * simpl.
          apply Util.not_in_iff_mem_false in HC'origin.
          rewrite HC'origin. reflexivity.
      (* external return - states match *)
      + eauto.

    (* context store *)
    - unfold PS.maps_match_on.
      intros C' C'mem HC'origin.
      split.
      + intros HC'map.
        apply Hmem; auto.
        unfold Memory.set in H9.
        destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
        * inversion H9. subst.
          apply M.add_3 in HC'map. auto.
          unfold not. intro contra. subst. apply Hcontrol. auto.
        * inversion H9.
      + intro HC'map.
        unfold Memory.set in H9.
        destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
        * inversion H9. subst.
          apply M.add_2.
          unfold not. intro contra. subst. apply Hcontrol. auto.
          apply Hmem in HC'map. auto.
          auto.
        * inversion H9.

    (* context call is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* external call - step *)
      + apply PS.Context_External_Call;
          try assumption.
        * apply PS.push_by_context_preserves_partial_stack; eauto.
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
      + apply PS.Context_Internal_Call;
          try assumption.
        * apply PS.push_by_context_preserves_partial_stack; eauto.
      (* internal call - states match *)
      + eauto.

    (* context is returning *)
    - destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
        eexists; split.
      (* external return - step*)
      + apply PS.Context_External_Return; auto.
        * simpl. apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin.
          reflexivity.
      (* external return - states match *)
      + eauto.
      (* internal return - step *)
      + apply PS.Context_Internal_Return; auto.
        * apply PS.push_by_context_preserves_partial_stack; auto.
      (* internal return - states match *)
      + eauto.
  Qed.

  Theorem forward_simulation_between_CS_and_PS:
    forward_simulation (CS.semantics p) (PS.semantics pp).
  Proof.
    apply forward_simulation_step with (match_states split).
    - apply initial_states_match.
    - apply final_states_match.
    - rewrite p_transfto_pp.
      apply lockstep_simulation.
  Defined.

  (* We can prove something stronger, that is, PS 
     preserves exactly all behaviors. *)

  (* IDEA:
     when CS goes wrong we might be in two cases:
     - the program is executing, which means that PS
       must be stuck as well
     - the context is executing, which means that the
       last step of our simulation must go into a 
       WentWrong state
     by proving this two lemmas, we should be able to
     show that the trace produced when going wrong
     is exactly the same we observed in CS.
   *)

  Lemma nonfinal_preservation_for_program:
    forall s pstate,
      match_states split s (PS.PC pstate) ->
      ~ CS.final_state s ->
      ~ PS.final_state (PS.PC pstate).
  Proof.
    intros s pstate Hmatch_states Hnot_final.
    unfold not, PS.final_state.
    destruct pstate as [[[[C d] mem] regs] pc].
    destruct s as [[[[C' d'] mem'] regs'] pc'].
    intro Hhalt.
    apply Hnot_final. unfold CS.final_state.
    inversion Hmatch_states; subst. auto.
  Qed.

  Lemma nostep_preservation_for_program:
    forall s pstate,
      match_states split s (PS.PC pstate) ->
      (forall t s', ~ CS.step G s t s') -> 
      (forall t ps', ~ PS.step G' (PS.PC pstate) t ps'). 
  Proof.
    intros s pstate Hmatch_states Hnostep.
    intros t ps'. unfold not. intro contra.
    inversion Hmatch_states. subst.
    inversion contra; subst;
      (* epsilon steps *)
      try (match goal with
             Hmaps_match : PS.maps_match_on split ?MEM ?PMEM,
             HCwmem : M.MapsTo ?C ?CMEM ?WMEM,
             HCwmem' : M.MapsTo ?C ?CMEM' ?WMEM',
             HCSstep : CS.step ?ENV1 ?S E0 ?S',
             HCpmem : M.MapsTo ?C ?CMEM ?PMEM,
             Hcontra : PS.step ?ENV2 ?PS E0 ?PS'
             |- _ => apply Hmaps_match in HCpmem; eauto;
                     destruct (CS.epsilon_step_weakening
                                 (PS.genv_interfaces G') E
                                 C s wmem wmem' cmem cmem'
                                 regs regs' pc pc' HCwmem HCwmem' HCSstep
                                 (PS.genv_entrypoints G')
                                 s0 mem HCpmem);
                     eapply Hnostep; eauto
           end);
      (* Calls *)
      try (match goal with
             Hcontra : executing (Call ?C2 ?P) ?C ?MEM ?PC
             |- _ => eapply Hnostep; eapply CS.Call; eauto
           end);
      (* Returns *)
      try (match goal with
             Hpartial_stack : PS.to_partial_stack ?STACK split = ?PSTACK,
             Hcontra : executing Return ?C ?MEM ?PC
             |- _ => destruct s0; inversion Hpartial_stack;
                     destruct p0; subst;
                     unfold PS.to_partial_stack in Hpartial_stack;
                     simpl in Hpartial_stack;
                     inversion Hpartial_stack;
                     destruct (Util.mem i split);
                     inversion H1; inversion H2; subst;
                     eapply Hnostep; eapply CS.Return; eauto
           end).
  Qed.

  Definition sim_index {L1 L2 : semantics}
             (FS : forward_simulation L1 L2) :=
    match FS with
    | Forward_simulation index _ _ _ => index
    end.

  Definition sim_order {L1 L2 : semantics}
             (FS : forward_simulation L1 L2) :=
    match FS
          return (sim_index FS) -> (sim_index FS) -> Prop
    with
    | Forward_simulation _ order _ _ => order
    end.

  Definition sim_rel {L1 L2 : semantics}
             (FS : forward_simulation L1 L2) :=
    match FS
          return sim_index FS -> state L1 -> state L2 -> Prop
    with
    | Forward_simulation _ _ rel _ => rel
    end.

  Definition sim_props {L1 L2 : semantics}
             (FS : forward_simulation L1 L2) :=
    match FS
          return fsim_properties
                   L1 L2
                   (sim_index FS) (sim_order FS)
                   (sim_rel FS)
    with
    | Forward_simulation _ _ _ props => props
    end.

  Definition s_match_states :=
    sim_rel forward_simulation_between_CS_and_PS.

  Definition s_props :=
    sim_props forward_simulation_between_CS_and_PS.

  Lemma generic_match_implies_specific_match:
    forall i s pstate,
      s_match_states i s (PS.PC pstate) ->
      CS_PS_SIMULATION.match_states split s (PS.PC pstate).
  Proof.
    intros i s pstate Hmatch_states.
    destruct Hmatch_states; auto.
  Qed.

  Lemma goes_wrong_preservation:
    forall i s ps t s',
      Star (CS.semantics p) s t s' ->
      Nostep (CS.semantics p) s' ->
      ~final_state (CS.semantics p) s' ->
      s_match_states i s ps ->
    exists ps',
      Star (PS.semantics pp) ps t ps' /\
      Nostep (PS.semantics pp) ps' /\
      ~final_state (PS.semantics pp) ps'.
  Proof.
    intros i s ps t s'.
    intros HCS_star HCS_nostep HCS_nofinal.
    intros Hs_match_states.
    destruct (simulation_star
                s_props HCS_star i ps Hs_match_states)
      as [i' [ps' [HPS_star Hs_match_states']]].
    destruct ps' as [pstate | cstate exec_state].
    (* the program got stuck *)
    - exists (PS.PC pstate). split; auto. split.
      (* we cannot step anymore *)
      + simpl. unfold nostep.
        rewrite p_transfto_pp.
        unfold PS.apply_split. simpl.
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
    - exists (PS.CC cstate PS.WentWrong).
      split.
      (* we prove that there exists a star execution *)
      * destruct exec_state.
        (* the execution is in a normal state, hence we make
           an ulterior step to go in a WentWrong state *)
        ** apply star_right with
               t (PS.CC cstate PS.Normal) E0.
           *** apply HPS_star.
           *** destruct cstate. destruct p0.
               apply PS.Context_GoesWrong.
           *** symmetry. apply E0_right.
        (* the execution is already in a WentWrong state*)
        ** auto.
      (* we prove that we cannot step and the state is not final *)
      * split.
        (* WentWrong doesn't step *)
        ** unfold nostep. intros.
           unfold not. intro contra. inversion contra.
        (* WentWrong is not final *)
        ** unfold not. intro.
           enough (Hnot_final:
                     ~ PS.final_state
                       (PS.CC cstate PS.WentWrong)).
           apply Hnot_final; auto.
           unfold not, PS.final_state.
           destruct cstate as [[C d] mem].
           intro contra. inversion contra.
  Qed.

  Theorem state_goes_wrong_preservation:
    forall i s ps t,
      s_match_states i s ps ->
      state_behaves (CS.semantics p) s (Goes_wrong t) ->
      state_behaves (PS.semantics pp) ps (Goes_wrong t).
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
      program_behaves (CS.semantics p) (Goes_wrong t) ->
      program_behaves (PS.semantics pp) (Goes_wrong t).
  Proof.
    intros t Hprogbeh.
    inversion Hprogbeh as [ s beh Hs_init Hstatebeh
                          | Hnot_init ].
    (* goes wrong when an initial state exists *)
    - (* initial states *)
      destruct (fsim_match_initial_states s_props s Hs_init)
        as [i [ps [Hps_init Hmatch_states]]].
      (* simulation *)
      eapply program_runs; eauto.
      apply state_goes_wrong_preservation with i s; auto.
    (* goes intially wrong *)
    - assert (Hgoingwrong_state:
                exists ps,
                  ps = (PS.CC (0%nat, [],
                                 @M.empty (list nat))
                                PS.WentWrong) /\
                  Nostep (PS.semantics pp) ps /\
                  PS.initial_state pp ps /\
                  ~PS.final_state ps). {
        exists (PS.CC (0%nat, [], @M.empty (list nat))
                        PS.WentWrong).
        split; auto.
        split.
        - unfold nostep. intros.
          unfold not. intro contra. inversion contra.
        - unfold PS.initial_state. split; auto.
          unfold PS.final_state.
          unfold not. intro contra. inversion contra.
      }
      destruct Hgoingwrong_state
        as [ps [Hps_state [Hps_nostep
                             [Hps_init Hps_notfinal]]]].
      apply program_runs with ps; eauto. subst.
      apply state_goes_wrong with
          (PS.CC (0%nat, [], M.empty (list nat))
                   PS.WentWrong).
      apply star_refl; auto.
      unfold nostep. intros t ps' contra.
      inversion contra.
      unfold not. intro contra.
      apply Hps_notfinal. auto.
  Qed.

  Corollary strong_behavior_preservation:
    forall beh,
      program_behaves (CS.semantics p) beh ->
      program_behaves (PS.semantics pp) beh.
  Proof.
    intros beh Hprogbeh.
    destruct beh.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CS_and_PS.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CS_and_PS.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CS_and_PS.
      simpl. reflexivity.
    - destruct forward_simulation_between_CS_and_PS.
      apply wrong_behavior_preservation; auto.
  Qed.

  (* OLD ATTEMPT (it is interesting because is generic and
     doesn't rely on the specific instance of forward
     simulation that we built)

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
*)
End CS_PS_SIMULATION.
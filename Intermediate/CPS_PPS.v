Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Events.
Require Import Common.Smallstep.
Require Import Common.Behavior.
Require Import Intermediate.Machine.
Require Import Intermediate.CPS.
Require Import Intermediate.PPS.

Require Import Coq.Logic.Classical.

Import IntermediateMachine.

Section CPS_PPS_SIMULATION.
  Variable p : CPS.program.
  Variable pp : PPS.program.
  Variable split : list Component.id.

  (* the split is well-formed w.r.t. to the program interface *)
  Hypothesis splitWF :
    forall C,
      In C split ->
    exists CI,
      In CI (CPS.prog_interface p) /\ Component.name CI = C.

  (* the partial program is obtained by "splitting" the original
     program w.r.t. to split *)
  Hypothesis p_transfto_pp :
    pp = PPS.apply_split p split splitWF.

  (* build the global environments *)
  Let G := CPS.mkGlobalEnv (CPS.prog_interface p)
                           (CPS.prog_entrypoints p).
  Let G' := PPS.mkGlobalEnv (CPS.prog_interface p)
                             (CPS.prog_entrypoints p)
                             split.

  Inductive match_states (split : list Component.id)
    : CPS.state -> PPS.partial_state -> Prop :=
  | program_control:
      forall C s ps mem pmem regs pc,
        PPS.is_program_component C split ->
        ps = PPS.to_partial_stack s split ->
        PPS.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PPS.PC (C, ps, pmem, regs, pc))

  | context_control:
      forall C s ps mem pmem regs pc,
        PPS.is_context_component C split ->
        ps = PPS.to_partial_stack s split ->
        PPS.maps_match_on split mem pmem ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PPS.CC (C, ps, pmem) PPS.Normal)

  | context_went_wrong:
      forall C s ps mem pmem regs pc,
        PPS.is_context_component C split ->
        ps = PPS.to_partial_stack s split ->
        PPS.maps_match_on split mem pmem ->
        (forall s' t, ~ CPS.step G (C,s,mem,regs,pc) t s') ->
        ~ CPS.final_state (C,s,mem,regs,pc) ->
        match_states split
                     (C, s, mem, regs, pc)
                     (PPS.CC (C, ps, pmem) PPS.WentWrong).

  Hint Constructors match_states.

  Lemma initial_states_match:
    forall s,
      CPS.initial_state p s ->
    exists ps,
      PPS.initial_state pp ps /\ match_states split s ps.
  Proof.
    intros s Hs_init.
    rewrite p_transfto_pp.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    destruct Hs_init
      as [C_is_0 [empty_stack [empty_regs main_proc]]].
    destruct (Util.mem 0 split) eqn:Hcontrol.
    - exists (PPS.PC (0, [], mem, regs,
                       EntryPoint.get 0 0 (CPS.genv_entrypoints G))).
      split.
      + unfold PPS.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply program_control; auto.
        * unfold PPS.is_program_component.
          apply Util.in_iff_mem_true. auto.
    - exists (PPS.CC (0, [], mem) PPS.Normal).
      split.
      + unfold PPS.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply context_control; auto.
        * unfold PPS.is_context_component.
          apply Util.not_in_iff_mem_false. auto.
  Qed.

  Lemma final_states_match:
    forall s ps,
      match_states split s ps ->
      CPS.final_state s ->
      PPS.final_state ps.
  Proof.
    intros s ps Hmatch_states Hs_final.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    unfold CPS.final_state in Hs_final.
    inversion Hmatch_states; subst;
      unfold PPS.final_state; auto.
    - exfalso. apply H9. auto.
  Qed.

  Lemma lockstep_simulation:
    forall s t s',
      CPS.step G s t s' ->
      forall ps,
        match_states split s ps ->
      exists ps',
        PPS.step G' ps t ps' /\ match_states split s' ps'.
  Proof.
    intros s t s'.
    intros Hstep ps Hmatch_states.

    (* extract the currently executing component memory *)
    destruct (CPS.step_implies_memory_existence G s t s' Hstep)
      as [Cmem HCmem].

    (* useful facts *)
    pose (CPS.prog_entrypoints p) as E.
    pose (CPS.prog_entrypoints_wf p) as EWF.
    assert (HG_unfolded:
              G = {|
                CPS.genv_interfaces := CPS.genv_interfaces G;
                CPS.genv_entrypoints := CPS.genv_entrypoints G
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
             [ apply PPS.Context_Epsilon
             | apply context_control; auto
             ]);

        (* program epsilon steps (except store) *)
        try (eexists; split;
             [ eapply PPS.Program_Epsilon;
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
    - exists (PPS.PC (C, PPS.to_partial_stack d split,
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
        eapply PPS.Program_Epsilon with
            (s:=d) (cmem:=Cmem)
            (cmem':=updated_Cmem)
            (wmem':=M.add C updated_Cmem mem).
        * apply HCmem.
        * apply M.add_1. reflexivity.
        * unfold PPS.maps_match_on.
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
        * apply PPS.update_related_memories with
              (C:=C) (mem1:=mem) (mem2:=pmem)
              (addr:=Register.get r1 regs)
              (val:=Register.get r2 regs);
            auto.

    (* program is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* internal call - step *)
      + apply PPS.Program_Internal_Call; auto.
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
      + apply PPS.Program_External_Call; auto.
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
      + apply PPS.Program_Internal_Return; auto.
        * simpl.
          apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin. reflexivity.
      (* internal return - states match *)
      + eauto.
      (* external return - step *)
      + apply PPS.Program_External_Return; auto.
        * simpl.
          apply Util.not_in_iff_mem_false in HC'origin.
          rewrite HC'origin. reflexivity.
      (* external return - states match *)
      + eauto.

    (* context store - states match *)
    - unfold PPS.maps_match_on.
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
        * assert (HC'mem: M.MapsTo C' C'mem mem).
          { apply Hmem; assumption. }
          eapply M.add_2; assumption.
        * apply Hmem; auto.

    (* context call is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* external call - step *)
      + apply PPS.Context_External_Call;
          try assumption.
        * apply PPS.push_by_context_preserves_partial_stack; eauto.
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
      + apply PPS.Context_Internal_Call;
          try assumption.
        * apply PPS.push_by_context_preserves_partial_stack; eauto.
      (* internal call - states match *)
      + eauto.

    (* context is returning *)
    - destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
        eexists; split.
      (* external return - step*)
      + apply PPS.Context_External_Return; auto.
        * simpl. apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin.
          reflexivity.
      (* external return - states match *)
      + eauto.
      (* internal return - step *)
      + apply PPS.Context_Internal_Return; auto.
        * apply PPS.push_by_context_preserves_partial_stack; auto.
      (* internal return - states match *)
      + eauto.
  Qed.

  Theorem forward_simulation_between_CPS_and_PPS:
    forward_simulation (CPS.semantics p) (PPS.semantics pp).
  Proof.
    apply forward_simulation_step with (match_states split).
    - apply initial_states_match.
    - apply final_states_match.
    - rewrite p_transfto_pp.
      apply lockstep_simulation.
  Defined.

  (* We can prove something stronger, that is, PPS 
     preserves exactly all behaviors. *)

  (* IDEA:
     when CPS goes wrong we might be in two cases:
     - the program is executing, which means that PPS
       must be stuck as well
     - the context is executing, which means that the
       last step of our simulation must go into a 
       WentWrong state
     by proving this two lemmas, we should be able to
     show that the trace produced when going wrong
     is exactly the same we observed in CPS.
   *)

  Lemma nonfinal_preservation_for_program:
    forall s pstate,
      match_states split s (PPS.PC pstate) ->
      ~ CPS.final_state s ->
      ~ PPS.final_state (PPS.PC pstate).
  Proof.
    intros s pstate Hmatch_states Hnot_final.
    unfold not, PPS.final_state.
    destruct pstate as [[[[C d] mem] regs] pc].
    destruct s as [[[[C' d'] mem'] regs'] pc'].
    intro Hhalt.
    apply Hnot_final. unfold CPS.final_state.
    inversion Hmatch_states; subst. auto.
  Qed.

  Lemma nostep_preservation_for_program:
    forall s pstate,
      match_states split s (PPS.PC pstate) ->
      (forall t s', ~ CPS.step G s t s') -> 
      (forall t ps', ~ PPS.step G' (PPS.PC pstate) t ps'). 
  Proof.
    intros s pstate Hmatch_states Hnostep.
    intros t ps'. unfold not. intro contra.
    inversion Hmatch_states. subst.
    inversion contra; subst;
      (* epsilon steps *)
      try (match goal with
             Hmaps_match : PPS.maps_match_on split ?MEM ?PMEM,
             HCwmem : M.MapsTo ?C ?CMEM ?WMEM,
             HCwmem' : M.MapsTo ?C ?CMEM' ?WMEM',
             HCPSstep : CPS.step ?ENV1 ?S E0 ?S',
             HCpmem : M.MapsTo ?C ?CMEM ?PMEM,
             Hcontra : PPS.step ?ENV2 ?PS E0 ?PS'
             |- _ => apply Hmaps_match in HCpmem; eauto;
                     destruct (CPS.epsilon_step_weakening
                                 (PPS.genv_interfaces G') E
                                 C s wmem wmem' cmem cmem'
                                 regs regs' pc pc' HCwmem HCwmem' HCPSstep
                                 (PPS.genv_entrypoints G')
                                 s0 mem HCpmem);
                     eapply Hnostep; eauto
           end);
      (* Calls *)
      try (match goal with
             Hcontra : executing (Call ?C2 ?P) ?C ?MEM ?PC
             |- _ => eapply Hnostep; eapply CPS.Call; eauto
           end);
      (* Returns *)
      try (match goal with
             Hpartial_stack : PPS.to_partial_stack ?STACK split = ?PSTACK,
             Hcontra : executing Return ?C ?MEM ?PC
             |- _ => destruct s0; inversion Hpartial_stack;
                     destruct p0; subst;
                     unfold PPS.to_partial_stack in Hpartial_stack;
                     simpl in Hpartial_stack;
                     inversion Hpartial_stack;
                     destruct (Util.mem i split);
                     inversion H1; inversion H2; subst;
                     eapply Hnostep; eapply CPS.Return; eauto
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
    sim_rel forward_simulation_between_CPS_and_PPS.

  Definition s_props :=
    sim_props forward_simulation_between_CPS_and_PPS.

  Lemma generic_match_implies_specific_match:
    forall i s pstate,
      s_match_states i s (PPS.PC pstate) ->
      CPS_PPS_SIMULATION.match_states split s (PPS.PC pstate).
  Proof.
    intros i s pstate Hmatch_states.
    destruct Hmatch_states; auto.
  Qed.

  Lemma goes_wrong_preservation:
    forall i s ps t s',
      Star (CPS.semantics p) s t s' ->
      Nostep (CPS.semantics p) s' ->
      ~final_state (CPS.semantics p) s' ->
      s_match_states i s ps ->
    exists ps',
      Star (PPS.semantics pp) ps t ps' /\
      Nostep (PPS.semantics pp) ps' /\
      ~final_state (PPS.semantics pp) ps'.
  Proof.
    intros i s ps t s'.
    intros HCPS_star HCPS_nostep HCPS_nofinal.
    intros Hs_match_states.
    destruct (simulation_star
                s_props HCPS_star i ps Hs_match_states)
      as [i' [ps' [HPPS_star Hs_match_states']]].
    destruct ps' as [pstate | cstate exec_state].
    (* the program got stuck *)
    - exists (PPS.PC pstate). split; auto. split.
      (* we cannot step anymore *)
      + simpl. unfold nostep.
        rewrite p_transfto_pp.
        unfold PPS.apply_split. simpl.
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
    - exists (PPS.CC cstate PPS.WentWrong).
      split.
      (* we prove that there exists a star execution *)
      * destruct exec_state.
        (* the execution is in a normal state, hence we make
           an ulterior step to go in a WentWrong state *)
        ** apply star_right with
               t (PPS.CC cstate PPS.Normal) E0.
           *** apply HPPS_star.
           *** destruct cstate. destruct p0.
               apply PPS.Context_GoesWrong.
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
                     ~ PPS.final_state
                       (PPS.CC cstate PPS.WentWrong)).
           apply Hnot_final; auto.
           unfold not, PPS.final_state.
           destruct cstate as [[C d] mem].
           intro contra. inversion contra.
  Qed.

  Theorem state_goes_wrong_preservation:
    forall i s ps t,
      s_match_states i s ps ->
      state_behaves (CPS.semantics p) s (Goes_wrong t) ->
      state_behaves (PPS.semantics pp) ps (Goes_wrong t).
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
      program_behaves (CPS.semantics p) (Goes_wrong t) ->
      program_behaves (PPS.semantics pp) (Goes_wrong t).
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
                  ps = (PPS.CC (0%nat, [],
                                 @M.empty (list nat))
                                PPS.WentWrong) /\
                  Nostep (PPS.semantics pp) ps /\
                  PPS.initial_state pp ps /\
                  ~PPS.final_state ps). {
        exists (PPS.CC (0%nat, [], @M.empty (list nat))
                        PPS.WentWrong).
        split; auto.
        split.
        - unfold nostep. intros.
          unfold not. intro contra. inversion contra.
        - unfold PPS.initial_state. split; auto.
          unfold PPS.final_state.
          unfold not. intro contra. inversion contra.
      }
      destruct Hgoingwrong_state
        as [ps [Hps_state [Hps_nostep
                             [Hps_init Hps_notfinal]]]].
      apply program_runs with ps; eauto. subst.
      apply state_goes_wrong with
          (PPS.CC (0%nat, [], M.empty (list nat))
                   PPS.WentWrong).
      apply star_refl; auto.
      unfold nostep. intros t ps' contra.
      inversion contra.
      unfold not. intro contra.
      apply Hps_notfinal. auto.
  Qed.

  Corollary strong_behavior_preservation:
    forall beh,
      program_behaves (CPS.semantics p) beh ->
      program_behaves (PPS.semantics pp) beh.
  Proof.
    intros beh Hprogbeh.
    destruct beh.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CPS_and_PPS.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CPS_and_PPS.
      simpl. reflexivity.
    - eapply forward_simulation_same_safe_behavior; eauto.
      apply forward_simulation_between_CPS_and_PPS.
      simpl. reflexivity.
    - destruct forward_simulation_between_CPS_and_PPS.
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
End CPS_PPS_SIMULATION.
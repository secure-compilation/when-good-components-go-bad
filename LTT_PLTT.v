Require Import Common.
Require Import Traces.
Require Import Machine.
Require Import LTT.
Require Import PLTT.

Module LTT_TO_PLTT.

Include AbstractMachine.

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
                   (PLTT.CC (C, ps, pmem)).

Definition memory_wf (Is : list Component.interface) (mem : Memory.data) :=
  forall CI C,
    In CI Is -> Component.name CI = C ->
    exists Cmem, M.MapsTo C Cmem mem.

Theorem option_simulation:
  forall split s C d mem regs pc s' ps Is E EWF t,
    let G := LTT.mkGlobalEnv Is E EWF in
    s = (C,d,mem,regs,pc) ->

    (* Memory well-formedness *)
    (* - each declared component has its own memory *)
    memory_wf (LTT.get_interfaces G) mem ->

    (* Simulation premises *)
    match_states split s ps ->
    LTT.step G s t s' ->

    (* Simulation argument *)
    (t = E0 /\ match_states split s' ps)
    \/
    (forall E' E'WF SplitWF,
        (* Entrypoints preservation *)
        PLTT.maps_match_on split E E' ->
        let G' := PLTT.mkGlobalEnv Is E' split E'WF SplitWF in
        (* Simulation step *)
        exists ps',
          PLTT.step G' ps t ps' /\ match_states split s' ps').
Proof.
  intros split s C d mem regs pc s' ps Is E EWF t.
  intros G Hstate HmemWF Hstates_match Hstep.

  inversion Hstates_match as [ C0 ? ? ? ? ? ? Hcontrol Hpstack Hmem |
                               C0 ? ? ? ? ? ? Hcontrol Hpstack Hmem ];
    inversion Hstep;
    rewrite Hpstack;
    match goal with
    | Hstate'  : (C0, _, _, _, _) = s,
      Hstate'' : (_, _, _, _, _) = s |- _ =>
      rewrite <- Hstate'' in Hstate'; inversion Hstate'; subst
    end;

    (* prove context epsilon steps by staying still *)
    try (left; split; 
         [ | apply context_control ];
         auto);

    (* prove program epsilon steps *)
    try (right;
         intros E' HE'WF SplitWF HEE'match;
         intros G';
         eexists; split;
         [ (* step *)
           destruct (PLTT.split_wellformed G' C1 Hcontrol)
             as [C1I [C1_in_Is C1I_name]];
           destruct (HmemWF C1I C1 C1_in_Is C1I_name)
             as [C1mem HC1mem];
           eapply PLTT.Program_Epsilon;
           [ apply HC1mem
           | apply HC1mem
           | simpl; unfold PLTT.maps_match_on;
             split; intro; apply HEE'match; assumption
           | simpl;
             match goal with
             | Heq_state : (_, _, _, _, _) = (C, _, _, _, _)
               |- _ =>
               inversion Heq_state
             end;
             match goal with
             | Heq_C : _ = C,
               Heq_d : _ = d,
               Heq_mem : _ = mem,
               Heq_regs : _ = regs,
               Heq_pc : _ = pc
               |- _ =>
               try (rewrite Heq_pc in Hstep);
               rewrite Heq_C, Heq_d, Heq_mem, Heq_regs in Hstep
             end;
             apply Hstep
           | apply Hmem;
             [ assumption
             | match goal with
               | Heq_state : (_, _, _, _, _) = (C, _, _, _, _)
                 |- _ =>
                 inversion Heq_state
               end;
               match goal with
               | Heq_C : _ = C
                 |- _ =>
                 rewrite <- Heq_C; auto
               end
             ]
           | eassumption ]

         | (* states match *)
           simpl;
           match goal with
           | Heq_state : (_, _, _, _, _) = (C, _, _, _, _)
             |- _ =>
             inversion Heq_state
           end;
           match goal with
           | Heq_C : _ = C,
             Heq_pc : _ = pc
             |- _ =>
             try (rewrite <- Heq_pc); apply program_control;
             [ rewrite <- Heq_C; auto
             | reflexivity
             | simpl; unfold PLTT.maps_match_on;
               intros; split; intro; assumption ]
           end ]).

  (* program store *)
  - right. intros E' HE'WF SplitWF HEE'match G'.
    exists (PLTT.PC (C1, PLTT.to_partial_stack d0 split,
                     Memory.set pmem C1
                                (Register.get r1 regs1)
                                (Register.get r2 regs1),
                     regs1, pc1+1)).
    split.
    (* step *)
    + destruct (PLTT.split_wellformed G' C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name)
        as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon with
        (s:=d) (cmem:=C1mem)
        (cmem':=Memory.local_update
                  (Register.get r1 regs1)
                  (Register.get r2 regs1) C1mem)
        (wmem':=M.add C1
                      (Memory.local_update
                         (Register.get r1 regs1)
                         (Register.get r2 regs1) C1mem)
                      mem1).
      * apply HC1mem.
      * apply M.add_1. reflexivity.
      * unfold G'. simpl.
        unfold PLTT.maps_match_on.
        intros. split; intro; apply HEE'match; assumption.
      * simpl. 
        unfold G in Hstep.
        rewrite H5 in H. inversion H.
        rewrite H2,H3,H4,H6,H7 in Hstep.
        unfold Memory.set in Hstep.
        rewrite H2 in HC1mem.
        rewrite (M.find_1 HC1mem) in Hstep.
        apply Hstep.
      * apply Hmem. assumption.
        rewrite H5 in H. inversion H.
        rewrite <- H2. assumption.
      * unfold Memory.set.
        rewrite H5 in H. inversion H.
        rewrite <- H4 in HC1mem.
        apply Hmem in HC1mem.
        rewrite H2 in HC1mem.
        rewrite (M.find_1 HC1mem).
        apply M.add_1.
        ** reflexivity.
        ** assumption.
    (* states match *)
    + apply program_control.
      * assumption.
      * reflexivity.
      * apply PLTT.update_related_memories with
          (C:=C1) (mem1:=mem1) (mem2:=pmem)
          (addr:=Register.get r1 regs1)
          (val:=Register.get r2 regs1);
          try assumption;
          reflexivity.

  (* program is calling *)
  - right.
    intros E' HE'WF SplitWF HEE'match G'.
    destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
      eexists; split.
    (* internal call - step *)
    + apply PLTT.Program_Internal_Call; auto.
    (* internal call - states match *)
    + unfold PLTT.maps_match_on in HEE'match.
      destruct (PLTT.split_wellformed G' C' HC'origin)
        as [CI HCI].
      destruct HCI as [CI_in_Is CI_name_is_C'].
      destruct (PLTT.entrypoints_exist
                  G' CI C' CI_in_Is CI_name_is_C')
        as [C'_in_E' [addrs C'_mapsto_E']].
      rewrite EntryPoint.get_works_locally with
        (E':=E') (addrs:=addrs).
      apply program_control;
        try auto.
      * simpl.
        apply Util.in_implies_mem_true in Hcontrol.
        rewrite Hcontrol.
        reflexivity.
      * apply HEE'match; auto.
      * auto.
    (* external call - step *)
    + apply PLTT.Program_External_Call; auto.
    (* external call - states match *)
    + apply context_control;
        try auto.
      * simpl.
        apply Util.in_implies_mem_true in Hcontrol.
        rewrite Hcontrol.
        reflexivity.

  (* program is returning *)
  - right.
    intros E' HE'WF SplitWF HEE'match G'.
    destruct (in_dec Nat.eq_dec C' split)
      as [ HC'origin | HC'origin ];
      eexists; split.
    (* internal return - step *)
    + apply PLTT.Program_Internal_Return;
        try auto.
      * simpl.
        apply Util.in_implies_mem_true in HC'origin.
        rewrite HC'origin. reflexivity.
    (* internal return - states match *)
    + apply program_control; auto.
    (* external return - step *)
    + apply PLTT.Program_External_Return;
        try auto.
      * simpl.
        apply Util.not_in_implies_mem_false in HC'origin.
        rewrite HC'origin. reflexivity.
    (* external return - states match *)
    + apply context_control; auto.

  (* context store *)
  - unfold PLTT.maps_match_on.
    intros C' C'mem HC'origin.
    split.
    + intro HC'map.
      apply Hmem.
      * auto.
      * destruct (M.find (elt:=list nat) C1 mem1) eqn:HC1find.
        ** unfold Memory.set in HC'map.
           rewrite HC1find in HC'map.
           apply M.add_3 in HC'map.
           *** assumption.
           *** unfold not. intros HeqC1C'.
               apply Hcontrol.
               rewrite <- HeqC1C' in HC'origin.
               apply HC'origin.
        ** unfold Memory.set in HC'map.
           rewrite HC1find in HC'map.
           assumption.
    + intro HC'map.
      assert (HneqC1C': C1 <> C').
      { intro HeqCC'. apply Hcontrol.
        rewrite <- HeqCC' in HC'origin. apply HC'origin. }
      unfold Memory.set.
      * destruct (M.find (elt:=list nat) C1 mem1) eqn:HC1find.
        ** assert (HC'mem: PLTT.M.MapsTo C' C'mem mem1).
           { apply Hmem; assumption. }
           eapply M.add_2; assumption.
        ** apply Hmem; auto.

  (* context call is calling *) 
  - right.
    destruct (in_dec Nat.eq_dec C' split)
      as [ HC'origin | ? ];
      intros E' HE'WF SplitWF HEE'match G'; eexists; split.
    (* external call - step *)
    + apply PLTT.Context_External_Call;
        try assumption.
      * apply PLTT.push_by_context_preserves_partial_stack.
        eassumption.
        reflexivity.
    (* external call - states match *)
    + unfold PLTT.maps_match_on in HEE'match.
      destruct (PLTT.split_wellformed G' C' HC'origin)
        as [CI HCI].
      destruct HCI as [CI_in_Is CI_name_is_C'].
      destruct (PLTT.entrypoints_exist
                  G' CI C' CI_in_Is CI_name_is_C')
        as [C'_in_E' [addrs C'_mapsto_E']].
      rewrite EntryPoint.get_works_locally with
        (E':=E') (addrs:=addrs).
      apply program_control;
        auto.
      * apply (HEE'match C' addrs);
          assumption.
      * assumption.

    (* internal call - step *)
    + apply PLTT.Context_Internal_Call;
        try assumption.
      * apply PLTT.push_by_context_preserves_partial_stack.
        eassumption.
        reflexivity.
    (* internal call - states match *)
    + apply context_control; auto.

  (* context is returning *)
  - right.
    destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
      intros E' HE'WF SplitWF HEE'match G'; eexists; split.
    (* external return - step*)
    + apply PLTT.Context_External_Return.
      * simpl. apply Util.in_implies_mem_true in HC'origin.
        rewrite HC'origin.
        reflexivity.
      * assumption.
    (* external return - states match *)
    + apply program_control; auto.

    (* internal return - step *)
    + apply PLTT.Context_Internal_Return.
      * intro HCeqC'. apply H3. symmetry. apply HCeqC'.
      * assumption.
      * apply PLTT.push_by_context_preserves_partial_stack; auto.
    (* internal return - states match *)
    + apply context_control;
        try assumption;
        reflexivity.
Qed.

End LTT_TO_PLTT.
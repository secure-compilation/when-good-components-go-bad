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
  forall split s C d mem regs pc s' ps Is E t,
    let G := LTT.mkGlobalEnv Is E in
    s = (C,d,mem,regs,pc) ->

    (* Global environment well-formedness *)
    (* - entrypoints exist for each declared component *)
    LTT.global_env_wf G ->

    (* Memory well-formedness *)
    (* - each declared component has its own memory *)
    memory_wf (LTT.get_interfaces G) mem ->

    (* Simulation premises *)
    match_states split s ps ->
    LTT.step G s t s' ->

    (* Simulation argument *)
    (t = E0 /\ match_states split s' ps)
    \/
    (forall E',
        (* Entrypoints preservation *)
        PLTT.maps_match_on split E E' ->
        (* Global environment well-formedness *)
        let G' := PLTT.mkGlobalEnv Is E' split in
        PLTT.global_env_wf G' ->
        (* Simulation step *)
        exists ps',
          PLTT.step G' ps t ps' /\ match_states split s' ps').
Proof.
  intros split s C d mem regs pc s' ps Is E t.
  intros G Hstate HGwf HmemWF Hstates_match Hstep.

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
         [ reflexivity
         | apply context_control;
           try assumption;
           try reflexivity;
           try apply Hmem]).

  (* program epsilon steps *)
  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name) as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H2 in H.
        inversion H.
        rewrite H3 in Hstep.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H2 in H.
        inversion H.
        rewrite <- H3. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H2 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H3. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name) as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H3 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H3 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H3 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name) as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H3 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H3 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H3 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name) as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H5 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H3 in Hstep.
        rewrite H4 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H5 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H5 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name) as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H5 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H4 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        rewrite H8 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H5 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H5 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  (* store *)
  - right. intros E' HE'WF G' HG'WF.
    exists (PLTT.PC (C1, PLTT.to_partial_stack d0 split,
                     Memory.set pmem C1
                                (Register.get r1 regs1)
                                (Register.get r2 regs1),
                     regs1, pc1+1)).
    split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
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
        intros. split; intro; apply HE'WF; assumption.
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

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name)
        as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H4 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H3 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H4 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H4 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name)
        as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H3 in H.
        inversion H.
        rewrite H2 in Hstep.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H3 in H.
        inversion H.
        rewrite <- H2. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H3 in H.
      inversion H.
      (* NOTE here we don't rewrite *)
      apply program_control.
      rewrite <- H2. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name)
        as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H3 in H.
        inversion H.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        rewrite H8 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H3 in H.
        inversion H.
        rewrite <- H4. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H3 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H4. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  - right.
    intros E' HE'WF G' HG'WF.
    eexists. split.
    (* step *)
    + destruct (PLTT.split_wellformed G' HG'WF C1 Hcontrol)
        as [C1I [C1_in_Is C1I_name]].
      destruct (HmemWF C1I C1 C1_in_Is C1I_name)
        as [C1mem HC1mem].
      eapply PLTT.Program_Epsilon.
      * apply HC1mem.
      * apply HC1mem.
      * simpl. unfold PLTT.maps_match_on.
        intros. split; intro; apply HE'WF; assumption.
      * simpl. rewrite H3 in H.
        inversion H.
        rewrite H4 in Hstep.
        rewrite H5 in Hstep.
        rewrite H6 in Hstep.
        rewrite H7 in Hstep.
        rewrite H8 in Hstep.
        eapply Hstep.
      * apply Hmem. assumption.
        rewrite H3 in H.
        inversion H.
        rewrite <- H4. assumption.
      * eassumption.
    (* states match *)
    + simpl. rewrite H3 in H.
      inversion H.
      rewrite <- H7.
      apply program_control.
      rewrite <- H4. assumption.
      reflexivity.
      simpl. unfold PLTT.maps_match_on.
      intros. split; intro; assumption.

  (* program is calling *)
  - right.
    intros E' HE'WF G' HG'WF.
    destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ].
    (* internal call *)
    + eexists. split.
      (* step *)
      * apply PLTT.Program_Internal_Call;
          try assumption;
          reflexivity.
      (* states match *)
      * unfold PLTT.maps_match_on in HE'WF.
        destruct
          (PLTT.split_wellformed G' HG'WF C' HC'origin)
          as [CI HCI].
        destruct HCI as [CI_in_Is CI_name_is_C'].
        destruct (PLTT.entrypoints_exist
                    G' HG'WF CI C' CI_in_Is CI_name_is_C')
          as [C'_in_E' [addrs C'_mapsto_E']].
        rewrite EntryPoint.get_works_locally with
          (E':=E') (addrs:=addrs).
        apply program_control;
          try assumption.
        ** simpl.
           apply Util.in_implies_mem_true in Hcontrol.
           rewrite Hcontrol.
           reflexivity.
        ** apply HE'WF. assumption. assumption.
        ** assumption.
    (* external call *)
    + eexists. split.
      (* step *)
      * apply PLTT.Program_External_Call;
          try assumption;
          reflexivity.
      (* states match *)
      * apply context_control.
        ** assumption.
        ** simpl.
           apply Util.in_implies_mem_true in Hcontrol.
           rewrite Hcontrol.
           reflexivity.
        ** assumption.

  (* program is returning *)
  - right.
    intros E' HE'WF G' HG'WF.
    destruct (in_dec Nat.eq_dec C' split)
      as [ HC'origin | HC'origin ].
    (* internal return *)
    + eexists. split.
      (* step *)
      * apply PLTT.Program_Internal_Return;
          try assumption.
        ** simpl.
           apply Util.in_implies_mem_true in HC'origin.
           rewrite HC'origin. reflexivity.
      (* states match *)
      * apply program_control;
          try assumption;
          reflexivity.
    (* external return *)
    + eexists. split.
      (* step *)
      * apply PLTT.Program_External_Return;
          try assumption.
          ** simpl.
             apply Util.not_in_implies_mem_false in HC'origin.
             rewrite HC'origin. reflexivity.
      (* states match *)
      * apply context_control;
          try assumption;
          reflexivity.

  (* context store *)
  - unfold PLTT.maps_match_on.
    intros C' C'mem HC'origin.
    split.
    + intro HC'map.
      apply Hmem.
      * assumption.
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
        ** apply Hmem; assumption.

  (* context call is calling *) 
  - right.
    destruct (in_dec Nat.eq_dec C' split)
      as [ HC'origin | ? ];
      intros E' HE'WF G' HG'WF; eexists; split.
    (* external call - step *)
    + apply PLTT.Context_External_Call;
        try assumption.
      * apply PLTT.push_by_context_preserves_partial_stack.
        eassumption.
        reflexivity.
    (* external call - states match *)
    + unfold PLTT.maps_match_on in HE'WF.
      destruct (PLTT.split_wellformed G' HG'WF C' HC'origin)
        as [CI HCI].
      destruct HCI as [CI_in_Is CI_name_is_C'].
      destruct (PLTT.entrypoints_exist
                  G' HG'WF CI C' CI_in_Is CI_name_is_C')
        as [C'_in_E' [addrs C'_mapsto_E']].
      rewrite EntryPoint.get_works_locally with
        (E':=E') (addrs:=addrs).
      apply program_control;
        try assumption;
        try reflexivity.
      * apply (HE'WF C' addrs);
          assumption.
      * assumption.

    (* internal call - step *)
    + apply PLTT.Context_Internal_Call;
        try assumption.
      * apply PLTT.push_by_context_preserves_partial_stack.
        eassumption.
        reflexivity.
    (* internal call - states match *)
    + apply context_control;
        try assumption;
        reflexivity.

  (* context is returning *)
  - right.
    destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
      intros E' HE'WF G' HG'WF; eexists; split.
    (* external return - step*)
    + apply PLTT.Context_External_Return.
      * simpl. apply Util.in_implies_mem_true in HC'origin.
        rewrite HC'origin.
        reflexivity.
      * assumption.
    (* external return - states match *)
    + apply program_control;
        try assumption;
        reflexivity.

    (* internal return - step *)
    + apply PLTT.Context_Internal_Return.
      * intro HCeqC'. apply H3. symmetry. apply HCeqC'.
      * assumption.
      * apply PLTT.push_by_context_preserves_partial_stack.
        ** assumption.
        ** reflexivity.
    (* internal return - states match *)
    + apply context_control;
        try assumption;
        reflexivity.
Qed.

End LTT_TO_PLTT.
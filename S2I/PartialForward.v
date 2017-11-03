Require Import Common.Definitions.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.
Require Import S2I.Compiler.
Require Import S2I.Definitions.

Section PartialForward.
  Variable prog: Source.program.
  Variable tprog: Intermediate.program.

  Variable ctx: Program.interface.

  Hypothesis input_program_well_formedness:
    Source.well_formed_program prog.

  Hypothesis input_program_closedness:
    Source.closed_program prog.

  Hypothesis context_validity:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (Source.prog_interface prog).

  Hypothesis successful_compilation:
    compile_program prog = Some tprog.

  (* we assume to have a forward simulation proved for whole programs
     in the complete semantics (I.CS simulates S.CS) *)

  Variable match_comp_mems: ComponentMemory.t -> ComponentMemory.t -> Prop.

  Definition match_mems (mem1 mem2: Memory.t) : Prop :=
    forall C Cmem Cmem',
      PMap.MapsTo C Cmem mem1 /\ PMap.MapsTo C Cmem' mem2 ->
      match_comp_mems Cmem Cmem'.

  Variable match_stack_frames: Component.id * value * cont -> Pointer.t -> Prop.

  Inductive match_stacks : list (Component.id * value * cont) -> list Pointer.t -> Prop :=
  | match_stacks_nil:
      match_stacks [] []
  | match_stacks_cons: forall s1 s2 sf1 sf2,
      match_stacks s1 s2 ->
      match_stack_frames sf1 sf2 ->
      match_stacks (sf1 :: s1) (sf2 :: s2).

  Variable index: Type.
  Variable order: index -> index -> Prop.

  Hypothesis well_founded_order: well_founded order.

  (* the matching relation is built on the previous definitions *)

  Variable match_states : index -> S.CS.state -> I.CS.state -> Prop.

  Hypothesis match_turn:
    forall i scs ics psi,
      match_states i scs ics  -> (turn_of ics psi <-> turn_of scs psi).

  Hypothesis match_executing_component:
    forall i gps mem1 regs pc C s mem2 k e,
      match_states i (C, s, mem2, k, e) (gps, mem1, regs, pc) ->
      Pointer.component pc = C.

  Hypothesis match_related_stacks:
    forall i gps mem1 regs pc C s mem2 k e,
      match_states i (C, s, mem2, k, e) (gps, mem1, regs, pc) ->
      match_stacks s gps.   

  Hypothesis match_memories:
    forall i gps mem1 regs pc C s mem2 k e,
      match_states i (C, s, mem2, k, e) (gps, mem1, regs, pc) ->
      match_mems mem1 mem2.

  (* TODO this is a first attempt, think more about it *)
  Hypothesis match_calls:
    forall i gps mem1 regs pc C s mem2 k v C' P,
      match_states i (C, s, mem1, Kcall C' P k, E_val (Int v)) (gps, mem2, regs, pc) ->
      GlobalEnv.executing (GlobalEnv.init_genv tprog) pc (ICall C' P).

  (* match_states is used to build the forward simulation *)

  Hypothesis match_initial_states:
    forall s1,
      initial_state (S.CS.sem prog) s1 ->
    exists i s2,
      initial_state (I.CS.sem tprog) s2 /\ match_states i s1 s2.

  Hypothesis match_final_states:
    forall i s1 s2 r,
      match_states i s1 s2 ->
      final_state (S.CS.sem prog) s1 r ->
      final_state (I.CS.sem tprog) s2 r.

  Hypothesis wp_simulation:
    forall s1 t s1',
      Step (S.CS.sem prog) s1 t s1' ->
    forall i s2,
      match_states i s1 s2 ->
    exists i', exists s2',
      (Plus (I.CS.sem tprog) s2 t s2' \/
       Star (I.CS.sem tprog) s2 t s2' /\ order i' i) /\ match_states i' s1' s2'.

  Theorem transl_program_correct:
    forward_simulation (S.CS.sem prog) (I.CS.sem tprog).
  Proof.
    eapply Forward_simulation.
    econstructor; eauto.
  Qed.

  (* global environments are built out of programs *)

  Let SG : Source.GlobalEnv.global_env := Source.GlobalEnv.init_genv prog.
  Let IG : Intermediate.GlobalEnv.global_env := Intermediate.GlobalEnv.init_genv tprog.

  (* we prove a forward simulation for partial programs *)
  (* we start by defining the relation between partial states *)

  Inductive match_stack_frames_p:
    Component.id * option (value * CS.cont) -> I.PS.PartialPointer.t -> Prop :=
  | match_stack_frames_without_holes: forall C b o v k,
      match_stack_frames (C, v, k) (C, b, o) ->
      match_stack_frames_p (C, Some (v, k)) (C, Some (b, o))
  | match_stack_frames_with_holes: forall C,
      match_stack_frames_p (C, None) (C, None).

  Inductive match_stacks_p:
    list (Component.id * option (value * CS.cont)) -> list I.PS.PartialPointer.t -> Prop :=
  | match_stacks_nil_p:
      match_stacks_p [] []
  | match_stacks_cons_p: forall s1 s2 sf1 sf2,
      match_stacks_p s1 s2 ->
      match_stack_frames_p sf1 sf2 ->
      match_stacks_p (sf1 :: s1) (sf2 :: s2).

  Inductive match_states_p: index -> S.PS.state -> I.PS.state -> Prop :=
  | match_states_program:
      forall i scs ics sps ips,
        match_states i scs ics ->
        S.PS.partial_state ctx scs (S.PS.PC sps) ->
        I.PS.partial_state ctx ics (I.PS.PC ips) ->
        match_states_p i (S.PS.PC sps) (I.PS.PC ips)
  | match_states_context:
      forall i sps ips C s1 s2 mem1 mem2,
        sps = S.PS.CC (C, s1, mem1) Normal ->
        ips = I.PS.CC (C, s2, mem2) Normal ->
        match_stacks_p s1 s2 ->
        match_mems mem1 mem2 ->
        match_states_p i sps ips.
 
  (* now we prove the forward simulation between partial semantics *)

  Lemma transl_initial_states:
    forall s1, S.PS.initial_state prog ctx s1 ->
    exists i s2, I.PS.initial_state tprog ctx s2 /\
            match_states_p i s1 s2.
  Proof.
  Admitted.

  Lemma transl_final_states:
    forall i (sps:S.PS.state) (ips:I.PS.state) (r:int),
      match_states_p i sps ips ->
      S.PS.final_state prog ctx sps r ->
      I.PS.final_state tprog ctx ips r.
  Proof.
  Admitted.

  (* this should be provable, although it might be quite technical *)
  Lemma aux:
    forall scs1 scs2 sps,
      S.PS.partial_state ctx scs1 (S.PS.PC sps) ->
      S.PS.partial_state ctx scs2 (S.PS.PC sps) ->
    forall scs1' sps',
      S.CS.kstep SG scs1 E0 scs1' ->
      S.PS.partial_state ctx scs1' (S.PS.PC sps') ->
    exists scs2',
      S.CS.kstep SG scs2 E0 scs2' /\
      S.PS.partial_state ctx scs2' (S.PS.PC sps').
  Proof. Admitted.

  Theorem decomp_star_E0:
    forall ics ics' ips,
      Star (I.CS.sem tprog) ics E0 ics' ->
      I.PS.partial_state ctx ics ips ->
    exists ips',
      Star (I.PS.sem tprog ctx) ips E0 ips' /\
      I.PS.partial_state ctx ics' ips'.
  Proof.
    intros.
    assert (H' := H).
    generalize dependent ips. induction H.
    - intro. exists ips. split.
      constructor. auto.
    - intros.
      destruct (lockstep_simulation tprog ctx s1 t1 s2 H ips H2) as [ips1 []].
      specialize (IHstar H0 ips1 H4).
      destruct IHstar as [ips' []].
      exists ips'. split.
      + eapply star_trans.
        * eapply star_step. apply H3.
          eapply star_refl. eauto.
        * apply H5.
        * rewrite E0_right. auto.
      + assumption.
  Qed.

  Theorem decomp_plus_E0:
    forall ics ics' ips,
      Plus (I.CS.sem tprog) ics E0 ics' -> I.PS.partial_state ctx ics ips ->
    exists ips',
      Plus (I.PS.sem tprog ctx) ips E0 ips' /\ I.PS.partial_state ctx ics' ips'.
  Proof.
    intros.
    inversion H; subst.
    symmetry in H3.
    destruct (Eapp_E0_inv t1 t2 H3); subst.
    destruct (lockstep_simulation tprog ctx ics E0 s2 H1 ips H0) as [ips1 []].
    destruct (decomp_star_E0 s2 ics' ips1 H2 H5) as [ips' []].
    exists ips'. split.
    - econstructor; eauto.
    - auto.
  Qed.

  Ltac simplify_turn :=
    unfold S.PS.is_program_component, S.PS.is_context_component in *;
    unfold I.PS.is_program_component, I.PS.is_context_component in *;
    unfold turn_of, S.PS.state_turn, I.PS.state_turn in *;
    simpl in *;
    auto.

  Theorem transl_step_correct:
    forall s1 t s1',
      S.PS.kstep ctx SG s1 t s1' ->
    forall i s2,
      match_states_p i s1 s2 ->
    exists i', exists s2',
      (Plus (I.PS.sem tprog ctx) s2 t s2' \/
       Star (I.PS.sem tprog ctx) s2 t s2' /\ order i' i) /\ match_states_p i' s1' s2'.
  Proof.
    intros s1 t s1' Hstep i s2 Hmatch.
    inversion Hstep
      as [ ? ? ? scs2 scs2' sps sps'
           ? ? ? Hsource_step
           Hscs2_partial Hscs2'_partial
         | ?|?|?|?|?|?|?|?|?]; subst.

    (** program has control **)

    (* epsilon *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch
             Hscs1_partial Hics_partial |]; subst; try discriminate.
      destruct (aux scs2 scs1 sps
                    Hscs2_partial Hscs1_partial
                    scs2' sps' Hsource_step Hscs2'_partial)
        as [scs1' [Hsource_step' Hmatch']].
      destruct (wp_simulation
                  scs1 E0 scs1' Hsource_step' i ics Hwmatch)
        as [i'' [ics' [Hinter_step Hwmatch']]].
      destruct ics' as [[[gps' mem'] regs'] pc'].
      destruct Hinter_step.
      + eapply decomp_plus_E0 in H; eauto.
        destruct H as [ips' []].
        eexists. exists ips'. split.
        * left. auto.
        * inversion H0; subst.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst.
             *** simplify_turn. 
                 apply match_executing_component in Hwmatch'.
                 destruct sps'. destruct p. destruct p. destruct p.
                 inversion H1; subst. inversion H5; subst.
                 contradiction.
             *** inversion H1; subst. inversion H5; subst.
      + destruct H.
        eapply decomp_star_E0 in H; eauto.
        destruct H as [ips' []].
        eexists i''. exists ips'. split.
        * right. split. eauto. eauto.
        * inversion H1; subst.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst.
             *** simplify_turn.
                 apply match_executing_component in Hwmatch'.
                 destruct sps'. destruct p. destruct p. destruct p.
                 inversion H2; subst. inversion H6; subst.
                 contradiction.
             *** inversion H2; subst. inversion H6; subst.

    (* internal call *)
    - admit.
    (* inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch
             Hscs1_partial Hics_partial |]; subst; try discriminate.
      inversion Hscs1_partial; subst. inversion H0; subst.
      inversion Hics_partial; subst. inversion H3; subst.
      eexists.

      (* TODO show the existence of the entrypoint for the called procedure *)

      (*exists (I.PS.PC (, pmem0, Intermediate.Register.invalidate regs, )*)
      (* TODO provide explicit resulting state *)
      eexists.
      split.
      + left. econstructor.
        * eapply I.PS.Program_Internal_Call.
          ** reflexivity.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
        * econstructor.
        * admit.
      + admit.
    *)

    (* internal return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch
             Hscs1_partial Hics_partial |]; subst; try discriminate.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Program_Internal_Return.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
        * econstructor.
        * admit.
      + admit.

    (* external call *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch
             Hscs1_partial Hics_partial |]; subst; try discriminate.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Program_External_Call.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
        * admit.
        * admit.
      + admit.

    (* external return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch
             Hscs1_partial Hics_partial |]; subst; try discriminate.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Program_External_Return.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
        * econstructor.
        * admit.
      + admit.

    (** context has control **)

    (* epsilon *)
    - inversion Hmatch; subst. inversion H; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Epsilon; auto.
        * econstructor.
        * auto.
      + econstructor; auto.

    (* internal call *)
    - inversion Hmatch; subst. inversion H; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Call; auto.
          ** simplify_turn. apply H3.
          ** assumption.
          ** eassumption.
        * econstructor.
        * rewrite E0_right. eauto.
      + econstructor; auto.
        * constructor; eauto.
          constructor.

    (* internal return *)
    - inversion Hmatch; subst. inversion H; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Return; auto.
          ** simplify_turn. apply H3.
          ** assumption.
          ** admit.
        * econstructor.
        * reflexivity.
      + admit.

    (* external calls/returns depend on the match_states relation *)

    (* external call *)
    - inversion Hmatch; subst. inversion H; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Call; auto.
          ** simplify_turn. apply H3.
          ** apply H4.
          ** admit.
          ** admit.
        * econstructor.
        * reflexivity.
      + econstructor.
        * admit.
        * admit.
        * admit.

    (* external return *)
    - inversion Hmatch; subst. inversion H; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Return; auto.
          ** simplify_turn. apply H3.
          ** admit.
          ** admit.
        * econstructor.
        * reflexivity.
      + econstructor.
        * admit.
        * admit.
        * admit.
  Admitted.

  (* I simulates S, L1=I.PS.sem L2=S.PS.sem *)
  Theorem transl_program_correct_p:
    forward_simulation (S.PS.sem prog ctx) (I.PS.sem tprog ctx).
  Proof.
    eapply Forward_simulation.
    econstructor.
    - eauto.
    - apply transl_initial_states.
    - apply transl_final_states.
    - apply transl_step_correct.
  Qed.

  Corollary behavior_refinement_p:
    forall beh1, program_behaves (S.PS.sem prog ctx) beh1 ->
    exists beh2, program_behaves (I.PS.sem tprog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply transl_program_correct_p.
  Qed.
End PartialForward.
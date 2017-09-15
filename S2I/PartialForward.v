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

  Hypothesis simulation:
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

  (* we assume to have a forward simulation from intermediate whole program to 
     intermediate partial programs. This is what we usually call decomposition step *)

  Hypothesis decomp_step_correct:
    forall ics t ics',
      I.CS.step IG ics t ics' ->
    forall ips,
      I.PS.partial_state ctx ics ips ->
    exists ips',
      I.PS.step ctx IG ips t ips' /\ I.PS.partial_state ctx ics' ips'.

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
      destruct (decomp_step_correct s1 t1 s2 H ips H2) as [ips1 []].
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
    destruct (decomp_step_correct ics E0 s2 H1 ips H0) as [ips1 []].
    destruct (decomp_star_E0 s2 ics' ips1 H2 H5) as [ips' []].
    exists ips'. split.
    - econstructor; eauto.
    - auto.
  Qed. 

  Hypothesis decomp_initial_states:
    forall ics,
      I.CS.initial_state tprog ics ->
    exists ips,
      I.PS.initial_state tprog ctx ips /\ I.PS.partial_state ctx ics ips.

  Hypothesis decomp_final_states:
    forall ics ips r,
      I.PS.partial_state ctx ics ips ->
      I.CS.final_state IG ics r ->
      I.PS.final_state tprog ctx ips r.

  Theorem decomposition:
    forward_simulation (I.CS.sem tprog) (I.PS.sem tprog ctx).
  Proof.
    eapply forward_simulation_step; eauto.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1, program_behaves (I.CS.sem tprog) beh1 ->
    exists beh2, program_behaves (I.PS.sem tprog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.

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
      forall i C1 C2 s1 s2 mem1 mem2 exec_st1 exec_st2,
        C1 = C2 ->
        match_stacks_p s1 s2 ->
        match_mems mem1 mem2 ->
        exec_st1 = exec_st2 ->
        match_states_p i (S.PS.CC (C1, s1, mem1) exec_st1)
                         (I.PS.CC (C2, s2, mem2) exec_st2).
 
  (* now we prove the forwad simulation between partial semantics *)

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
      as [ scs2 scs2' sps sps'
           Hscs2_partial Hsource_step
           Hscs2'_partial
         | ?|?|?|?|?|?|?|?|?|?]; subst;
    inversion Hmatch
      as [ i' scs1 ics ? ips Hwmatch
           Hscs1_partial Hics_partial |]; subst.

    (** program has control **)

    (* epsilon *)
    - destruct (aux scs2 scs1 sps
                    Hscs2_partial Hscs1_partial
                    scs2' sps' Hsource_step Hscs2'_partial)
        as [scs1' [Hsource_step' Hmatch']].
      destruct (simulation
                  scs1 E0 scs1' Hsource_step' i ics Hwmatch)
        as [i'' [ics' [Hinter_step Hwmatch']]].
      destruct ics' as [[[gps' mem'] regs'] pc'].
      destruct Hinter_step.
      + eapply decomp_plus_E0 in H; eauto.
        destruct H as [ips' []].
        eexists. exists ips'. split.
        * left. auto.
        * inversion H0; subst; subst ps.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst ps; subst.
             unfold I.PS.is_context_component, turn_of, I.PS.state_turn in *.
             unfold S.PS.is_program_component, S.PS.is_context_component in *.
             unfold turn_of, S.PS.state_turn in *.
             apply match_executing_component in Hwmatch'.
             rewrite Hwmatch' in H6. contradiction.
          ** (* contra *)
             inversion Hmatch'; subst ps; subst.
             unfold I.PS.is_context_component, turn_of, I.PS.state_turn in *.
             unfold S.PS.is_program_component, S.PS.is_context_component in *.
             unfold turn_of, S.PS.state_turn in *.
             apply match_executing_component in Hwmatch'.
             rewrite Hwmatch' in H6. contradiction.
      + destruct H.
        eapply decomp_star_E0 in H; eauto.
        destruct H as [ips' []].
        eexists i''. exists ips'. split.
        * right. split. eauto. eauto.
        * inversion H1; subst; subst ps.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst ps; subst.
             unfold I.PS.is_context_component, turn_of, I.PS.state_turn in *.
             unfold S.PS.is_program_component, S.PS.is_context_component in *.
             unfold turn_of, S.PS.state_turn in *.
             apply match_executing_component in Hwmatch'.
             rewrite Hwmatch' in H7. contradiction.
          ** (* contra *)
             inversion Hmatch'; subst ps; subst.
             unfold I.PS.is_context_component, turn_of, I.PS.state_turn in *.
             unfold S.PS.is_program_component, S.PS.is_context_component in *.
             unfold turn_of, S.PS.state_turn in *.
             apply match_executing_component in Hwmatch'.
             rewrite Hwmatch' in H7. contradiction.

    (* internal call *)
    - eexists. eexists. split.
      + left. econstructor.
        * inversion Hics_partial; subst.
          eapply I.PS.Program_Internal_Call; eauto.
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

    (* internal return *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Program_Internal_Return; eauto.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
          ** admit.
        * econstructor.
        * admit.
      + admit.

    (* external call *)
    - eexists.
      destruct ips as [[[gps_ mem_] regs_] pc_].
      exists (I.PS.CC (C', (Pointer.component pc_,
                       Some (Pointer.block pc_, Pointer.offset (Pointer.inc pc_))) :: gps_,
                  PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem_) Normal).
      split.
      + left. econstructor.
        * unfold step. simpl.
          eapply I.PS.Program_External_Call;
            inversion Hscs1_partial; subst;
            inversion Hics_partial; subst.
          (* we executing a call instruction *)
          ** eapply match_calls; eauto.
          (* we are not calling ourself *)
          ** admit.
          (* we are calling an imported procedure *)
          ** admit.
          (* we are calling the context *)
          ** subst ps4.
             unfold I.PS.is_program_component, I.PS.is_context_component in *.
             unfold turn_of, I.PS.state_turn in *.
             (* something is wrong, redo with correct existential instances*)
             admit.
          ** (* the stack changes *) admit.
          ** (* the call argument is in R_COM *) admit.
          ** admit.
          ** admit.
          ** admit.
        * admit.
        * admit.
      + admit.

    (* external return *)
    - eexists.
      destruct ips as [[[gps_ mem_] regs_] pc_].
      eexists.
      split.
      + left. econstructor.
        * admit.
        * econstructor.
        * admit.
      + admit.

    (** context has control **)

    (* epsilon *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Epsilon; eauto.
        * econstructor.
        * auto.
      + econstructor; auto.

    (* goes wrong *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_GoesWrong; eauto.
        * econstructor.
        * auto.
      + econstructor; auto.

    (* internal call *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Call; eauto.
          ** auto.
        * econstructor.
        * subst t0. rewrite E0_right. eauto.
      + econstructor; auto.
        * constructor; auto.
          constructor.

    (* internal return *)
    - inversion H2; subst.
      eexists. exists (I.PS.CC (C', s2, mem2) Normal). split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Return; eauto.
          ** auto.
          ** inversion H7. subst. reflexivity.
        * econstructor.
        * subst t0. simpl. auto.
      + econstructor; eauto.

    (* external calls/returns depend on the match_states relation *)

    (* external call *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Call; eauto.
          ** auto.
          ** (* the call argument that is in RCOM is the same argument I used 
                in the source call *)
            admit.
          ** (* the entrypoint I'm jumping to corresponds to the procedure
                I was calling at the source *)
            admit.
        * econstructor.
        * subst t0. reflexivity.
      + econstructor.
        * admit.
        * admit.
        * admit.

    (* external return *)
    - eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Return; eauto.
          (* we are returning to the program *)
          ** unfold I.PS.is_program_component, I.PS.is_context_component.
             unfold S.PS.is_program_component, S.PS.is_context_component in *.
             simpl in *. eapply H.
          ** (* the call return value that is in RCOM is the same return value of 
                the source call *)
            admit.
          ** (* the stack changes as at the source *)
            inversion H3; subst.
            inversion H8; subst. admit.
        * econstructor.
        * subst t0. reflexivity.
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
(* EXPERIMENT, might be useful in the future
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

 Hypothesis successful_compilation:
    compile_program prog = Some tprog.

  Hypothesis context_validity:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (Source.prog_interface prog).

  (* reasonable assumption, the context interface is preserved during compilation *)
  Hypothesis target_context_validity:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (Intermediate.prog_interface tprog). 

  (* we assume to have a forward simulation proved for whole programs
     in the complete semantics (I.CS simulates S.CS) *)

  Variable match_comp_mems: ComponentMemory.t -> ComponentMemory.t -> Prop.

  Definition match_mems (mem1 mem2: Memory.t) : Prop :=
    forall C Cmem Cmem',
      PMap.MapsTo C Cmem mem1 /\ PMap.MapsTo C Cmem' mem2 ->
      match_comp_mems Cmem Cmem'.

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

  Hypothesis match_memories:
    forall i gps mem1 regs pc C s mem2 k e,
      match_states i (C, s, mem2, k, e) (gps, mem1, regs, pc) ->
      match_mems mem1 mem2.

  Hypothesis match_calls:
    forall i gps mem1 regs pc C s mem2 k v C' P,
      match_states i (C, s, mem1, Kcall C' P k, E_val (Int v)) (gps, mem2, regs, pc) ->
      GlobalEnv.executing (GlobalEnv.init_genv tprog) pc (ICall C' P).

  Hypothesis match_call_argument:
    forall i gps mem1 regs pc C s mem2 k v C' P,
      match_states i (C, s, mem1, Kcall C' P k, E_val (Int v)) (gps, mem2, regs, pc) ->
      Intermediate.Register.get R_COM regs = Int v.

  (* match_states is used to build the forward simulation *)

  Hypothesis match_initial_states:
    forall s1,
      initial_state (S.CS.sem prog) s1 ->
    exists i s2,
      initial_state (I.CS.sem tprog) s2 /\ match_states i s1 s2.

  Hypothesis match_final_states:
    forall i s1 s2,
      match_states i s1 s2 ->
      final_state (S.CS.sem prog) s1 ->
      final_state (I.CS.sem tprog) s2.

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

  Hypothesis match_procedure_entrypoint:
    forall C C_procs P P_expr,
      PMap.find C (genv_procedures SG) = Some C_procs ->
      PMap.find P C_procs = Some P_expr ->
    exists b,
      Intermediate.EntryPoint.get C P (Intermediate.GlobalEnv.genv_entrypoints IG) = Some b.

  Hypothesis global_environments_same_interface:
    Intermediate.GlobalEnv.genv_interface IG = Source.GlobalEnv.genv_interface SG.

  (* we prove a forward simulation for partial programs *)
  (* we start by defining the relation between partial states *)

  Inductive match_states_p: index -> S.PS.state -> I.PS.state -> Prop :=
  | match_states_partial:
      forall i scs ics sps ips,
        match_states i scs ics ->
        S.PS.partial_state ctx scs sps ->
        I.PS.partial_state ctx ics ips ->
        match_states_p i sps ips.

  (* now we prove the forward simulation between partial semantics *)

  Lemma transl_initial_states:
    forall s1,
      S.PS.initial_state prog ctx s1 ->
    exists i s2,
      I.PS.initial_state tprog ctx s2 /\ match_states_p i s1 s2.
  Proof.
    intros s1 Hs1_init.

    inversion Hs1_init; subst.
    destruct (match_initial_states scs H0) as [i [ics [Hics_init Hmatch]]].
    destruct ics as [[[gps mem] regs] pc].
    exists i.

    (* case analysis on who has control *)
    inversion H; subst.

    (* program has control *)
    - simplify_turn.
      exists (I.PS.PC (I.PS.to_partial_stack gps (map fst (PMap.elements ctx)),
                       PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem,
                       regs, pc)).
      split.
      + econstructor.
        * econstructor; auto.
          ** simplify_turn.
             erewrite match_executing_component; eauto.
          ** apply PMapFacts.Equal_refl.
        * auto.
      + econstructor.
        * eauto.
        * eauto.
        * econstructor; auto.
          ** simplify_turn.
             erewrite match_executing_component; eauto.
          ** apply PMapFacts.Equal_refl.

    (* context has control *)
    - simplify_turn.
      exists (I.PS.CC (Pointer.component pc,
                       I.PS.to_partial_stack gps (map fst (PMap.elements ctx)),
                       PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) Normal).
      split.
      + econstructor.
        * eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             erewrite match_executing_component; eauto.
          ** apply PMapFacts.Equal_refl.
        * eauto.
      + econstructor.
        * eauto.
        * eauto.
        * eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             erewrite match_executing_component; eauto.
          ** apply PMapFacts.Equal_refl.
  Qed.

  Lemma transl_final_states:
    forall i (sps:S.PS.state) (ips:I.PS.state),
      match_states_p i sps ips ->
      S.PS.final_state prog ctx sps ->
      I.PS.final_state tprog ctx ips.
  Proof.
    intros i sps ips Hmatch Hsps_final.

    inversion Hmatch
      as [ i' scs1 ics ? ips' Hwmatch Hscs1_partial Hics_partial ]; subst.

    (* case analysis on who has control *)
    inversion Hsps_final; subst.

    (* program has control *)
    - inversion Hscs1_partial; subst; simplify_turn; try contradiction.
      inversion Hics_partial; subst; simplify_turn.
      + eapply I.PS.final_state_program.
        * simplify_turn. auto.
        * eauto.
        * eapply match_final_states; eauto.
          ** unfold S.CS.final_state in H1.
             S.CS.unfold_state.
             destruct H1.
             *** inversion H6; subst.
                 inversion H7; subst.
                 econstructor; auto.
             *** inversion H0; subst; try discriminate.
                 inversion H6; subst.
                 inversion H7; subst.
                 unfold S.CS.final_state. right.
                 destruct H1 as [? [? []]].
                 eexists x. repeat split; eauto.
                 subst. simpl in H12.
                 destruct gps; try discriminate; auto.
      + erewrite match_executing_component with (C:=C) in H2; eauto.
        contradiction.

    (* context has control *)
    - inversion Hscs1_partial; subst; simplify_turn; try contradiction.
      inversion Hics_partial; subst; simplify_turn.
      + erewrite match_executing_component with (C:=C) in H0; eauto.
        contradiction.
      + eapply I.PS.final_state_context.
        * simplify_turn. auto.
  Qed.

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
  Proof.
    intros scs1 scs2 sps.
    intros Hscs1_partial Hscs2_partial.
    intros scs1' sps'.
    intros Hsc_step Hscs1'_partial.
  Admitted.

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
      destruct (lockstep_simulation tprog ctx s1 t1 s2 H ips H2)
        as [ips1 []].
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
    destruct (lockstep_simulation tprog ctx ics E0 s2 H1 ips H0)
      as [ips1 []].
    destruct (decomp_star_E0 s2 ics' ips1 H2 H5) as [ips' []].
    exists ips'. split.
    - econstructor; eauto.
    - auto.
  Qed.

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
    inversion Hstep as [ sps t' sps' scs scs' ]; subst.
    inversion Hmatch as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.

    (*

    destruct s1; subst;
    destruct s1'; subst;
    destruct t; subst.

    (* program epsilon steps *)
    - destruct (aux scs scs1 p H0 Hscs1_partial scs' p0 H H1)
        as [scs1' [Hsource_step' Hmatch']].
      destruct (wp_simulation
                  scs1 E0 scs1' Hsource_step' i ics Hwmatch)
        as [i'' [ics' [Hinter_step Hwmatch']]].
      destruct ics' as [[[gps' mem'] regs'] pc'].
      destruct Hinter_step.
      + eapply decomp_plus_E0 in H2; eauto.
        destruct H2 as [ips' []].
        eexists. exists ips'. split.
        * left. auto.
        * inversion H3; subst.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst.
             *** simplify_turn. 
                 apply match_executing_component in Hwmatch'.
                 repeat destruct p0.
                 inversion H8; subst. inversion H4; subst.
                 contradiction.
             *** inversion H8; subst.
      + destruct H2.
        eapply decomp_star_E0 in H2; eauto.
        destruct H2 as [ips' []].
        eexists i''. exists ips'. split.
        * right. split. eauto. eauto.
        * inversion H4; subst.
          ** econstructor; eauto.
          ** (* contra *)
             inversion Hmatch'; subst.
             *** simplify_turn.
                 apply match_executing_component in Hwmatch'.
                 repeat destruct p0.
                 inversion H9; subst. inversion H5; subst.
                 contradiction.
             *** inversion H9; subst.

    (* program call & ret *)
    - admit.

    (* contra *)
    - admit.

    (* contra *)
    - admit.

    (* contra *)
    - admit.

    (* contra *)
    - admit.
      
    (** program has control **)

    (* epsilon *)
    - destruct (aux scs2 scs1 sps
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
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst. 
      inversion Hscs1_partial; subst; try discriminate. inversion H0; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion Hics_partial; subst; try discriminate. inversion H13; subst.
      (* show the existence of the entrypoint for the called procedure *)
      destruct (match_procedure_entrypoint C' C'_procs P P_expr H8 H9)
        as [entrypoint Hentrypoint].
      eexists.
      exists (I.PS.PC ((Pointer.component pc,
                   Some (Pointer.block pc, Pointer.offset (Pointer.inc pc))) ::
                  I.PS.to_partial_stack gps0 (map fst (PMap.elements ctx)),
                  pmem0, Intermediate.Register.invalidate regs, (C', entrypoint, 0))).
      split.
      + left. econstructor.
        * eapply I.PS.Program_Internal_Call; auto.
          ** eapply match_calls. eauto.
          ** simplify_turn.
          ** erewrite match_executing_component; eassumption.
          ** erewrite match_executing_component.
             simpl. subst IG.
             rewrite global_environments_same_interface.
             eassumption. eauto.
          ** eapply match_call_argument. eauto.
          ** apply Hentrypoint.
        * econstructor.
        * erewrite match_executing_component. reflexivity.
          eauto.
      + admit.
       (* STUCK, have to prove that the next complete states are related *)

    (* internal return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      eexists.
      (* TODO don't use existential exists *)
      eexists. split.
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
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst; try discriminate. inversion H0; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion Hics_partial; subst; try discriminate. inversion H9; subst.
      eexists.
      exists (I.PS.CC (C',
                  (Pointer.component pc,
                   Some (Pointer.block pc, Pointer.offset (Pointer.inc pc))) ::
                  I.PS.to_partial_stack gps0 (map fst (PMap.elements ctx)),
                  pmem0) Normal).
      split.
      + left. econstructor.
        * eapply I.PS.Program_External_Call; auto.
          ** eapply match_calls. eauto.
          ** simplify_turn.
          ** erewrite match_executing_component.
             simpl. subst IG.
             rewrite global_environments_same_interface.
             eassumption. eauto.
          ** eapply match_call_argument. eauto.
        * econstructor.
        * erewrite match_executing_component. reflexivity.
          eauto.
      + admit.

    (* external return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst; try discriminate. inversion H0; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion Hics_partial; subst; try discriminate. inversion H7; subst.
      admit.
      (*
      apply match_related_stacks in Hwmatch.
      inversion Hwmatch; subst.
      + (* contra *)
        simpl in *. discriminate.
      + simpl in *.
        inversion H4; subst.
        eexists. eexists. split.
        * left. econstructor.
          ** eapply I.PS.Program_External_Return.
             *** eauto.
             *** eauto.
             *** reflexivity.
             *** admit.
             *** simplify_turn.
             *** simplify_turn. eassumption.
             *** admit.
             *** admit.
          ** econstructor.
          ** admit.
        * admit.
        *)

    (** context has control **)

    (* epsilon *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion H0. subst.
      inversion Hics_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Epsilon; auto.
        * econstructor.
        * auto.
      + econstructor; eauto.

    (* internal call *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion H0. subst.
      inversion Hics_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Call; auto.
          ** simplify_turn. apply H3.
          ** admit. (* assumption. *)
          ** admit. (*assumption. *)
        * econstructor.
        * rewrite E0_right. admit. (*eauto.*)
      + admit.

    (* internal return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion H0. subst.
      inversion Hics_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_Internal_Return; auto.
          ** simplify_turn. apply H3.
          ** admit. (*assumption.*)
          ** admit.
        * econstructor.
        * admit. (*reflexivity.*)
      + admit.

    (* external calls/returns depend on the match_states relation *)

    (* external call *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion H0. subst.
      inversion Hics_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      destruct (match_procedure_entrypoint C' C'_procs P P_expr H5 H6)
        as [entrypoint Hentrypoint].
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Call; auto.
          ** simplify_turn. apply H3.
          ** admit. (* apply H4. *)
          ** eapply match_call_argument. eauto. admit.
          ** subst IG. simpl. eassumption.
        * econstructor.
        * admit. (*reflexivity.*)
      + admit.
        (* STUCK, have to prove that the next complete states are related *)

    (* external return *)
    - inversion Hmatch
        as [ i' scs1 ics ? ips Hwmatch Hscs1_partial Hics_partial ]; subst.
      inversion Hscs1_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      inversion H0. subst.
      inversion Hics_partial; subst.
      destruct Hmatch_aux as [[? [? []]] | [? [? []]]]; try discriminate; subst.
      eexists. eexists. split.
      + left. econstructor.
        * eapply I.PS.Context_External_Return; auto.
          ** simplify_turn. apply H3.
          ** eapply match_call_argument. eauto. admit.
          ** admit.
        * econstructor.
        * admit. (*reflexivity.*)
      + admit.
        (* STUCK, have to prove that the next complete states are related *)
     *)
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
*)

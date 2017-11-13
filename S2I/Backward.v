(***
 * OLD look at PartialForward.v
 * First attempt at building a backward simulation for partial semantics by reusing
 * a backward simulation for complete semantics. 
 *)

Require Import Common.Definitions.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
(* Require Import CompCert.Behaviors. *)
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import S2I.Compiler.
Require Import S2I.Definitions.

Variable prog: Source.program.
Variable tprog: Intermediate.program.

Hypothesis input_program_well_formedness:
  Source.well_formed_program prog.

Hypothesis input_program_closedness:
  Source.closed_program prog.

Hypothesis successful_compilation:
  compile_program prog = Some tprog.

Module Cbs.
  Axiom match_comp_mems: ComponentMemory.t -> ComponentMemory.t -> Prop.

  Definition match_mems (mem1 mem2: Memory.t) : Prop :=
    forall C Cmem Cmem',
      PMap.MapsTo C Cmem mem1 /\ PMap.MapsTo C Cmem' mem2 ->
      match_comp_mems Cmem Cmem'.

  Axiom match_stack_frames: Pointer.t -> Component.id * value * cont -> Prop.

  Inductive match_stacks : list Pointer.t -> list (Component.id * value * cont) -> Prop :=
  | match_stacks_nil:
      match_stacks [] []
  | match_stacks_cons: forall s1 s2 sf1 sf2,
      match_stacks s1 s2 ->
      match_stack_frames sf1 sf2 ->
      match_stacks (sf1 :: s1) (sf2 :: s2).

  (* intuition: match_states will be defined with the previous match axioms *)
  Axiom match_states: I.CS.state -> S.CS.state -> Prop.

  (* match relation respects turns *)
  Axiom match_turn:
    forall ics scs psi,
    match_states ics scs -> (turn_of ics psi <-> turn_of scs psi).

  Axiom match_executing_component:
    forall gps mem1 regs pc C s mem2 k e,
      match_states (gps, mem1, regs, pc) (C, s, mem2, k, e) ->
      Pointer.component pc = C.

  Axiom match_related_stacks:
    forall gps mem1 regs pc C s mem2 k e,
      match_states (gps, mem1, regs, pc) (C, s, mem2, k, e) ->
      match_stacks gps s.   

  Axiom match_memories:
    forall gps mem1 regs pc C s mem2 k e,
      match_states (gps, mem1, regs, pc) (C, s, mem2, k, e) ->
      match_mems mem1 mem2.

  Axiom match_initial_states:
    forall s1, initial_state (I.CS.sem tprog) s1 ->
    exists s2, initial_state (S.CS.sem prog) s2 /\ match_states s1 s2.

  Axiom match_final_states:
    forall s1 s2 r,
      match_states s1 s2 ->
      final_state (I.CS.sem tprog) s1 r ->
      final_state (S.CS.sem prog) s2 r.

  Axiom simulation:
    forall s1 t s1', Step (I.CS.sem tprog) s1 t s1' ->
    forall s2, match_states s1 s2 ->
    exists s2', Step (S.CS.sem prog) s2 t s2' /\ match_states s1' s2'.

  Theorem transl_program_correct:
    forward_simulation (I.CS.sem tprog) (S.CS.sem prog).
  Proof.
    eapply forward_simulation_step.
    eexact match_initial_states.
    eexact match_final_states.
    eexact simulation.
  Qed.
End Cbs.

Module Pbs.
Variable ctx: Program.interface.

Inductive match_stack_frames:
  I.PS.PartialPointer.t -> Component.id * option (value * CS.cont) -> Prop :=
| match_stack_frames_without_holes: forall C b o v k,
    Cbs.match_stack_frames (C, b, o) (C, v, k) ->
    match_stack_frames (C, Some (b, o)) (C, Some (v, k))
| match_stack_frames_with_holes: forall C,
    match_stack_frames (C, None) (C, None).

Inductive match_stacks:
  list I.PS.PartialPointer.t -> list (Component.id * option (value * CS.cont)) -> Prop :=
| match_stacks_nil:
    match_stacks [] []
| match_stacks_cons: forall s1 s2 sf1 sf2,
    match_stacks s1 s2 ->
    match_stack_frames sf1 sf2 ->
    match_stacks (sf1 :: s1) (sf2 :: s2).

Inductive match_states: I.PS.state -> S.PS.state -> Prop :=
| match_states_program:
    forall ics scs ips sps,
      Cbs.match_states ics scs ->
      S.PS.partial_state ctx scs (S.PS.PC sps) ->
      I.PS.partial_state ctx ics (I.PS.PC ips) ->
      match_states (I.PS.PC ips) (S.PS.PC sps)
| match_states_context:
    forall C1 C2 s1 s2 mem1 mem2 exec_st1 exec_st2,
      C1 = C2 ->
      match_stacks s1 s2 ->
      Cbs.match_mems mem1 mem2 ->
      exec_st1 = exec_st2 ->
      match_states (I.PS.CC (C1, s1, mem1) exec_st1)
                   (S.PS.CC (C2, s2, mem2) exec_st2).

Lemma eval_kstep_nostep:
  forall G s,
    S.CS.eval_kstep G s = None ->
    nostep S.CS.kstep G s.
Proof.
  unfold nostep, not.
  intros G s Hnostep t s' Hstep.
  apply S.CS.eval_kstep_correct in Hstep.
  rewrite Hnostep in Hstep.
  discriminate.
Qed.

Lemma S2I_turn_preservation:
  forall ips sps,
    match_states ips sps ->
    (turn_of ips ctx <-> turn_of sps ctx).
Proof.
  intros ips sps Hmatch.
  inversion Hmatch; subst.
  (* program *)
  - split; intro Hturn.
    + (* bottom-up *)
      eapply I.PS.partial_state_preserves_turn_of in Hturn; eauto;
      eapply Cbs.match_turn in Hturn; eauto;
      eapply S.PS.partial_state_preserves_turn_of in Hturn; eauto.
    + (* top-down *)
      eapply S.PS.partial_state_preserves_turn_of in Hturn; eauto;
      eapply Cbs.match_turn in Hturn; eauto;
      eapply I.PS.partial_state_preserves_turn_of in Hturn; eauto.
  (* context *)
  - split; intro Hturn; auto.
Qed.

Lemma transl_initial_states:
  forall s1, I.PS.initial_state tprog ctx s1 ->
  exists s2, S.PS.initial_state prog ctx s2 /\ match_states s1 s2.
Proof.
  intros s1 Hs1_init.
  inversion Hs1_init as [cs1 ps1 Hpartial Hcs1_init]. subst.
  destruct (Cbs.match_initial_states cs1 Hcs1_init) as [cs2 [Hcs2_init Hmatch]].
  destruct cs2 as [[[[C gps] mem] k] e].
  (* case analysis on who has control *)
  destruct (PMap.mem C ctx) eqn:Hexec_comp.
  - (* context has control *)
    inversion Hpartial; subst; subst ps.
    (* contra *)
    + exfalso.
      unfold I.PS.is_program_component, I.PS.is_context_component in H.
      apply H.
      apply (Cbs.match_turn (gps0, mem0, regs, pc) (C, gps, mem, k, e) ctx Hmatch).
      unfold turn_of, S.CS.state_turn.
      apply PMapFacts.mem_in_iff in Hexec_comp.
      auto.
    (* normal execution *)
    + eexists. split.
      (* intial state *)
      * eapply S.PS.initial_state_intro.
        ** apply S.PS.ContextControl_Normal.
           *** apply PMapFacts.mem_in_iff; eauto.
           *** apply PMapFacts.Equal_refl.
        ** apply Hcs2_init.
      (* matching states *)
      * eapply match_states_context.
        ** eapply Cbs.match_executing_component; eauto.
        ** (* provable but probably quite technical *) admit.
(*           induction (Cbs.match_related_stacks gps0 mem0 regs pc C gps mem k e Hmatch).
           *** constructor.
           *** unfold I.PS.to_partial_stack, S.PS.to_partial_stack.
               simpl. constructor.
               apply IHm; auto.
               **** eapply I.PS.initial_state_intro.
                    eapply I.PS.ContextControl_Normal.
                    ***** auto.
                    ***** eauto.
                    ***** admit.
               **** admit.
               **** admit. 
               *)
        ** (* provable but probably quite technical *) admit.
        ** auto.
    (* went wrong state *)
    + eexists. split.
      (* intial state *)
      * eapply S.PS.initial_state_intro.
        ** apply S.PS.ContextControl_WentWrong.
           *** apply PMapFacts.mem_in_iff; eauto.
           *** apply PMapFacts.Equal_refl.
        ** apply Hcs2_init.
      (* matching states *)
      * eapply match_states_context.
        ** eapply Cbs.match_executing_component; eauto.
        ** (* provable but probably quite technical *) admit.
        ** (* provable but probably quite technical *) admit.
        ** auto.
  - (* program has control *)
    inversion Hpartial; subst;
      try (exfalso;
           unfold I.PS.is_context_component in H;
           eapply (Cbs.match_turn _ _ _ Hmatch) in H;
           unfold turn_of, S.CS.state_turn in H;
           apply PMapFacts.not_mem_in_iff in Hexec_comp;
           contradiction).
    + eexists. split.
      (* initial state *)
      * eapply S.PS.initial_state_intro.
        ** constructor.
           *** apply PMapFacts.not_mem_in_iff; eauto.
           *** apply PMapFacts.Equal_refl.
        ** apply Hcs2_init.
      (* matching states *)
      * eapply match_states_program.
        ** eauto.
        ** apply S.PS.ProgramControl.
           *** apply PMapFacts.not_mem_in_iff; auto.
           *** apply PMapFacts.Equal_refl.
        ** auto.
Admitted.

(* TODO simplify context cases *)
Lemma transl_final_states:
  forall (ips:I.PS.state) (sps:S.PS.state) (r:int),
    match_states ips sps ->
    I.PS.final_state tprog ctx ips r ->
    S.PS.final_state prog ctx sps r.
Proof.
  intros ips sps r Hmatch Hips_final.
  inversion Hmatch as [ ics scs ips' sps' Hmatch' Hpartial1 Hpartial2 | ]; subst.
  - destruct scs as [[[[C gps] mem] k] e].
    inversion Hips_final as [ics'' ips'' r'' Hprog Hpartial Hics_final|]; subst.
    + apply S.PS.final_state_intro with (C, gps, mem, k, e); auto.
      * unfold not. intro Hturn.
        apply (S2I_turn_preservation (I.PS.PC ips') (S.PS.PC sps') Hmatch) in Hturn.
        contradiction.
      * apply (Cbs.match_final_states ics (C, gps, mem, k, e) r Hmatch').
        inversion Hpartial2; inversion Hpartial; subst;
          try discriminate; try contradiction.
        ** inversion H3. subst. auto.
    + inversion Hpartial2; subst.
      unfold I.PS.is_program_component, I.PS.is_context_component in *.
      unfold turn_of, I.PS.state_turn in *.
      subst ps. simpl in *.
      contradiction.
  - apply S.PS.final_state_context.
    inversion Hips_final as [ics'' ips'' r'' Hprog Hpartial Hics_final|]; subst.
    + inversion Hpartial; subst; subst ps0; auto.
    + unfold I.PS.is_context_component in *.
      unfold turn_of, I.PS.state_turn, S.PS.state_turn in *.
      auto.
Qed. 

Let SG : Source.GlobalEnv.global_env := Source.GlobalEnv.init_genv prog.
Let IG : Intermediate.GlobalEnv.global_env := Intermediate.GlobalEnv.init_genv tprog.

(* Is this provable? Intuitively, it should be *)
Lemma aux:
  forall ics1 ics2 ips,
    I.PS.partial_state ctx ics1 (I.PS.PC ips) ->
    I.PS.partial_state ctx ics2 (I.PS.PC ips) ->
  forall ics1',
    I.CS.step IG ics1 E0 ics1' ->
  exists ics2',
    I.CS.step IG ics2 E0 ics2'.
Proof.
  intros ics1 ics2 ips Hpartial1 Hpartial2 ics1' Hstep.
  inversion Hpartial1; subst; subst ps.
  inversion Hpartial2; subst; subst ps0. subst ps1. subst ps2.
  inversion Hstep; subst.
  - eexists. econstructor; eauto.
  - eexists. eapply I.CS.Label; eauto.
  - eexists. eapply I.CS.Const; eauto.
  - eexists. eapply I.CS.Mov; eauto.
  - eexists. eapply I.CS.BinOp; eauto.
  - eexists. eapply I.CS.Load; eauto. admit.
  - eexists. eapply I.CS.Store; eauto. admit.
  - eexists. eapply I.CS.Jal; eauto.
  - eexists. eapply I.CS.Jump; eauto.
  - eexists. eapply I.CS.BnzNZ; eauto.
  - eexists. eapply I.CS.BnzZ; eauto.
  - eexists. eapply I.CS.Alloc; eauto. admit.
Admitted.

Theorem transl_step_correct:
  forall s1 t s1',
    I.PS.step ctx IG s1 t s1' ->
  forall s2,
    match_states s1 s2 ->
  exists s2',
    S.PS.kstep ctx SG s2 t s2' /\ match_states s1' s2'.
Proof.
  intros s1 t s1' HIstep.
  inversion HIstep; subst.

  (** program has control **)

  (* epsilon *)
  (* should be provable without exploiting match_states *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    destruct (aux cs ics ps H H5 cs' H0) as [ics'].
    destruct (Cbs.simulation ics E0 ics' H2 scs H3) as [scs' []].
    inversion H4; subst.
    destruct scs' as [[[[C' gps'] mem'] k'] e'].
    exists (S.PS.PC (C', S.PS.to_partial_stack gps' (map fst (PMap.elements ctx)),
                PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem',
                k', e')).
    split.
    + eapply S.PS.Program_Epsilon; eauto.
      * constructor.
        ** unfold S.PS.is_program_component, S.PS.is_context_component in *.
           unfold turn_of, S.PS.state_turn, I.PS.state_turn in *.
           simpl in *.
           inversion H6; subst; auto.
           *** destruct (C =? C')%positive eqn:HCeqC'.
               **** rewrite Pos.eqb_eq in HCeqC'. subst. auto.
               **** discriminate.
           *** destruct (C =? C')%positive eqn:HCeqC'.
               **** rewrite Pos.eqb_eq in HCeqC'. subst. auto.
               **** discriminate.
        ** apply PMapFacts.Equal_refl.
    + econstructor; eauto.
      * econstructor.
        ** unfold S.PS.is_program_component, S.PS.is_context_component in *.
           unfold turn_of, S.PS.state_turn, I.PS.state_turn in *.
           simpl in *.
           inversion H6; subst; auto.
           *** destruct (C =? C')%positive eqn:HCeqC'.
               **** rewrite Pos.eqb_eq in HCeqC'. subst. auto.
               **** discriminate.
           *** destruct (C =? C')%positive eqn:HCeqC'.
               **** rewrite Pos.eqb_eq in HCeqC'. subst. auto.
               **** discriminate.
        ** apply PMapFacts.Equal_refl.
      * (* a little bit stuck *)
        destruct ics as [[[gps'' mem''] regs''] pc''].
        destruct ics' as [[[gps''' mem'''] regs'''] pc'''].
        inversion H1. subst.
        replace pc''' with pc.
        replace regs''' with regs.
        replace gps''' with gps0.
        eapply I.PS.ProgramControl.
        ** auto.
        ** admit.
        ** admit.
        ** admit.
        ** admit.

  (* all calls/returns depend on Cbs.the match_states relation *)

  (* internal call *)
  - admit.

  (* internal return *)
  - admit.

  (* external call *)
  - admit.

  (* external return *)
  - admit.

  (** context has control **)

  (* epsilon *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    eexists. split.
    + eapply S.PS.Context_Epsilon.
    + econstructor; auto.

  (* goes wrong *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    eexists. split.
    + eapply S.PS.Context_GoesWrong.
    + econstructor; auto.

  (* context calls/returns should be provable without exploiting Cbs.match_states *)

  (* internal call *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    eexists. split.
    + apply S.PS.Context_Internal_Call; auto.
    + econstructor; auto.
      * constructor; auto.
        constructor.

  (* internal return *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    inversion H7; subst.
    exists (S.PS.CC (C', s2, mem2) Normal). split.
    + apply S.PS.Context_Internal_Return; auto.
      * inversion H5. subst. reflexivity.
    + econstructor; eauto.

  (* external calls/returns depend on the Cbs.match_states relation *)

  (* external call *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    admit.

  (* external return *)
  - intros s2 Hmatch.
    inversion Hmatch; subst.
    admit.
Admitted.

(* S simulates I, L1=I.PS.sem L2=S.PS.sem *)
Theorem transl_program_correct:
  forward_simulation (I.PS.sem tprog ctx) (S.PS.sem prog ctx).
Proof.
  eapply forward_simulation_step.
  - apply transl_initial_states.
  - apply transl_final_states.
  - apply transl_step_correct.
Qed.
End Pbs.
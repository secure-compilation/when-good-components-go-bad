Require Import Common.Definitions.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
(* Require Import CompCert.Behaviors. *)
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import S2I.Compiler.

Module SP := Source.PS.PS.
Module SC := Source.CS.CS.
Module IP := Intermediate.PS.PS.
Module IC := Intermediate.CS.CS.

Variable prog: Source.program.
Variable tprog: Intermediate.program.
Hypothesis TRANSL: S2I.Compiler.compile_program prog = Some tprog.

(* Definition L1 := IC.sem tprog. *)
(* Definition L2 := SC.sem prog. *)

Module Cbs.

  Axiom match_stacks: IC.stack -> SC.stack -> Prop.
  Axiom match_states: IC.state -> SC.state -> Prop.

  Axiom match_initial_states:
    forall s1, initial_state (IC.sem tprog) s1 ->
               exists s2, initial_state (SC.sem prog) s2 /\ match_states s1 s2.

  (* TODO this goes with r both nat or int, where is the type checking??!! *)
  Axiom match_final_states:
    forall s1 s2 r,
      match_states s1 s2 ->
      final_state (IC.sem tprog) s1 r ->
      final_state (SC.sem prog) s2 r.

  Axiom simulation:
    forall s1 t s1', Step (IC.sem tprog) s1 t s1' ->
                     forall s2, match_states s1 s2 ->
                      exists s2', Step (SC.sem prog) s2 t s2' /\ match_states s1' s2'.


  Theorem transl_program_correct:
    forward_simulation (IC.sem tprog) (SC.sem prog).
  Proof.
    eapply forward_simulation_step.
    eexact match_initial_states.
    eexact match_final_states.
    eexact simulation.
  Qed.
End Cbs.

Module Pbs.

Variable psi: Program.interface.
(* TODO more general definition pulled from the semantics *)
(* Definition SPstate := state (SP.sem prog psi). *)
(* Definition IPstate := state (IP.sem tprog psi). *)
(* Definition ICinitial_state := initial_state (IC.sem tprog). *)
(* Definition SCinitial_state := initial_state (SC.sem prog). *)

(* TODO why was this definition requiring to introduce an 'exists' in the proof
while the other doesn't?! *)
(* Definition SPinitial_state *)
(*            (p: Source.program) (ctx: Program.interface) *)
(*            (ps: SP.state) : Prop := *)
(*   forall cs, SC.initial_state p cs -> *)
(*              SPpartialize_state ctx cs ps. *)

(* TODO recheck this definition *)
Inductive match_states: IP.state -> SP.state -> Prop :=
| match_states_intro:
    forall ics scs ips sps,
      Cbs.match_states ics scs ->
      sps = SP.partialize_state psi scs ->
      ips = IP.partialize_state psi ics ->
      match_states ips sps.

(* TODO we should use the match_states inside the simulation to make the proof more general, but compcert's simulations have a match_states with index, not sure how to make that work *)
Lemma transl_initial_states:
  forall S, IP.initial_state2 tprog psi S ->
  exists R, SP.initial_state2 prog psi R /\ match_states S R.
Proof.
  intros S HinitS.
  destruct Cbs.transl_program_correct as [index order Cmatch_states props].
  destruct HinitS as [ips ics [h1 h2]].
  specialize (Cbs.match_initial_states ics h1). intro Cmatch_initial_states.
  destruct Cmatch_initial_states as [scs [h3 h4]].
  exists (SP.partialize_state psi scs).
  split.
  - econstructor.
    split.
    apply h3.
    auto.
  - econstructor.
    apply h4.
    auto.
    auto.
Qed.

Lemma transl_final_states:
  forall (ips:IP.state) (sps:SP.state) (r:int),
    match_states ips sps -> IP.final_state2 psi ips r -> SP.final_state2 psi sps r.
Proof.
  intros ips sps r H1 H2.
  destruct H1.
  destruct H2.
  subst.
  destruct (SP.final_state_intro psi sps r scs).

  destruct H2.
  subst.  
  -
    specialize (Cbs.match_final_states ics scs r H).
    intro H3.

    subst.
    specialize (IP.final_state_intro psi ips r).
  intro H4.
  destruct h2.
  

    apply Cbs.match_final_states in H.
  specialize (IP.final_state_intro psi ips r).
  intro H.
  subst.

  intro H.

  destruct h2 as [ics h3].
  destruct (H ics). h3 H0).
                          specialize (H ics h3 H0).
  destruct H as [].
  subst.
  - apply Cbs.match_final_states with (r:=r) in H.
    econstructor.
    split.
    apply H.
    auto.
    Check IP.IC.final_state2.
    (* IP.IC.final_state *)
    (*  : GlobalEnv.global_env -> IP.IC.state -> nat -> Prop *)

    Check final_state (IC.sem tprog).
    (* final_state (IC.sem tprog) *)
    (*      : state (IC.sem tprog) -> int -> Prop *)

    apply h3.



Let ge : Source.GlobalEnv.global_env := Source.GlobalEnv.init_genv prog.
Let tge : Intermediate.GlobalEnv.global_env := Intermediate.GlobalEnv.init_genv tprog.


Axiom transl_step_correct:
  forall s1 t s1', IPS.step psi tge s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', SPS.kstep psi ge s2 t s2' /\ match_states s1' s2'.

(* S simulates I, L1=IPS.sem L2=SPS.sem *)
Theorem transl_program_correct:
  forward_simulation (IPS.sem tprog psi) (SPS.sem prog psi).
Proof.
  eapply forward_simulation_step.
  (* apply senv_preserved. *)
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step_correct.
Qed.
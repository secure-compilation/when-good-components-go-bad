Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Module PS.

Import Intermediate.

Module PartialPointer.
  Definition t : Type := Component.id * option (Block.id * Block.offset).
End PartialPointer.

Definition stack := list PartialPointer.t.

Definition program_state : Type := stack * Memory.t * Register.t * Pointer.t.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state.

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    match s with
    | PC (_, _, _, pc) => PMap.In (Pointer.component pc) iface
    | CC (C, _, _) _ => PMap.In C iface
    end
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := ~ is_context_component ps ctx.

Module IC := Intermediate.CS.CS.

(* stack partialization *)

Definition to_partial_frame pc frame : PartialPointer.t :=
  let '(C, b, o) := frame in
  if Util.Lists.mem C pc then
    (C, Some (b, o))
  else
    (C, None).

Definition to_partial_stack (s : CS.stack) (pc : list Component.id) :=
  map (to_partial_frame pc) s.

Lemma push_by_prog_preserves_partial_stack:
  forall s ps pc C b o,
    Util.Lists.mem C pc = true ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,b,o)::s) pc = (C,Some (b,o)) :: ps.
Proof.
  intros s ps pc C b o Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_context_preserves_partial_stack:
  forall s ps pc C b o,
    ~ (In C pc) ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,b,o)::s) pc = (C,None) :: ps.
Proof.
  intros s ps pc C b o Hprogturn Hpstack.
  simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

(* predicates over states *)

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl:
    forall gps mem pmem regs pc,
      let ps := PC (to_partial_stack gps (map fst (PMap.elements ctx)),
                    pmem, regs, pc) in
      is_program_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      partial_state ctx (gps, mem, regs, pc) ps
| ContextControl_Normal:
    forall gps mem pmem regs pc,
      let ps := CC (Pointer.component pc,
                    to_partial_stack gps (map fst (PMap.elements ctx)), pmem) Normal in
      is_context_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      (*(exists s' t, CS.step (init_genv p) (gps,mem,regs,pc) t s') ->*)
      partial_state ctx (gps, mem, regs, pc) ps
| ContextControl_WentWrong:
    forall gps mem pmem regs pc,
      let ps := CC (Pointer.component pc,
                    to_partial_stack gps (map fst (PMap.elements ctx)), pmem) WentWrong in
      is_context_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      (*(forall s' t, ~ CS.step (init_genv p) (gps,mem,regs,pc) t s') ->*)
      partial_state ctx (gps, mem, regs, pc) ps.

Theorem partial_state_preserves_turn_of:
  forall psi cs ps,
    partial_state psi cs ps -> (turn_of ps psi <-> turn_of cs psi).
Proof.
  intros psi cs ps Hpartial.
  split.
  - intro Hturn.
    unfold turn_of, state_turn in Hturn.
    unfold turn_of, IC.state_turn.
    IC.unfold_state.
    destruct ps.
    + repeat destruct p.
      inversion Hpartial; subst; auto.
    + destruct c. destruct p.
      inversion Hpartial; subst; auto.
  - intro Hturn.
    unfold turn_of, state_turn.
    unfold turn_of, IC.state_turn in Hturn.
    IC.unfold_state.
    destruct ps.
    + repeat destruct p.
      inversion Hpartial; subst; auto.
    + destruct c. destruct p.
      inversion Hpartial; subst; auto.
Qed.

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall ics ips,
    partial_state ctx ics ips ->
    IC.initial_state p ics ->
    initial_state p ctx ips.

Inductive final_state (p: program) (ctx: Program.interface) : state -> int -> Prop :=
| final_state_program: forall ics ips r,
    ~ turn_of ips ctx ->
    partial_state ctx ics ips ->
    IC.final_state (init_genv p) ics r ->
    final_state p ctx ips r
| final_state_context: forall ips r,
    turn_of ips ctx ->
    final_state p ctx ips r.

Inductive step (ctx: Program.interface) (G : global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall ips t ips' ics ics' ps ps',
      (* conditions *)
      partial_state ctx ics ips ->
      partial_state ctx ics' ips' ->
      CS.step G ics E0 ics' ->

      (* states transition *)
      ips = PC ps ->
      ips' = PC ps' ->
      t = E0 ->

      step ctx G ips E0 ips'

| Program_Internal_Call:
    forall ips t ips' pgps pgps' mem regs regs' b pc C' P val,
      let C := Pointer.component pc in

      (* conditions *)
      executing G pc (ICall C' P) ->
      is_program_component (PC (pgps, mem, regs, pc)) ctx ->
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->

      (* extra information *)
      Register.get R_COM regs = Int val ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->

      (* updates *)
      pgps' = (C, Some (Pointer.block pc, Pointer.offset (Pointer.inc pc))) :: pgps ->
      regs' = Register.invalidate regs ->

      (* states transition *)
      ips = PC (pgps, mem, regs, pc) ->
      ips' = PC (pgps', mem, regs', (C', b, 0)) ->
      t = [ECall C P val C'] ->

      step ctx G ips t ips'

| Program_Internal_Return:
    forall ips t ips' pgps pgps' mem regs regs' pc C' b o val,
      let C := Pointer.component pc in

      (* conditions *)
      executing G pc IReturn ->
      is_program_component ips ctx ->
      C' <> C ->

      (* extra information *)
      Register.get R_COM regs = Int val ->

      (* updates *)
      pgps = (C', Some (b, o)) :: pgps' ->
      regs' = Register.invalidate regs ->

      (* states transition *)
      ips = PC (pgps, mem, regs, pc) ->
      ips' = PC (pgps', mem, regs', (C, b, o)) ->
      t = [ERet C val C'] ->

      step ctx G ips t ips'

| Program_External_Call:
    forall ips t ips' pgps pgps' mem regs pc C' P val,
      let C := Pointer.component pc in

      (* conditions *)
      executing G pc (ICall C' P) ->
      is_context_component ips ctx ->
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->

      (* extra information *)
      Register.get R_COM regs = Int val ->

      (* updates *)
      pgps' = (C, Some (Pointer.block pc, Pointer.offset (Pointer.inc pc))) :: pgps ->

      (* states transition *)
      ips = PC (pgps, mem, regs, pc) ->
      ips' = CC (C', pgps', mem) Normal ->
      t = [ECall C P val C'] ->

      step ctx G ips t ips'

| Program_External_Return:
    forall ips t ips' pgps pgps' mem regs pc C' val,
      let C := Pointer.component pc in

      (* conditions *)
      executing G pc IReturn ->
      is_context_component ips ctx ->
      C' <> C ->

      (* extra information *)
      Register.get R_COM regs = Int val ->

      (* updates *)
      pgps = (C', None) :: pgps' ->

      (* states transition *)
      ips = PC (pgps, mem, regs, pc) ->
      ips' = CC (C', pgps', mem) Normal ->
      t = [ERet C val C'] ->

      step ctx G ips t ips'

(* does this rule create problems? e.g. w.r.t. the anti-stuttering measure *)
| Context_Epsilon:
    forall ips t ips' pgps mem C,
      (* states transition *)
      ips = CC (pgps, mem,C) Normal ->
      ips' = CC (pgps, mem,C) Normal ->
      t = E0 ->

      step ctx G ips E0 ips'

| Context_GoesWrong:
    forall ips t ips' pgps mem C,
      (* states transitions *)
      ips = CC (pgps, mem, C) Normal ->
      ips' = CC (pgps, mem, C) WentWrong ->
      t = E0 ->

      step ctx G ips t ips'

| Context_Internal_Call:
    forall ips t ips' pgps pgps' mem C C' P call_arg,
      (* conditions *)
      is_context_component ips' ctx ->
      imported_procedure ctx C C' P ->
      C' <> C ->

      (* updates *)
      pgps' = (C, None) :: pgps ->

      (* states transition *)
      ips = CC (C, pgps, mem) Normal ->
      ips' = CC (C', pgps', mem) Normal ->
      t = [ECall C P call_arg C'] ->

      step ctx G ips t ips'

| Context_Internal_Return:
    forall ips t ips' pgps pgps' mem C C' return_val,
      (* conditions *)
      is_context_component ips' ctx ->
      C' <> C ->

      (* updates *)
      pgps = (C', None) :: pgps' ->

      (* states transition *)
      ips = CC (C, pgps, mem) Normal ->
      ips' = CC (C', pgps', mem) Normal ->
      t = [ERet C return_val C'] ->

      step ctx G ips t ips'

| Context_External_Call:
    forall ips t ips' pgps pgps' mem regs pc' C C' P b val,
      (* conditions *)
      is_program_component ips' ctx ->
      imported_procedure ctx C C' P ->
      C' <> C ->

      (* extra information *)
      Register.get R_COM regs = Int val ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->

      (* updates *)
      pgps' = (C, None) :: pgps ->
      pc' = (C', b, 0) ->

      (* states transition *)
      ips = CC (C, pgps, mem) Normal ->
      ips' = PC (pgps', mem, regs, pc') ->
      t = [ECall C P val C'] ->

      step ctx G ips t ips'

| Context_External_Return:
    forall ips t ips' pgps pgps' mem regs pc' C C' b o val,
      (* conditions *)
      is_program_component ips' ctx ->

      (* extra information *)
      Register.get R_COM regs = Int val ->

      (* updates *)
      pgps = (C', Some (b, o)) :: pgps' ->
      pc' = (C', b, o) ->

      (* states transition *)
      ips = CC (C, pgps, mem) Normal ->
      ips' = PC (pgps', mem, regs, pc') ->
      t = [ERet C val C'] ->

      step ctx G ips t ips'.

(*
Definition partialize (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       PMapExtra.diff (prog_interface p) ctx;
     prog_procedures :=
       PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) (prog_procedures p);
     prog_buffers :=
       PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) (prog_buffers p);
     prog_main := prog_main p |}.
*)

Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Let G := init_genv p.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  (* the context is part of p *)
  Hypothesis valid_context:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (prog_interface p).

  Definition sem :=
    @Semantics_gen state global_env (step ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.

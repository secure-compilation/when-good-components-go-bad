Require Import Coq.Classes.Morphisms.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Module PS.

Import Source.

Definition stack : Type := list (Component.id * option (value * CS.cont)).

Definition program_state : Type := Component.id * stack * Memory.t * CS.cont * expr.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state.

Definition component_of_state (scs: state) : Component.id :=
  match scs with
  | PC (C, _, _, _, _) => C
  | CC (C, _, _) _     => C
  end.

(** Equality on partial states uses extensional equality on maps, and Leibniz
    equality on other components. *)
Inductive state_eq : state -> state -> Prop :=
| PCE C stk mem1 mem2 k e :
  PMap.Equal mem1 mem2 ->
  state_eq (PC (C, stk, mem1, k, e)) (PC (C, stk, mem2, k, e))
| CCE C stk mem1 mem2 :
  PMap.Equal mem1 mem2 ->
  state_eq (CC (C, stk, mem1) Normal) (CC (C, stk, mem2) Normal).

Instance state_eq_Equivalence : Equivalence state_eq.
Proof.
  constructor.
  - intros [[[[[? ?] ?] ?] ?] | [[? ?] ?] []]; constructor;
    reflexivity.
  - intros sps1 sps2 H. now destruct H; constructor; symmetry.
  - intros sps1 sps2 sps3 H1 H2.
    destruct H1; inversion H2; subst; constructor; etransitivity; eassumption.
Qed.

Instance component_of_state_Proper : Proper (state_eq ==> eq) component_of_state.
Proof.
  intros sps1 sps2 H. now destruct H.
Qed.

(* TODO not sure if this Program.interface should be list Component.id *)

Instance state_turn : HasTurn state := {
  turn_of s iface := PMap.In (component_of_state s) iface
}.

Module SC := Source.CS.CS.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := ~ is_context_component ps ctx.

(* stack partialization *)

Definition to_partial_frame ctx frame : Component.id * option (value * CS.cont) :=
  let '(C, v, k) := frame in
  if Util.Lists.mem C ctx then
    (C, None)
  else
    (C, Some (v, k)).

Definition to_partial_stack (s : CS.stack) (pc : list Component.id) :=
  map (to_partial_frame pc) s.

Lemma push_by_context_preserves_partial_stack:
  forall s ps ctx C v k,
    Util.Lists.mem C ctx = true ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,v,k)::s) ctx = (C,None) :: ps.
Proof.
  intros s ctx pc C v k Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_prog_preserves_partial_stack:
  forall s ps ctx C v k,
    ~ (In C ctx) ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,v,k)::s) ctx = (C,Some (v,k)) :: ps.
Proof.
  intros s ps ctx C v k Hprogturn Hpstack.
  simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

Inductive partial_state (ctx: Program.interface) (scs: CS.state) (sps: PS.state) : Prop :=
| ProgramControl: forall C gps pgps mem pmem k e,
    (* related states *)
    scs = (C, gps, mem, k, e) ->
    sps = PC (C, pgps, pmem, k, e) ->

    (* program has control *)
    is_program_component sps ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx scs sps

| ContextControl_Normal: forall C gps pgps mem pmem k e,
    (* related states *)
    scs = (C, gps, mem, k, e) ->
    sps = CC (C, pgps, pmem) Normal ->

    (* context has control *)
    is_context_component sps ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx scs sps.

Definition partialize (ctx: Program.interface) (scs: CS.state) : PS.state :=
  let '(C, gps, mem, k, e) := scs in
  let pgps := to_partial_stack gps (map fst (PMap.elements ctx)) in
  let pmem := PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem in
  if PMapFacts.In_dec ctx C then CC (C, pgps, pmem) Normal
  else PC (C, pgps, pmem, k, e).

Lemma partialize_partial_state ctx scs : partial_state ctx scs (partialize ctx scs).
Proof.
  destruct scs as [[[[C gps] mem] k] e]. simpl.
  destruct (PMapFacts.In_dec ctx C) as [H|H].
  - eapply ContextControl_Normal; eauto. reflexivity.
  - eapply ProgramControl; eauto. reflexivity.
Qed.

Lemma partial_state_partialize ctx scs sps :
  partial_state ctx scs sps ->
  state_eq sps (partialize ctx scs).
Proof.
  intros H.
  destruct H as [C gps pgps mem pmem k e ? ? Hcomp Hmem ?
                |C gps pgps mem pmem k e ? ? Hcomp Hmem];
  subst scs sps pgps;
  unfold is_program_component, is_context_component in Hcomp;
  simpl in *;
  destruct (PMapFacts.In_dec ctx C) as [?|?]; try easy.
  - now apply PCE.
  - now apply CCE.
Qed.

Theorem partial_state_preserves_turn_of:
  forall psi cs ps,
    partial_state psi cs ps -> (turn_of ps psi <-> turn_of cs psi).
Proof.
  intros psi scs sps H. simpl.
  apply partial_state_partialize in H.
  destruct scs as [[[[C gps] mem] k] e].
  rewrite H. simpl.
  now destruct (PMapFacts.In_dec _ _).
Qed.

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall scs sps,
    partial_state ctx scs sps ->
    SC.initial_state p scs ->
    initial_state p ctx sps.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_intro: forall scs sps,
    ~ turn_of sps ctx ->
    partial_state ctx scs sps ->
    SC.final_state scs->
    final_state p ctx sps
| final_state_context: forall sps,
    turn_of sps ctx ->
    final_state p ctx sps.

(* small-step semantics *)

Inductive kstep (ctx: Program.interface) (G: global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall sps t sps' scs scs' ps ps',
      (* state transition *)
      sps = PC ps ->
      sps' = PC ps' ->
      t = E0 ->

      (* conditions *)
      CS.kstep G scs E0 scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->

      kstep ctx G sps E0 sps'

| Program_Internal_Call:
   forall sps t sps' C s s' mem mem' k k' kont e e' C' P v C'_procs P_expr b b' old_call_arg,
     (* state transition *)
     sps = PC (C, s, mem, k, e) ->
     sps' = PC (C', s', mem', k', e') ->
     t = [ECall C P v C'] ->

     (* conditions *)
     e = E_val (Int v) ->
     k = Kcall C' P kont ->
     is_program_component sps ctx ->
     is_program_component sps' ctx ->
     C' <> C ->
     imported_procedure (genv_interface G) C C' P ->
     PMap.find C' (genv_procedures G) = Some C'_procs ->
     PMap.find P C'_procs = Some P_expr ->
     PMap.find C (genv_buffers G) = Some b ->
     Memory.load mem (C, b, 0) = Some old_call_arg ->
     PMap.find C' (genv_buffers G) = Some b' ->

     (* updates *)
     s' = (C, Some (old_call_arg, kont)) :: s ->
     Memory.store mem (C', b', 0) (Int v) = Some mem' ->
     k' = Kstop ->
     e' = P_expr ->

     kstep ctx G sps t sps'

| Program_Internal_Return:
    forall sps t sps' C s s' srest mem mem' k k' kont e e' v C' old_call_arg b,
      (* state transition *)
      sps = PC (C, s, mem, k, e) ->
      sps' = PC (C', s', mem', k', e') ->
      t = [ERet C v C'] ->

      (* conditions *)
      e = E_val (Int v) ->
      k = Kstop ->
      s = (C', Some (old_call_arg, kont)) :: srest ->
      is_program_component sps ctx ->
      is_program_component sps' ctx ->
      C' <> C ->
      PMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->

      (* updates *)
      s' = srest ->
      k' = kont ->
      e' = E_val (Int v) ->

      kstep ctx G sps t sps'

| Program_External_Call:
    forall sps t sps' C s s' mem k kont e C' P v b old_call_arg,
      (* state transition *)
      sps = PC (C, s, mem, k, e) ->
      sps' = CC (C', s', mem) Normal ->
      t = [ECall C P v C'] ->

      (* conditions *)
      e = E_val (Int v) ->
      k = Kcall C' P kont ->
      is_program_component sps ctx ->
      is_context_component sps' ctx ->
     imported_procedure (genv_interface G) C C' P ->
      PMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C, b, 0) = Some old_call_arg ->

      (* updates *)
      s' = (C, Some (old_call_arg,kont)) :: s ->

      kstep ctx G sps t sps'

| Program_External_Return:
    forall sps t sps' C s s' srest mem k e v C',
      (* state transition *)
      sps = PC (C, s, mem, k, e) ->
      sps' = CC (C', s', mem) Normal ->
      t = [ERet C v C'] ->

      (* conditions *)
      e = E_val (Int v) ->
      k = Kstop ->
      s = (C', None) :: srest ->
      is_program_component sps ctx ->
      is_context_component sps' ctx ->

      (* updates *)
      s' = srest ->

      kstep ctx G sps t sps'

| Context_Epsilon:
    forall sps t sps' s mem C,
      (* state transition *)
      sps = CC (C, s, mem) Normal ->
      sps' = CC (C, s, mem) Normal ->
      t = E0 ->

      (* conditions *)
      is_context_component sps ctx ->
      is_context_component sps' ctx ->

      kstep ctx G sps t sps'

| Context_Internal_Call:
    forall sps t sps' s s' mem C C' P call_arg,
      (* state transition *)
      sps = CC (C, s, mem) Normal ->
      sps' = CC (C', s', mem) Normal ->
      t = [ECall C P call_arg C'] ->

      (* conditions *)
      is_context_component sps ctx ->
      is_context_component sps' ctx ->
      C' <> C ->
      imported_procedure ctx C C' P ->

      (* updates *)
      s' = (C, None) :: s ->

      kstep ctx G sps t sps'

| Context_Internal_Return:
    forall sps t sps' s s' srest mem C C' return_val,
      (* state transition *)
      sps = CC (C, s, mem) Normal ->
      sps' = CC (C', s', mem) Normal ->
      t = [ERet C return_val C'] ->

      (* conditions *)
      is_context_component sps ctx ->
      is_context_component sps' ctx ->
      s = (C', None) :: srest ->
      C' <> C ->

      (* updates *)
      s' = srest ->

      kstep ctx G sps t sps'

| Context_External_Call:
    forall sps t sps' s s' mem mem' k' e' C C' P C'_procs P_expr b' val,
      (* state transition *)
      sps = CC (C, s, mem) Normal ->
      sps' = PC (C', s', mem', k', e') ->
      t = [ECall C P val C'] ->

      (* conditions *)
      is_context_component sps ctx ->
      is_program_component sps' ctx ->
      imported_procedure ctx C C' P ->
      PMap.find C' (genv_procedures G) = Some C'_procs ->
      PMap.find P C'_procs = Some P_expr ->
      PMap.find C' (genv_buffers G) = Some b' ->

      (* updates *)
      s' = (C, None) :: s ->
      Memory.store mem (C', b', 0) (Int val) = Some mem' ->
      k' = Kstop ->
      e' = P_expr ->

      kstep ctx G sps t sps'

| Context_External_Return:
    forall sps t sps' C s s' srest mem mem' kont k' e' v C' old_call_arg b,
      (* state transition *)
      sps =  CC (C, s, mem) Normal ->
      sps' = PC (C', s', mem', k', e') ->
      t = [ERet C v C'] ->

      (* conditions *)
      is_context_component sps ctx ->
      is_program_component sps' ctx ->
      s = (C', Some (old_call_arg, kont)) :: srest ->
      PMap.find C' (genv_buffers G) = Some b ->

      (* updates *)
      s' = srest ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      k' = kont ->
      e' = E_val (Int v) ->

      kstep ctx G sps t sps'.

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
    @Semantics_gen state global_env (kstep ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.

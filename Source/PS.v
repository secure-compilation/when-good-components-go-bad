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

(* TODO not sure if this Program.interface should be list Component.id *)

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    match s with
    | PC (C, _, _, _, _) => PMap.In C iface
    | CC (C, _, _) _ => PMap.In C iface
    end
}.

Module SC := Source.CS.CS.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := ~ is_context_component ps ctx.

(* stack partialization *)

Definition to_partial_frame pc frame : Component.id * option (value * CS.cont) :=
  let '(C, v, k) := frame in
  if Util.Lists.mem C pc then
    (C, Some (v, k))
  else
    (C, None).

Definition to_partial_stack (s : CS.stack) (pc : list Component.id) :=
  map (to_partial_frame pc) s.

Lemma push_by_prog_preserves_partial_stack:
  forall s ps pc C v k,
    Util.Lists.mem C pc = true ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,v,k)::s) pc = (C,Some (v,k)) :: ps.
Proof.
  intros s ps pc C v k Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_context_preserves_partial_stack:
  forall s ps pc C v k,
    ~ (In C pc) ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,v,k)::s) pc = (C,None) :: ps.
Proof.
  intros s ps pc C v k Hprogturn Hpstack.
  simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl:
    forall C gps mem pmem k e,
      let ps := PC (C, to_partial_stack gps (map fst (PMap.elements ctx)),
                    pmem, k, e) in
      is_program_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      partial_state ctx (C, gps, mem, k, e) ps

| ContextControl_Normal:
    forall C gps mem pmem k e,
      let ps := CC (C, to_partial_stack gps (map fst (PMap.elements ctx)), pmem) Normal in
      is_context_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      (*(exists s' t, CS.kstep (init_genv p) (C,gps,mem,k,e) t s') ->*)
      partial_state ctx (C, gps, mem, k, e) ps
| ContextControl_WentWrong:
    forall C gps mem pmem k e,
      let ps := CC (C, to_partial_stack gps (map fst (PMap.elements ctx)), pmem)
                   WentWrong in
      is_context_component ps ctx ->
      PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->
      (*(forall s' t, ~ CS.kstep (init_genv p) (C,gps,mem,k,e) t s') ->*)
      partial_state ctx (C, gps, mem, k, e) ps.

Theorem partial_state_preserves_turn_of:
  forall psi cs ps,
    partial_state psi cs ps -> (turn_of ps psi <-> turn_of cs psi).
Proof.
  intros psi cs ps Hpartial.
  split.
  - intro Hturn.
    unfold turn_of, state_turn in Hturn.
    unfold turn_of, SC.state_turn.
    SC.unfold_state.
    destruct ps.
    + repeat destruct p.
      inversion Hpartial; subst; auto.
    + destruct c. destruct p.
      inversion Hpartial; subst; auto.
  - intro Hturn.
    unfold turn_of, state_turn.
    unfold turn_of, SC.state_turn in Hturn.
    SC.unfold_state.
    destruct ps.
    + repeat destruct p.
      inversion Hpartial; subst; auto.
    + destruct c. destruct p.
      inversion Hpartial; subst; auto.
Qed.

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall cs ps,
    partial_state ctx cs ps ->
    SC.initial_state p cs ->
    initial_state p ctx ps.

Inductive final_state (p: program) (ctx: Program.interface) : state -> int -> Prop :=
| final_state_intro: forall cs ps r,
    ~ turn_of ps ctx ->
    partial_state ctx cs ps ->
    SC.final_state cs r ->
    final_state p ctx ps r
| final_state_context: forall ps r,
    turn_of ps ctx ->
    final_state p ctx ps r.

(* small-step semantics *)

Inductive kstep (ctx: Program.interface) (G: global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall cs cs' ps ps',
      partial_state ctx cs (PC ps) ->
      CS.kstep G cs E0 cs' ->
      partial_state ctx cs' (PC ps') ->
      kstep ctx G (PC ps) E0 (PC ps')

| Program_Internal_Call:
    forall C s mem mem' k C' P v C'_procs P_expr b b' old_call_arg,
      is_program_component
        (PC (C', (C, Some (old_call_arg, k)) :: s, mem', Kstop, P_expr)) ctx ->
      (* retrieve the procedure code *)
      PMap.find C' (genv_procedures G) = Some C'_procs ->
      PMap.find P C'_procs = Some P_expr ->
      (* save the old call argument *)
      PMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      (* place the call argument in the target memory *)
      PMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int v) = Some mem' ->
      let t := if Pos.eqb C C' then E0 else [ECall C P v C'] in
      kstep ctx G
            (PC (C, s, mem, Kcall C' P k, E_val (Int v))) t
            (PC (C', (C, Some (old_call_arg, k)) :: s, mem', Kstop, P_expr))

| Program_Internal_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component (PC (C', s, mem', k, E_val (Int v))) ctx ->
      (* restore the old call argument *)
      PMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := if Pos.eqb C C' then E0 else [ERet C v C'] in
      kstep ctx G
            (PC (C, (C', Some (old_call_arg, k)) :: s, mem, Kstop, E_val (Int v))) t
            (PC (C', s, mem', k, E_val (Int v)))

| Program_External_Call:
    forall C s mem k C' P v b old_call_arg,
      is_context_component
        (CC (C', (C, Some (old_call_arg,k)) :: s, mem) Normal) ctx ->
      (* save the old call argument *)
      PMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      let t := [ECall C P v C'] in
      kstep ctx G
            (PC (C, s, mem, Kcall C' P k, E_val (Int v))) t
            (CC (C', (C, Some (old_call_arg,k)) :: s, mem) Normal)

| Program_External_Return:
    forall C s mem k v C' old_call_arg,
      is_context_component (CC (C', s, mem) Normal) ctx ->
      let t := [ERet C v C'] in
      kstep ctx G
            (PC (C, (C', Some (old_call_arg, k)) :: s, mem, Kstop, E_val (Int v))) t
            (CC (C', s, mem) Normal)

| Context_Epsilon:
    forall s mem C,
      kstep ctx G (CC (C,s,mem) Normal) E0 (CC (C,s,mem) Normal)

| Context_GoesWrong:
    forall s mem C,
      kstep ctx G (CC (C,s,mem) Normal) E0 (CC (C,s,mem) WentWrong)

| Context_Internal_Call:
    forall s s' mem C C' P call_arg,
      C' <> C ->
      imported_procedure ctx C C' P ->
      is_context_component (CC (C',s',mem) Normal) ctx ->
      s' = (C, None) :: s ->
      let t := [ECall C P call_arg C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_Internal_Return:
    forall s s' mem C C' return_val,
      C' <> C ->
      is_context_component (CC (C',s',mem) Normal) ctx ->
      s = (C', None) :: s' ->
      let t := [ERet C return_val C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_External_Call:
    forall s s' mem mem' C C' P C'_procs P_expr b' val,
      C' <> C ->
      imported_procedure ctx C C' P ->
      is_program_component (PC (C',s',mem,Kstop,P_expr)) ctx ->
      s' = (C, None) :: s ->
      (* retrieve the procedure code *)
      PMap.find C' (genv_procedures G) = Some C'_procs ->
      PMap.find P C'_procs = Some P_expr ->
      (* place the call argument in the target memory *)
      PMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int val) = Some mem' ->
      let t := [ECall C P val C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (PC (C',s',mem,Kstop,P_expr))

| Context_External_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component (PC (C', s, mem', k, E_val (Int v))) ctx ->
      (* restore the old call argument *)
      PMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := [ERet C v C'] in
      kstep ctx G
            (CC (C, (C', Some (old_call_arg, k)) :: s, mem) Normal) t
            (PC (C', s, mem', k, E_val (Int v))).

(*
Definition partialize (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       PMapExtra.diff (prog_interface p) ctx;
     prog_procedures :=
       PMapExtra.filter (fun C _ => negb (PMap.mem C ctx)) (prog_procedures p);
     prog_buffers :=
       PMapExtra.filter (fun C _ => negb (PMap.mem C ctx)) (prog_buffers p);
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
    @Semantics_gen state global_env (kstep ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.
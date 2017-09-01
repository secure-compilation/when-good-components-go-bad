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
Definition context_state : Type := stack * Memory.t * Component.id.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state
with exec_state : Type := Normal | WentWrong.

Definition is_program_component G C := NMap.In C (genv_interface G).
Definition is_context_component (ctx: Program.interface) C := NMap.In C ctx.

Definition initial_state
           (p: program) (G: global_env) (ctx: Program.interface)
           (s: state) : Prop :=
  match s with
  | PC (gps, mem, regs, pc) =>
    (* the global protected stack is empty *)
    gps = [] /\
    (* mem exaclty contains all components memories and it comes from the init routine *)
    (forall C, is_program_component G C <-> NMap.In C mem) /\
    (let '(m, _, _) := init_all p in mem = m) /\
    (* the origin register (R_AUX2) is set to 1 (meaning external call) *)
    (* the R_ONE register is set to 1 *)
    (* the other registers are set to undef *)
    regs = [Int 1; Undef; Undef; Undef; Int 1; Undef; Undef] /\
    (* the program counter is pointing to the start of the main procedure *)
    is_program_component G (Pointer.component pc) /\
    Pointer.component pc = fst (prog_main p) /\
    EntryPoint.get (fst (prog_main p)) (snd (prog_main p))
                   (genv_entrypoints G) = Some (Pointer.block pc) /\
    Pointer.offset pc = 0
  | CC (pgps, mem, C) execst =>
    (* the global protected stack is empty *)
    pgps = [] /\
    (* mem exaclty contains all program components memories *)
    (forall C, is_program_component G C <-> NMap.In C mem) /\
    (let '(m, _, _) := init_all p in mem = m) /\
    (* the executing component is the main one *)
    is_context_component ctx C /\
    C = fst (prog_main p) /\
    (* the execution didn't go wrong *)
    execst = Normal
  end.

(* maybe check whether mem is sound and pc & C are in the program or the context *)
Definition final_state (G: global_env) (s: state) (r: nat) : Prop :=
  match s with
  | PC (gps, mem, regs, pc) =>
    Register.get R_COM regs = Int r /\
    executing G pc IHalt
  | CC (pgps, mem, C) execst =>
    execst = Normal
  end.

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

Inductive step (ctx: Program.interface) (G : global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall G' pgps (mem mem' wmem wmem' : Memory.t) Cmem'
      (regs regs' : Register.t) (pc pc' : Pointer.t),

      (* G' is an extension of G w.r.t. ctx *)
      (* 1) the interface is G plus ctx *)
      NMap.Equal (genv_interface G') (NMapExtra.update (genv_interface G) ctx) ->
      (* 2) the procedures are the same of G plus some new ones for ctx *)
      (forall C Cprocs, NMap.MapsTo C Cprocs (genv_procedures G') <->
                   (NMap.MapsTo C Cprocs (genv_procedures G) \/
                    (NMap.In C ctx /\ ~ NMap.In C (genv_procedures G)))) ->
      (* 3) the entrypoints are the same of G plus some new ones for ctx *)
      (forall C Centrypoints, NMap.MapsTo C Centrypoints (genv_entrypoints G') <->
                         (NMap.MapsTo C Centrypoints (genv_entrypoints G) \/
                          (NMap.In C ctx /\ ~ NMap.In C (genv_entrypoints G)))) ->

      (* wmem is an extension of mem w.r.t. ctx *)
      (* 1) wmem contains mem *)
      (forall C Cmem, NMap.MapsTo C Cmem mem -> NMap.MapsTo C Cmem wmem) ->
      (* 2) wmem has the context components memories *)
      (forall C, is_context_component ctx C -> NMap.In C wmem) ->
      (* 3) wmem extends mem exactly w.r.t. ctx *)
      (forall C Cmem, NMap.MapsTo C Cmem wmem <->
                 (NMap.MapsTo C Cmem mem \/
                  (is_context_component ctx C /\ ~ NMap.In C mem))) ->

      (* the complete semantics steps silently with the extended versions of
         memory and global environment
         NOTE that the stack (gps) is not related to the partial one (pgps) *)
      (exists gps, CS.step G' (gps,wmem,regs,pc) E0 (gps,wmem',regs',pc')) ->

      (* mem' is mem with the updated version of the current
         executing component's memory *)
      NMap.MapsTo (Pointer.component pc') Cmem' wmem' ->
      NMap.Equal mem' (NMap.add (Pointer.component pc') Cmem' mem) ->

      step ctx G (PC (pgps,mem,regs,pc)) E0 (PC (pgps,mem',regs',pc'))

| Program_External_Load_In_Program:
    forall pgps mem regs regs' pc r1 r2 ptr v,
      executing G pc (ILoad r1 r2) ->
      Register.get r1 regs = Ptr ptr ->
      Pointer.component ptr <> Pointer.component pc ->
      is_program_component G (Pointer.component ptr) ->
      Memory.load mem ptr = Some v ->
      Register.set r2 v regs = regs' ->
      (* TODO fix the read value in the event *)
      let t := [ELoad (Pointer.component pc) 0 (Pointer.component ptr)] in
      step ctx G (PC (pgps, mem, regs, pc)) t (PC (pgps, mem, regs', Pointer.inc pc))

| Program_External_Load_In_Context:
    forall pgps mem regs regs' pc r1 r2 ptr v,
      executing G pc (ILoad r1 r2) ->
      Register.get r1 regs = Ptr ptr ->
      Pointer.component ptr <> Pointer.component pc ->
      is_context_component ctx (Pointer.component ptr) ->
      Register.set r2 v regs = regs' ->
      (* TODO fix the read value in the event *)
      let t := [ELoad (Pointer.component pc) 0 (Pointer.component ptr)] in
      step ctx G (PC (pgps, mem, regs, pc)) t (PC (pgps, mem, regs', Pointer.inc pc))

| Program_Internal_Call:
    forall pgps pgps' mem regs b o pc C' P val,
      executing G pc (ICall C' P) ->
      let C := Pointer.component pc in
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_program_component G C' ->
      pgps' = (C, Some (b, o)) :: pgps ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->
      Register.get R_COM regs = Int val ->
      let pc' := (C', b, 0) in
      let t := [ECall C P val C'] in
      step ctx G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,Register.invalidate regs,pc'))

| Program_Internal_Return:
    forall pgps pgps' mem regs pc pc' C' b o val,
      let C := Pointer.component pc in
      executing G pc IReturn ->
      pgps = (C', Some (b,o)) :: pgps' ->
      C' <> C ->
      is_program_component G C' ->
      Register.get R_COM regs = Int val ->
      let t := [ERet C val C'] in
      step ctx G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,Register.invalidate regs,pc'))

| Program_External_Call:
    forall pgps pgps' mem regs pc C' b o P val,
      let C := Pointer.component pc in
      executing G pc (ICall C' P) ->
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_context_component ctx C' ->
      pgps' = (C, Some (b,o)) :: pgps ->
      Register.get R_COM regs = Int val ->
      (* TODO fix the read value in the event *)
      let t := [ECall C P val C'] in
      step ctx G (PC (pgps,mem,regs,pc)) t (CC (pgps',mem,C') Normal)

| Program_External_Return:
    forall pgps pgps' mem regs pc C' val,
      let C := Pointer.component pc in
      executing G pc IReturn ->
      C' <> C ->
      is_context_component ctx C' ->
      pgps = (C', None) :: pgps' ->
      Register.get R_COM regs = Int val ->
      (* TODO fix the read value in the event *)
      let t := [ERet C val C'] in
      step ctx G (PC (pgps,mem,regs,pc)) t (CC (pgps',mem,C') Normal)

| Context_Epsilon:
    forall pgps mem C,
      step ctx G (CC (pgps,mem,C) Normal) E0 (CC (pgps,mem,C) Normal)

| Context_GoesWrong:
    forall pgps mem C,
      step ctx G (CC (pgps,mem,C) Normal) E0 (CC (pgps,mem,C) WentWrong)

| Context_Internal_Call:
    forall pgps pgps' mem C C' P call_arg,
      C' <> C ->
      imported_procedure ctx C C' P ->
      is_context_component ctx C' ->
      pgps' = (C, None) :: pgps ->
      let t := [ECall C P call_arg C'] in
      step ctx G (CC (pgps,mem,C) Normal) t (CC (pgps',mem,C') Normal)

| Context_Internal_Return:
    forall pgps pgps' mem C C' return_val,
      C' <> C ->
      is_context_component ctx C' ->
      pgps = (C', None) :: pgps' ->
      let t := [ERet C return_val C'] in
      step ctx G (CC (pgps,mem,C) Normal) t (CC (pgps',mem,C') Normal)

| Context_External_Load_In_Context:
    forall pgps mem C ptr,
      Pointer.component ptr <> C ->
      is_context_component ctx (Pointer.component ptr) ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      step ctx G (CC (pgps, mem, C) Normal) t (CC (pgps, mem, C) Normal)

| Context_External_Load_In_Program:
    forall pgps mem C ptr v,
      Pointer.component ptr <> C ->
      is_program_component G (Pointer.component ptr) ->
      Memory.load mem ptr = Some v ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      step ctx G (CC (pgps, mem, C) Normal) t (CC (pgps, mem, C) Normal)

| Context_External_Call:
    forall pgps pgps' mem regs C C' P b val,
      C' <> C ->
      imported_procedure ctx C C' P ->
      is_program_component G C' ->
      pgps' = (C, None) :: pgps ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->
      Register.get R_COM regs = Int val ->
      let t := [ECall C P val C'] in
      let pc' := (C', b, 0) in
      step ctx G (CC (pgps,mem,C) Normal) t (PC (pgps',mem,regs,pc'))

| Context_External_Return:
    forall pgps pgps' mem regs C C' b o val,
      pgps = (C', Some (b,o)) :: pgps' ->
      is_program_component G C' ->
      Register.get R_COM regs = Int val ->
      let t := [ERet C val C'] in
      step ctx G (CC (pgps,mem,C) Normal) t (PC (pgps',mem,regs, (C',b,o))).

Definition partialize (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       NMapExtra.diff (prog_interface p) ctx;
     prog_procedures :=
       NMapExtra.filter (fun k _ => negb (NMap.mem k ctx)) (prog_procedures p);
     prog_buffers :=
       NMapExtra.filter (fun k _ => negb (NMap.mem k ctx)) (prog_buffers p);
     prog_main := prog_main p |}.

Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Let G := init_genv (partialize p ctx).

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  (* the context is part of p *)
  Hypothesis valid_context:
    forall C CI, NMap.MapsTo C CI ctx -> NMap.MapsTo C CI (prog_interface p).

  Definition sem :=
    @Semantics_gen state global_env (step ctx)
                   (initial_state (partialize p ctx) G ctx)
                   (final_state G) G.
End Semantics.
End PS.

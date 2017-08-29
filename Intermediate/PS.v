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

(* The split between program and context is represented by the domain of the
   entrypoints map. *)
Definition is_program_component G C := NMap.In C (genv_entrypoints G).
Definition is_context_component G C := ~ is_program_component G C.

Definition initial_state
           (G: global_env)
           (mainC: Component.id) (mainP: Procedure.id)
           (s: state) : Prop :=
  match s with
  | PC (gps, mem, regs, pc) =>
    (* the global protected stack is empty *)
    gps = [] /\
    (* the program counter is pointing to the start of the main procedure *)
    EntryPoint.get mainC mainP (genv_entrypoints G) = Some (Pointer.block pc) /\
    Pointer.component pc = mainC /\
    Pointer.offset pc = 0 /\
    (* each program component has its own memory *)
    (forall C, is_program_component G C -> NMap.In C mem)
  | CC (pgps, mem, C) execst =>
    (* the global protected stack is empty *)
    pgps = [] /\
    (* the execution didn't go wrong *)
    execst = Normal /\
    (* the executing component is the main one *)
    C = mainC /\
    (* each program component has its own memory *)
    (forall C, is_program_component G C -> NMap.In C mem)
  end.

Definition final_state (G: global_env) (s: state) (r: nat) : Prop :=
  match s with
  | PC (gps, mem, regs, pc) => executing G pc IHalt
  | CC (pgps, mem, C) execst => execst = Normal
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

Inductive step (G : global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall G' pgps (mem mem' wmem wmem' : Memory.t) Cmem'
      (regs regs' : Register.t) (pc pc' : Pointer.t),
      (* G' has the same interface as G, but it can contain more
         information regarding procedures and entrypoints *)
      genv_extension G' G ->
      (* wmem contains mem *)
      (forall C Cmem, NMap.MapsTo C Cmem mem -> NMap.MapsTo C Cmem wmem) ->
      (* wmem has the context components memories *)
      (forall C, is_context_component G C -> NMap.In C wmem) ->
      (* the complete semantics steps silently with the extended versions of
         memory and global environment
         NOTE that the stack (gps) is not related to the partial one (pgps) *)
      (exists gps, CS.step G' (gps,wmem,regs,pc) E0 (gps,wmem',regs',pc')) ->
      (* mem' is mem with the updated version of the current
         executing component's memory *)
      NMap.MapsTo (Pointer.component pc) Cmem' wmem' ->
      NMap.Equal mem' (NMap.add (Pointer.component pc) Cmem' mem) ->
      step G (PC (pgps,mem,regs,pc)) E0 (PC (pgps,mem',regs',pc'))

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
      step G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,Register.invalidate regs,pc'))

| Program_Internal_Return:
    forall pgps pgps' mem regs pc pc' C' b o val,
      let C := Pointer.component pc in
      executing G pc IReturn ->
      pgps = (C', Some (b,o)) :: pgps' ->
      C' <> C ->
      is_program_component G C' ->
      Register.get R_COM regs = Int val ->
      let t := [ERet C val C'] in
      step G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,Register.invalidate regs,pc'))

| Program_External_Call:
    forall pgps pgps' mem regs pc C' b o P val,
      let C := Pointer.component pc in
      executing G pc (ICall C' P) ->
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_context_component G C' ->
      pgps' = (C, Some (b,o)) :: pgps ->
      Register.get R_COM regs = Int val ->
      let t := [ECall C P val C'] in
      step G (PC (pgps,mem,regs,pc)) t (CC (pgps',mem,C') Normal)

| Program_External_Return:
    forall pgps pgps' mem regs pc C' val,
      let C := Pointer.component pc in
      executing G pc IReturn ->
      C' <> C ->
      is_context_component G C' ->
      pgps = (C', None) :: pgps' ->
      Register.get R_COM regs = Int val ->
      let t := [ERet C val C'] in
      step G (PC (pgps,mem,regs,pc)) t (CC (pgps',mem,C') Normal)

| Context_Epsilon:
    forall pgps mem C,
      step G (CC (pgps,mem,C) Normal) E0 (CC (pgps,mem,C) Normal)

| Context_GoesWrong:
    forall pgps mem C,
      step G (CC (pgps,mem,C) Normal) E0 (CC (pgps,mem,C) WentWrong)

| Context_Internal_Call:
    forall pgps pgps' mem C C' P call_arg,
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_context_component G C' ->
      pgps' = (C, None) :: pgps ->
      let t := [ECall C P call_arg C'] in
      step G (CC (pgps,mem,C) Normal) t (CC (pgps',mem,C') Normal)

| Context_Internal_Return:
    forall pgps pgps' mem C C' return_val,
      C' <> C ->
      is_context_component G C' ->
      pgps = (C', None) :: pgps' ->
      let t := [ERet C return_val C'] in
      step G (CC (pgps,mem,C) Normal) t (CC (pgps',mem,C') Normal)

| Context_External_Call:
    forall pgps pgps' mem regs C C' P b val,
      C' <> C ->
      exported_procedure (genv_interface G) C' P ->
      imported_procedure (genv_interface G) C C' P ->
      is_program_component G C' ->
      pgps' = (C, None) :: pgps ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->
      Register.get R_COM regs = Int val ->
      let t := [ECall C P val C'] in
      let pc' := (C', b, 0) in
      step G (CC (pgps,mem,C) Normal) t (PC (pgps',mem,regs,pc'))

| Context_External_Return:
    forall pgps pgps' mem regs C C' b o val,
      pgps = (C', Some (b,o)) :: pgps' ->
      is_program_component G C' ->
      Register.get R_COM regs = Int val ->
      let t := [ERet C val C'] in
      step G (CC (pgps,mem,C) Normal) t (PC (pgps',mem,regs, (C',b,o))).

Definition partialize (p: program) (ctx: Program.interface)
           (mainC: Component.id) (mainP: Procedure.id)
  : program :=
  {| prog_interface := NMapExtra.update (prog_interface p) ctx;
     prog_procedures := prog_procedures p;
     prog_buffers := prog_buffers p;
     prog_main := (mainC, mainP) |}.

Section Semantics.
  Variable p: program.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.
  Variable context_interface : Program.interface.

  Definition partial_program := partialize p context_interface mainC mainP.

  Let G := init_genv partial_program.

  Definition sem :=
    @Semantics_gen state global_env step
                   (initial_state G (fst (prog_main partial_program))
                                    (snd (prog_main partial_program)))
                   (final_state G) G.
End Semantics.

Definition maps_match_on {T : Type} split (map map' : NMap.t T) :=
  forall C Cmap,
    In C split ->
    (NMap.MapsTo C Cmap map <-> NMap.MapsTo C Cmap map').

Lemma maps_match_on_reflexive:
  forall T split (mem: NMap.t T),
    maps_match_on split mem mem.
Proof.
  unfold maps_match_on. intros.
  split; auto.
Qed.

End PS.

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

  Inductive exec_state : Type := Normal | WentWrong | Halted.

  Inductive state : Type :=
  | PC : program_state -> state
  | CC : context_state -> exec_state -> state.

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
      Pointer.offset pc = 0
    | CC (pgps, mem, C) execst =>
      (* the global protected stack is empty *)
      pgps = [] /\
      (* the execution didn't go wrong *)
      execst = Normal /\
      (* the executing component is the main one *)
      C = mainC
    end.

  Definition final_state (G: global_env) (s: state) (r: int) : Prop :=
    match s with
    | PC (gps, mem, regs, pc) => executing G pc IHalt
    | CC (pgps, mem, C) execst => execst = Halted
    end.

  Definition to_partial_frame pc frame : PartialPointer.t :=
    let '(C, b, o) := frame in
    if Util.Lists.mem C pc then
      (C, Some (b, o))
    else
      (C, None).

  Definition to_partial_stack (s : CS.stack) (pc : list Component.id) :=
    map (to_partial_frame pc) s.

  Lemma push_by_prog_preserves_partial_stack :
    forall s ps pc C b o,
      Util.Lists.mem C pc = true ->
      to_partial_stack s pc = ps ->
      to_partial_stack ((C,b,o)::s) pc = (C,Some (b,o)) :: ps.
  Proof.
    intros s ps pc C b o Hprogturn H.
    simpl. rewrite Hprogturn. rewrite H. reflexivity.
  Qed.

  Lemma push_by_context_preserves_partial_stack :
    forall s ps pc C b o,
      ~ (In C pc) ->
      to_partial_stack s pc = ps ->
      to_partial_stack ((C,b,o)::s) pc = (C,None) :: ps.
  Proof.
    intros s ps pc C b o Hprogturn Hpstack.
    simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
    rewrite Hprogturn. rewrite Hpstack. reflexivity.
  Qed.

  (* The split between program and context is represented by the domain of the
     entrypoints map. *)
  Definition is_program_component G C := NMap.In C (genv_entrypoints G).
  Definition is_context_component G C := ~ is_program_component G C.

  Inductive step (G : global_env) : state -> trace -> state -> Prop :=
  | Program_Epsilon:
      forall gps pgps
        (mem mem' wmem wmem' : Memory.t) cmem cmem'
        (regs regs' : Register.t) (pc pc' : Pointer.t),
        let C := Pointer.component pc in
        NMap.MapsTo C cmem wmem ->
        NMap.MapsTo C cmem' wmem' ->
        CS.step G (gps,wmem,regs,pc) E0 (gps,wmem',regs',pc') ->
        NMap.MapsTo C cmem mem ->
        NMap.MapsTo C cmem' mem' ->
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
        step G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,regs,pc'))

  | Program_Internal_Return:
      forall pgps pgps' mem regs pc pc' C' b o val,
        let C := Pointer.component pc in
        executing G pc IReturn ->
        pgps = (C', Some (b,o)) :: pgps' ->
        C' <> C ->
        is_program_component G C' ->
        Register.get R_COM regs = Int val ->
        let t := [ERet C val C'] in
        step G (PC (pgps,mem,regs,pc)) t (PC (pgps',mem,regs,pc'))

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

  | Context_Halt:
      forall pgps mem C,
        step G (CC (pgps,mem,C) Normal) E0 (CC (pgps,mem,C) Halted)

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

  Definition partialize (p: program) (split: list Component.id) : program :=
    {| prog_interface := prog_interface p;
       prog_procedures :=
         NMapExtra.filter
           (fun C _ => negb (count_occ eq_nat_dec split C =? 0))
           (prog_procedures p);
       prog_buffers :=
         NMapExtra.filter
           (fun C _ => negb (count_occ eq_nat_dec split C =? 0))
           (prog_buffers p) |}.

  Section Semantics.
    Variable p: program.
    Variable mainC: Component.id.
    Variable mainP: Procedure.id.

    Definition sem :=
      let G := init_env p in
      @Semantics_gen state global_env step
                     (initial_state G mainC mainP)
                     (final_state G) G.
  End Semantics.
End PS.
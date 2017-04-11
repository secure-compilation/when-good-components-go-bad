Require Import Common.
Require Import Machine.
Require Import Traces.
Require Import LTT.

Module PLTT.
  Include AbstractMachine.

  Definition stack := list (Component.id * option Memory.address).

  Definition program_state : Type :=
    (Component.id * stack * Memory.data * Register.data * Memory.address).
  Definition context_state : Type :=
    (Component.id * stack * Memory.data).

  Inductive partial_state : Type :=
    | PC : program_state -> partial_state
    | CC : context_state -> partial_state.

  Fixpoint to_partial_stack (s : LTT.stack) (pc : list Component.id)
    : PLTT.stack :=
    match s with
    | [] => []
    | (C,i) :: s' =>
      if existsb (fun C' => C =? C') pc then
        (C,Some i) :: to_partial_stack s' pc
      else
        (C,None) :: to_partial_stack s' pc
    end.

  Lemma push_by_prog_preserves_partial_stack :
    forall s ps pc C i,
      existsb (fun C' => C =? C') pc = true ->
      to_partial_stack s pc = ps ->
      to_partial_stack ((C,i)::s) pc = (C,Some i) :: ps.
  Proof.
    intros s ps pc C i Hprogturn H.
    simpl. rewrite Hprogturn. rewrite H. reflexivity.
  Qed.

  Lemma push_by_context_preserves_partial_stack :
    forall s ps pc C i,
      existsb (fun C' => C =? C') pc = false ->
      to_partial_stack s pc = ps ->
      to_partial_stack ((C,i)::s) pc = (C,None) :: ps.
  Proof.
    intros s ps pc C i Hprogturn H.
    simpl. rewrite Hprogturn. rewrite H. reflexivity.
  Qed.

  Definition is_program_component
             (C : Component.id)
             (E : EntryPoint.data) : Prop :=
    EntryPoint.mem C E = true.

  Definition is_context_component
             (C : Component.id)
             (E : EntryPoint.data) : Prop :=
    EntryPoint.mem C E = false.

  Reserved Notation "Is ; E |-PLTT s1 '=>[' t ']' s2" (at level 40).

  Inductive step (Is : Program.interface) (E : EntryPoint.data)
    : partial_state -> trace -> partial_state -> Prop :=

    | Program_Epsilon:
        forall C s ps mem mem' wmem wmem' cmem cmem' regs regs' pc pc',
          M.MapsTo C cmem wmem ->
          M.MapsTo C cmem' wmem' ->
          LTT.step Is E (C,s,wmem,regs,pc) E0 (C,s,wmem',regs',pc') ->
          M.MapsTo C cmem mem ->
          M.MapsTo C cmem' mem' ->
          Is;E |-PLTT (PC (C,ps,mem,regs,pc)) =>[E0] (PC (C,ps,mem',regs',pc'))

    | Program_Internal_Call:
        forall mem C pc regs d d' C' P,
          executing (Call C' P) C mem pc ->
          C' <> C ->
          call_exists Is C' P ->
          call_permitted Is C C' P ->
          is_program_component C' E ->
          d' = (C,Some (pc+1)) :: d ->
          let t := [ECall C P (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (PC (C,d,mem,regs,pc)) =>[t]
                      (PC (C',d',mem,regs,EntryPoint.get C' P E))

    | Program_Internal_Return:
        forall mem C C' pc pc' d d' regs,
          executing Return C mem pc ->
          is_program_component C' E ->
          d = (C',Some pc') :: d' ->
          let t := [ERet C (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (PC (C',d',mem,regs,pc'))

    | Program_External_Call:
        forall mem C pc regs d d' C' P,
          executing (Call C' P) C mem pc ->
          C' <> C ->
          call_exists Is C' P ->
          call_permitted Is C C' P ->
          is_context_component C' E ->
          d' = (C,Some (pc+1)) :: d ->
          let t := [ECall C P (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem))

    | Program_External_Return:
        forall mem C C' pc d d' regs,
          executing Return C mem pc ->
          d = (C',None) :: d' ->
          is_context_component C' E ->
          let t := [ERet C (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem))

    | Context_Internal_Call:
        forall mem C d d' C' P call_arg,
          C' <> C ->
          call_exists Is C' P ->
          call_permitted Is C C' P ->
          is_context_component C' E ->
          d' = (C,None) :: d ->
          let t := [ECall C P call_arg C'] in
          Is;E |-PLTT (CC (C,d,mem)) =>[t] (CC (C',d',mem))

    | Context_Internal_Return:
        forall mem C C' d d' return_val,
          C' <> C ->
          is_context_component C' E ->
          d = (C',None) :: d' ->
          let t := [ERet C return_val C'] in
          Is;E |-PLTT (CC (C,d,mem)) =>[t] (CC (C',d',mem))

    | Context_External_Call:
        forall mem C regs d d' C' P,
          C' <> C ->
          call_exists Is C' P ->
          call_permitted Is C C' P ->
          is_program_component C' E ->
          d' = (C,None) :: d ->
          let t := [ECall C P (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (CC (C,d,mem)) =>[t]
                      (PC (C',d',mem,regs,EntryPoint.get C' P E))

    | Context_External_Return:
        forall mem C C' pc' d d' regs,
          d = (C',Some pc') :: d' ->
          is_program_component C' E ->
          let t := [ERet C (Register.get Register.R_COM regs) C'] in
          Is;E |-PLTT (CC (C,d,mem)) =>[t] (PC (C',d',mem,regs,pc'))

  where "Is ; E |-PLTT s1 '=>[' t ']' s2" := (step Is E s1 t s2).
End PLTT.
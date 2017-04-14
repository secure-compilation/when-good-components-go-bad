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

Definition to_partial_frame pc frame : Component.id * option Memory.address :=
  match frame with (C,i) =>
    if Util.mem C pc then (C, Some i) else (C, None)
  end.

Definition to_partial_stack (s : LTT.stack) (pc : list Component.id) :=
  map (to_partial_frame pc) s.

Lemma push_by_prog_preserves_partial_stack :
  forall s ps pc C i,
    Util.mem C pc = true ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,i)::s) pc = (C,Some i) :: ps.
Proof.
  intros s ps pc C i Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_context_preserves_partial_stack :
  forall s ps pc C i,
    ~ (In C pc) ->
    to_partial_stack s pc = ps ->
    to_partial_stack ((C,i)::s) pc = (C,None) :: ps.
Proof.
  intros s ps pc C i Hprogturn Hpstack.
  simpl. apply Util.not_in_implies_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

Record global_env := mkGlobalEnv {
  get_interfaces : Program.interface;
  get_entrypoints : EntryPoint.data;
  get_split : list Component.id
}.

Record global_env_wf (G : global_env) := mkGlobalEnvWF {
  entrypoints_exist :
    forall CI C,
      In CI (get_interfaces G) ->
      Component.name CI = C ->
      M.In C (get_entrypoints G) /\
      exists addrs, M.MapsTo C addrs (get_entrypoints G);
  split_wellformed :
    forall C,
      In C (get_split G) ->
      exists CI, In CI (get_interfaces G) /\ Component.name CI = C
}.

Definition is_program_component C (prog_comps : list Component.id) :=
  In C prog_comps.
Definition is_context_component C (prog_comps : list Component.id) :=
  ~ (In C prog_comps).

Reserved Notation "G |-PLTT s1 '=>[' t ']' s2" (at level 40).

Inductive step (G : global_env)
  : partial_state -> trace -> partial_state -> Prop :=
| Program_Epsilon:
    forall C s ps mem mem' wmem wmem' cmem cmem' regs regs' pc pc',
      M.MapsTo C cmem wmem ->
      M.MapsTo C cmem' wmem' ->
      let G' := LTT.mkGlobalEnv (get_interfaces G) (get_entrypoints G) in
      LTT.step G' (C,s,wmem,regs,pc) E0 (C,s,wmem',regs',pc') ->
      M.MapsTo C cmem mem ->
      M.MapsTo C cmem' mem' ->
      G |-PLTT (PC (C,ps,mem,regs,pc)) =>[E0] (PC (C,ps,mem',regs',pc'))

| Program_Internal_Call:
    forall mem C pc regs d d' C' P,
      executing (Call C' P) C mem pc ->
      C' <> C ->
      call_is_public_and_exists (get_interfaces G) C' P ->
      call_is_in_imports (get_interfaces G) C C' P ->
      is_program_component C' (get_split G) ->
      d' = (C,Some (pc+1)) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t]
               (PC (C',d',mem,regs,EntryPoint.get C' P (get_entrypoints G)))

| Program_Internal_Return:
    forall mem C C' pc pc' d d' regs,
      executing Return C mem pc ->
      is_program_component C' (get_split G) ->
      d = (C',Some pc') :: d' ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (PC (C',d',mem,regs,pc'))

| Program_External_Call:
    forall mem C pc regs d d' C' P,
      executing (Call C' P) C mem pc ->
      C' <> C ->
      call_is_public_and_exists (get_interfaces G) C' P ->
      call_is_in_imports (get_interfaces G) C C' P ->
      is_context_component C' (get_split G) ->
      d' = (C,Some (pc+1)) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem))

| Program_External_Return:
    forall mem C C' pc d d' regs,
      executing Return C mem pc ->
      d = (C',None) :: d' ->
      is_context_component C' (get_split G) ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem))

| Context_Internal_Call:
    forall mem C d d' C' P call_arg,
      C' <> C ->
      call_is_public_and_exists (get_interfaces G) C' P ->
      call_is_in_imports (get_interfaces G) C C' P ->
      is_context_component C' (get_split G) ->
      d' = (C,None) :: d ->
      let t := [ECall C P call_arg C'] in
      G |-PLTT (CC (C,d,mem)) =>[t] (CC (C',d',mem))

| Context_Internal_Return:
    forall mem C C' d d' return_val,
      C' <> C ->
      is_context_component C' (get_split G) ->
      d = (C',None) :: d' ->
      let t := [ERet C return_val C'] in
      G |-PLTT (CC (C,d,mem)) =>[t] (CC (C',d',mem))

| Context_External_Call:
    forall mem C regs d d' C' P,
      C' <> C ->
      call_is_public_and_exists (get_interfaces G) C' P ->
      call_is_in_imports (get_interfaces G) C C' P ->
      is_program_component C' (get_split G) ->
      d' = (C,None) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (CC (C,d,mem)) =>[t]
               (PC (C',d',mem,regs,EntryPoint.get C' P (get_entrypoints G)))

| Context_External_Return:
    forall mem C C' pc' d d' regs,
      d = (C',Some pc') :: d' ->
      is_program_component C' (get_split G) ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (CC (C,d,mem)) =>[t] (PC (C',d',mem,regs,pc'))

where "G |-PLTT s1 '=>[' t ']' s2" := (step G s1 t s2).

End PLTT.
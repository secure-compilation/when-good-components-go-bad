Require Import Common.
Require Import Machine.
Require Import Events.
Require Import LTT.
Require Import Smallstep.

Module PLTT.

Include AbstractMachine.

Record program := {
  prog_interface : Program.interface;
  prog_memory : Memory.data;
  prog_entrypoints : EntryPoint.data;
  prog_split : list Component.id;
  prog_entrypoints_wf :
    forall CI C,
      In CI prog_interface ->
      Component.name CI = C ->
      In C prog_split ->
      M.In C prog_entrypoints /\
      exists addrs, M.MapsTo C addrs prog_entrypoints;
  prog_split_wf :
    forall C,
      In C prog_split ->
      exists CI, In CI prog_interface /\ Component.name CI = C
}.

Definition stack := list (Component.id * option Memory.address).

Definition program_state : Type :=
  Component.id * stack * Memory.data * Register.data * Memory.address.
Definition context_state : Type :=
  Component.id * stack * Memory.data.

Inductive exec_state : Type :=
| Normal
| WentWrong.

Inductive partial_state : Type :=
| PC : program_state -> partial_state
| CC : context_state -> exec_state -> partial_state.

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
  simpl. apply Util.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

Record global_env := mkGlobalEnv {
  genv_interfaces : Program.interface;
  genv_entrypoints : EntryPoint.data;
  genv_split : list Component.id;
}.

Definition initial_state_for
           (p : program)
           (split : list Component.id) : partial_state :=
  let mem := prog_memory p in
  let E := prog_entrypoints p in
  let split := prog_split p in
  if Util.mem 0 split then
    PC (0, [], mem, Register.empty, EntryPoint.get 0 0 E)
  else
    CC (0, [], mem) Normal.

Definition initial_state p (s : partial_state) : Prop :=
  match s with
  | PC (C, d, mem, regs, pc) =>
    C = 0 /\ d = [] /\ regs = Register.empty /\
    pc = EntryPoint.get 0 0 (prog_entrypoints p)
  | CC (C, d, mem) state =>
    C = 0 /\ d = []
  end.

Definition final_state (s : partial_state) : Prop :=
  match s with
  | PC (C, d, mem, regs, pc) =>
    executing Halt C mem pc
  | CC (C, d, mem) state =>
    state = Normal
  end.

Definition is_program_component C (prog_comps : list Component.id) :=
  In C prog_comps.
Definition is_context_component C (prog_comps : list Component.id) :=
  ~ (In C prog_comps).

Definition maps_match_on {T : Type} split (map map' : M.t T) :=
  forall C Cmap,
    PLTT.is_program_component C split ->
    (M.MapsTo C Cmap map <-> M.MapsTo C Cmap map').

Reserved Notation "G |-PLTT s1 '=>[' t ']' s2" (at level 40).

Inductive step (G : global_env)
  : partial_state -> trace -> partial_state -> Prop :=
| Program_Epsilon:
    forall E C s ps
           mem mem' wmem wmem' cmem cmem'
           regs regs' pc pc',
      M.MapsTo C cmem wmem ->
      M.MapsTo C cmem' wmem' ->
      maps_match_on (genv_split G) E (genv_entrypoints G) ->
      let G' := LTT.mkGlobalEnv (genv_interfaces G) E in
      LTT.step G' (C,s,wmem,regs,pc) E0 (C,s,wmem',regs',pc') ->
      M.MapsTo C cmem mem ->
      M.MapsTo C cmem' mem' ->
      G |-PLTT (PC (C,ps,mem,regs,pc)) =>[E0] (PC (C,ps,mem',regs',pc'))

| Program_Internal_Call:
    forall mem C pc regs d d' C' P,
      executing (Call C' P) C mem pc ->
      C' <> C ->
      call_is_public_and_exists (genv_interfaces G) C' P ->
      call_is_in_imports (genv_interfaces G) C C' P ->
      is_program_component C' (genv_split G) ->
      d' = (C,Some (pc+1)) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t]
               (PC (C',d',mem,regs,EntryPoint.get C' P (genv_entrypoints G)))

| Program_Internal_Return:
    forall mem C C' pc pc' d d' regs,
      executing Return C mem pc ->
      C' <> C ->
      is_program_component C' (genv_split G) ->
      d = (C',Some pc') :: d' ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (PC (C',d',mem,regs,pc'))

| Program_External_Call:
    forall mem C pc regs d d' C' P,
      executing (Call C' P) C mem pc ->
      C' <> C ->
      call_is_public_and_exists (genv_interfaces G) C' P ->
      call_is_in_imports (genv_interfaces G) C C' P ->
      is_context_component C' (genv_split G) ->
      d' = (C,Some (pc+1)) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem) Normal)

| Program_External_Return:
    forall mem C C' pc d d' regs,
      executing Return C mem pc ->
      C' <> C ->
      is_context_component C' (genv_split G) ->
      d = (C',None) :: d' ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (PC (C,d,mem,regs,pc)) =>[t] (CC (C',d',mem) Normal)

| Context_Epsilon:
    forall mem C d,
      G |-PLTT (CC (C,d,mem) Normal) =>[E0] (CC (C,d,mem) Normal)

| Context_GoesWrong:
    forall mem C d,
      G |-PLTT (CC (C,d,mem) Normal) =>[E0] (CC (C,d,mem) WentWrong)

| Context_Internal_Call:
    forall mem C d d' C' P call_arg,
      C' <> C ->
      call_is_public_and_exists (genv_interfaces G) C' P ->
      call_is_in_imports (genv_interfaces G) C C' P ->
      is_context_component C' (genv_split G) ->
      d' = (C,None) :: d ->
      let t := [ECall C P call_arg C'] in
      G |-PLTT (CC (C,d,mem) Normal) =>[t] (CC (C',d',mem) Normal)

| Context_Internal_Return:
    forall mem C C' d d' return_val,
      C' <> C ->
      is_context_component C' (genv_split G) ->
      d = (C',None) :: d' ->
      let t := [ERet C return_val C'] in
      G |-PLTT (CC (C,d,mem) Normal) =>[t] (CC (C',d',mem) Normal)

| Context_External_Call:
    forall mem C regs d d' C' P,
      C' <> C ->
      call_is_public_and_exists (genv_interfaces G) C' P ->
      call_is_in_imports (genv_interfaces G) C C' P ->
      is_program_component C' (genv_split G) ->
      d' = (C,None) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      G |-PLTT (CC (C,d,mem) Normal) =>[t]
               (PC (C',d',mem,regs,EntryPoint.get C' P (genv_entrypoints G)))

| Context_External_Return:
    forall mem C C' pc' d d' regs,
      d = (C',Some pc') :: d' ->
      is_program_component C' (genv_split G) ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-PLTT (CC (C,d,mem) Normal) =>[t] (PC (C',d',mem,regs,pc'))

where "G |-PLTT s1 '=>[' t ']' s2" := (step G s1 t s2).

Lemma maps_match_on_reflexive :
  forall T split (map : M.t T),
  maps_match_on split map map.
Proof.
  split; intros; auto.
Qed.

Lemma maps_match_on_symmetric :
  forall T split (map1 map2 : M.t T),
  maps_match_on split map1 map2 ->
  maps_match_on split map2 map1.
Proof.
  intros ? split map1 map2 Hmaps_match.
  split; intro; apply Hmaps_match; auto.
Qed.

Hint Resolve maps_match_on_reflexive.
Hint Resolve maps_match_on_symmetric.

Lemma update_related_memories_generic :
  forall split mem1 mem2 C Cmem C' addr val,
    maps_match_on split mem1 mem2 ->
    is_program_component C split ->
    M.MapsTo C Cmem (Memory.set mem1 C' addr val) ->
    M.MapsTo C Cmem (Memory.set mem2 C' addr val).
Proof.
  intros split mem1 mem2 C Cmem C' addr val.
  intros Hmems_match HCorigin HCmem.
  unfold Memory.set.
  unfold Memory.set in HCmem.
  destruct (C =? C') eqn:HeqCC'.
    + apply beq_nat_true in HeqCC'. subst.
      destruct (M.find (elt:=list nat) C' mem2) eqn:Hfind.
      * apply M.find_2 in Hfind. apply Hmems_match in Hfind.
        ** rewrite (M.find_1 Hfind) in HCmem.
           apply M.find_2.
           apply M.find_1 in HCmem.
           rewrite <- HCmem.
           rewrite F.add_eq_o, F.add_eq_o;
             reflexivity.
        ** assumption.
      * apply Hmems_match.
        ** assumption.
        ** assert (M.find (elt:=list nat) C' mem1 = None).
           { destruct (M.find (elt:=list nat) C' mem1) eqn:Hfind'.
             *** exfalso.
                 apply F.not_find_in_iff in Hfind. apply Hfind.
                 exists l. apply Hmems_match.
                 **** assumption.
                 **** apply M.find_2. assumption.
             *** reflexivity. }
           rewrite H in HCmem. assumption.
    + apply beq_nat_false in HeqCC'.
      destruct (M.find (elt:=list nat) C' mem2) eqn:Hfind.
      * apply M.add_2.
        ** unfold not. intro. apply HeqCC'. symmetry. apply H.
        ** apply Hmems_match.
           *** assumption.
           *** destruct (M.find (elt:=list nat) C' mem1) eqn:Hfind'.
               **** eapply M.add_3.
                    ***** intro. apply HeqCC'. symmetry. apply H.
                    ***** apply HCmem.
               **** assumption.
      * apply Hmems_match.
        ** assumption.
        ** destruct (M.find (elt:=list nat) C' mem1) eqn:Hfind'.
           *** eapply M.add_3.
               **** intro. apply HeqCC'. symmetry. apply H.
               **** apply HCmem.
           *** assumption.
Qed.

Lemma update_related_memories :
  forall split mem1 mem1' mem2 mem2' C addr val,
    maps_match_on split mem1 mem2 ->
    mem1' = Memory.set mem1 C addr val ->
    mem2' = Memory.set mem2 C addr val ->
    maps_match_on split mem1' mem2'.
Proof.
  intros split mem1 mem1' mem2 mem2' C addr val.
  intros Hmems_match Hmem1' Hmem2'.
  unfold PLTT.maps_match_on.
  intros C0 C0mem HC0_origin.
  split;
    intro HC0map;
    [ rewrite Hmem2';
      rewrite Hmem1' in HC0map;
      apply update_related_memories_generic with
          (split:=split) (mem1:=mem1) (mem2:=mem2)
    | rewrite Hmem1';
      rewrite Hmem2' in HC0map;
      apply update_related_memories_generic with
          (split:=split) (mem1:=mem2) (mem2:=mem1)
    ];
    auto.
Qed.

Section SEMANTICS.
  Variable p : program.

  Definition semantics :=
    @Semantics_gen partial_state global_env
                   step
                   (initial_state p)
                   final_state
                   (mkGlobalEnv (prog_interface p)
                                (prog_entrypoints p)
                                (prog_split p)).
End SEMANTICS.

(* if entrypoints are well-formed, then they remain
   well-formed even if we consider only the ones relative
   to the components in the split *)
Lemma entrypoints_exist_wrt_split split :
  forall p CI C,
    In CI (LTT.prog_interface p) ->
    Component.name CI = C ->
    In C split ->
    M.In C (LTT.prog_entrypoints p) /\
  exists addrs, M.MapsTo C addrs (LTT.prog_entrypoints p).
Proof.
  intros p CI C.
  intros HCI_in_I HCI_name_is_C HC_in_split.
  apply (LTT.prog_entrypoints_wf p) with CI; assumption.
Qed.

Definition apply_split (p : LTT.program) split splitWF :=
  {| prog_interface := LTT.prog_interface p;
     prog_memory := LTT.prog_memory p;
     prog_entrypoints := LTT.prog_entrypoints p;
     prog_split := split;
     prog_entrypoints_wf :=
       entrypoints_exist_wrt_split split p;
     prog_split_wf := splitWF |}.
End PLTT.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Module PS.

Import Source.

Definition stack : Type := list (Component.id * option (value * CS.cont)).

Definition program_state : Type := Component.id * stack * Memory.t * CS.cont * expr.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive exec_state : Type := Normal | WentWrong | Halted.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state.

(* The split between program and context is represented by the domain of the
   procedures map. *)
Definition is_program_component G C := NMap.In C (genv_procedures G).
Definition is_context_component G C := ~ is_program_component G C.

Inductive kstep (G: global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall C s s' mem mem' cmem cmem' wmem wmem' k k' e e',
      NMap.MapsTo C cmem wmem ->
      NMap.MapsTo C cmem' wmem' ->
      CS.kstep G (C,s',wmem,k,e) E0 (C,s',wmem',k',e') ->
      NMap.MapsTo C cmem mem ->
      NMap.MapsTo C cmem' mem' ->
      kstep G (PC (C,s,mem,k,e)) E0 (PC (C,s,mem',k',e'))

| Program_Internal_Call:
    forall C s mem mem' k C' P v C'_procs P_expr b b' old_call_arg,
      is_program_component G C' ->
      (* retrieve the procedure code *)
      NMap.find C' (genv_procedures G) = Some C'_procs ->
      NMap.find P C'_procs = Some P_expr ->
      (* save the old call argument *)
      NMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      (* place the call argument in the target memory *)
      NMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int v) = Some mem' ->
      let t := if C =? C' then E0 else [ECall C P v C'] in
      kstep G (PC (C, s, mem, Kcall C' P k, E_val (Int v)))
            t (PC (C', (C, Some (old_call_arg, k)) :: s, mem', Kstop, P_expr))

| Program_Internal_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component G C' ->
      (* restore the old call argument *)
      NMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := if C =? C' then E0 else [ERet C v C'] in
      kstep G (PC (C, (C', Some (old_call_arg, k)) :: s, mem, Kstop, E_val (Int v)))
            t (PC (C', s, mem', k, E_val (Int v)))

| Program_External_Call:
    forall C s mem k C' P v b old_call_arg,
      is_context_component G C' ->
      (* save the old call argument *)
      NMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      let t := [ECall C P v C'] in
      kstep G (PC (C, s, mem, Kcall C' P k, E_val (Int v)))
            t (CC (C', (C, Some (old_call_arg,k)) :: s, mem) Normal)

| Program_External_Return:
    forall C s mem k v C' old_call_arg,
      is_context_component G C' ->
      let t := [ERet C v C'] in
      kstep G (PC (C, (C', Some (old_call_arg, k)) :: s, mem, Kstop, E_val (Int v)))
            t (CC (C', s, mem) Normal)

| Context_Epsilon:
    forall s mem C,
      kstep G (CC (C,s,mem) Normal) E0 (CC (C,s,mem) Normal)

| Context_GoesWrong:
    forall s mem C,
      kstep G (CC (C,s,mem) Normal) E0 (CC (C,s,mem) WentWrong)

| Context_Halt:
    forall s mem C,
      kstep G (CC (C,s,mem) Normal) E0 (CC (C,s,mem) Halted)

| Context_Internal_Call:
    forall s s' mem C C' P call_arg,
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_context_component G C' ->
      s' = (C, None) :: s ->
      let t := [ECall C P call_arg C'] in
      kstep G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_Internal_Return:
    forall s s' mem C C' return_val,
      C' <> C ->
      is_context_component G C' ->
      s = (C', None) :: s' ->
      let t := [ERet C return_val C'] in
      kstep G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_External_Call:
    forall s s' mem mem' C C' P C'_procs P_expr b' val,
      C' <> C ->
      exported_procedure (genv_interface G) C' P ->
      imported_procedure (genv_interface G) C C' P ->
      is_program_component G C' ->
      s' = (C, None) :: s ->
      (* retrieve the procedure code *)
      NMap.find C' (genv_procedures G) = Some C'_procs ->
      NMap.find P C'_procs = Some P_expr ->
      (* place the call argument in the target memory *)
      NMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int val) = Some mem' ->
      let t := [ECall C P val C'] in
      kstep G (CC (C,s,mem) Normal) t (PC (C',s',mem,Kstop,P_expr))

| Context_External_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component G C' ->
      (* restore the old call argument *)
      NMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := [ERet C v C']in
      kstep G (CC (C, (C', Some (old_call_arg, k)) :: s, mem) Normal)
            t (PC (C', s, mem', k, E_val (Int v))).

End PS.
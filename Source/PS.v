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
| CC : context_state -> exec_state -> state
with exec_state : Type := Normal | WentWrong.

Module SC := Source.CS.CS.

Axiom partialize_state: Program.interface -> SC.state -> state. 
Axiom partialize_stack: Program.interface -> SC.stack -> stack -> Prop.

Inductive initial_state2 (p: program) (ctx: Program.interface): state -> Prop :=
| initial_state_intro: forall ps cs,
    SC.initial_state p cs /\
    ps = partialize_state ctx cs ->
    initial_state2 p ctx ps.

Inductive final_state2 (ctx: Program.interface) (ps: state) (r: int) : Prop :=
| final_state_intro:
    forall cs,
      SC.final_state2 cs r ->
      ps = partialize_state ctx cs ->
      final_state2 ctx ps r.

Definition initial_state (p: program) (st: state) : Prop :=
  match st with
  | PC (C, s, mem, k, e) =>
    (* the executing component is the main one *)
    C = fst (prog_main p) /\
    (* the stack is empty *)
    s = [] /\
    (* mem exaclty contains all components memories and it comes from the init routine *)
    (forall C, ZMap.In C (prog_interface p) <-> ZMap.In C mem) /\
    (let '(_, m) := init_all p in mem = m) /\
    (* the expression under evaluation is the main procedure *)
    (exists main_procs,
        ZMap.find (fst (prog_main p)) (prog_procedures p) = Some main_procs /\
        ZMap.find (snd (prog_main p)) main_procs = Some e) /\
    (* the continuation is stop *)
    k = Kstop
  | CC (C, s, mem) execst =>
    (* the executing component is the main one *)
    C = fst (prog_main p) /\
    (* the stack is empty *)
    s = [] /\
    (* mem exaclty contains all components memories and it comes from the init routine *)
    (forall C, ZMap.In C (prog_interface p) <-> ZMap.In C mem) /\
    (let '(_, m) := init_all p in mem = m) /\
    (* the execution didn't go wrong *)
    execst = Normal
  end.

Definition final_state (st: state) (r: nat) : Prop :=
  match st with
  | PC (C, s, mem, k, e) =>
    e = E_exit
  | CC (C, s, mem) execst =>
    execst = Normal
  end.

Definition is_program_component G C := ZMap.In C (genv_interface G).
Definition is_context_component (ctx: Program.interface) C := ZMap.In C ctx.

Inductive kstep (ctx: Program.interface) (G: global_env) : state -> trace -> state -> Prop :=
| Program_Epsilon:
    forall G' C s mem mem' Cmem' wmem wmem' k k' e e',
      (* G' is an extension of G w.r.t. ctx *)
      (* 1) the interface is G plus ctx *)
      ZMap.Equal (genv_interface G') (ZMapExtra.update (genv_interface G) ctx) ->
      (* 2) the procedures are the same of G plus some new ones for ctx *)
      (forall C Cprocs, ZMap.MapsTo C Cprocs (genv_procedures G') <->
                   (ZMap.MapsTo C Cprocs (genv_procedures G) \/
                    (ZMap.In C ctx /\ ~ ZMap.In C (genv_procedures G)))) ->
      (* 3) the buffers are the same of G plus some new ones for ctx *)
      (forall C Cbufs, ZMap.MapsTo C Cbufs (genv_buffers G') <->
                  (ZMap.MapsTo C Cbufs (genv_buffers G) \/
                   (ZMap.In C ctx /\ ~ ZMap.In C (genv_buffers G)))) ->

      (* wmem is an extension of mem w.r.t. ctx *)
      (* 1) wmem contains mem *)
      (forall C Cmem, ZMap.MapsTo C Cmem mem -> ZMap.MapsTo C Cmem wmem) ->
      (* 2) wmem has the context components memories *)
      (forall C, is_context_component ctx C -> ZMap.In C wmem) ->
      (* 3) wmem extends mem exactly w.r.t. ctx *)
      (forall C Cmem, ZMap.MapsTo C Cmem wmem <->
                 (ZMap.MapsTo C Cmem mem \/
                  (is_context_component ctx C /\ ~ ZMap.In C mem))) ->

      (* the complete semantics steps silently with the extended versions of
         memory and global environment
         NOTE that the stack (s) is not related to the partial one (ps) *)
      (exists ps, CS.kstep G' (C,ps,wmem,k,e) E0 (C,ps,wmem',k',e')) ->

      (* mem' is mem with the updated version of the current
         executing component's memory *)
      ZMap.MapsTo C Cmem' wmem' ->
      ZMap.Equal mem' (ZMap.add C Cmem' mem) ->

      kstep ctx G (PC (C,s,mem,k,e)) E0 (PC (C,s,mem',k',e'))

| Program_External_Load_In_Program:
    forall C s mem k ptr v,
      Pointer.component ptr <> C ->
      is_program_component G (Pointer.component ptr) ->
      Memory.load mem ptr = Some v ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      kstep ctx G
            (PC (C, s, mem, Kderef k, E_val (Ptr ptr))) t
            (PC (C, s, mem, k, E_val v))

| Program_External_Load_In_Context:
    forall C s mem k ptr v,
      Pointer.component ptr <> C ->
      is_context_component ctx (Pointer.component ptr) ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      kstep ctx G
            (PC (C, s, mem, Kderef k, E_val (Ptr ptr))) t
            (PC (C, s, mem, k, E_val v))

| Program_Internal_Call:
    forall C s mem mem' k C' P v C'_procs P_expr b b' old_call_arg,
      is_program_component G C' ->
      (* retrieve the procedure code *)
      ZMap.find C' (genv_procedures G) = Some C'_procs ->
      ZMap.find P C'_procs = Some P_expr ->
      (* save the old call argument *)
      ZMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      (* place the call argument in the target memory *)
      ZMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int v) = Some mem' ->
      let t := if C =? C' then E0 else [ECall C P v C'] in
      kstep ctx G
            (PC (C, s, mem, Kcall C' P k, E_val (Int v))) t
            (PC (C', (C, Some (old_call_arg, k)) :: s, mem', Kstop, P_expr))

| Program_Internal_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component G C' ->
      (* restore the old call argument *)
      ZMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := if C =? C' then E0 else [ERet C v C'] in
      kstep ctx G
            (PC (C, (C', Some (old_call_arg, k)) :: s, mem, Kstop, E_val (Int v))) t
            (PC (C', s, mem', k, E_val (Int v)))

| Program_External_Call:
    forall C s mem k C' P v b old_call_arg,
      is_context_component ctx C' ->
      (* save the old call argument *)
      ZMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      let t := [ECall C P v C'] in
      kstep ctx G
            (PC (C, s, mem, Kcall C' P k, E_val (Int v))) t
            (CC (C', (C, Some (old_call_arg,k)) :: s, mem) Normal)

| Program_External_Return:
    forall C s mem k v C' old_call_arg,
      is_context_component ctx C' ->
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

| Context_External_Load_In_Context:
    forall s mem C ptr,
      Pointer.component ptr <> C ->
      is_context_component ctx (Pointer.component ptr) ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      kstep ctx G (CC (C,s,mem) Normal) t (CC (C, s, mem) Normal)

| Context_External_Load_In_Program:
    forall s mem C ptr v,
      Pointer.component ptr <> C ->
      is_program_component G (Pointer.component ptr) ->
      Memory.load mem ptr = Some v ->
      (* TODO fix the read value in the event *)
      let t := [ELoad C 0 (Pointer.component ptr)] in
      kstep ctx G (CC (C, s, mem) Normal) t (CC (C, s, mem) Normal)

| Context_Internal_Call:
    forall s s' mem C C' P call_arg,
      C' <> C ->
      imported_procedure (genv_interface G) C C' P ->
      is_context_component ctx C' ->
      s' = (C, None) :: s ->
      let t := [ECall C P call_arg C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_Internal_Return:
    forall s s' mem C C' return_val,
      C' <> C ->
      is_context_component ctx C' ->
      s = (C', None) :: s' ->
      let t := [ERet C return_val C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (CC (C',s',mem) Normal)

| Context_External_Call:
    forall s s' mem mem' C C' P C'_procs P_expr b' val,
      C' <> C ->
      exported_procedure (genv_interface G) C' P ->
      imported_procedure (genv_interface G) C C' P ->
      is_program_component G C' ->
      s' = (C, None) :: s ->
      (* retrieve the procedure code *)
      ZMap.find C' (genv_procedures G) = Some C'_procs ->
      ZMap.find P C'_procs = Some P_expr ->
      (* place the call argument in the target memory *)
      ZMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int val) = Some mem' ->
      let t := [ECall C P val C'] in
      kstep ctx G (CC (C,s,mem) Normal) t (PC (C',s',mem,Kstop,P_expr))

| Context_External_Return:
    forall C s mem mem' k v C' old_call_arg b,
      is_program_component G C' ->
      (* restore the old call argument *)
      ZMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
      let t := [ERet C v C'] in
      kstep ctx G
            (CC (C, (C', Some (old_call_arg, k)) :: s, mem) Normal) t
            (PC (C', s, mem', k, E_val (Int v))).

Definition partialize (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       ZMapExtra.diff (prog_interface p) ctx;
     prog_procedures :=
       ZMapExtra.filter (fun C _ => negb (ZMap.mem C ctx)) (prog_procedures p);
     prog_buffers :=
       ZMapExtra.filter (fun C _ => negb (ZMap.mem C ctx)) (prog_buffers p);
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
    forall C CI, ZMap.MapsTo C CI ctx -> ZMap.MapsTo C CI (prog_interface p).

  Definition sem :=
    @Semantics_gen state global_env (kstep ctx)
                   (initial_state (partialize p ctx)) final_state G.
End Semantics.
End PS.
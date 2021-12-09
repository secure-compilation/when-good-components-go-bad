Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Reachability.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect eqtype ssrfun.
From mathcomp Require ssrbool.
From extructures Require Import fmap fset.

Set Bullet Behavior "Strict Subproofs".

Module CS.

Import Intermediate.

Definition stack : Type := list Pointer.t.

(* NOTE: Consider parameterizing the semantics by a type of "additional state",
   and instantiate the non-/informative semantics as specializations of the
   parametric semantics. *)
Definition state : Type := stack * Memory.t * Register.t * Pointer.t.

Ltac unfold_state st :=
  let gps := fresh "gps" in
  let mem := fresh "mem" in
  let regs := fresh "regs" in
  let pc := fresh "pc" in
  destruct st as [[[gps mem] regs] pc].

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    let '(_, _, _, pc) := s in
    Pointer.component pc \in domm iface
}.

Definition is_context_component (st: state) ctx := turn_of st ctx.
Definition is_program_component (st: state) ctx := negb (is_context_component st ctx).

Ltac simplify_turn :=
  unfold is_program_component, is_context_component in *;
  unfold turn_of, state_turn in *;
  simpl in *.

Definition state_stack (st : state) : stack :=
  let '(gps, _, _, _) := st in gps.

Definition state_mem (st : state) : Memory.t :=
  let '(_, mem, _, _) := st in mem.

Definition state_regs (s : CS.state) : Register.t :=
  let '(_, _, regs, _) := s in regs.

Definition state_pc (st : state) : Pointer.t :=
  let '(_, _, _, pc) := st in pc.

Definition state_component (st : CS.state) : Component.id :=
  Pointer.component (state_pc st).


(*************************************************
Ltac unfold_Register_set e1 k'mem :=
  unfold Register.set in k'mem; rewrite setmE in k'mem; rewrite e1 in k'mem;
  simpl in k'mem.

Ltac unfold_regs_ptrs :=
  do 2 (unfold regs_data_ptrs; rewrite in_fset; rewrite seq.mem_pmap; rewrite seq.map_id);
  intros Hin; apply/codommP; destruct (@codommP _ _ _ _ Hin) as [k' k'mem].

Ltac solve_untouched_registers e1 k' k'mem :=
  exists k'; rewrite filtermE; rewrite filtermE in k'mem; simpl; simpl in k'mem;
         rewrite mapmE; rewrite mapmE in k'mem; unfold_Register_set e1 k'mem; exact k'mem.

Lemma Register_get_regs_ptrs :
  forall r1 regs ptrC ptrB ptrO,
    Register.get r1 regs = Ptr (Permission.data, ptrC, ptrB, ptrO) ->
    (ptrC, ptrB) \in regs_data_ptrs regs.
Proof.
  intros r1 regs ptrC ptrB ptrO Hget.
  unfold regs_data_ptrs; rewrite in_fset; rewrite seq.mem_pmap;
    rewrite seq.map_id. apply/codommP.
  unfold Register.get in Hget.
  destruct (regs (Register.to_nat r1)) as [v |] eqn:e.
  - exists (Register.to_nat r1).
    rewrite filtermE. rewrite mapmE. rewrite e. rewrite Hget. auto.
  - discriminate.
Qed.

Lemma regs_ptrs_set_get_in :
  forall (regs: Register.t) r1 r2 v,
    v \in regs_data_ptrs (Register.set r2 (Register.get r1 regs) regs) ->
    v \in regs_data_ptrs regs.
Proof.
  intros regs r1 r2 v.
  unfold_regs_ptrs.
  destruct (Some v == value_to_data_pointer_err (Register.get r1 regs)) eqn:copied;
    destruct (k' == Register.to_nat r2) eqn:e1; try solve_untouched_registers e1 k' k'mem.
  - pose (copied' := eqP copied); pose (e1' := eqP e1).
    exists (Register.to_nat r1).
    rewrite filtermE. rewrite filtermE in k'mem. simpl. simpl in k'mem.
    rewrite mapmE. rewrite mapmE in k'mem.
    destruct (regs (Register.to_nat r1)) as [vOfr1 |] eqn:e.
    + simpl.
      (rewrite e; simpl)
        || idtac "ExStructures 0.1 legacy rewrite".
      destruct vOfr1 as [| t |];
        try (
            simpl;
            unfold Register.get in copied';
            erewrite e in copied'; simpl in copied'; discriminate
          ).
      simpl.
      unfold Register.get in k'mem. rewrite e in k'mem.
      unfold_Register_set e1 k'mem. simpl in k'mem. exact k'mem.
    + unfold Register.get in k'mem.
      rewrite e in k'mem.
      unfold_Register_set e1 k'mem. discriminate.
  - (* here, obtain a contradiction *)
    rewrite filtermE in k'mem. simpl in k'mem.
    rewrite mapmE in k'mem.
    unfold_Register_set e1 k'mem.
    pose (@negPf (Some v == value_to_data_pointer_err (Register.get r1 regs))) as n.
    assert (ineq : Some v != value_to_data_pointer_err (Register.get r1 regs)).
    {
      apply/n. exact copied.
    }
    pose (negP ineq) as n0. exfalso. apply n0. apply/eqP.
    destruct (value_to_data_pointer_err (Register.get r1 regs)).
    + simpl in k'mem. injection k'mem as eq. subst. reflexivity.
    + simpl in k'mem. discriminate.
Qed.

Lemma regs_ptrs_set_get :
  forall regs r1 r2,
    fsubset (regs_data_ptrs (Register.set r2 (Register.get r1 regs) regs))
            (regs_data_ptrs regs).
Proof.
  intros. apply in_fsubset. apply regs_ptrs_set_get_in.
Qed.

(*Lemma Pointer_add_p_c_b :
  forall p z p', Pointer.add p z = p' ->
                 Pointer.permission p' = Pointer.permission p /\
                 Pointer.component p' = Pointer.component p /\
                 Pointer.block p' = Pointer.block p.
Proof.
  intros p z p' Hadd.
  destruct p as [[pc pb] po]. rewrite <- Hadd.
  simpl. auto.
Qed.

Lemma Pointer_sub_c_b :
  forall p z p', Pointer.sub p z = p' ->
                 Pointer.component p' = Pointer.component p /\
                 Pointer.block p' = Pointer.block p.
Proof.
  intros p z p' Hsub.
  destruct p as [[pc pb] po]. rewrite <- Hsub.
  simpl. auto.
Qed.
*)

 ******************************************************************************)

Lemma is_program_component_pc_notin_domm s ctx :
  is_program_component s ctx ->
  Pointer.component (CS.state_pc s) \notin domm ctx.
Proof.
  now destruct s as [[[? ?] ?] ?].
Qed.

(* preparing the machine for running a program *)

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | true =>
    let '(mem, _, entrypoints) := prepare_procedures_initial_memory p in
    let regs := Register.init in
    let b := match EntryPoint.get Component.main Procedure.main entrypoints with
             | Some b => b
             | None => 0 (* This case shouldn't happen for a well-formed p *)
             end in
    ([], mem, regs, (Permission.code, Component.main, b, 0%Z))
  (* this case shoudln't happen for a well-formed p *)
  | false => ([], emptym, emptym, (Permission.code, Component.main, 0, 0%Z))
  end.

(* A slightly hacky way to express the initial pc of a linked program as a
   function of its components, subject to well-formed conditions given in the
   following theorem. *)
Definition prog_main_block (p : program) : Block.id :=
  match prog_main p with
  | true =>
    match EntryPoint.get Component.main Procedure.main (prepare_procedures_entrypoints p) with
    | Some b => b
    | None => 0
    end
  | false => 0
  end.

Lemma prog_main_block_no_main:
  forall p,
    well_formed_program p ->
    Component.main \notin domm (prog_interface p) ->
    prog_main_block p = 0.
Proof.
  intros p Hwf Hdomm.
  unfold prog_main_block. (* Enable automatic rewrite on destruct. *)
  destruct (prog_main p) as [main |] eqn:Hmain'.
  - (* https://github.com/coq/coq/issues/5129 *)
    inversion Hwf as [BUGGY1 _ _ _ _ _ BUGGY2 [BUGGY3 Hcontra]]; clear BUGGY1 BUGGY2 BUGGY3.
    rewrite Hmain' in Hcontra. specialize (Hcontra (is_true_true)).
    rewrite Hcontra in Hdomm.
    discriminate.
  - reflexivity.
Qed.

Theorem initial_machine_state_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    closed_program (program_link p c) ->
    initial_machine_state (program_link p c) =
    ([],
     unionm (prepare_procedures_memory p)
            (prepare_procedures_memory c),
     Register.init,
     (Permission.code, Component.main,
      prog_main_block p + prog_main_block c,
      0%Z)).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hclosed.
  unfold initial_machine_state.
  inversion Hclosed as [_ [mainpc [Hmainpc [Hprocspc Hdommpc]]]];
    rewrite Hmainpc.
  rewrite -> prepare_procedures_initial_memory_after_linking;
    try assumption.
  destruct (prog_main p) as [mainp |] eqn:Hmainp;
    destruct (prog_main c) as [mainc |] eqn:Hmainc.
  - exfalso.
    pose proof proj2 (wfprog_main_component Hwfp) as Hdommp.
    rewrite Hmainp in Hdommp. specialize (Hdommp isT).
    pose proof proj2 (wfprog_main_component Hwfc) as Hdommc.
    rewrite Hmainc in Hdommc. specialize (Hdommc isT).
    inversion Hlinkable as [_ Hdisjoint].
    eapply fdisjoint_partition_notinboth; eassumption.
  - (* RB: NOTE: As usual, the following two cases are symmetric. *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc; simpl in Hmainpc.
    unfold prog_main_block, EntryPoint.get.
    rewrite Hmainp. rewrite Hmainc. rewrite unionmE.
    pose proof proj2 (wfprog_main_component Hwfp) as Hdommp.
    rewrite Hmainp in Hdommp. specialize (Hdommp isT).
    pose proof proj1 (wfprog_main_component Hwfc) as Hdommc.
    destruct (Component.main \in domm (prog_interface c)) eqn:Hcase;
      first (specialize (Hdommc isT); now rewrite Hmainc in Hdommc).
    rewrite <- domm_prepare_procedures_entrypoints in Hdommp, Hcase.
    destruct (@dommP _ _ _ _ Hdommp) as [entrypointsp Hentrypointsp].
    do 2 setoid_rewrite Hentrypointsp.
    now rewrite Nat.add_0_r.
  - (* Deal with the symmetries upfront; because of disjointness it is also
       possible to delay that and work on the "else" branch. *)
    setoid_rewrite unionmC at 1 2 3;
      try (try rewrite 2!domm_prepare_procedures_memory;
           try rewrite 2!domm_prepare_procedures_entrypoints;
           now inversion Hlinkable).
    (* Proceed (no symmetry on the hypothesis, here). *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc; rewrite Hmainc in Hmainpc; simpl in Hmainpc.
    unfold prog_main_block, EntryPoint.get.
    rewrite Hmainp. rewrite Hmainc. rewrite unionmE.
    pose proof proj2 (wfprog_main_component Hwfc) as Hdommc.
    rewrite Hmainc in Hdommc. specialize (Hdommc isT).
    pose proof proj1 (wfprog_main_component Hwfp) as Hdommp.
    destruct (Component.main \in domm (prog_interface p)) eqn:Hcase;
      first (specialize (Hdommp isT); now rewrite Hmainp in Hdommp).
    rewrite <- domm_prepare_procedures_entrypoints in Hdommc, Hcase.
    destruct (@dommP _ _ _ _ Hdommc) as [entrypointsc Hentrypointsc].
    do 2 setoid_rewrite Hentrypointsc.
    reflexivity.
  - (* Another easy/contra goal. *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc. rewrite Hmainc in Hmainpc.
    now inversion Hmainpc.
Qed.

(* transition system *)

Definition initial_state (p: program) (ics: state) : Prop :=
  ics = initial_machine_state p.

Definition final_state (G: global_env) (s: state) : Prop :=
  let '(gsp, mem, regs, pc) := s in
  executing G pc IHalt.

(* relational specification *)

(* RB: TODO: [DynShare] Do we need mappings like [imm_to_val] and [reg_to_Ereg],
   can we do the plain types? *)
Inductive step (G : global_env) : state -> trace event_inform -> state -> Prop :=
| Nop: forall gps mem regs pc,
    executing G pc INop ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, Pointer.inc pc)

| Label: forall gps mem regs pc l,
    executing G pc (ILabel l) ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, Pointer.inc pc)

| Const: forall gps mem regs regs' pc r v,
    executing G pc (IConst v r) ->
    Register.set r (imm_to_val v) regs = regs' ->
    step G (gps, mem, regs, pc)
           [EConst (Pointer.component pc) (imm_to_val v) (reg_to_Ereg r) mem regs']
           (gps, mem, regs', Pointer.inc pc)

| Mov: forall gps mem regs regs' pc rsrc rdest,
    executing G pc (IMov rsrc rdest) ->
    Register.set rdest (Register.get rsrc regs) regs = regs' ->
    step G (gps, mem, regs, pc)
           [EMov (Pointer.component pc) (reg_to_Ereg rsrc) (reg_to_Ereg rdest) mem regs']
           (gps, mem, regs', Pointer.inc pc)

| BinOp: forall gps mem regs regs' pc r1 r2 r3 op,
    executing G pc (IBinOp op r1 r2 r3) ->
    let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
    Register.set r3 result regs = regs' ->
    step G (gps, mem, regs, pc)
           [EBinop (Pointer.component pc) (binop_to_Ebinop op)
                   (reg_to_Ereg r1) (reg_to_Ereg r2) (reg_to_Ereg r3) mem regs']
           (gps, mem, regs', Pointer.inc pc)

| PtrOfLabel: forall gps mem regs regs' pc l r ptr,
    executing G pc (IPtrOfLabel l r) ->
    find_label_in_component G pc l = Some ptr ->
    Register.set r (Ptr ptr) regs = regs' ->
    step G (gps, mem, regs, pc)
           [EConst (Pointer.component pc) (Ptr ptr) (reg_to_Ereg r) mem regs']
           (gps, mem, regs', Pointer.inc pc)
| Load: forall gps mem regs regs' pc r1 r2 ptr v,
    executing G pc (ILoad r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    (* RB: NOTE: [DynShare] Even though cross-component pointer forging is
       possible at the program level, it WAS detected and stopped here. *)
    (* Pointer.component ptr = Pointer.component pc -> *)
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    step G (gps, mem, regs, pc)
           [ELoad (Pointer.component pc) (reg_to_Ereg r1) (reg_to_Ereg r2) mem regs']
           (gps, mem, regs', Pointer.inc pc)

| Store: forall gps mem mem' regs pc ptr r1 r2 (* v reach' e *),
    executing G pc (IStore r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    (* RB: NOTE: [DynShare] Even though cross-component pointer forging is
       possible at the program level, it WAS detected and stopped here. *)
    (* Pointer.component ptr = Pointer.component pc -> *)
    Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
    step G (gps, mem, regs, pc)
           [EStore (Pointer.component pc) (reg_to_Ereg r1) (reg_to_Ereg r2) mem' regs]
           (gps, mem', regs, Pointer.inc pc)

| Jal: forall gps mem regs regs' pc pc' l,
    executing G pc (IJal l) ->
    find_label_in_component G pc l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    step G
         (gps, mem, regs, pc)
         [EConst (Pointer.component pc)
                 (Ptr (Pointer.inc pc)) (reg_to_Ereg R_RA) mem regs']
         (gps, mem, regs', pc')

| Jump: forall gps mem regs pc pc' r,
    executing G pc (IJump r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.permission pc' = Permission.code ->
    Pointer.component pc' = Pointer.component pc ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, pc')

(** IJumpFunPtr is nothing but a Jump together with an extra check on the offset. *)
| JumpFunPtr: forall gps mem regs pc pc' r,
    executing G pc (IJumpFunPtr r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.permission pc' = Permission.code ->
    Pointer.component pc' = Pointer.component pc ->
    Pointer.offset pc' = 3%Z ->
    (** The offset 3%Z makes sure that the destination is    *)
    (** the beginning of the body of a compiled function.    *)
    (** Compiled functions have a prologue of 3 instructions *)
    (** before the entry ILabel instruction comes at offset 3*)
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, pc')
           
| BnzNZ: forall gps mem regs pc pc' r l val,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int val ->
    (val <> 0) % Z ->
    find_label_in_procedure G pc l = Some pc' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, pc')

| BnzZ: forall gps mem regs pc r l,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int 0 ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs, Pointer.inc pc)

| Alloc: forall gps mem mem' regs regs' pc rsize rptr size ptr,
    executing G pc (IAlloc rptr rsize) ->
    Register.get rsize regs = Int size ->
    (size > 0) % Z ->
    Memory.alloc mem (Pointer.component pc) (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    step G (gps, mem, regs, pc)
           [EAlloc (Pointer.component pc) (reg_to_Ereg rptr) (reg_to_Ereg rsize) mem' regs']
           (gps, mem', regs', Pointer.inc pc)

| Call: forall gps mem regs pc b C' P call_arg,
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    (* RB: TODO: [DynShare] Re-lift restriction to integer values.
       -- Unnecessary? *)
    Register.get R_COM regs = call_arg ->
    step G (gps, mem, regs, pc)
           [ECallInform (Pointer.component pc) P call_arg mem (Register.invalidate regs) C']
           (Pointer.inc pc :: gps, mem, Register.invalidate regs, (Permission.code, C', b, 0%Z))

| Return: forall gps' mem regs pc pc' ret_arg,
    executing G pc IReturn ->
    Pointer.component pc <> Pointer.component pc' ->
    (* RB: TODO: [DynShare] Re-lift restriction to integer values.
       -- Unnecessary? *)
    Register.get R_COM regs = ret_arg ->
    step G (pc' :: gps', mem, regs, pc)
           [ERetInform (Pointer.component pc) ret_arg mem (Register.invalidate regs) (Pointer.component pc')]
           (gps', mem, Register.invalidate regs, pc').

Ltac step_of_executing :=
  match goal with
  | H : executing _ _ ?INSTR |- _ =>
    match INSTR with
    | INop           => eapply Nop
    | ILabel _       => eapply Label
    | IConst _ _     => eapply Const
    | IMov _ _       => eapply Mov
    | IBinOp _ _ _ _ => eapply BinOp
    | IPtrOfLabel _ _ => eapply PtrOfLabel
    | ILoad _ _      => eapply Load
    | IStore _ _     => eapply Store
    | IAlloc _ _     => eapply Alloc
    | IBnz _ _       =>
      match goal with
      | H : Register.get _ _ = Int 0 |- _ => eapply BnzZ
      | _                                 => eapply BnzNZ
      end
    | IJump _        => eapply Jump
    | IJal _         => eapply Jal
    | ICall _ _      => eapply Call
    | IReturn        => eapply Return
    | IHalt          => fail
    end
  end.

Inductive step_non_inform (G : global_env) : state -> trace event -> state -> Prop :=
| Step_non_inform: forall s t t_noninform s',
    step G s t s' ->
    t_noninform = event_non_inform_of t ->
    step_non_inform G s t_noninform s'.

(* executable specification *)

Import MonadNotations.
Open Scope monad_scope.

Definition eval_step (G: global_env) (s: state) : option (trace event_inform * state) :=
  let '(gps, mem, regs, pc) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- getm (genv_procedures G) (Pointer.component pc);
  do P_code <- getm C_procs (Pointer.block pc);
  if (Pointer.offset pc <? 0) % Z then
    None
  else
    if (Permission.eqb (Pointer.permission pc) Permission.code) then
      do instr <- nth_error P_code (Z.to_nat (Pointer.offset pc));
      (* decode and execute the instruction *)
      match instr with
      | ILabel l =>
        ret (E0, (gps, mem, regs, Pointer.inc pc))
      | INop =>
        ret (E0, (gps, mem, regs, Pointer.inc pc))
      | IConst v r =>
        let regs' := Register.set r (imm_to_val v) regs in
        ret ([EConst (Pointer.component pc) (imm_to_val v) (reg_to_Ereg r) mem regs'],
             (gps, mem, regs', Pointer.inc pc))
      | IMov r1 r2 =>
        let regs' := Register.set r2 (Register.get r1 regs) regs in
        ret ([EMov (Pointer.component pc) (reg_to_Ereg r1) (reg_to_Ereg r2) mem regs'],
             (gps, mem, regs', Pointer.inc pc))
      | IBinOp op r1 r2 r3 =>
        let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
        let regs' := Register.set r3 result regs in
        ret ([EBinop (Pointer.component pc) (binop_to_Ebinop op) (reg_to_Ereg r1)
                     (reg_to_Ereg r2) (reg_to_Ereg r3) mem regs'],
             (gps, mem, regs', Pointer.inc pc))
      | IPtrOfLabel l r =>
        do ptr <- find_label_in_component G pc l;
        let regs' := Register.set r (Ptr ptr) regs in
        ret ([EConst (Pointer.component pc) (Ptr ptr) (reg_to_Ereg r) mem regs'],
             (gps, mem, regs', Pointer.inc pc)
            )
      | ILoad r1 r2 =>
        match Register.get r1 regs with
        | Ptr ptr =>
          (*if Component.eqb (Pointer.component ptr) (Pointer.component pc) then*)
          do v <- Memory.load mem ptr;
          let regs' := Register.set r2 v regs in
          ret ([ELoad (Pointer.component pc) (reg_to_Ereg r1) (reg_to_Ereg r2) mem regs'],
               (gps, mem, regs', Pointer.inc pc))
        (*else
        None*)
        | _ => None
        end
      | IStore r1 r2 =>
        match Register.get r1 regs with
        | Ptr ptr =>
          (*if Component.eqb (Pointer.component ptr) (Pointer.component pc) then*)
          do mem' <- Memory.store mem ptr (Register.get r2 regs);
          ret ([EStore (Pointer.component pc) (reg_to_Ereg r1) (reg_to_Ereg r2) mem' regs],
               (gps, mem', regs, Pointer.inc pc))
        (*else
        None*)
        | _ => None
        end
      | IJal l =>
        do pc' <- find_label_in_component G pc l;
        let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) regs in
        ret ([EConst (Pointer.component pc)
                     (Ptr (Pointer.inc pc)) (reg_to_Ereg R_RA) mem regs'],
             (gps, mem, regs', pc'))
      | IJump r =>
        match Register.get r regs with
        | Ptr pc' =>
          if Component.eqb (Pointer.component pc') (Pointer.component pc) then
            if Permission.eqb (Pointer.permission pc') Permission.code then
              ret (E0, (gps, mem, regs, pc'))
            else
              None
          else
            None
        | _ => None
        end
      | IJumpFunPtr r =>
        match Register.get r regs with
        | Ptr pc' =>
          if Component.eqb (Pointer.component pc') (Pointer.component pc) then
            if Permission.eqb (Pointer.permission pc') Permission.code then
              if Pointer.offset pc' == 3%Z then
                ret (E0, (gps, mem, regs, pc'))
              else
                None
            else
              None
          else
            None
        | _ => None
        end
      | IBnz r l =>
        match Register.get r regs with
        | Int 0 =>
          ret (E0, (gps, mem, regs, Pointer.inc pc))
        | Int val =>
          do pc' <- find_label_in_procedure G pc l;
          ret (E0, (gps, mem, regs, pc'))
        | _ => None
        end
      | IAlloc rptr rsize =>
        match Register.get rsize regs with
        | Int size =>
          if (size <=? 0) % Z then
            None
          else
            do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
            let regs' := Register.set rptr (Ptr ptr) regs in
            ret ([EAlloc (Pointer.component pc) (reg_to_Ereg rptr) (reg_to_Ereg rsize) mem' regs'],
                 (gps, mem', regs', Pointer.inc pc))
        | _ => None
        end
      | ICall C' P =>
        if negb (Component.eqb (Pointer.component pc) C') then
          if imported_procedure_b (genv_interface G) (Pointer.component pc) C' P then
            do b <- EntryPoint.get C' P (genv_entrypoints G);
            let val := Register.get R_COM regs in
            let pc' := (Permission.code, C', b, 0%Z) in
            let t := [ECallInform (Pointer.component pc) P val mem (Register.invalidate regs) C'] in
            ret (t, (Pointer.inc pc :: gps, mem, Register.invalidate regs, pc'))
          else
            None
        else
          None
      | IReturn =>
        match gps with
        | pc' :: gps' =>
          if negb (Component.eqb (Pointer.component pc) (Pointer.component pc')) then
            let val := Register.get R_COM regs in
            let t := [ERetInform (Pointer.component pc) val mem (Register.invalidate regs) (Pointer.component pc')] in
            ret (t, (gps', mem, Register.invalidate regs, pc'))
          else
            None
        | _ => None
        end
      | IHalt => None
      end
    else
      None.

Fixpoint execN (n: nat) (G: global_env) (st: state) : option Z :=
  match n with
  | O => None
  | S n' =>
    match eval_step G st with
    | None =>
      let '(_, _, regs, _) := st in
      match Register.get R_COM regs with
      | Int i => Some i
      | _ => None
      end
    | Some (_, st') => execN n' G st'
    end
  end.

Close Scope monad_scope.

(* equivalence between relational and executable specification *)

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st = Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    (* extract information about the state *)
    match goal with
    | Hexec: executing _ _ _ |- _ =>
      destruct Hexec as [procs [P_code [Hprocs [HP_code [? [Hperm Hinstr]]]]]]
    end;
    (* simplify *)
    simpl; unfold code in *;
      rewrite -> Hprocs, HP_code, Hinstr, Hperm; (* <- beq_nat_refl; *)
    (* the program counter is good *)
    match goal with
    | Hpc: (Pointer.offset _ >= 0) % Z |- _ =>
      apply Z.ge_le in Hpc; apply Z.ltb_ge in Hpc;
      rewrite Hpc
    end;
    (* solve simple cases *)
    try reflexivity.
  
  - match goal with
    | Hfind: find_label_in_component _ _ _ = _ |- _ =>
      rewrite Hfind
    end.
    reflexivity.
    
  - match goal with
    | Hregs_update: Register.get _ _ = _ |- _ =>
      rewrite -> Hregs_update
    end.
    unfold Memory.load in *.
    match goal with
    | Hperm: (if _ then _ else _) = Some _ |- _ => rewrite Hperm
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite -> Hregs_value
    end.
    unfold Memory.store in *.
    match goal with
    | Hperm: (if _ then _ else _) = Some _ |- _ => rewrite Hperm
    end.
    reflexivity.

  - match goal with
    | Hfind: find_label_in_component _ _ _ = _ |- _ =>
      rewrite Hfind
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _,
      Hcode: Pointer.permission _ = Permission.code
      |- _ =>
      rewrite -> Hregs_value, Hsame_component, Hcode, !Nat.eqb_refl
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _,
      Hcode: Pointer.permission _ = Permission.code,
      Hoff: Pointer.offset _ = _                        
      |- _ =>
      rewrite -> Hregs_value, Hsame_component, Hcode, Hoff, !Nat.eqb_refl
    end.
    reflexivity.
    
  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hfind: find_label_in_procedure _ _ _ = _ |- _ =>
      rewrite -> Hregs_value, Hfind
    end.
    destruct val;
      try contradiction;
      try reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite Hregs_value
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hpositive_size: (size > 0) % Z |- _ =>
      rewrite Hregs_value;
      apply Zgt_not_le in Hpositive_size; apply Z.leb_nle in Hpositive_size;
      rewrite Hpositive_size
    end.
    unfold Memory.alloc in *.
    rewrite H2. reflexivity.

  - match goal with
    | Hentrypoint: EntryPoint.get _ _ _ = _ |- _ =>
      rewrite -> Hentrypoint
    end.
    apply Nat.eqb_neq in H0. unfold Component.eqb. rewrite H0. simpl.
    apply imported_procedure_iff in H1. rewrite H1.
    reflexivity.

  - unfold Component.eqb.
    match goal with
    | Hdifferent_target: Pointer.component _ <> Pointer.component _ |- _ =>
      apply Nat.eqb_neq in Hdifferent_target; rewrite Hdifferent_target; simpl
    end.
    reflexivity.
Qed.

Theorem eval_step_sound:
  forall G st t st',
    eval_step G st = Some (t, st') -> step G st t st'.
Proof.
  intros G st t st' Heval_step.
  repeat unfold_states.
  destruct (getm (genv_procedures G) (Pointer.component pc0))
    as [C_procs | ] eqn:HC_procs.
  - destruct (getm C_procs (Pointer.block pc0))
      as [P_code | ] eqn:HP_code.
    + destruct ((Pointer.offset pc0 >=? 0) % Z) eqn:Hpc.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        (* case analysis on the fetched instruction *)
        ** assert ((Pointer.offset pc0 <? 0) % Z = false) as rewr. {
             destruct (Pointer.offset pc0); auto.
           }
           assert ((Pointer.offset pc0 >= 0) % Z). {
             destruct (Pointer.offset pc0); discriminate.
           }
           simpl in Heval_step. unfold code in *.
           rewrite -> HC_procs, HP_code, Hinstr, rewr in Heval_step.
           assert (Pointer.permission pc0 = Permission.code) as Hperm.
           {
             destruct (Permission.eqb (Pointer.permission pc0) Permission.code) eqn:e;
               try discriminate.
             by apply: Permission.eqP.
           }
           rewrite -> Hperm in Heval_step.
           destruct instr; inversion Heval_step; subst; clear Heval_step.
             (*; try (match goal with
                  | Hpcfalse: (Pointer.offset ?PC <? 0) % Z = false,
                    Heq: (if (Pointer.offset ?PC <? 0) % Z then None else Some _) = Some _
                    |- _ =>
                    rewrite Hpcfalse in Heq; inversion Heq; subst; clear Heq Hpcfalse
                  end).
              *)
           *** eapply Nop.
               eexists. eexists. eauto.

           *** eapply Label;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** eapply Const;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** eapply Mov;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** eapply BinOp;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** destruct (find_label_in_component G pc0 l) eqn:Hlabel;
                 try discriminate.
               inversion H1; subst.
               eapply PtrOfLabel;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.

           *** destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               unfold Memory.load in *.
               destruct (Permission.eqb (Pointer.permission t0) Permission.data) eqn:Hperm';
                 try discriminate.
               destruct (mem0 (Pointer.component t0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.load s (Pointer.block t0) (Pointer.offset t0))
                        eqn:Hload;
                 try discriminate.
               inversion H1; subst.
               eapply Load with (ptr:=t0);
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** assumption.
               **** unfold Memory.load.
                    rewrite Hmem. rewrite Hperm'. assumption.

           *** 
             destruct (Register.get r regs0) eqn:Hreg;
               try discriminate.
             unfold Memory.store in *.
             destruct (Permission.eqb (Pointer.permission t0) Permission.data) eqn:Hperm';
               try discriminate.
             destruct (mem0 (Pointer.component t0)) eqn:Hmem;
               try discriminate.
             destruct (ComponentMemory.store s (Pointer.block t0) (Pointer.offset t0)
                                             (Register.get r0 regs0))
                      eqn:Hstore;
               try discriminate.
             inversion H1; subst.
             eapply Store with (ptr:=t0);
               try reflexivity;
               try (eexists; eexists; eauto).
             **** assumption.
             **** unfold Memory.store.
                  rewrite Hmem. rewrite Hstore. rewrite Hperm'. reflexivity.

           *** destruct (Register.get r0 regs0) eqn:Hreg;
                 try discriminate.
               destruct ((z <=? 0) % Z) eqn:Hzpos;
                 try discriminate.
               unfold Memory.alloc in *.
               destruct (mem0 (Pointer.component pc0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.alloc s (Z.to_nat z)) eqn:Halloc;
                 try discriminate.
               inversion H1; subst.
               eapply Alloc;
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** eassumption.
               **** apply Z.lt_gt. apply Z.leb_gt. assumption.
               **** unfold Memory.alloc.
                    rewrite Hmem. rewrite Halloc. reflexivity.

           *** (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.*)
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct z eqn:Hn.
               **** inversion H1. subst.
                    eapply BnzZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H1. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** eassumption.
                    ***** intro contra. discriminate.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H1. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ****** eexists. eexists. eauto.
                    ****** eassumption.
                    ****** intro contra. discriminate.
                    ****** assumption.

           *** (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.*)
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcompcheck;
                 try discriminate.
               destruct (Permission.eqb (Pointer.permission t0) Permission.code) eqn:Hcode;
                 try discriminate.
               inversion H1; subst.
               eapply Jump with (pc':=pc);
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.
               **** by apply /Permission.eqP.
               **** apply Nat.eqb_eq. assumption.

           *** (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
             subst.
             destruct (find_label_in_component G pc0 l) eqn:Hlabel;
               try discriminate.
             inversion H1; subst.
             eapply Jal;
               try reflexivity.
             **** eexists. eexists. eauto.
             **** assumption.

           *** (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.*)
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcompcheck;
                 try discriminate.
               destruct (Permission.eqb (Pointer.permission t0) Permission.code) eqn:Hcode;
                 try discriminate.
               destruct (Pointer.offset t0 == 3%Z) eqn:Hoff; last discriminate.
               inversion H1; subst.
               eapply JumpFunPtr with (pc':=pc);
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.
               **** by apply /Permission.eqP.
               **** apply Nat.eqb_eq. assumption.
               **** by apply/eqP.
                  
           *** (*match goal with
                 | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
             destruct (Component.eqb (Pointer.component pc0) i) eqn:Hcomp;
               try discriminate; simpl in *.
             destruct (imported_procedure_b (genv_interface G)
                                            (Pointer.component pc0) i i0)
                      eqn:Himport;
               try discriminate.
             destruct (EntryPoint.get i i0 (genv_entrypoints G)) eqn:Hentrypoint;
               try discriminate.
             simpl in *. inversion H1. subst.
             eapply Call;
               try reflexivity.
             **** eexists. eexists. eauto.
             **** apply Nat.eqb_neq. assumption.
             **** apply imported_procedure_iff. auto.
             **** assumption.

           *** (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
               destruct gps0;
                 try discriminate.
               destruct (Component.eqb (Pointer.component pc0) (Pointer.component t0))
                        eqn:Hcomp;
                 try discriminate.
               simpl in *.
               inversion H1. subst.
               eapply Return;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Nat.eqb_neq. assumption.

           
        ** simpl in Heval_step. unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); try discriminate.
           destruct (Permission.eqb (Pointer.permission pc0) Permission.code);
             try discriminate.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z) eqn:Hpc';
             try discriminate.
           exfalso. unfold Z.geb in Hpc.
           destruct (Pointer.offset pc0);
             try discriminate.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); try discriminate.
           destruct (Permission.eqb (Pointer.permission pc0) Permission.code);
             try discriminate.
    + simpl in Heval_step.
      unfold code in *.
      rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step. discriminate.
  - simpl in Heval_step.
    unfold code in *.
    rewrite HC_procs in Heval_step.
    discriminate.
Qed.

Theorem eval_step_correct:
  forall G st t st',
    step G st t st' <-> eval_step G st = Some (t, st').
Proof.
  split.
  - apply eval_step_complete.
  - apply eval_step_sound.
Qed.

(* complete semantics and some properties *)

Corollary step_deterministic:
  forall G st t st1 st2,
    step G st t st1 -> step G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hstep1 Hstep2.
  apply eval_step_correct in Hstep1.
  apply eval_step_correct in Hstep2.
  rewrite Hstep1 in Hstep2.
  inversion Hstep2; subst.
  reflexivity.
Qed.


Section SemanticsInform.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem_inform :=
    @Semantics_gen event_inform state global_env step (initial_state p) (final_state G) G.

  Lemma determinate_step:
    forall s t1 s1 t2 s2,
      step G s t1 s1 ->
      step G s t2 s2 ->
      equal_and_nil_or_singleton t1 t2 /\ (t1 = t2 -> s1 = s2).
  Proof.
    intros s t1 s21 t2 s2 Hstep1 Hstep2.
    inversion Hstep1; subst; inversion Hstep2; subst;
      (* extract information about the instruction we are executing *)
      try (match goal with
             Hexec1: executing ?G ?PC ?INSTR1,
             Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
             destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? [Hperm Hinstr]]]]]];
             destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? [Hperm' Hinstr']]]]]];
             rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
             rewrite HP_code in HP_code'; inversion HP_code'; subst;
             rewrite Hperm in Hperm'; inversion Hperm'; subst;
             rewrite Hinstr in Hinstr'; inversion Hinstr'; subst
           end);
      (* *)
      try (match goal with
           | H1: Register.get ?REGS ?REG = _,
             H2: Register.get ?REGS ?REG = _ |- _ =>
             rewrite H1 in H2; inversion H2; subst
           end);
      try (match goal with
           | H1: Memory.load ?MEM ?PTR = _,
             H2: Memory.load ?MEM ?PTR = _ |- _ =>
             rewrite H1 in H2; inversion H2; subst
           end);
      try (match goal with
           | H1: Memory.store ?MEM ?PTR ?REG = _,
             H2: Memory.store ?MEM ?PTR ?REG = _ |- _ =>
             rewrite H1 in H2; inversion H2; subst
           end);
      try (match goal with
           | H1: Memory.alloc ?MEM ?PTR ?SZ = _,
             H2: Memory.alloc ?MEM ?PTR ?SZ = _ |- _ =>
             rewrite H1 in H2; inversion H2; subst
           end);
      (* solve simple cases *)
      try (split; [ constructor |
                    intro Hsame_trace; eapply step_deterministic; eauto ]).
    - apply match_events_EConst.
    - apply match_events_EMov.
    - apply match_events_EBinop.
    - match goal with
      | H1: find_label_in_component G pc l0 = _,
        H2: find_label_in_component G pc l0 = _ |- _ =>
        rewrite H1 in H2; inversion H2; subst
      end.
      apply match_events_EConst.
    - congruence.
    - apply match_events_ELoad.
    - apply match_events_EStore.
    - apply match_events_EConst.
    - apply match_events_EAlloc.
    - apply match_events_ECallInform.
    - apply match_events_ERetInform.
  Qed.

  Lemma singleton_traces_inform:
    single_events sem_inform.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; simpl; auto.
  Qed.

  Lemma determinate_initial_states:
    forall s1 s2,
      initial_state p s1 -> initial_state p s2 ->
      s1 = s2.
  Proof.
    intros s1 s2 Hs1_init Hs2_init.
    unfold initial_state in *. subst.
    reflexivity.
  Qed.

  Lemma final_states_stuckness_inform:
    forall s,
      final_state G s ->
      nostep step G s.
  Proof.
    intros s Hs_final.
    unfold nostep.
    unfold_states.
    unfold final_state in Hs_final.
    intros t s'. unfold not. intro Hstep.
    inversion Hstep; subst;
    try (match goal with
         | Hexec1: executing ?G ?PC ?INSTR1,
           Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
           destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? [Hperm Hinstr]]]]]];
           destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? [Hperm' Hinstr']]]]]];
           rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
           rewrite HP_code in HP_code'; inversion HP_code'; subst;
           rewrite Hperm in Hperm'; inversion Hperm'; subst;
           rewrite Hinstr in Hinstr'; inversion Hinstr'
         end).
  Qed.

  Lemma determinacy_inform:
    determinate sem_inform.
  Proof.
    constructor.
    - apply determinate_step.
    - apply singleton_traces_inform.
    - apply determinate_initial_states.
    - apply final_states_stuckness_inform.
  Qed.

  Lemma program_behaves_inv_inform:
    forall b,
      program_behaves sem_inform b ->
    exists s,
      initial_state p s /\ state_behaves sem_inform s b.
  Proof.
    intros b [s b' Hini Hbeh | Hini]; subst.
    - now exists s.
    - simpl in Hini.
      specialize (Hini (initial_machine_state p)).
      unfold initial_state in Hini.
      contradiction.
  Qed.

  Lemma non_inform_is_call_or_ret s1 t s2 e:
    step G s1 t s2 ->
    event_non_inform_of t = [e] ->
    (
      (exists cid pid v mem reg cid', t = [ECallInform cid pid v mem reg cid'])
      \/
      (exists cid v mem reg cid', t = [ERetInform cid v mem reg cid'])
    ).
  Proof.
    intros Hstep Henoninf.
    inversion Hstep; subst;
      unfold event_non_inform_of in *; try discriminate.
    - left. do 6 eexists. eauto.
    - right. do 5 eexists. eauto.
  Qed.

Import ssreflect eqtype.

Definition stack_state_of (cs:CS.state) : stack_state :=
  let '(gps, mem, regs, pc) := cs in
  StackState (Pointer.component pc) (List.map Pointer.component gps).

Lemma intermediate_well_bracketed_trace t cs cs' :
  Star sem_inform cs t cs' ->
  well_bracketed_trace (stack_state_of cs) t.
Proof.
elim: cs t cs' / => [|cs1 t1 cs2 t2 cs3 t Hstep _ IH ->] //=.
case: cs1 t1 cs2 / Hstep IH => /=;
try by move=> *; match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H end.
- move=> *; rewrite eqxx; rewrite andTb;
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *. rewrite eqxx. rewrite andTb.
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *. rewrite eqxx. rewrite andTb.
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *. rewrite eqxx. rewrite andTb.
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *. rewrite eqxx. rewrite andTb.
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *; rewrite eqxx; rewrite andTb;
  match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
  rewrite Pointer.inc_preserves_component in H; assumption
  end.
- move=> *. rewrite eqxx. rewrite andTb.
  match goal with H: find_label_in_component _ _ _ = _ |- _ =>
                  apply find_label_in_component_1 in H; rewrite H
  end.
  assumption.
- by move=> ????????? ->.
- by move=> ????????? ->.
- by move=> ??????????? /find_label_in_procedure_1 ->.
- by move=> ????????????; rewrite eqxx Pointer.inc_preserves_component.
- move=> ??????????????. rewrite !eqxx. rewrite andTb.
  rewrite <- Pointer.inc_preserves_component. assumption.
- move=> ??????????. rewrite !eqxx. rewrite !andTb. assumption.
Qed.

Canonical ssrnat.nat_eqType.

End SemanticsInform.

Section SemanticsNonInform.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem_non_inform :=
    @Semantics_gen event state global_env step_non_inform (initial_state p) (final_state G) G.

  Lemma determinate_step_non_inform:
    forall s t1 s1 t2 s2,
      step_non_inform G s t1 s1 ->
      step_non_inform G s t2 s2 ->
      equal_and_nil_or_singleton t1 t2 /\ (t1 = t2 -> s1 = s2).
  Proof.
    intros s t1 s21 t2 s2 Hstep1 Hstep2.
    inversion Hstep1 as [s'1 t1' s21' ? Hstep1'];
      inversion Hstep2 as [s'2 t2' s2' ? Hstep2'];
      subst.
    pose proof determinate_step _ _ _ _ _ _ Hstep1' Hstep2' as [Heqnil Heq].
    inversion Heqnil as [| e e' Heveq]; subst.
    - split.
      + now constructor.
      + now auto.
    - apply event_equal_equal in Heveq; subst e'. split.
      + destruct e; now repeat constructor.
      + now auto.
  Qed.

  Lemma singleton_traces_non_inform:
    single_events sem_non_inform.
  Proof.
    unfold single_events. intros s t s' Hstep.
    inversion Hstep as [? t' ? ? Hstep']; subst; inversion Hstep'; now auto.
  Qed.

  Lemma no_step_no_step_non_inform:
    forall s, nostep step G s -> nostep step_non_inform G s.
  Proof.
    intros s Hnostep t s' Hstep.
    inversion Hstep; subst.
    eapply Hnostep; eassumption.
  Qed.

  Lemma final_states_stuckness_non_inform:
    forall s,
      final_state G s ->
      nostep step_non_inform G s.
  Proof.
    intros s Hs_final.
    pose proof final_states_stuckness_inform p s Hs_final as no_step.
    pose proof no_step_no_step_non_inform s no_step as g. exact g.
  Qed.

  Lemma determinacy_non_inform:
    determinate sem_non_inform.
  Proof.
    constructor.
    - apply determinate_step_non_inform.
    - apply singleton_traces_non_inform.
    - apply determinate_initial_states.
    - apply final_states_stuckness_non_inform.
  Qed.

  Lemma program_behaves_inv_non_inform:
    forall b,
      program_behaves sem_non_inform b ->
    exists s,
      initial_state p s /\ state_behaves sem_non_inform s b.
  Proof.
    intros b [s b' Hini Hbeh | Hini]; subst.
    - now exists s.
    - simpl in Hini.
      specialize (Hini (initial_machine_state p)).
      unfold initial_state in Hini.
      contradiction.
  Qed.

Import ssreflect eqtype.

(* RB: TODO: Rename these two functions to make the difference between them
   clear, at the moment it is rather confusing. This equivalence is of use
   to simplify several subsequent results. *)
Lemma project_event_non_inform s t s' :
  step G s t s' ->
  project_non_inform t = event_non_inform_of t.
Proof.
  intros Hstep.
  pose proof singleton_traces_inform _ _ _ _ Hstep.
  destruct t as [| e1 [| e2 t]]; easy.
Qed.

Lemma step_non_inform_step_inform cs t cs':
  step_non_inform G cs t cs' ->
  exists t_inform, step G cs t_inform cs' /\ project_non_inform t_inform = t.
Proof.
  intros Hstep.
  inversion Hstep as [? t' ? Hstep']; subst.
  exists t'. split; [assumption |].
  eapply project_event_non_inform; eassumption.
Qed.

Lemma step_inform_step_non_inform cs t_inform cs':
  step G cs t_inform cs' ->
  step_non_inform G cs (project_non_inform t_inform) cs'.
Proof.
  intros Hstep. rewrite (project_event_non_inform _ _ _ Hstep).
  inversion Hstep; subst; eapply Step_non_inform; eauto.
Qed.

Lemma star_sem_non_inform_star_sem_inform cs t cs' :
  Star sem_non_inform cs t cs' ->
exists t_inform,
  Star (sem_inform p) cs t_inform cs' /\ project_non_inform t_inform = t.
Proof.
  intros Hstar. induction Hstar. exists E0. split. constructor. auto.
  match goal with
  | Hstep: Step _ ?s1 ?t1 ?s2 |- _ =>
    pose proof step_non_inform_step_inform s1 t1 s2 Hstep as Hexists;
    destruct Hexists as [t1_inform [Hstep_t1_inform Hproj_t1_inform]]
  end.
  match goal with
  | IH: exists _, _ |- _ =>
    destruct IH as [t2_inform [Hstar_t2_inform Hproj_t2_inform]]
  end.
  exists (t1_inform ** t2_inform). split.
  apply star_trans with (t1 := t1_inform) (s2 := s2) (t2 := t2_inform); auto.
  - apply star_one. auto.
  - rewrite project_non_inform_append. rewrite Hproj_t1_inform Hproj_t2_inform. auto.
Qed.

Lemma star_sem_inform_star_sem_non_inform cs t_inform cs' :
  Star (sem_inform p) cs t_inform cs' ->
  Star sem_non_inform cs (project_non_inform t_inform) cs'.
Proof.
  intros Hstar. induction Hstar.
  - simpl. constructor.
  - match goal with Hstep: Step _ ?s1 ?t1 ?s2 |- _ =>
                    pose proof step_inform_step_non_inform s1 t1 s2 Hstep as Hstep_non_inform
    end.
    subst.
    rewrite project_non_inform_append.
    apply star_trans with (t1 := project_non_inform t1) (t2 := project_non_inform t2)
                          (s2 := s2); auto.
    apply star_one. auto.
Qed.

Definition stack_state_of_non_inform (cs:CS.state) : Traces.stack_state :=
  let '(gps, mem, regs, pc) := cs in
  Traces.StackState (Pointer.component pc) (List.map Pointer.component gps).


Lemma well_bracketed_inform_well_bracketed_project_non_inform
      s t_inform t_non_inform:
  TracesInform.well_bracketed_trace (stack_state_of s) t_inform ->
  project_non_inform t_inform = t_non_inform ->
  Traces.well_bracketed_trace (stack_state_of_non_inform s) t_non_inform.
Admitted.

Lemma intermediate_well_bracketed_trace_non_inform t cs cs' :
  Star sem_non_inform cs t cs' ->
  Traces.well_bracketed_trace (stack_state_of_non_inform cs) t.
Proof.
  intros Hstar.
  pose proof star_sem_non_inform_star_sem_inform cs t cs' Hstar
    as [t_inform [Hstar_inform Hproj]].
  pose proof intermediate_well_bracketed_trace p t_inform cs cs' Hstar_inform
    as Hwbrack_inform.
  exact (well_bracketed_inform_well_bracketed_project_non_inform
           cs t_inform t Hwbrack_inform Hproj).
Qed.

Canonical ssrnat.nat_eqType.

End SemanticsNonInform.

(* RB: TODO: Use SSR imports consistently (we use SSR exclusively for the next
   lemma). *)
Import ssreflect.
Remark step_preserves_mem_domm G s t s' :
  CS.step G s t s' ->
  domm (state_mem s) = domm (state_mem s').
Proof.
  intros Hstep.
  inversion Hstep; subst;
    try reflexivity. (* Most operations do not modify the memory. *)
  - (* Preservation by Memory.store. *)
    match goal with
    | Hstore : Memory.store _ ?PTR (Register.get ?REG ?REGS) = _ |- _ =>
      unfold Memory.store in Hstore;
        destruct (Permission.eqb (Pointer.permission PTR) Permission.data) eqn:Hperm;
        [| discriminate];
        destruct (mem (Pointer.component PTR)) as [memC |] eqn:Hcase1;
        [| discriminate];
        destruct (ComponentMemory.store
                    memC (Pointer.block PTR) (Pointer.offset PTR) (Register.get REG REGS))
          as [memC' |] eqn:Hcase2;
        [| discriminate];
        inversion Hstore as [Hsetm];
        simpl; rewrite domm_set fsetU1in;
          [reflexivity |];
          apply /dommP; now eauto
    end.
  - (* Preservation by Memory.alloc. *)
    match goal with
    | Halloc : Memory.alloc _ _ _ = _ |- _ =>
      unfold Memory.alloc in Halloc;
      destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase;
        [| discriminate];
      destruct (ComponentMemory.alloc memC (Z.to_nat size)) as [memC' b];
      inversion Halloc; subst; simpl;
      rewrite domm_set fsetU1in; [reflexivity |];
      apply /dommP; now eauto
    end.
Qed.

Definition comes_from_initial_state (s: state) (iface : Program.interface) : Prop :=
  exists p s0 t,
    well_formed_program p /\
    prog_main p /\
    prog_interface p = iface /\
    initial_state p s0 /\
    Star (sem_inform p) s0 t s.

Remark comes_from_initial_state_mem_domm s ctx :
  comes_from_initial_state s ctx ->
  domm (state_mem s) = domm ctx.
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hiface [Hini Hstar]]]]]]].
  apply star_iff_starR in Hstar.
  revert ctx Hwf Hmain Hiface Hini.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros ctx Hwf Hmain Hiface Hini.
  - unfold initial_state, initial_machine_state in Hini; subst s.
    rewrite Hmain. simpl.
    rewrite domm_map domm_prepare_procedures_initial_memory_aux. congruence.
  - specialize (IHHstar _ Hwf Hmain Hiface Hini).
    apply step_preserves_mem_domm in Hstep23. congruence.
Qed.

Lemma comes_from_initial_state_stack_domm s ctx :
  comes_from_initial_state s ctx ->
  All (fun frame => Pointer.component frame \in domm ctx) (state_stack s).
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hiface [Hini Hstar]]]]]]].
  apply star_iff_starR in Hstar.
  revert ctx Hwf Hmain Hiface Hini.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros ctx Hwf Hmain Hiface Hini.
  - unfold initial_state, initial_machine_state in Hini; subst s.
    now rewrite Hmain.
  - specialize (IHHstar _ Hwf Hmain Hiface Hini).
    (* Case analysis on the step. Most operations do not modify the stack, and
       returns only pop. *)
    inversion Hstep23; subst;
      simpl in *;
      try easy.
    (* The only semi-interesting cases is the call instruction. *)
    split; [| assumption].
    rewrite Pointer.inc_preserves_component.
    match goal with
    | Himp : imported_procedure _ _ _ _ |- _ =>
      destruct Himp as [CI [Hhas_comp Himp]];
      exact (has_component_in_domm_prog_interface Hhas_comp)
    end.
Qed.

(* RB: TODO: This result admits more general formulations (see above).
   Replace this with those whenever convenient, including the "bootstrapping"
   on the stack in the result for the domain of the PC, just below. *)
Corollary comes_from_initial_state_stack_cons_domm frame gps mem regs pc iface :
  comes_from_initial_state (frame :: gps, mem, regs, pc) iface ->
  Pointer.component frame \in domm iface.
Proof.
  intros Hcomes_from.
  apply comes_from_initial_state_stack_domm in Hcomes_from.
  now simpl in Hcomes_from.
Qed.

Lemma comes_from_initial_state_pc_domm s ctx :
  comes_from_initial_state s ctx ->
  Pointer.component (state_pc s) \in domm ctx.
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hctx [Hinitial Hstar]]]]]]].
  revert Hwf Hmain Hctx Hinitial.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros Hwf Hmain Hctx Hinitial.
  - unfold initial_state, initial_machine_state in Hinitial; subst.
    rewrite Hmain.
    apply (wfprog_main_component Hwf). now rewrite Hmain.
  - specialize (IHHstar Hwf Hmain Hctx Hinitial).
    inversion Hstep23; subst; simpl;
      match goal with
      | Hlabel : find_label_in_component _ _ _ = _
        |- _=>
        now rewrite <- (find_label_in_component_1 _ _ _ _ Hlabel)
      | Hlabel : find_label_in_procedure _ _ _ = _
        |- _=>
        now rewrite <- (find_label_in_procedure_1 _ _ _ _ Hlabel)
      | Heq : Pointer.component _ = Pointer.component _
        |- _ =>
        now rewrite -> Heq
      | Hentry : EntryPoint.get _ _ _ = _
        |- _ =>
        change (genv_entrypoints _)
          with (genv_entrypoints (prepare_global_env p))
          in Hentry;
        pose proof EntryPoint.get_some Hentry as Hdomm;
        now rewrite domm_genv_entrypoints in Hdomm
      | Hop : executing _ _ IReturn
        |- _ =>
        eapply comes_from_initial_state_stack_cons_domm;
        unfold comes_from_initial_state;
        apply star_iff_starR in Hstar12;
        now eauto 9
      | |- _ =>
        now rewrite -> Pointer.inc_preserves_component
      end.
Qed.

Lemma silent_step_preserves_memory G s s':
  CS.step G s E0 s' ->
  state_mem s = state_mem s'.
Proof. intros Hstep. by inversion Hstep; subst; simpl. Qed.

Lemma silent_step_preserves_registers G s s':
  CS.step G s E0 s' ->
  state_regs s = state_regs s'.
Proof. intros Hstep. by inversion Hstep; subst; simpl. Qed.

Lemma epsilon_star_preserves_memory p s1 s2 :
  Star (CS.sem_inform p) s1 E0 s2 ->
  CS.state_mem s1 = CS.state_mem s2.
Proof.
  intros Hstar. remember E0 as t. induction Hstar; auto; subst.
  assert (t1 = E0) by now induction t1. subst.
  assert (t2 = E0) by now induction t2. subst.
  apply silent_step_preserves_memory in H. specialize (IHHstar Logic.eq_refl).
  congruence.
Qed.

Lemma epsilon_star_preserves_registers p s1 s2:
  Star (CS.sem_inform p) s1 E0 s2 ->
  CS.state_regs s1 = CS.state_regs s2.
Proof.
  intros Hstar. remember E0 as t. induction Hstar; auto; subst.
  assert (t1 = E0) by now induction t1. subst.
  assert (t2 = E0) by now induction t2. subst.
  apply silent_step_preserves_registers in H. specialize (IHHstar Logic.eq_refl).
  congruence.
Qed.

Lemma starR_memory_of_event_inform p s t1 e1 s1: 
  starR step (GlobalEnv.prepare_global_env p) s (seq.rcons t1 e1) s1 ->
  mem_of_event_inform e1 = state_mem s1.
Proof.
  rewrite -seq.cats1. intros Hstar. apply star_iff_starR in Hstar.
  specialize (star_app_inv (singleton_traces_inform p) _ _ Hstar)
    as [? [_ Hstar2]].
  remember [e1] as t. revert Heqt.
  induction Hstar2; subst; intros Hrewr; first discriminate.
  destruct t0 as [|e0 t0]; destruct t2 as [|e2 t2]; simpl in *; try discriminate.
  + destruct t2; try discriminate. inversion Hrewr; subst. by intuition.
  + destruct t0; try discriminate; simpl in *. inversion Hrewr; subst. clear Hrewr.
    assert (Hrewr: mem_of_event_inform e1 = state_mem s2).
    {
      unfold_states. by inversion H.
    }
    rewrite Hrewr. eapply epsilon_star_preserves_memory. apply Hstar2.
  + unfold Eapp in *. rewrite app_comm_cons in Hrewr.
    apply app_eq_unit in Hrewr as [[? _]|[_ ?]]; discriminate.
Qed.


Lemma starR_register_file_of_event_inform p s t1 e1 s1: 
  starR step (GlobalEnv.prepare_global_env p) s (seq.rcons t1 e1) s1 ->
  register_file_of_event_inform e1 = state_regs s1.
Proof.
  rewrite -seq.cats1. intros Hstar. apply star_iff_starR in Hstar.
  specialize (star_app_inv (singleton_traces_inform p) _ _ Hstar)
    as [? [_ Hstar2]].
  remember [e1] as t. revert Heqt.
  induction Hstar2; subst; intros Hrewr; first discriminate.
  destruct t0 as [|e0 t0]; destruct t2 as [|e2 t2]; simpl in *; try discriminate.
  + destruct t2; try discriminate. inversion Hrewr; subst. by intuition.
  + destruct t0; try discriminate; simpl in *. inversion Hrewr; subst. clear Hrewr.
    assert (Hrewr: register_file_of_event_inform e1 = state_regs s2).
    {
      unfold_states. by inversion H.
    }
    rewrite Hrewr. eapply epsilon_star_preserves_registers. apply Hstar2.
  + unfold Eapp in *. rewrite app_comm_cons in Hrewr.
    apply app_eq_unit in Hrewr as [[? _]|[_ ?]]; discriminate.
Qed.


Lemma silent_step_preserves_component G s s' :
  CS.step G s E0 s' ->
  Pointer.component (state_pc s) = Pointer.component (state_pc s').
Proof.
  intros Hstep.
  inversion Hstep; subst; simpl;
    try now rewrite Pointer.inc_preserves_component.
  - auto.
  - auto.
(*  - erewrite find_label_in_component_1; try eassumption. reflexivity.
  - congruence.*)
  - erewrite find_label_in_procedure_1; try eassumption. reflexivity.
Qed.

Lemma silent_step_non_inform_preserves_component G s s' :
  CS.step_non_inform G s E0 s' ->
  Pointer.component (state_pc s) = Pointer.component (state_pc s').
Proof.
  intros Hstep. inversion Hstep as [? t ? ? Hstep']; subst.
  inversion Hstep'; subst;
    try (now rewrite Pointer.inc_preserves_component).
  - eapply find_label_in_component_1; now eauto.
  - eapply silent_step_preserves_component; eassumption.
  - eapply silent_step_preserves_component; eassumption.
  - eapply silent_step_preserves_component; eassumption.
  - discriminate.
  - discriminate.
Qed.

Lemma silent_step_preserves_program_component : forall s1 s2 G ctx,
  CS.is_program_component s1 ctx ->
  CS.step G s1 E0 s2 ->
  CS.is_program_component s2 ctx.
Proof.
  intros [[[? ?] ?] pc1] [[[? ?] ?] pc2] G ctx Hcomp1 Hstep12.
  pose proof CS.silent_step_preserves_component _ _ _ Hstep12 as Heq.
  simplify_turn. now rewrite <- Heq.
Qed.

Lemma silent_step_non_inform_preserves_program_component : forall s1 s2 G ctx,
  CS.is_program_component s1 ctx ->
  CS.step_non_inform G s1 E0 s2 ->
  CS.is_program_component s2 ctx.
Proof.
  intros [[[? ?] ?] pc1] [[[? ?] ?] pc2] G ctx Hcomp1 Hstep12.
  pose proof CS.silent_step_non_inform_preserves_component _ _ _ Hstep12 as Heq.
  simplify_turn. now rewrite <- Heq.
Qed.

(* RB: TODO: Remove reliance on auto-names. Also note that this follows from
   silent_step_preserves_program_component, posed below. *)
Lemma epsilon_star_preserves_program_component p c s1 s2 :
  CS.is_program_component s1 (prog_interface c) ->
  Star (CS.sem_inform (program_link p c)) s1 E0 s2 ->
  CS.is_program_component s2 (prog_interface c).
Proof.
  intros Hprg_component Hstar.
  remember E0 as t.
  induction Hstar.
  - assumption.
  - subst; assert (t1 = E0) by now induction t1.
    assert (t2 = E0) by now induction t1. subst.
    apply IHHstar; auto.
    clear H0 IHHstar Hstar.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in *.
    inversion H;
      try (match goal with
           | Heq : (_, _, _, _) = s1 |- _ => rewrite -Heq in Hprg_component
           end);
      try now rewrite Pointer.inc_preserves_component.
    (*+ erewrite <- find_label_in_component_1; eassumption.*)
    + match goal with
      | H: Pointer.component _ = Pointer.component _ |- _ =>
        now rewrite H
      end.
    + match goal with
      | H: Pointer.component _ = Pointer.component _ |- _ =>
        now rewrite H
      end.
    + erewrite <- find_label_in_procedure_1; eassumption.
Qed.

Lemma epsilon_star_non_inform_preserves_component p s1 s2:
  Star (CS.sem_non_inform p) s1 E0 s2 ->
  Pointer.component (CS.state_pc s1) = Pointer.component (CS.state_pc s2).
Proof.
  intros Hstar.
  remember E0 as t.
  induction Hstar.
  - reflexivity.
  - subst; assert (t1 = E0) by now induction t1.
    assert (t2 = E0) by now induction t1. subst.
    inversion H as [? t ? ? Hstep]; subst.
    inversion Hstep; subst; unfold_state s3; simpl in *;
      rewrite <- IHHstar; auto;
      try (now rewrite Pointer.inc_preserves_component).
    + erewrite find_label_in_component_1; by eauto.
    + erewrite find_label_in_procedure_1; by eauto.
    + discriminate.
    + discriminate.
Qed.

Lemma epsilon_star_inform_preserves_component p s1 s2:
  Star (CS.sem_inform p) s1 E0 s2 ->
  Pointer.component (CS.state_pc s1) = Pointer.component (CS.state_pc s2).
Proof.
  intros Hstar.
  remember E0 as t.
  induction Hstar; auto.
  subst; assert (t1 = E0) by now induction t1.
  assert (t2 = E0) by now induction t1. subst.
  inversion H; subst; unfold_state s3; simpl in *;
    rewrite <- IHHstar; auto;
      try (now rewrite Pointer.inc_preserves_component).
  erewrite find_label_in_procedure_1; by eauto.
Qed.
  

Lemma epsilon_star_non_inform_preserves_program_component p c s1 s2 :
  CS.is_program_component s1 (prog_interface c) ->
  Star (CS.sem_non_inform (program_link p c)) s1 E0 s2 ->
  CS.is_program_component s2 (prog_interface c).
Proof.
  intros Hprg_component Hstar.
  remember E0 as t.
  induction Hstar.
  - assumption.
  - subst; assert (t1 = E0) by now induction t1.
    assert (t2 = E0) by now induction t1. subst.
    apply IHHstar; auto.
    clear H0 IHHstar. simpl in H.
    inversion H as [? t ? ? Hstep]; subst.
    inversion Hstep; subst; CS.simplify_turn;
      try (now rewrite Pointer.inc_preserves_component).
    + erewrite <- find_label_in_component_1; eassumption.
    + congruence.
    + congruence.
    + erewrite <- find_label_in_procedure_1; eassumption.
    + discriminate.
    + discriminate.
Qed.

Lemma next_comp_of_event_cur_comp_of_event p s t1 e1 s1 e s2:
  starR step (GlobalEnv.prepare_global_env p) s (seq.rcons t1 e1) s1 ->
  step (GlobalEnv.prepare_global_env p) s1 [e] s2 ->
  next_comp_of_event e1 = cur_comp_of_event e.
Proof.
  intros Hstar01 Hstep.
  rewrite -seq.cats1 in Hstar01. apply star_iff_starR in Hstar01.
  specialize (star_app_inv (singleton_traces_inform p) _ _ Hstar01)
    as [? [_ Hstar2]].
  remember [e1] as t. revert Heqt.
  induction Hstar2; subst; intros Hrewr; first discriminate.
    destruct t0 as [|e0 t0]; destruct t2 as [|e2 t2]; try (simpl in *; discriminate).
  + destruct t2; try discriminate. inversion Hrewr; subst. by intuition.
  + destruct t0; try discriminate. inversion Hrewr; simpl in Hrewr; subst. clear Hrewr.
    apply epsilon_star_inform_preserves_component in Hstar2.
    unfold_state s0. unfold_state s3. unfold_state s1. unfold_state s2.
    simpl in Hstar2.
    inversion Hstep; inversion H; subst; simpl in *;
      try (congruence);
      try (rewrite Pointer.inc_preserves_component in Hstar2; congruence);
      try (
          match goal with
          | Hfind: find_label_in_component _ _ _ = _ |- _ =>
            apply find_label_in_component_1 in Hfind
          end;
          congruence
        ).
  + unfold Eapp in *. 
    apply app_eq_unit in Hrewr as [[? _]|[_ ?]]; discriminate.
Qed.

  
(* RB: Could be phrased in terms of does_prefix. *)
Theorem behavior_prefix_star {p b m} :
  program_behaves (CS.sem_inform p) b ->
  prefix m b ->
exists s1 s2,
  CS.initial_state p s1 /\
  Star (CS.sem_inform p) s1 (finpref_trace m) s2.
Proof.
  destruct m as [tm | tm | tm].
  - intros Hb Hm.
    destruct b as [t | ? | ? | ?];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh |]; subst.
    inversion Hbeh as [? s2 Hstar Hfinal | | |]; subst.
    eexists; eexists; split; now eauto.
  - intros Hb Hm.
    destruct b as [? | ? | ? | t];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh | Hini]; subst.
    + inversion Hbeh as [| | | ? s2 Hstar Hnostep Hfinal]; subst.
      eexists; eexists; split; now eauto.
    + specialize (Hini (CS.initial_machine_state p)).
      congruence.
  - revert b.
    induction tm as [| e t IHt] using rev_ind;
      intros b Hb Hm;
      simpl in *.
    + exists (CS.initial_machine_state p), (CS.initial_machine_state p).
      split; [congruence | now apply star_refl].
    + pose proof behavior_prefix_app_inv Hm as Hprefix.
      specialize (IHt _ Hb Hprefix).
      destruct IHt as [s1 [s2 [Hini Hstar]]].
      inversion Hm as [b']; subst.
      inversion Hb as [s1' ? Hini' Hbeh' | Hini' Hbeh']; subst.
      * assert (Heq : s1 = s1')
          by now (inversion Hini; inversion Hini').
        subst s1'.
        inversion Hbeh' as [ t' s2' Hstar' Hfinal' Heq
                           | t' s2' Hstar' Hsilent' Heq
                           | T' Hreact' Heq
                           | t' s2' Hstar' Hstep' Hfinal' Heq];
          subst.
        (* RB: TODO: Refactor block. *)
        -- destruct b' as [tb' | ? | ? | ?];
             simpl in Heq;
             try discriminate.
           inversion Heq; subst t'; clear Heq.
           destruct (star_app_inv (CS.singleton_traces_inform p) _ _ Hstar')
             as [s' [Hstar'1 Hstar'2]].
           now eauto.
        -- (* Same as Terminates case. *)
          destruct b' as [? | tb' | ? | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces_inform p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
        -- (* Similar to Terminates and Diverges, but on an infinite trace.
              Ltac can easily take care of these commonalities. *)
          destruct b' as [? | ? | Tb' | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst T'; clear Heq.
          destruct (forever_reactive_app_inv (CS.singleton_traces_inform p) _ _ Hreact')
            as [s' [Hstar'1 Hreact'2]].
          now eauto.
        -- (* Same as Terminate and Diverges. *)
          destruct b' as [? | ? | ? | tb'];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces_inform p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
      * specialize (Hini' (CS.initial_machine_state p)).
        congruence.
Qed.

Theorem behavior_prefix_star_non_inform {p b m} :
  program_behaves (CS.sem_non_inform p) b ->
  prefix m b ->
exists s1 s2,
  CS.initial_state p s1 /\
  Star (CS.sem_non_inform p) s1 (finpref_trace m) s2.
Proof.
  destruct m as [tm | tm | tm].
  - intros Hb Hm.
    destruct b as [t | ? | ? | ?];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh |]; subst.
    inversion Hbeh as [? s2 Hstar Hfinal | | |]; subst.
    eexists; eexists; split; now eauto.
  - intros Hb Hm.
    destruct b as [? | ? | ? | t];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh | Hini]; subst.
    + inversion Hbeh as [| | | ? s2 Hstar Hnostep Hfinal]; subst.
      eexists; eexists; split; now eauto.
    + specialize (Hini (CS.initial_machine_state p)).
      congruence.
  - revert b.
    induction tm as [| e t IHt] using rev_ind;
      intros b Hb Hm;
      simpl in *.
    + exists (CS.initial_machine_state p), (CS.initial_machine_state p).
      split; [congruence | now apply star_refl].
    + pose proof behavior_prefix_app_inv Hm as Hprefix.
      specialize (IHt _ Hb Hprefix).
      destruct IHt as [s1 [s2 [Hini Hstar]]].
      inversion Hm as [b']; subst.
      inversion Hb as [s1' ? Hini' Hbeh' | Hini' Hbeh']; subst.
      * assert (Heq : s1 = s1')
          by now (inversion Hini; inversion Hini').
        subst s1'.
        inversion Hbeh' as [ t' s2' Hstar' Hfinal' Heq
                           | t' s2' Hstar' Hsilent' Heq
                           | T' Hreact' Heq
                           | t' s2' Hstar' Hstep' Hfinal' Heq];
          subst.
        (* RB: TODO: Refactor block. *)
        -- destruct b' as [tb' | ? | ? | ?];
             simpl in Heq;
             try discriminate.
           inversion Heq; subst t'; clear Heq.
           destruct (star_app_inv (CS.singleton_traces_non_inform p) _ _ Hstar')
             as [s' [Hstar'1 Hstar'2]].
           now eauto.
        -- (* Same as Terminates case. *)
          destruct b' as [? | tb' | ? | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces_non_inform p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
        -- (* Similar to Terminates and Diverges, but on an infinite trace.
              Ltac can easily take care of these commonalities. *)
          destruct b' as [? | ? | Tb' | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst T'; clear Heq.
          destruct (forever_reactive_app_inv (CS.singleton_traces_non_inform p) _ _ Hreact')
            as [s' [Hstar'1 Hreact'2]].
          now eauto.
        -- (* Same as Terminate and Diverges. *)
          destruct b' as [? | ? | ? | tb'];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces_non_inform p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
      * specialize (Hini' (CS.initial_machine_state p)).
        congruence.
Qed.

(*Print program_behavior.
SearchAbout traceinf.
Print project_non_inform.
Print project_non_inform.

CoFixpoint project_non_inform_traceinf (tinf: traceinf event_inform) :=
  match tinf with
  | Econsinf e_inform tinf' =>
    match e_inform with
    | ECall C P call_arg C' => Econsinf
                                 _ (Events.ECall C P call_arg C')
                                 (project_non_inform_traceinf tinf')
    | ERet C v C' => Econsinf
                       _ (Events.ERet C v C')
                       (project_non_inform_traceinf tinf')
    | _ => Eappinf E0 (project_non_inform_traceinf tinf')
    end
  end.

Definition project_non_inform_program_behavior (b: @program_behavior event_inform) :=
  match b with
  | Terminates t -> Terminates (project_non_inform t)
  | Diverges t -> Diverges (project_non_inform t)
  | Reacts tinf

Lemma program_behaves_non_inform_program_behaves_inform {p b} :
  program_behaves (CS.sem_non_inform p) b ->
  exists b_inform, program_behaves (CS.sem_inform p) b_inform /\
.
  

Theorem behavior_prefix_star_non_inform {p b m} :
  program_behaves (CS.sem_non_inform p) b ->
  prefix m b ->
exists s1 s2,
  CS.initial_state p s1 /\
  Star (CS.sem_non_inform p) s1 (finpref_trace m) s2.
Proof.
  intros Hbeh Hpref.
  pose proof program_behaves_non_inform_program_behaves_inform
*)
(* RB: TODO: These domain lemmas should now be renamed to reflect their
   operation on linked programs. *)
Section ProgramLink.
  Variables p c : program.
  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).
  Hypothesis Hprog_is_closed  : closed_program (program_link p c).

  (* RB: NOTE: Check with existing results.
     Possibly rewrite in terms of state_pc. *)
  Lemma star_pc_domm : forall {s st mem reg pc t},
    initial_state (program_link p c) s ->
    Star (sem_inform (program_link p c)) s t (st, mem, reg, pc) ->
    Pointer.component pc \in domm (prog_interface p) \/
    Pointer.component pc \in domm (prog_interface c).
  Proof.
    intros s st mem reg pc t Hini Hstar.
    assert (H : Pointer.component pc \in domm (prog_interface (program_link p c))).
    { replace pc with (CS.state_pc (st, mem, reg, pc)); try reflexivity.
      apply CS.comes_from_initial_state_pc_domm.
      destruct (cprog_main_existence Hprog_is_closed) as [_ [? _]].
      exists (program_link p c), s, t.
      split; first (destruct Hmergeable_ifaces; now apply linking_well_formedness).
      repeat split; eauto. }
    move: H. simpl. rewrite domm_union. now apply /fsetUP.
  Qed.

  Lemma star_pc_domm_non_inform : forall {s st mem reg pc t},
    initial_state (program_link p c) s ->
    Star (sem_non_inform (program_link p c)) s t (st, mem, reg, pc) ->
    Pointer.component pc \in domm (prog_interface p) \/
                             Pointer.component pc \in domm (prog_interface c).
  Proof.
    intros s st mem reg pc t Hini Hstar.
    pose proof star_sem_non_inform_star_sem_inform
         (program_link p c) s t (st, mem, reg, pc) Hstar
      as [t_inform [Hstar_inform Hproj]].
    exact (star_pc_domm Hini Hstar_inform).
  Qed.
End ProgramLink.


(************************************************************
Lemma genv_procedures_prog_procedures_in p cid fid instlst :
  well_formed_program p ->
  (omap (fun m => getm m fid)
        ((genv_procedures (globalenv (sem_inform p))) cid) = Some (Some instlst)
   <->
   omap (fun m => getm m fid) ((prog_procedures p) cid) = Some (Some instlst)).
Proof.
  intros Hwfp.
  pose (domm_domm := wfprog_defined_procedures Hwfp).
  pose (domm_domm1 := domm_prepare_procedures_initial_memory_aux p).
  unfold sem_inform. simpl. rewrite mapmE. rewrite mkfmapfE. simpl.
  destruct (cid \in domm (prog_interface p)) eqn:e; rewrite e; erewrite domm_domm in e;
    simpl; pose proof (mem_domm (prog_procedures p) cid) as e1; erewrite e1 in e;
      unfold isSome in e1;
      (
       destruct (@getm nat_ordType
                        (*(Phant (forall _ : Ord.sort nat_ordType, NMap code))*) _
                        (prog_procedures p)
                        cid) eqn:contra
       ||
       destruct (@getm nat_ordType
                       (NMap code)
                       (*(Phant (forall _ : Ord.sort nat_ordType, NMap code))*) _
                       (prog_procedures p)
                       cid) eqn:contra;
       idtac "ExStructures 0.1 legacy"
      ); try discriminate.
  
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { by erewrite domm_domm. }
    move : etmp => /dommP => e0.
    destruct ((prog_interface p) cid) eqn:e1';
      destruct e0 as [x H0]; rewrite -e1' in H0; rewrite e1' in H0; last discriminate.
    inversion H0. subst. clear H0 e. simpl in *.
    unfold reserve_component_blocks.
    destruct (ComponentMemoryExtra.reserve_blocks
                (ComponentMemory.prealloc
                   match prog_buffers p cid with
                   | Some buf => setm (T:=nat_ordType) emptym Block.local buf
                   | None => emptym
                   end)
                (length (elementsm n)))
      as [compMem bs] eqn:rsvblk.
    split; intros H.
    + rewrite rsvblk in H.
      simpl in H. rewrite <- H.      
      inversion H as [H1]. apply mkfmap_Some in H1.
      specialize (in_zip1 H1) as Hin1.
      specialize (in_zip2 H1) as Hin2.
      Search ComponentMemoryExtra.reserve_blocks.
      apply in_unzip2 in Hin2 as [].
      Search seq.unzip2.
      apply 
      Search in_mem seq.zip.
      destruct n. simpl.
      (* Search _ bs. *)
      (** Is there really any relationship between bs and the domain of the NMap n? *)
      admit.
    + rewrite rsvblk. simpl.
      rewrite <- H.
      rewrite mkfmapE. destruct n. simpl.
      (* Search _ bs. *)
      (** Is there really any relationship between bs and the domain of the NMap n? *)
      admit.
    
  - split; by intros.

Admitted.
******************************************************************)

Lemma genv_procedures_prog_procedures p cid proc:
  well_formed_program p ->
  (
    exists procs bid,
      (genv_procedures (globalenv (sem_inform p))) cid = Some procs
      /\ procs bid = Some proc
  )
  ->
  (
    exists procs' bid', 
      (prog_procedures p) cid = Some procs' /\ procs' bid' = Some proc
  ).
Proof.
  intros Hwfp.
  pose (domm_domm := wfprog_defined_procedures Hwfp).
  pose (domm_domm1 := domm_prepare_procedures_initial_memory_aux p).
  unfold sem_inform. simpl. rewrite mapmE. rewrite mkfmapfE. simpl.
  destruct (cid \in domm (prog_interface p)) eqn:e; rewrite e; erewrite domm_domm in e;
    simpl; pose (mem_domm (prog_procedures p) cid) as e1; erewrite e in e1;
      unfold isSome in e1; destruct ((prog_procedures p) cid) eqn:contra; auto;
        (* rewrite contra in e1; *)
        try discriminate; auto; clear e1;
          unfold reserve_component_blocks; intros [procs [bid H]].
Qed.

(****************************************************************
- assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose proof (@dommP _ _ (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0];
           try (rewrite e1 in H0 || idtac "ExStructures 0.1 legacy rewrite");
           discriminate).
    destruct (ComponentMemoryExtra.reserve_blocks
                (ComponentMemory.prealloc (*(odflt emptym ((prog_buffers p) cid))*)
                   match prog_buffers p cid with
                   | Some buf => setm (T:=nat_ordType) emptym Block.local buf
                   | None => emptym
                   end
                )
         (length (elementsm (odflt emptym (Some n)))))
             as [compMem bs] eqn:rsvblk.
    rewrite rsvblk.
    destruct H as [H1 H2].
    apply ComponentMemoryExtra.reserve_blocks_length in rsvblk.
    Search wfprog_well_formed_instructions.
    exists n. inversion H1. subst. apply mkfmap_Some in H2.
    specialize (in_zip2 H2) as H2_2.
    unfold elementsm in *. apply in_unzip2 in H2_2 as [? ?]. by eauto. 
  
***************************************************************************)



    


(*******************************************************************
Lemma genv_procedures_prog_procedures p cid proc :
  well_formed_program p ->
  (genv_procedures (globalenv (sem_inform p))) cid = proc <-> (prog_procedures p) cid = proc.
Proof.
  intros Hwfp.
  pose (domm_domm := wfprog_defined_procedures Hwfp).
  pose (domm_domm1 := domm_prepare_procedures_initial_memory_aux p).
  unfold sem_inform. simpl. rewrite mapmE. rewrite mkfmapfE. simpl.
  destruct (cid \in domm (prog_interface p)) eqn:e; rewrite e; erewrite domm_domm in e;
    simpl; pose (mem_domm (prog_procedures p) cid) as e1; erewrite e in e1;
      unfold isSome in e1; destruct ((prog_procedures p) cid) eqn:contra; auto;
        (* rewrite contra in e1; *)
        try discriminate; split; auto; clear e1;
          unfold reserve_component_blocks; intros H.
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose proof (@dommP _ _ (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0];
           try (rewrite e1 in H0 || idtac "ExStructures 0.1 legacy rewrite");
           discriminate).
    destruct (ComponentMemoryExtra.reserve_blocks
                (ComponentMemory.prealloc (*(odflt emptym ((prog_buffers p) cid))*)
                   match prog_buffers p cid with
                   | Some buf => setm (T:=nat_ordType) emptym Block.local buf
                   | None => emptym
                   end
                )
         (length (elementsm (odflt emptym (Some n)))))
             as [compMem bs] eqn:rsvblk.
    rewrite rsvblk in H.
    simpl in H. rewrite <- H.
    assert (g: n = mkfmap (T:=nat_ordType) (seq.zip bs (seq.unzip2 (elementsm n)))).
    {
      (* This goal is hard.
         n is a map. So, it is better if the lemma were stated in terms of
       equality of the contents rather than just equality.*)
      admit.
    }
    rewrite <- g; auto.
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose proof (@dommP _ _ (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0]; rewrite e1 in H0; discriminate).

Admitted.
************************************************************************)


(* RB: TODO: [DynShare] This result may not be in standard form for this file,
   adjust if needed ([does_prefix] not being used here, say). *)
Theorem does_prefix_inform_non_inform :
  forall p m,
    does_prefix (sem_inform p) m ->
    does_prefix (sem_non_inform p) (project_finpref_behavior m).
Admitted.

Lemma star_final_no_more_events p t_inform sinit s':
  star step (prepare_global_env p) sinit t_inform s' ->
  forall s'0,
  Star (sem_non_inform p) sinit (project_non_inform t_inform) s'0 ->
  Smallstep.final_state (sem_non_inform p) s'0 ->
  Star (sem_inform p) sinit t_inform s'0.
Proof.
  intros Hstarinform.
  induction Hstarinform; intros s'0 Hstarproj Hfinal; simpl in *.
  - 
    apply star_sem_non_inform_star_sem_inform in Hstarproj as [t_inform Hstar].
    
(****    inversion Hstarproj; subst; first by apply star_refl.
    + 
 ******)
Abort.

(**********************
Theorem does_prefix_non_inform_inform :
  forall p m,
 does_prefix (sem_non_inform p) m ->
 exists m_inform,
   does_prefix (sem_inform p) m_inform /\ project_finpref_behavior m_inform = m.
Proof.
   unfold does_prefix. intros ? ? H_doesm_noninform.
   destruct H_doesm_noninform as [b_noninform [Hb_noninform Hpref]].
   specialize (behavior_prefix_star_non_inform Hb_noninform Hpref)
     as [s_init [s' [Hinit Hstar]]].
   apply star_sem_non_inform_star_sem_inform in Hstar as [t_inform [Hstar Hproj]].
   exists (match m with
           | FTbc _ => FTbc t_inform
           | FGoes_wrong _ => FGoes_wrong t_inform
           | FTerminates _ => FTerminates t_inform
           end
          ).
   destruct m; split; try (simpl; by rewrite Hproj).
   - simpl in Hpref. destruct b_noninform; subst; try contradiction.
     inversion Hb_noninform as [s ? Hinit2 Hbeh | ]; subst.
     simpl in *.
     unfold initial_state in *. rewrite -Hinit in Hinit2. subst.
     exists (Terminates t_inform). split; last easy.
     econstructor.
     + simpl. reflexivity.
     + inversion Hbeh; subst.
       econstructor; last eassumption.
       Search _ "det" step.
       generalize dependent 
       SearchAbout s'.
       last eassumption.
       Search _ "_non" "inform".
       apply star_sem_non_inform_star_sem_inform in H0.
   -  by eapply program_behaves_finpref_exists; eauto.
       
Qed.
************************************)

(* RB: TODO: Inspired by [domm_partition] on PS. Consider how to select the
   right semantics, the best shape of the premises, and naming conventions to
   avoid confusion, esp. if it similar lemmas will be used (again) elsewhere.
   This statement a little less generic than other similar lemmas, but easier
   to use where it is needed now (recomposition). *)
Lemma domm_partition :
  forall p1 p2 s t gps mem regs pc,
    well_formed_program p1 ->
    well_formed_program p2 ->
    closed_program (program_link p1 p2) ->   
    mergeable_interfaces (prog_interface p1) (prog_interface p2) ->
    CS.initial_state (program_link p1 p2) s ->
    Star (CS.sem_non_inform (program_link p1 p2)) s t (gps, mem, regs, pc) ->
    Pointer.component pc \notin domm (prog_interface p2) ->
    Pointer.component pc \in domm (prog_interface p1).
Proof.
  intros ? ? ? ? ? ? ? ? Hwf1 Hwf2 Hclosed Hmerge Hinit Hstar Hnotin.
  specialize (@star_pc_domm_non_inform _ _ Hwf1 Hwf2 Hmerge Hclosed
                                       _ _ _ _ _ _ Hinit Hstar
             ) as [G | G]; auto.
  - by rewrite G in Hnotin.
Qed.

Lemma domm_partition_in_left_not_in_right :
  forall p1 p2 s t gps mem regs pc,
    mergeable_interfaces (prog_interface p1) (prog_interface p2) ->
    CS.initial_state (program_link p1 p2) s ->
    Star (CS.sem_non_inform (program_link p1 p2)) s t (gps, mem, regs, pc) ->
    Pointer.component pc \in domm (prog_interface p1) ->
    Pointer.component pc \notin domm (prog_interface p2).
Proof.
  intros ? ? ? ? ? ? ? ? [[_ Hdisj] _] _ _ Hin.
  pose proof (fdisjointP _ _ Hdisj) as G. by apply G in Hin.
Qed.

Section SemanticsInformProperties.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  (* Should follow from well_formed_program p *)
Lemma IConst_possible_values pc v r:
  executing G pc (IConst v r) ->
  (
    (exists i : Z, v = IInt i) \/
    (exists
        (perm : Permission.id) (cid : Component.id) (bid : Block.id) 
        (off : Block.offset) (*procs*),
        v = IPtr (perm, cid, bid, off) /\
        cid = Pointer.component pc /\
        bid = Block.local /\
        perm = Permission.data (*/\*)
        (*prog_procedures p (Pointer.component pc) = Some procs /\
        procs bid*)
    )
  ).
Proof.
  destruct pc as [[[pcperm pcc] pcb] pcoff].
  intros [C_procs [P_code [H1 [H2 [H3 [H4 H5]]]]]].
  destruct valid_program.
  simpl in *; subst.
  assert (Hprepare: prepare_procedures_procs p pcc = Some C_procs).
  {
    by unfold prepare_procedures_procs, prepare_procedures_initial_memory.
  }
  specialize (prepare_procedures_procs_prog_procedures
                valid_program Hprepare H2) as [C_procs' [b' [HC_procs'1 HC_procs'2]]].
  assert (In (IConst v r) P_code) as Hin.
  {
    by eapply nth_error_In; eauto. 
  }
  specialize (wfprog_well_formed_instructions0 _ _ HC_procs'1 _ _ HC_procs'2 _ Hin).
  unfold well_formed_instruction in *.
  destruct v as [|[[[perm c] b] off]]; first by left; eexists; eauto.
  right. simpl in *.
  destruct wfprog_well_formed_instructions0 as [? [? [buf [Hbuf ?]]]]. subst.
  exists Permission.data, pcc, Block.local, off (*, C_procs'*).
  repeat (split; try reflexivity).
  (*split; first assumption.*)
Qed.

Lemma intermediate_well_formed_events st t st' :
  Star (sem_inform p) st t st' ->
  seq.all (well_formed_event
             (Intermediate.prog_interface p)
             (Intermediate.prog_procedures p)
          )
          t.
Proof.
elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
rewrite seq.all_cat IH andbT {Hstar}.
case: st1 t1 st2 / Hstep => //=.
- (* Relies on lemma IConst_possible_values above. *)
  intros _ _ ? ? ? ? ? Hexec Hreg.
  specialize (IConst_possible_values _ _ _ Hexec)
    as [[i ev]|[perm [cid [bid [off [? [? [? ?]]] ]]]]];
    subst; auto.
  simpl. by rewrite !eqxx.

- intros ? ? ? ? ? ? ? ? Hexec Hfind _.
  specialize (find_label_in_component_1 _ _ _ _ Hfind) as Hcomp.
  destruct ptr as [[[perm cid] bid] ?]. simpl in *. subst.
  destruct perm eqn:eperm; auto; simpl in *; subst; last first.
  + specialize (find_label_in_component_perm _ _ _ _ Hfind) as Hperm.
    destruct pc as [[[perm ?] ?] ?]. simpl in *. subst.
    destruct Hexec as [? [? [? [? [? [? ?]]]]]]. discriminate.
  + unfold find_label_in_component in *.
    destruct (genv_procedures (prepare_global_env p) (Pointer.component pc))
      as [procMap|] eqn:eSome;
      last discriminate.
    assert (exists x, prog_procedures p (Pointer.component pc) = Some x) as [? HSome].
    {
      apply/dommP. rewrite <- wfprog_defined_procedures; auto.
      rewrite <- domm_genv_procedures. apply/dommP. by eauto.
    }
    erewrite <- genv_procedures_prog_procedures_eq; eauto.
    rewrite eSome andbT -beq_nat_refl andTb.
    apply find_label_in_component_helper_Some_exists_code in Hfind as [? G1]; auto.
    by rewrite G1.
    

- intros ? ? ? ? ? ? ? Hexec Hfind _.
  specialize (Pointer.inc_preserves_permission pc) as Hperm.
  specialize (Pointer.inc_preserves_component pc) as Hcomp.
  specialize (Pointer.inc_preserves_block pc) as Hblock.
  
  destruct (Pointer.inc pc) as [[[perm cid] bid] ?].
  simpl in *. subst.

  assert (Pointer.permission pc = Permission.code) as HShouldBeProvable.
  { by inversion Hexec as [? [? [? [? [? [? ?]]]]]].  }

  rewrite HShouldBeProvable. rewrite <- !beq_nat_refl.

  assert (exists procs, prog_procedures p (Pointer.component pc) = Some procs)
    as [procs HShouldBeProvable2].
  {
    apply/dommP. rewrite -wfprog_defined_procedures; last assumption.
    inversion Hexec as [? [? [G1 _]]].
    rewrite <- domm_genv_procedures.
    apply/dommP. by eauto.
  }

  rewrite HShouldBeProvable2 andTb andbT.
  inversion Hexec as [? [? [G1 [G2 _]]]].
  erewrite genv_procedures_prog_procedures_eq in G1; eauto.
  rewrite HShouldBeProvable2 in G1.
  inversion G1. subst. by rewrite G2.
- move=> ????????? /eqP ->.
    by move=> /imported_procedure_iff /= ->.
- by move=> ??????? /eqP ->.
Qed.

(* Print Assumptions intermediate_well_formed_events. *)

Lemma intermediate_well_formed_trace : forall t cs cs',
  Star (sem_inform p) cs t cs' ->
  CS.initial_state p cs ->
  Intermediate.prog_main p ->
  Intermediate.well_formed_program p ->
  well_formed_trace (Intermediate.prog_interface p) (prog_procedures p) t.
Proof.
  intros t cs cs' H H' H'' H'''.
  unfold well_formed_trace. apply/andP; split; last by apply: intermediate_well_formed_events H.
  apply intermediate_well_bracketed_trace in H.
  suffices <- : stack_state_of cs = stack_state0 by [].
  rewrite /initial_state /initial_machine_state in H'.
  by rewrite H' H''.
Qed.


End SemanticsInformProperties.


Section SemanticsNonInformProperties.
  
  Variable p: program.
  
  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.
  
  Let G := prepare_global_env p.

  
Lemma well_formed_event_inform_well_formed_event_project_non_inform t_inform t_non_inform:
  seq.all
    (TracesInform.well_formed_event
       (Intermediate.prog_interface p)
       (prog_procedures p)
    )
    t_inform
  ->
  project_non_inform t_inform = t_non_inform ->
  seq.all (Traces.well_formed_event (Intermediate.prog_interface p)) t_non_inform.
Admitted.

Lemma intermediate_well_formed_events_non_inform st t st' :
  Star (sem_non_inform p) st t st' ->
  seq.all (Traces.well_formed_event (Intermediate.prog_interface p)) t.
Proof.
  intros Hstar.
  pose proof star_sem_non_inform_star_sem_inform p st t st' Hstar
    as [t_inform [Hstar_inform Hproj]].
  pose proof intermediate_well_formed_events
       p
       valid_program
       st t_inform st' Hstar_inform as Hwf_inform.
  exact (well_formed_event_inform_well_formed_event_project_non_inform
           t_inform t Hwf_inform Hproj).
Qed.

Lemma well_formed_trace_inform_well_formed_trace_project_non_inform t_inform t_non_inform:
  TracesInform.well_formed_trace
    (Intermediate.prog_interface p)
    (prog_procedures p)
    t_inform ->
  project_non_inform t_inform = t_non_inform ->
  Traces.well_formed_trace (Intermediate.prog_interface p) t_non_inform.
Admitted.

Lemma intermediate_well_formed_trace_non_inform : forall t cs cs',
  Star (sem_non_inform p) cs t cs' ->
  CS.initial_state p cs ->
  Intermediate.prog_main p ->
  Intermediate.well_formed_program p ->
  Traces.well_formed_trace (Intermediate.prog_interface p) t.
Proof.
  intros t cs cs' H H' H'' H'''.
  pose proof star_sem_non_inform_star_sem_inform p cs t cs' H
    as [t_inform [Hstar_inform Hproj]].
  pose proof intermediate_well_formed_trace p valid_program
       t_inform cs cs' Hstar_inform H' H'' H'''
    as Hwf_trace_inform.
  exact (well_formed_trace_inform_well_formed_trace_project_non_inform
           t_inform t Hwf_trace_inform Hproj).
Qed.

End SemanticsNonInformProperties.

End CS.

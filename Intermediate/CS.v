Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Lib.Monads.

Module CS.

Import Intermediate.

Definition stack : Type := list Pointer.t.

Definition state : Type := stack * Memory.t * Register.t * Pointer.t.

Definition initial_state
           (G: global_env)
           (mainC: Component.id) (mainP: Procedure.id)
           (s: state) : Prop :=
  let '(gps, mem, regs, pc) := s in
  (* the global protected stack is empty *)
  gps = [] /\
  (* the program counter is pointing to the start of the main procedure *)
  EntryPoint.get mainC mainP (genv_entrypoints G) = Some (Pointer.block pc) /\
  Pointer.component pc = mainC /\
  Pointer.offset pc = 0.

Definition final_state (G: global_env) (s: state) (r: int) : Prop :=
  let '(gsp, mem, regs, pc) := s in
  executing G pc IHalt.

Inductive step (G : global_env) : state -> trace -> state -> Prop :=
| Nop: forall gps mem regs pc,
    executing G pc INop ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc)

| Label: forall gps mem regs pc l,
    executing G pc (ILabel l) ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc)

| Const: forall gps mem regs regs' pc r v,
    executing G pc (IConst v r) ->
    Register.set r (imm_to_val v) regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

| Mov: forall gps mem regs regs' pc r1 r2,
    executing G pc (IMov r1 r2) ->
    Register.set r2 (Register.get r1 regs) regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

| BinOp: forall gps mem regs regs' pc r1 r2 r3 op,
    executing G pc (IBinOp op r1 r2 r3) ->
    Register.set r3
                 (eval_binop op (Register.get r1 regs) (Register.get r2 regs))
                 regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

| Load: forall gps mem regs regs' pc r1 r2 ptr v,
    executing G pc (ILoad r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

| Store: forall gps mem regs pc ptr r1 r2 mem',
    executing G pc (IStore r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = Pointer.component pc ->
    Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
    step G (gps, mem, regs, pc) E0 (gps, mem', regs, Pointer.inc pc)

| Jal: forall gps mem regs regs' pc pc' l,
    executing G pc (IJal l) ->
    find_label_in_component G pc l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs', pc')

| Jump: forall gps mem regs pc pc' r,
    executing G pc (IJump r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.component pc' = Pointer.component pc ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc')

| BnzNZ: forall gps mem regs pc pc' r l val,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int val ->
    val <> 0 ->
    find_label_in_procedure G pc l = Some pc' ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc')

| BnzZ: forall gps mem regs pc r l,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int 0 ->
    step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc)

| Alloc: forall gps mem mem' regs regs' pc rsize rptr size ptr,
    executing G pc (IAlloc rptr rsize) ->
    Register.get rsize regs = Int size ->
    Memory.alloc mem (Pointer.component pc) size = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem', regs', Pointer.inc pc)

| Call: forall gps gps' mem regs pc b C' P rcomval,
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    gps' = Pointer.inc pc :: gps ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    let pc' := (C', b, 0) in
    Register.get R_COM regs = Int rcomval ->
    let t := [ECall (Pointer.component pc) P rcomval C'] in
    step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc')

| Return: forall gps gps' mem regs pc pc' rcomval,
    executing G pc IReturn ->
    gps = pc' :: gps' ->
    Pointer.component pc <> Pointer.component pc' ->
    Register.get R_COM regs = Int rcomval ->
    let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
    step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc').

(* TODO use init instead of init_env *)
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

Import MonadNotations.
Open Scope monad_scope.

Definition eval_step (G: global_env) (s: state) : option (trace * state) :=
  let '(gps, mem, regs, pc) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- NMap.find (Pointer.component pc) (genv_procedures G);
  do P_code <- NMap.find (Pointer.block pc) C_procs;
  do instr <- nth_error P_code (Pointer.offset pc);
  (* decode and execute the instruction *)
  match instr with
  | ILabel l =>
    ret (E0, (gps, mem, regs, Pointer.inc pc))
  | INop =>
    ret (E0, (gps, mem, regs, Pointer.inc pc))
  | IConst v r =>
    let regs' := Register.set r (imm_to_val v) regs in
    ret (E0, (gps, mem, regs', Pointer.inc pc))
  | IMov r1 r2 =>
    let regs' := Register.set r2 (Register.get r1 regs) regs in
    ret (E0, (gps, mem, regs', Pointer.inc pc))
  | IBinOp op r1 r2 r3 =>
    let regs' := Register.set
                   r3 (eval_binop op (Register.get r1 regs) (Register.get r2 regs))
                   regs in
    ret (E0, (gps, mem, regs', Pointer.inc pc))
  | ILoad r1 r2 =>
    match Register.get r1 regs with
    | Ptr ptr =>
      do v <- Memory.load mem ptr;
      let regs' := Register.set r2 v regs in
      ret (E0, (gps, mem, regs', Pointer.inc pc))
    | _ => None
    end
  | IStore r1 r2 =>
    match Register.get r1 regs with
    | Ptr ptr =>
      if Pointer.component ptr =? Pointer.component pc then
        do mem' <- Memory.store mem ptr (Register.get r2 regs);
        ret (E0, (gps, mem', regs, Pointer.inc pc))
      else
        None
    | _ => None
    end
  | IJal l =>
    do pc' <- find_label_in_component G pc l;
    let regs' :=  Register.set R_RA (Ptr (Pointer.inc pc)) regs in
    ret (E0, (gps, mem, regs', pc'))
  | IJump r =>
    match Register.get r regs with
    | Ptr pc' =>
      if Pointer.component pc' =? Pointer.component pc then
        ret (E0, (gps, mem, regs, pc'))
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
    do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) size;
      let regs' := Register.set rptr (Ptr ptr) regs in
      ret (E0, (gps, mem', regs', Pointer.inc pc))
    | _ => None
    end
  | ICall C' P =>
    if negb (Pointer.component pc =? C') then
      if imported_procedure_b (genv_interface G) (Pointer.component pc) C' P then
        do b <- EntryPoint.get C' P (genv_entrypoints G);
        match Register.get R_COM regs with
        | Int rcomval =>
          let pc' := (C', b, 0) in
          let t := [ECall (Pointer.component pc) P rcomval C'] in
          ret (t, (Pointer.inc pc :: gps, mem, Register.invalidate regs, pc'))
        | _ => None
        end
      else
        None
    else
      None
  | IReturn =>
    match gps with
    | pc' :: gps' =>
      if negb (Pointer.component pc =? Pointer.component pc') then
        match Register.get R_COM regs with
        | Int rcomval =>
          let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
          ret (t, (gps', mem, Register.invalidate regs, pc'))
        | _ => None
        end
      else
        None
    | _ => None
    end
  | IHalt => None
  end.

Fixpoint init_mem m bufs :=
  match bufs with
  | [] => m
  | (C, Cbufs) :: bufs' =>
    let m' := NMap.add C (ComponentMemory.prealloc Cbufs) m in
    init_mem m' bufs'
  end.

Fixpoint init_comp_procs m E ps C Cprocs
  : option (Memory.t * EntryPoint.t * NMap.t (NMap.t code)) :=
  match Cprocs with
  | [] => Some (m, E, ps)
  | (P, bytecode) :: Cprocs' =>
    do Cmem <- NMap.find C m;
    let '(Cmem', b) := ComponentMemory.reserve_block Cmem in
    let m' := NMap.add C Cmem' m in
    let Centrypoints :=
        match NMap.find C E with
        | None => NMap.empty Block.id
        | Some old_Centrypoints => old_Centrypoints
        end in
    let Centrypoints' := NMap.add P b Centrypoints in
    let E' := NMap.add C Centrypoints' E in
    let Cps :=
        match NMap.find C ps with
        | None => NMap.empty code
        | Some oldCps => oldCps
        end in
    let Cps' := NMap.add b bytecode Cps in
    let ps' := NMap.add C Cps' ps in
    init_comp_procs m' E' ps' C Cprocs'
  end.

Definition init_all (p: program) :=
  let fix init_all_procs m E ps procs :=
      match procs with
      | [] => Some (m, E, ps)
      | (C, Cprocs) :: procs' =>
        do (m', E', ps') <- init_comp_procs m E ps C (NMap.elements Cprocs);
        init_all_procs m' E' ps' procs'
      end
  in
  let m := init_mem (Memory.empty []) (NMap.elements (prog_buffers p)) in
  init_all_procs m (NMap.empty (NMap.t Block.id)) (NMap.empty (NMap.t code))
                 (NMap.elements (prog_procedures p)).

Definition init
           (p: program) (mainC: Component.id) (mainP: Procedure.id)
  : option (global_env * state) :=
  do (mem, entrypoints, procs) <- init_all p;
  let G := {| genv_interface := prog_interface p;
              genv_procedures := procs;
              genv_entrypoints := entrypoints |} in
  do b <- EntryPoint.get mainC mainP entrypoints;
  ret (G, ([], mem, Register.init, (mainC, b, 0))).

Fixpoint execN (n: nat) (G: global_env) (st: state) : option nat :=
  match n with
  | 0 => None
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

Definition run (p: program) (input: value) (fuel: nat) : option nat :=
  do (G, st) <- init p 1 0;
  execN fuel G st.

Close Scope monad_scope.

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st =  Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    destruct H as [procs [P_code [Hprocs [HP_code Hinstr]]]];
    simpl; unfold code in *; rewrite Hprocs, HP_code, Hinstr;
      try reflexivity.
  - rewrite H0, H1. reflexivity.
  - rewrite H0, H1, H2.
    rewrite <- beq_nat_refl. reflexivity.
  - rewrite H0. reflexivity.
  - rewrite H0, H1.
    rewrite <- beq_nat_refl. reflexivity.
  - rewrite H0, H2.
    destruct val.
    + contradiction.
    + reflexivity.
  - rewrite H0. reflexivity.
  - rewrite H0, H1. reflexivity.
  - rewrite H3, H4.
    destruct (Pointer.component pc =? C') eqn:Hpc_eq_C'.
    + apply beq_nat_true_iff in Hpc_eq_C'.
      rewrite <- Hpc_eq_C' in H0.
      contradiction.
    + simpl.
      destruct (imported_procedure_iff (genv_interface G) (Pointer.component pc) C' P)
        as [H' H''].
      rewrite H'; auto.
  - rewrite H2.
    destruct (Pointer.component pc =? Pointer.component pc') eqn:Hpc_eq_pc'.
    + apply beq_nat_true_iff in Hpc_eq_pc'.
      rewrite <- Hpc_eq_pc' in H1.
      contradiction.
    + simpl. reflexivity.
Qed.

Ltac unfold_state :=
  match goal with
  | H: state |- _ =>
    let s := fresh "s" in
    let mem := fresh "mem" in
    let regs := fresh "regs" in
    let pc := fresh "pc" in
    destruct H as [[[s mem] regs] pc]
  end.

Theorem eval_step_sound:
  forall G st t st',
    eval_step G st =  Some (t, st') -> step G st t st'.
Proof.
  intros G st t st' Heval_step.
  repeat unfold_state.
  destruct (NMap.find (Pointer.component pc0) (genv_procedures G))
    as [C_procs | ?] eqn:HC_procs.
  - destruct (NMap.find (Pointer.block pc0) C_procs)
      as [P_code | ?] eqn:HP_code.
    + destruct (nth_error P_code (Pointer.offset pc0))
        as [instr | ?] eqn:Hinstr.
      (* case analysis on the fetched instruction *)
      * simpl in Heval_step. unfold code in *.
        rewrite HC_procs, HP_code, Hinstr in Heval_step.
        destruct instr; inversion Heval_step; subst; clear Heval_step.
        ** apply Nop. unfold executing. eexists. eexists. eauto.
        ** eapply Label. unfold executing. eexists. eexists. eauto.
        ** eapply Const. unfold executing. eexists. eexists. eauto.
           reflexivity.
        ** eapply Mov. unfold executing. eexists. eexists. eauto.
           reflexivity.
        ** eapply BinOp. unfold executing. eexists. eexists. eauto.
           reflexivity.
        ** destruct (Register.get r regs0) eqn:Hreg.
           *** discriminate.
           *** destruct (Memory.load mem0 t0) eqn:Hmem.
               **** inversion H0. subst.
                    eapply Load. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply Hmem. reflexivity.
               **** discriminate.
           *** discriminate.
        ** destruct (Register.get r regs0) eqn:Hreg.
           *** discriminate.
           *** destruct (Pointer.component t0 =? Pointer.component pc0) eqn:Hcompcheck.
               **** destruct (Memory.store mem0 t0 (Register.get r0 regs0)) eqn:Hmem.
                    ***** inversion H0. subst.
                    eapply Store. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply beq_nat_true_iff. apply Hcompcheck.
                    apply Hmem.
                    ***** discriminate.
               **** discriminate.
           *** discriminate.
        ** destruct (Register.get r0 regs0) eqn:Hreg.
           *** destruct (Memory.alloc mem0 (Pointer.component pc0) n) eqn:Hmem.
               **** destruct p. inversion H0. subst.
                    eapply Alloc. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply Hmem. reflexivity.
               **** discriminate.
           *** discriminate.
           *** discriminate.
        ** destruct (Register.get r regs0) eqn:Hreg.
           *** destruct n eqn:Hn.
               **** inversion H0. subst.
                    eapply BnzZ. unfold executing. eexists. eexists. eauto.
                    apply Hreg.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel.
                    ***** inversion H0. subst.
                          eapply BnzNZ. unfold executing. eexists. eexists. eauto.
                          apply Hreg. auto. auto.
                    ***** discriminate.
           *** discriminate.
           *** discriminate.
        ** destruct (Register.get r regs0) eqn:Hreg.
           *** discriminate.
           *** destruct (Pointer.component t0 =? Pointer.component pc0) eqn:Hcompcheck.
               **** inversion H0. subst.
                    eapply Jump. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply beq_nat_true_iff. auto.
               **** discriminate.
           *** discriminate.
        ** destruct (find_label_in_component G pc0 l) eqn:Hlabel.
           *** inversion H0. subst.
               eapply Jal. unfold executing. eexists. eexists. eauto.
               auto. reflexivity.
           *** discriminate.
        ** destruct (Pointer.component pc0 =? i) eqn:Hcomp.
           *** simpl in H0. discriminate.
           *** simpl in H0.
               destruct (imported_procedure_b (genv_interface G)
                                              (Pointer.component pc0) i i0) eqn:Himport.
               **** destruct (EntryPoint.get i i0 (genv_entrypoints G)) eqn:Hentrypoint.
                    ***** destruct (Register.get R_COM regs0) eqn:Hreg.
                          ****** inversion H0. subst.
                                 eapply Call. unfold executing. eexists. eexists. eauto.
                                 apply beq_nat_false_iff. auto.
                                 apply imported_procedure_iff. auto.
                                 reflexivity.
                                 auto. auto.
                          ****** discriminate.
                          ****** discriminate.
                    ***** discriminate.
               **** discriminate.
        ** destruct s0.
           *** discriminate.
           *** destruct (Pointer.component pc0 =? Pointer.component t0) eqn:Hcomp.
               **** simpl in H0. discriminate.
               **** simpl in H0.
                    destruct (Register.get R_COM regs0) eqn:Hreg.
                    ***** inversion H0. subst.
                          eapply Return. unfold executing. eexists. eexists. eauto.
                          reflexivity.
                          apply beq_nat_false_iff. auto.
                          auto.
                    ***** discriminate.
                    ***** discriminate.
      * simpl in Heval_step. unfold code in *.
        rewrite HC_procs, HP_code, Hinstr in Heval_step.
        discriminate.
    + simpl in Heval_step.
      unfold code in *.
      rewrite HC_procs, HP_code in Heval_step.
      discriminate.
  - simpl in Heval_step.
    unfold code in *.
    rewrite HC_procs in Heval_step.
    discriminate.
Qed.

Theorem eval_step_correct:
  forall G st t st',
    eval_step G st =  Some (t, st') <-> step G st t st'.
Proof.
  split.
  apply eval_step_sound.
  apply eval_step_complete.
Qed.

Corollary step_deterministic:
  forall G st t st1 st2,
    step G st t st1 -> step G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hstep1 Hstep2.
  apply eval_step_correct in Hstep1.
  apply eval_step_correct in Hstep2.
  rewrite Hstep1 in Hstep2.
  inversion Hstep2.
  reflexivity.
Qed.

End CS.
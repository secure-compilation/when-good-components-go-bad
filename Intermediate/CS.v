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

Definition initial_state (p: program) (s: state) : Prop :=
  let G := init_genv p in
  let '(gps, mem, regs, pc) := s in
  (* the global protected stack is empty *)
  gps = [] /\
  (* mem exaclty contains all components memories and it comes from the init routine *)
  (forall C, PMap.In C (prog_interface p) <-> PMap.In C mem) /\
  (let '(m, _, _) := init_all p in mem = m) /\
  (* the origin register (R_AUX2) is set to 1 (meaning external call) *)
  (* the R_ONE register is set to 1 *)
  (* the other registers are set to undef *)
  regs = [Int 1; Undef; Undef; Undef; Int 1; Undef; Undef] /\
  (* the program counter is pointing to the start of the main procedure *)
  Pointer.component pc = fst (prog_main p) /\
  EntryPoint.get (fst (prog_main p)) (snd (prog_main p))
                 (genv_entrypoints G) = Some (Pointer.block pc) /\
  Pointer.offset pc = 0.

(* TODO these are here to make work Cbs.match_final_states that has a problem with int/nat *)
Axiom final_state2: state -> int -> Prop.

Definition final_state (G: global_env) (s: state) (r: nat) : Prop :=
  let '(gsp, mem, regs, pc) := s in
  Register.get R_COM regs = Int (Z.of_nat r) /\
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
    size >= 0 ->
    Memory.alloc mem (Pointer.component pc) (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    step G (gps, mem, regs, pc) E0 (gps, mem', regs', Pointer.inc pc)

| Call: forall gps gps' mem regs pc b C' P rcomval,
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    gps' = Pointer.inc pc :: gps ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    let pc' := (C', b, 0) in
    (* TODO fix the read value in the event *)
    Register.get R_COM regs = Int rcomval ->
    let t := [ECall (Pointer.component pc) P rcomval C'] in
    step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc')

| Return: forall gps gps' mem regs pc pc' rcomval,
    executing G pc IReturn ->
    gps = pc' :: gps' ->
    Pointer.component pc <> Pointer.component pc' ->
    (* TODO fix the read value in the event *)
    Register.get R_COM regs = Int rcomval ->
    let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
    step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc').

Import MonadNotations.
Open Scope monad_scope.

Definition eval_step (G: global_env) (s: state) : option (trace * state) :=
  let '(gps, mem, regs, pc) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- PMap.find (Pointer.component pc) (genv_procedures G);
  do P_code <- PMap.find (Pointer.block pc) C_procs;
  if Pointer.offset pc <? 0 then
    None
  else
    do instr <- nth_error P_code (Z.to_nat (Pointer.offset pc));
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
        if Pos.eqb (Pointer.component ptr) (Pointer.component pc) then
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
        if Pos.eqb (Pointer.component pc') (Pointer.component pc) then
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
        if size <? 0 then
          None
        else
          do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
          let regs' := Register.set rptr (Ptr ptr) regs in
          ret (E0, (gps, mem', regs', Pointer.inc pc))
      | _ => None
      end
    | ICall C' P =>
      if negb (Pos.eqb (Pointer.component pc) C') then
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
        if negb (Pos.eqb (Pointer.component pc) (Pointer.component pc')) then
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

Import MonadNotations.
Open Scope monad_scope.

Definition init_genv_and_state (p: program) : option (global_env * state) :=
  let '(mem, E, ps) := init_all p in
  let G := {| genv_interface := prog_interface p;
              genv_procedures := ps;
              genv_entrypoints := E |} in
  do b <- EntryPoint.get (fst (prog_main p)) (snd (prog_main p)) (genv_entrypoints G);
  ret (G, ([], mem, Register.init, (fst (prog_main p), b, 0))).

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

Definition run (p: program) (input: value) (fuel: nat) : option Z :=
  do (G, st) <- init_genv_and_state p;
  execN fuel G st.

Close Scope monad_scope.

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st =  Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    destruct H as [procs [P_code [Hprocs [HP_code [? Hinstr]]]]];
    simpl; unfold code in *; rewrite Hprocs, HP_code, Hinstr;
    destruct (Pointer.offset pc) eqn:Hpc;
    try reflexivity; try (exfalso; pose proof (Zlt_neg_0 p); omega).
  - simpl. rewrite H0, H1. reflexivity.
  - simpl. rewrite H0, H1. reflexivity.
  - rewrite H0, H1, H2.
    rewrite Pos.eqb_refl. reflexivity.
  - simpl. rewrite H0, H1, H2. rewrite Pos.eqb_refl. reflexivity.
  - rewrite H0. reflexivity.
  - simpl. rewrite H0. reflexivity.
  - rewrite H0, H1.
    rewrite Pos.eqb_refl. reflexivity.
  - simpl. rewrite H0, H1. rewrite Pos.eqb_refl. reflexivity.
  - rewrite H0, H2.
    destruct val.
    + contradiction.
    + reflexivity.
    + simpl. reflexivity.
  - simpl. rewrite H0, H2. destruct val.
    + contradiction.
    + reflexivity.
    + reflexivity.
  - rewrite H0. reflexivity.
  - simpl. rewrite H0. reflexivity.
  - simpl. rewrite H0, H2.
    destruct size; simpl.
    + reflexivity.
    + reflexivity.
    + contradiction.
  - simpl. rewrite H0, H2.
    destruct size; simpl.
    + reflexivity.
    + reflexivity.
    + contradiction.
  - simpl. rewrite H3, H4.
    destruct (Pos.eqb (Pointer.component pc) C') eqn:Hpc_eq_C'.
    + apply Pos.eqb_eq in Hpc_eq_C'.
      rewrite <- Hpc_eq_C' in H0.
      contradiction.
    + simpl.
      destruct (imported_procedure_iff (genv_interface G) (Pointer.component pc) C' P)
        as [H' H''].
      rewrite H'; auto.
  - apply Pos.eqb_neq in H0. rewrite H0. simpl.
    destruct (imported_procedure_iff (genv_interface G) (Pointer.component pc) C' P)
      as [H' H''].
    rewrite H'; auto.
    rewrite H3, H4. reflexivity.
  - simpl. rewrite H2.
    destruct (Pos.eqb (Pointer.component pc) (Pointer.component pc')) eqn:Hpc_eq_pc'.
    + apply Pos.eqb_eq in Hpc_eq_pc'.
      rewrite Hpc_eq_pc' in H1.
      contradiction.
    + simpl. reflexivity.
  - simpl. rewrite H2.
    destruct (Pos.eqb (Pointer.component pc) (Pointer.component pc')) eqn:Hpc_eq_pc'.
    + apply Pos.eqb_eq in Hpc_eq_pc'.
      rewrite Hpc_eq_pc' in H1.
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
  destruct (PMap.find (Pointer.component pc0) (genv_procedures G))
    as [C_procs | ?] eqn:HC_procs.
  - destruct (PMap.find (Pointer.block pc0) C_procs)
      as [P_code | ?] eqn:HP_code.
    + destruct (Pointer.offset pc0 >=? 0) eqn:Hpc.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ?] eqn:Hinstr.
        (* case analysis on the fetched instruction *)
        ** assert (Pointer.offset pc0 <? 0 = false). {
             destruct (Pointer.offset pc0); auto.
           }
           assert (Pointer.offset pc0 >= 0). {
             destruct (Pointer.offset pc0); discriminate.
           }
           simpl in Heval_step. unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct instr; inversion Heval_step; subst; clear Heval_step;
             try (match goal with
                  | Hpcfalse: Pointer.offset ?PC <? 0 = false,
                    Heq: (if Pointer.offset ?PC <? 0 then None else Some _) = Some _
                    |- _ => rewrite Hpcfalse in Heq; inversion Heq; subst; clear Heq Hpcfalse
                  end).
           *** apply Nop. unfold executing. eexists. eexists. eauto.
           *** eapply Label. unfold executing. eexists. eexists. eauto.
           *** eapply Const. unfold executing. eexists. eexists. eauto.
               reflexivity.
           *** eapply Mov. unfold executing. eexists. eexists. eauto.
               reflexivity.
           *** eapply BinOp. unfold executing. eexists. eexists. eauto.
               reflexivity.
           *** destruct (Register.get r regs0) eqn:Hreg.
               **** rewrite H in H2. discriminate.
               **** destruct (Memory.load mem0 t0) eqn:Hmem.
                    ***** rewrite H in H2. inversion H2. subst.
                          eapply Load. unfold executing. eexists. eexists. eauto.
                          apply Hreg. apply Hmem. reflexivity.
                    ***** rewrite H in H2. discriminate.
               **** rewrite H in H2. discriminate.
           *** destruct (Register.get r regs0) eqn:Hreg.
               **** rewrite H in H2. discriminate.
               **** destruct (Pos.eqb (Pointer.component t0) (Pointer.component pc0))
                             eqn:Hcompcheck.
                    ***** rewrite H in H2.
                    destruct (Memory.store mem0 t0 (Register.get r0 regs0)) eqn:Hmem.
                    ****** inversion H2. subst.
                    eapply Store. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply Pos.eqb_eq. apply Hcompcheck.
                    apply Hmem.
                    ****** discriminate.
                    ***** rewrite H in H2. discriminate.
               **** rewrite H in H2. discriminate.
           *** rewrite H in H2.
               destruct (Register.get r0 regs0) eqn:Hreg.
               **** destruct (z <? 0) eqn:Hzpos.
                    ***** discriminate.
                    ***** destruct (Memory.alloc mem0 (Pointer.component pc0) (Z.to_nat z))
                          eqn:Hmem.
                    ****** destruct p. inversion H2. subst.
                    eapply Alloc. unfold executing. eexists. eexists. eauto.
                    apply Hreg.
                    apply Z.ltb_ge in Hzpos. apply Z.ge_le_iff in Hzpos. auto.
                    apply Hmem.
                    reflexivity.
                    ****** discriminate.
               **** discriminate.
               **** discriminate.
           *** rewrite H in H2. 
               destruct (Register.get r regs0) eqn:Hreg.
               **** destruct z eqn:Hn.
                    ***** inversion H2. subst.
                    eapply BnzZ. unfold executing. eexists. eexists. eauto.
                    apply Hreg.
                    ***** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel.
                    ****** inversion H2. subst.
                    eapply BnzNZ. unfold executing. eexists. eexists. eauto.
                    apply Hreg. auto. auto.
                    ****** discriminate.
                    ***** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel.
                    ****** inversion H2. subst.
                    eapply BnzNZ. unfold executing. eexists. eexists. eauto.
                    apply Hreg. auto. auto.
                    ****** discriminate.
               **** discriminate. 
               **** discriminate.
           *** rewrite H in H2.
               destruct (Register.get r regs0) eqn:Hreg.
               **** discriminate.
               **** destruct (Pos.eqb (Pointer.component t0) (Pointer.component pc0))
                             eqn:Hcompcheck.
                    ***** inversion H2. subst.
                    eapply Jump. unfold executing. eexists. eexists. eauto.
                    apply Hreg. apply Pos.eqb_eq. auto.
                    ***** discriminate.
               **** discriminate.
           *** rewrite H in H2.
               destruct (find_label_in_component G pc0 l) eqn:Hlabel.
               **** inversion H2. subst.
                    eapply Jal. unfold executing. eexists. eexists. eauto.
                    auto. reflexivity.
               **** discriminate.
           *** rewrite H in H2.
               destruct (Pos.eqb (Pointer.component pc0) i) eqn:Hcomp.
               **** simpl in H0. discriminate.
               **** simpl in H0.
                    destruct (imported_procedure_b (genv_interface G)
                                                   (Pointer.component pc0) i i0)
                             eqn:Himport.
                    ***** destruct (EntryPoint.get i i0 (genv_entrypoints G))
                          eqn:Hentrypoint.
                    ****** destruct (Register.get R_COM regs0) eqn:Hreg.
                    ******* simpl in H2. inversion H2. subst.
                    eapply Call. unfold executing. eexists. eexists. eauto.
                    apply Pos.eqb_neq. auto.
                    apply imported_procedure_iff. auto.
                    reflexivity.
                    auto. auto.
                    ******* discriminate.
                    ******* discriminate.
                    ****** discriminate.
                    ***** discriminate.
           *** rewrite H in H2.
               destruct s0.
               **** discriminate.
               **** destruct (Pos.eqb (Pointer.component pc0) (Pointer.component t0))
                             eqn:Hcomp.
                    ***** simpl in H2. discriminate.
                    ***** simpl in H2.
                    destruct (Register.get R_COM regs0) eqn:Hreg.
                    ****** inversion H2. subst.
                    eapply Return. unfold executing. eexists. eexists. eauto.
                    reflexivity.
                    apply Pos.eqb_neq. auto.
                    auto.
                    ****** discriminate.
                    ****** discriminate.
           *** rewrite H in H2. discriminate.
        ** simpl in Heval_step. unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct (Pointer.offset pc0 <? 0); discriminate.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ?] eqn:Hinstr.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct (Pointer.offset pc0 <? 0) eqn:Hpc'.
           *** discriminate.
           *** exfalso. unfold Z.geb in Hpc.
               destruct (Pointer.offset pc0).
               **** simpl in *. discriminate.
               **** simpl in *. discriminate.
               **** simpl in *. pose proof (Zlt_neg_0 p). apply Z.ltb_lt in H.
                    rewrite Hpc' in H. discriminate.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct (Pointer.offset pc0 <? 0); discriminate.
    + simpl in Heval_step.
      unfold code in *.
      rewrite HC_procs, HP_code in Heval_step. discriminate.
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

Section Semantics.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := init_genv p.

  Definition sem :=
    @Semantics_gen state global_env step (initial_state p) (final_state G) G.

  Lemma determinate_step:
    forall s t1 s1 t2 s2,
      step G s t1 s1 ->
      step G s t2 s2 ->
      match_traces t1 t2 /\ (t1 = t2 -> s1 = s2).
  Proof.
    intros s t1 s1 t2 s2 Hstep1 Hstep2.
    inversion Hstep1; subst;
      inversion Hstep2; subst;
        try (split; [ apply match_traces_E0 | intro; reflexivity ]);
        match goal with
        | Hexec1: executing ?G ?PC ?INSTR1,
          Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
          destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
          destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
          rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
          rewrite HP_code in HP_code'; inversion HP_code'; subst;
          rewrite Hinstr in Hinstr'; inversion Hinstr'; subst
        end;
        try (exfalso; discriminate Hinstr');
        try (match goal with
             | |- match_traces ?T ?T /\ ?REST =>
               split; [ constructor
                      | intro; apply (step_deterministic G (gps, mem, regs, pc) T); auto ]
             end).
    (* call *)
    - rewrite H3 in H14. inversion H14. subst.
      rewrite H4 in H15. inversion H15. subst.
      split.
      + constructor.
      + intro. reflexivity.
    (* return *)
    - rewrite H2 in H11. inversion H11. subst.
      inversion H9. subst.
      split.
      + constructor.
      + intro. reflexivity.
  Qed.

  Lemma singleton_traces:
    single_events sem.
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
    unfold initial_state.
    intros s1 s2 Hs1_init Hs2_init.
    repeat unfold_state.
    destruct Hs1_init
      as [Hstack [Hmem1 [Hmem2 [Hregs [Hpc_comp [Hpc_block Hpc_offset]]]]]].
    destruct Hs2_init
      as [Hstack' [Hmem1' [Hmem2' [Hregs' [Hpc_comp' [Hpc_block' Hpc_offset']]]]]].
    subst.
    rewrite <- Hpc_comp in Hpc_comp'.
    rewrite Hpc_block in Hpc_block'.
    rewrite <- Hpc_offset in Hpc_offset'.
    (* program counter component *)
    unfold Pointer.component in Hpc_comp'.
    destruct pc. destruct p0.
    destruct pc0. destruct p0.
    subst.
    (* program counter block *)
    inversion Hpc_block'. subst.
    (* program counter offset *)
    unfold Pointer.offset in Hpc_offset'.
    subst.
    (* memory *)
    destruct (init_all p). destruct p0.
    subst. reflexivity.
  Qed.

  Lemma final_states_stuckness:
    forall s r,
      final_state G s r ->
      nostep step G s.
  Proof.
    intros s r Hs_final.
    unfold nostep.
    unfold_state.
    unfold final_state in Hs_final.
    destruct Hs_final as [Hres Hexec].
    intros t s'. unfold not. intro Hstep.
    inversion Hstep; subst;
    try (match goal with
         | Hexec1: executing ?G ?PC ?INSTR1,
           Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
           destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
           destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
           rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
           rewrite HP_code in HP_code'; inversion HP_code'; subst;
           rewrite Hinstr in Hinstr'; inversion Hinstr'
         end).
  Qed.

  Lemma final_states_uniqueness:
    forall s r1 r2,
      final_state G s r1 ->
      final_state G s r2 -> r1 = r2.
  Proof.
    unfold final_state.
    intros s r1 r2 Hs_final1 Hs_final2.
    unfold_state.
    destruct Hs_final1 as [Hres1 Hexec1].
    destruct Hs_final2 as [Hres2 Hexec2].
    rewrite Hres1 in Hres2.
    inversion Hres2.
    omega.
  Qed.

  Lemma determinacy:
    determinate sem.
  Proof.
    constructor.
    - apply determinate_step.
    - apply singleton_traces.
    - apply determinate_initial_states.
    - apply final_states_stuckness.
    - apply final_states_uniqueness.
  Qed.
End Semantics.
End CS.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Traces.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require ssreflect ssrfun ssrbool eqtype.

Module CS.

Import Intermediate.

Definition stack : Type := list Pointer.t.

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

(* preparing the machine for running a program *)

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | Some mainP =>
    let initial_mem := prepare_initial_memory p in
    let '(mem, _, entrypoints) := prepare_procedures p initial_mem in
    let regs := Register.init in
    let b := match EntryPoint.get Component.main mainP entrypoints with
             | Some b => b
             | None => 0 (* This case shouldn't happen for a well-formed p *)
             end in
    ([], mem, regs, (Component.main, b, 0%Z))
  (* this case shoudln't happen for a well-formed p *)
  | None => ([], emptym, emptym, (Component.main, 0, 0%Z))
  end.

(* transition system *)

Definition initial_state (p: program) (ics: state) : Prop :=
  ics = initial_machine_state p.

Definition final_state (G: global_env) (s: state) : Prop :=
  let '(gsp, mem, regs, pc) := s in
  executing G pc IHalt.

(* relational specification *)

Inductive step (G : global_env) : state -> trace -> state -> Prop :=
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
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs', Pointer.inc pc)

| Mov: forall gps mem regs regs' pc r1 r2,
    executing G pc (IMov r1 r2) ->
    Register.set r2 (Register.get r1 regs) regs = regs' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs', Pointer.inc pc)

| BinOp: forall gps mem regs regs' pc r1 r2 r3 op,
    executing G pc (IBinOp op r1 r2 r3) ->
    let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
    Register.set r3 result regs = regs' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs', Pointer.inc pc)

| Load: forall gps mem regs regs' pc r1 r2 ptr v,
    executing G pc (ILoad r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = Pointer.component pc ->
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs', Pointer.inc pc)

| Store: forall gps mem mem' regs pc ptr r1 r2,
    executing G pc (IStore r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = Pointer.component pc ->
    Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem', regs, Pointer.inc pc)

| Jal: forall gps mem regs regs' pc pc' l,
    executing G pc (IJal l) ->
    find_label_in_component G pc l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    step G (gps, mem, regs, pc) E0
           (gps, mem, regs', pc')

| Jump: forall gps mem regs pc pc' r,
    executing G pc (IJump r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.component pc' = Pointer.component pc ->
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
    step G (gps, mem, regs, pc) E0
           (gps, mem', regs', Pointer.inc pc)

| Call: forall gps mem regs pc b C' P call_arg,
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    Register.get R_COM regs = Int call_arg ->
    step G (gps, mem, regs, pc)
           [ECall (Pointer.component pc) P call_arg C']
           (Pointer.inc pc :: gps, mem, Register.invalidate regs, (C', b, 0%Z))

| Return: forall gps' mem regs pc pc' ret_arg,
    executing G pc IReturn ->
    Pointer.component pc <> Pointer.component pc' ->
    Register.get R_COM regs = Int ret_arg ->
    step G (pc' :: gps', mem, regs, pc)
           [ERet (Pointer.component pc) ret_arg (Pointer.component pc')]
           (gps', mem, Register.invalidate regs, pc').

(* executable specification *)

Import MonadNotations.
Open Scope monad_scope.

Definition eval_step (G: global_env) (s: state) : option (trace * state) :=
  let '(gps, mem, regs, pc) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- getm (genv_procedures G) (Pointer.component pc);
  do P_code <- getm C_procs (Pointer.block pc);
  if (Pointer.offset pc <? 0) % Z then
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
      let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
      let regs' := Register.set r3 result regs in
      ret (E0, (gps, mem, regs', Pointer.inc pc))
    | ILoad r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do v <- Memory.load mem ptr;
          let regs' := Register.set r2 v regs in
          ret (E0, (gps, mem, regs', Pointer.inc pc))
        else
          None
      | _ => None
      end
    | IStore r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do mem' <- Memory.store mem ptr (Register.get r2 regs);
          ret (E0, (gps, mem', regs, Pointer.inc pc))
        else
          None
      | _ => None
      end
    | IJal l =>
      do pc' <- find_label_in_component G pc l;
      let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) regs in
      ret (E0, (gps, mem, regs', pc'))
    | IJump r =>
      match Register.get r regs with
      | Ptr pc' =>
        if Component.eqb (Pointer.component pc') (Pointer.component pc) then
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
        if (size <=? 0) % Z then
          None
        else
          do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
          let regs' := Register.set rptr (Ptr ptr) regs in
          ret (E0, (gps, mem', regs', Pointer.inc pc))
      | _ => None
      end
    | ICall C' P =>
      if negb (Component.eqb (Pointer.component pc) C') then
        if imported_procedure_b (genv_interface G) (Pointer.component pc) C' P then
          do b <- EntryPoint.get C' P (genv_entrypoints G);
          match Register.get R_COM regs with
          | Int rcomval =>
            let pc' := (C', b, 0%Z) in
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
        if negb (Component.eqb (Pointer.component pc) (Pointer.component pc')) then
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

(* equivalance between relational and executable specification *)

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st = Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    (* extract information about the state *)
    match goal with
    | Hexec: executing _ _ _ |- _ =>
      destruct Hexec as [procs [P_code [Hprocs [HP_code [? Hinstr]]]]]
    end;
    (* simplify *)
    simpl; unfold code in *; rewrite -> Hprocs, HP_code, Hinstr;
    (* the program counter is good *)
    match goal with
    | Hpc: (Pointer.offset _ >= 0) % Z |- _ =>
      apply Z.ge_le in Hpc; apply Z.ltb_ge in Hpc;
      rewrite Hpc
    end;
    (* solve simple cases *)
    try reflexivity.

  - match goal with
    | Hregs_update: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_update, Hsame_component, Nat.eqb_refl
    end.
    unfold Memory.load in *.
    destruct ptr as [[C' b'] o'].
    rewrite H2. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_value, Hsame_component, Nat.eqb_refl
    end.
    unfold Memory.store in *.
    destruct ptr as [[C' b'] o'].
    rewrite H2. reflexivity.

  - match goal with
    | Hfind: find_label_in_component _ _ _ = _ |- _ =>
      rewrite Hfind
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_value, Hsame_component, Nat.eqb_refl
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
    | Hentrypoint: EntryPoint.get _ _ _ = _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite -> Hentrypoint, Hregs_value
    end.
    apply Nat.eqb_neq in H0. unfold Component.eqb. rewrite H0. simpl.
    apply imported_procedure_iff in H1. rewrite H1.
    reflexivity.

  - unfold Component.eqb.
    match goal with
    | Hdifferent_target: Pointer.component _ <> Pointer.component _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      apply Nat.eqb_neq in Hdifferent_target; rewrite Hdifferent_target;
      rewrite Hregs_value; simpl
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
        ** assert ((Pointer.offset pc0 <? 0) % Z = false). {
             destruct (Pointer.offset pc0); auto.
           }
           assert ((Pointer.offset pc0 >= 0) % Z). {
             destruct (Pointer.offset pc0); discriminate.
           }
           simpl in Heval_step. unfold code in *.
           rewrite -> HC_procs, HP_code, Hinstr in Heval_step.
           destruct instr; inversion Heval_step; subst; clear Heval_step;
             try (match goal with
                  | Hpcfalse: (Pointer.offset ?PC <? 0) % Z = false,
                    Heq: (if (Pointer.offset ?PC <? 0) % Z then None else Some _) = Some _
                    |- _ =>
                    rewrite Hpcfalse in Heq; inversion Heq; subst; clear Heq Hpcfalse
                  end).

           *** eapply Nop.
               eexists. eexists. eauto.
                 try reflexivity;
                 try (eexists; eexists; eauto).

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

           *** rewrite H in H2.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcomp;
                 try discriminate.
               unfold Memory.load in *.
               destruct (mem0 (Pointer.component t0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.load t1 (Pointer.block t0) (Pointer.offset t0))
                        eqn:Hload;
                 try discriminate.
               inversion H2; subst.
               eapply Load with (ptr:=t0);
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** assumption.
               **** apply Nat.eqb_eq. assumption.
               **** unfold Memory.load.
                    rewrite Hmem. assumption.

           *** rewrite H in H2.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcomp;
                 try discriminate.
               unfold Memory.store in *.
               destruct (mem0 (Pointer.component t0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.store t1 (Pointer.block t0) (Pointer.offset t0)
                                               (Register.get r0 regs0))
                        eqn:Hstore;
                 try discriminate.
               inversion H2; subst.
               eapply Store with (ptr:=t0);
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** assumption.
               **** apply Nat.eqb_eq. assumption.
               **** unfold Memory.store.
                    rewrite Hmem. rewrite Hstore. reflexivity.

           *** rewrite H in H2.
               destruct (Register.get r0 regs0) eqn:Hreg;
                 try discriminate.
               destruct ((z <=? 0) % Z) eqn:Hzpos;
                 try discriminate.
               unfold Memory.alloc in *.
               destruct (mem0 (Pointer.component pc0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.alloc t0 (Z.to_nat z)) eqn:Halloc;
                 try discriminate.
               inversion H2; subst.
               eapply Alloc;
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** eassumption.
               **** apply Z.lt_gt. apply Z.leb_gt. assumption.
               **** unfold Memory.alloc.
                    rewrite Hmem. rewrite Halloc. reflexivity.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct z eqn:Hn.
               **** inversion H2. subst.
                    eapply BnzZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H2. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** eassumption.
                    ***** intro contra. discriminate.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H2. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ****** eexists. eexists. eauto.
                    ****** eassumption.
                    ****** intro contra. discriminate.
                    ****** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcompcheck;
                 try discriminate.
               inversion H2; subst.
               eapply Jump with (pc':=pc);
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.
               **** apply Nat.eqb_eq. assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               destruct (find_label_in_component G pc0 l) eqn:Hlabel;
                 try discriminate.
               inversion H2; subst.
               eapply Jal;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               destruct (Component.eqb (Pointer.component pc0) i) eqn:Hcomp;
                 try discriminate; simpl in *.
               destruct (imported_procedure_b (genv_interface G)
                                              (Pointer.component pc0) i i0)
                        eqn:Himport;
                 try discriminate.
               destruct (EntryPoint.get i i0 (genv_entrypoints G)) eqn:Hentrypoint;
                 try discriminate.
               destruct (Register.get R_COM regs0) eqn:Hreg;
                 try discriminate.
               simpl in *. inversion H2. subst.
               eapply Call;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Nat.eqb_neq. assumption.
               **** apply imported_procedure_iff. auto.
               **** assumption.
               **** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               destruct gps0;
                 try discriminate.
               destruct (Component.eqb (Pointer.component pc0) (Pointer.component t0))
                        eqn:Hcomp;
                 try discriminate.
               simpl in *.
               destruct (Register.get R_COM regs0) eqn:Hreg;
                 try discriminate.
               inversion H2. subst.
               eapply Return;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Nat.eqb_neq. assumption.
               **** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               discriminate.

        ** simpl in Heval_step. unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); discriminate.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z) eqn:Hpc';
             try discriminate.
           exfalso. unfold Z.geb in Hpc.
           destruct (Pointer.offset pc0);
             try discriminate.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); discriminate.
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

Section Semantics.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem :=
    @Semantics_gen state global_env step (initial_state p) (final_state G) G.

  Lemma determinate_step:
    forall s t1 s1 t2 s2,
      step G s t1 s1 ->
      step G s t2 s2 ->
      match_traces t1 t2 /\ (t1 = t2 -> s1 = s2).
  Proof.
    intros s t1 s21 t2 s2 Hstep1 Hstep2.
    inversion Hstep1; subst; inversion Hstep2; subst;
      (* extract information about the instruction we are executing *)
      try (match goal with
             Hexec1: executing ?G ?PC ?INSTR1,
             Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
             destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
             destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
             rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
             rewrite HP_code in HP_code'; inversion HP_code'; subst;
             rewrite Hinstr in Hinstr'; inversion Hinstr'; subst
           end);
      (* solve simple cases *)
      try (split; [ constructor |
                    intro Hsame_trace; eapply step_deterministic; eauto ]).

    (* external calls *)
    - split.
      + match goal with
        | Hcall_arg1: Register.get R_COM regs = Int ?CALL_ARG1,
          Hcall_arg2: Register.get R_COM regs = Int ?CALL_ARG2 |- _ =>
          rewrite Hcall_arg1 in Hcall_arg2; inversion Hcall_arg2; subst
        end; constructor.
      + intros Hsame_trace.
        match goal with
        | Hentrypoint1: EntryPoint.get _ _ _ = Some ?B1,
          Hentrypoint2: EntryPoint.get _ _ _ = Some ?B2 |- _ =>
          rewrite Hentrypoint1 in Hentrypoint2; inversion Hentrypoint2; subst
        end; reflexivity.

    (* external return *)
    - split.
      + match goal with
        | Hret_arg1: Register.get R_COM regs = Int ?RET_ARG1,
          Hret_arg2: Register.get R_COM regs = Int ?RET_ARG2 |- _ =>
          rewrite Hret_arg1 in Hret_arg2; inversion Hret_arg2; subst
        end; constructor.
      + intros Hsame_trace. reflexivity.
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
    intros s1 s2 Hs1_init Hs2_init.
    unfold initial_state in *. subst.
    reflexivity.
  Qed.

  Lemma final_states_stuckness:
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
           destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
           destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
           rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
           rewrite HP_code in HP_code'; inversion HP_code'; subst;
           rewrite Hinstr in Hinstr'; inversion Hinstr'
         end).
  Qed.

  Lemma determinacy:
    determinate sem.
  Proof.
    constructor.
    - apply determinate_step.
    - apply singleton_traces.
    - apply determinate_initial_states.
    - apply final_states_stuckness.
  Qed.

Import ssreflect eqtype.

Definition stack_state_of (cs:CS.state) : stack_state :=
  let '(gps, mem, regs, pc) := cs in
  StackState (Pointer.component pc) (List.map Pointer.component gps).

Lemma intermediate_well_bracketed_trace t cs cs' :
  Star sem cs t cs' ->
  well_bracketed_trace (stack_state_of cs) t.
Proof.
elim: cs t cs' / => [|cs1 t1 cs2 t2 cs3 t Hstep _ IH ->] //=.
case: cs1 t1 cs2 / Hstep IH => /=;
try by move=> *; match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
        rewrite Pointer.inc_preserves_component in H end.
- by move=> ???????? /find_label_in_component_1 ->.
- by move=> ???????? ->.
- by move=> ??????????? /find_label_in_procedure_1 ->.
- by move=> ???????????; rewrite eqxx Pointer.inc_preserves_component.
- by move=> ?????????; rewrite !eqxx.
Qed.

Canonical ssrnat.nat_eqType.

Lemma intermediate_well_formed_events st t st' :
  Star sem st t st' ->
  seq.all (well_formed_event (Intermediate.prog_interface p)) t.
Proof.
elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
rewrite seq.all_cat IH andbT {Hstar}.
case: st1 t1 st2 / Hstep => //=.
- move=> ????????? /eqP ->.
  by move=> /imported_procedure_iff /= ->.
- by move=> ??????? /eqP ->.
Qed.

Lemma intermediate_well_formed_trace : forall mainP t cs cs',
  Star sem cs t cs' ->
  CS.initial_state p cs ->
  Intermediate.prog_main p = Some mainP ->
  Intermediate.well_formed_program p ->
  well_formed_trace (Intermediate.prog_interface p) t.
Proof.
  intros mainP t cs cs' H H' H'' H'''.
  unfold well_formed_trace. apply/andP; split; last by apply: intermediate_well_formed_events H.
  apply intermediate_well_bracketed_trace in H.
  suffices <- : stack_state_of cs = stack_state0 by [].
  rewrite /initial_state /initial_machine_state in H'.
  rewrite H' H''.
  rewrite [Intermediate.prepare_procedures p _]surjective_pairing /=.
  by rewrite [fst (Intermediate.prepare_procedures p _)]surjective_pairing.
Qed.

End Semantics.

(* A similar result is used above. Here is a weaker formulation. *)
Lemma initial_state_stack_state0 p s :
  initial_state p s ->
  stack_state_of s = Traces.stack_state0.
Proof.
  intros Hini.
  unfold initial_state, initial_machine_state in Hini.
  destruct (prog_main p) as [mainP |]; simpl in Hini.
  - destruct (prepare_procedures p (prepare_initial_memory p))
      as [[mem dummy] entrypoints].
    destruct (EntryPoint.get Component.main mainP entrypoints).
    + subst. reflexivity.
    + subst. reflexivity.
  - subst. reflexivity.
Qed.

Definition comes_from_initial_state (s: state) (iface : Program.interface) : Prop :=
  exists p s0 t,
    well_formed_program p /\
    prog_interface p = iface /\
    initial_state p s0 /\
    Star (sem p) s0 t s.

Lemma comes_from_initial_state_mergeable_sym :
  forall s iface1 iface2,
    Linking.mergeable_interfaces iface1 iface2 ->
    comes_from_initial_state s (unionm iface1 iface2) ->
    comes_from_initial_state s (unionm iface2 iface1).
Proof.
  intros s iface1 iface2 [[_ Hdisjoint] _] Hfrom_initial.
  rewrite <- (unionmC Hdisjoint).
  exact Hfrom_initial.
Qed.

End CS.

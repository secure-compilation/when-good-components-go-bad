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

Ltac unfold_states :=
  match goal with
  | H: state |- _ =>
    let s := fresh "s" in
    let mem := fresh "mem" in
    let regs := fresh "regs" in
    let pc := fresh "pc" in
    destruct H as [[[s mem] regs] pc]
  end.

Inductive state_eq : state -> state -> Prop :=
| state_eq_intro: forall gps1 mem1 regs1 pc1 gps2 mem2 regs2 pc2,
    gps1 = gps2 ->
    PMap.Equal mem1 mem2 ->
    regs1 = regs2 ->
    pc1 = pc2 ->
    state_eq (gps1, mem1, regs1, pc1) (gps2, mem2, regs2, pc2).

Lemma state_eq_refl:
  forall s,
    state_eq s s.
Proof.
  intros s.
  unfold_states.
  constructor; reflexivity.
Qed.

Lemma state_eq_sym:
  forall s1 s2,
    state_eq s1 s2 -> state_eq s2 s1.
Proof.
  intros s1 s2 H.
  inversion H; subst.
  constructor;
    try reflexivity;
    try symmetry; assumption.
Qed.

Lemma state_eq_trans:
  forall s1 s2 s3,
    state_eq s1 s2 -> state_eq s2 s3 -> state_eq s1 s3.
Proof.
  intros s1 s2 s3 H1 H2.
  inversion H1; subst; inversion H2; subst;
    constructor;
    try reflexivity;
    try etransitivity; eauto.
Qed.

Add Parametric Relation: (state) (state_eq)
    reflexivity proved by (state_eq_refl)
    symmetry proved by (state_eq_sym)
    transitivity proved by (state_eq_trans)
      as state_eq_rel.

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    let '(_, _, _, pc) := s in
    PMap.In (Pointer.component pc) iface
}.

(* transition system *)

Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall gps mem regs pc,
    (* the global protected stack is empty *)
    gps = [] ->
    (* mem comes from the init routine *)
    PMap.Equal mem (let '(m, _, _) := init_all p in m) ->
    (* the registers are set to undef *)
    regs = [Undef; Undef; Undef; Undef; Undef; Undef] ->
    (* the program counter is pointing to the start of the main procedure *)
    Pointer.component pc = fst (prog_main p) ->
    EntryPoint.get (fst (prog_main p)) (snd (prog_main p))
                   (genv_entrypoints (init_genv p)) = Some (Pointer.block pc) ->
    Pointer.offset pc = 0 ->
    initial_state p (gps, mem, regs, pc).

Definition final_state (G: global_env) (s: state) : Prop :=
  let '(gsp, mem, regs, pc) := s in
  executing G pc IHalt.

Lemma same_program_initial_state:
  forall p1 p2,
    prog_eq p1 p2 ->
  forall ics,
    initial_state p1 ics ->
    initial_state p2 ics.
Proof.
  intros p1 p2 Heq ics Hics_init.
  inversion Heq; subst.
  inversion Hics_init; subst.
  simpl in *.
  constructor;
    try reflexivity;
    try assumption.
  - rewrite H3.
    (* init_all with equal programs *)
    admit.
  - simpl.
    rewrite <- H6.
    (* init_genv with equal programs *)
    admit.
Admitted.

Lemma same_genv_final_state:
  forall G1 G2,
    genv_eq G1 G2 ->
  forall ics,
    final_state G1 ics ->
    final_state G2 ics.
Proof.
  intros G1 G2 Heq ics Hics_final.
  inversion Heq; subst.
  unfold final_state in *.
  simpl in *.
  (* executing in the same environment *)
Admitted.

(* relational specification *)

Inductive step (G : global_env) : state -> trace -> state -> Prop :=
| Nop: forall ics ics' gps mem regs pc,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc INop ->
    state_eq ics' (gps, mem, regs, Pointer.inc pc) ->
    step G ics E0 ics'

| Label: forall ics ics' gps mem regs pc l,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (ILabel l) ->
    state_eq ics' (gps, mem, regs, Pointer.inc pc) ->
    step G ics E0 ics'

| Const: forall ics ics' gps mem regs regs' pc r v,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IConst v r) ->
    Register.set r (imm_to_val v) regs = regs' ->
    state_eq ics' (gps, mem, regs', Pointer.inc pc) ->
    step G ics E0 ics'

| Mov: forall ics ics' gps mem regs regs' pc r1 r2,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IMov r1 r2) ->
    Register.set r2 (Register.get r1 regs) regs = regs' ->
    state_eq ics' (gps, mem, regs', Pointer.inc pc) ->
    step G ics E0 ics'

| BinOp: forall ics ics' gps mem regs regs' pc r1 r2 r3 op,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IBinOp op r1 r2 r3) ->
    let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
    Register.set r3 result regs = regs' ->
    state_eq ics' (gps, mem, regs', Pointer.inc pc) ->
    step G ics E0 ics'

| Load: forall ics ics' gps mem regs regs' pc r1 r2 ptr v,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (ILoad r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = Pointer.component pc ->
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    state_eq ics' (gps, mem, regs', Pointer.inc pc) ->
    step G ics E0 ics'

| Store: forall ics ics' gps mem mem' regs pc ptr r1 r2,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IStore r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = Pointer.component pc ->
    Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
    state_eq ics' (gps, mem', regs, Pointer.inc pc) ->
    step G ics E0 ics'

| Jal: forall ics ics' gps mem regs regs' pc pc' l,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IJal l) ->
    find_label_in_component G pc l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    state_eq ics' (gps, mem, regs', pc') ->
    step G ics E0 ics'

| Jump: forall ics ics' gps mem regs pc pc' r,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IJump r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.component pc' = Pointer.component pc ->
    state_eq ics' (gps, mem, regs, pc') ->
    step G ics E0 ics'

| BnzNZ: forall ics ics' gps mem regs pc pc' r l val,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IBnz r l) ->
    Register.get r regs = Int val ->
    val <> 0 ->
    find_label_in_procedure G pc l = Some pc' ->
    state_eq ics' (gps, mem, regs, pc') ->
    step G ics E0 ics'

| BnzZ: forall ics ics' gps mem regs pc r l,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IBnz r l) ->
    Register.get r regs = Int 0 ->
    state_eq ics' (gps, mem, regs, Pointer.inc pc) ->
    step G ics E0 ics'

| Alloc: forall ics ics' gps mem mem' regs regs' pc rsize rptr size ptr,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (IAlloc rptr rsize) ->
    Register.get rsize regs = Int size ->
    size > 0 ->
    Memory.alloc mem (Pointer.component pc) (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    state_eq ics' (gps, mem', regs', Pointer.inc pc) ->
    step G ics E0 ics'

| Call: forall ics ics' gps mem regs pc b C' P rcomval,
    state_eq ics (gps, mem, regs, pc) ->
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    Register.get R_COM regs = Int rcomval ->
    state_eq ics' (Pointer.inc pc :: gps, mem, Register.invalidate regs, (C', b, 0)) ->
    step G ics [ECall (Pointer.component pc) P rcomval C'] ics'

| Return: forall ics ics' gps' mem regs pc pc' rcomval,
    state_eq ics (pc' :: gps', mem, regs, pc) ->
    executing G pc IReturn ->
    Pointer.component pc <> Pointer.component pc' ->
    Register.get R_COM regs = Int rcomval ->
    state_eq ics' (gps', mem, Register.invalidate regs, pc') ->
    step G ics [ERet (Pointer.component pc) rcomval (Pointer.component pc')] ics'.

Lemma equal_states_step:
  forall G ics1 t ics1' ics2 ics2',
    step G ics1 t ics1' ->
    state_eq ics1 ics2 ->
    state_eq ics1' ics2' ->
    step G ics2 t ics2'.
Proof.
  intros G ics1 t ics1' ics2 ics2'.
  intros Hstep Heq1 Heq2.
  inversion Heq1; subst; inversion Heq2; subst.
  inversion Hstep; subst;
    match goal with
    | Heq1': state_eq _ _,
      Heq2': state_eq _ _ |- _ =>
      inversion Heq1'; subst; inversion Heq2'; subst
    end.

  Ltac solve_mem_equality :=
    match goal with
    | H1: PMap.Equal ?MEM0 ?MEM1,
      H2: PMap.Equal ?MEM0 ?MEM2,
      H3: PMap.Equal ?MEM1 ?MEM3 |- PMap.Equal ?MEM2 ?MEM3 =>
      rewrite H1 in H2; rewrite H2 in H3; apply H3
    end.

  - eapply Nop;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H13, H14. reflexivity.

  - eapply Label;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H13, H14. reflexivity.

  - eapply Const;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H13, H14. reflexivity.

  - eapply Mov;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H13, H14. reflexivity.

  - eapply BinOp;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H13, H14. reflexivity.

  - eapply Load;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
      rewrite <- H0. auto.
    + constructor; try reflexivity.
      rewrite <- H1. auto.

  - eapply Store;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
      rewrite <- H0. auto.
    + constructor; try reflexivity.
      rewrite <- H1. auto.

  - eapply Jal;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H14, H15. reflexivity.

  - eapply Jump;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H15, H16. reflexivity.

  - eapply BnzNZ;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H16, H17. reflexivity.

  - eapply BnzZ;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H14, H15. reflexivity.

  - eapply Alloc;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
      rewrite <- H0. auto.
    + constructor; try reflexivity.
      rewrite <- H1. auto.

  - eapply Call;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H17, H18. reflexivity.

  - eapply Return;
      try solve_mem_equality;
      eauto.
    + constructor; try reflexivity.
    + constructor; try reflexivity.
      rewrite <- H0, <- H1, H15, H16. reflexivity.
Qed.

Lemma equal_genvs_step:
  forall G1 G2 ics t ics',
    genv_eq G1 G2 ->
    step G1 ics t ics' ->
    step G2 ics t ics'.
Proof.
  intros G1 G2 ics t ics' Heq Hstep.
  inversion Heq; subst.
  inversion Hstep; subst;
    match goal with
    | Heq1: state_eq _ _,
      Heq2: state_eq _ _ |- _ =>
      inversion Heq1; subst; inversion Heq2; subst
    end.

  - eapply Nop;
      try reflexivity.
    + eapply execution_in_same_environment; eauto.
    + constructor;
        try reflexivity.
      * match goal with
        | Heq_mem1: PMap.Equal ?MEM1 ?MEM,
          Heq_mem2: PMap.Equal ?MEM0 ?MEM |-
          PMap.Equal ?MEM0 ?MEM1 =>
          rewrite Heq_mem1; apply Heq_mem2
        end.

  - eapply Label;
      try reflexivity.
    + eapply execution_in_same_environment; eauto.
    + constructor;
        try reflexivity.
      * match goal with
        | Heq_mem1: PMap.Equal ?MEM1 ?MEM,
          Heq_mem2: PMap.Equal ?MEM0 ?MEM |-
          PMap.Equal ?MEM0 ?MEM1 =>
          rewrite Heq_mem1; apply Heq_mem2
        end.

  - eapply Const;
      try reflexivity.
    + eapply execution_in_same_environment; eauto.
    + constructor;
        try reflexivity.
      * match goal with
        | Heq_mem1: PMap.Equal ?MEM1 ?MEM,
          Heq_mem2: PMap.Equal ?MEM0 ?MEM |-
          PMap.Equal ?MEM0 ?MEM1 =>
          rewrite Heq_mem1; apply Heq_mem2
        end.

  - eapply Mov;
      try reflexivity.
    + eapply execution_in_same_environment; eauto.
    + constructor;
        try reflexivity.
      * match goal with
        | Heq_mem1: PMap.Equal ?MEM1 ?MEM,
          Heq_mem2: PMap.Equal ?MEM0 ?MEM |-
          PMap.Equal ?MEM0 ?MEM1 =>
          rewrite Heq_mem1; apply Heq_mem2
        end.

  - eapply BinOp;
      try reflexivity.
    + eapply execution_in_same_environment; eauto.
    + constructor;
        try reflexivity.
      * match goal with
        | Heq_mem1: PMap.Equal ?MEM1 ?MEM,
          Heq_mem2: PMap.Equal ?MEM0 ?MEM |-
          PMap.Equal ?MEM0 ?MEM1 =>
          rewrite Heq_mem1; apply Heq_mem2
        end.
Admitted.

(* executable specification *)

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
        if Pos.eqb (Pointer.component ptr) (Pointer.component pc) then
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
        if size <=? 0 then
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

Definition init_genv_and_state (p: program) (input: value) : option (global_env * state) :=
  let '(mem, E, ps) := init_all p in
  let G := {| genv_interface := prog_interface p;
              genv_procedures := ps;
              genv_entrypoints := E |} in
  do b <- EntryPoint.get (fst (prog_main p)) (snd (prog_main p)) (genv_entrypoints G);
  let regs := Register.set R_COM input Register.init in
  ret (G, ([], mem, regs, (fst (prog_main p), b, 0))).

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
  do (G, st) <- init_genv_and_state p input;
  execN fuel G st.

Close Scope monad_scope.

(* equivalance between relational and executable specification *)

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' ->
  exists st'',
    eval_step G st = Some (t, st'') /\ state_eq st' st''.
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    (* extract information about the state *)
    match goal with
    | Hexec: executing _ _ _,
      Heq1: state_eq _ _,
      Heq2: state_eq _ _ |- _ =>
      destruct Hexec as [procs [P_code [Hprocs [HP_code [? Hinstr]]]]];
      inversion Heq1; subst; clear Heq1; inversion Heq2; subst; clear Heq2
    end;
    (* simplify *)
    simpl; unfold code in *; rewrite Hprocs, HP_code, Hinstr;
    (* the program counter is good *)
    match goal with
    | Hpc: Pointer.offset _ >= 0 |- _ =>
      apply Z.ge_le in Hpc; apply Z.ltb_ge in Hpc;
      rewrite Hpc
    end.

  - eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8. assumption.

  - eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8. assumption.

  - eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8. assumption.

  - eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8. assumption.

  - eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8. assumption.

  - match goal with
    | Hregs_update: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite Hregs_update, Hsame_component, Pos.eqb_refl
    end.
    unfold Memory.load in *.
    destruct ptr as [[C' b'] o'].
    rewrite <- H11 in *. rewrite H3.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + assumption.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite Hregs_value, Hsame_component, Pos.eqb_refl
    end.
    unfold Memory.store in *.
    destruct ptr as [[C' b'] o'].
    rewrite <- H11 in *.
    destruct (PMap.find C' mem1); try discriminate.
    destruct (ComponentMemory.store t b' o' (Register.get r2 regs)); try discriminate.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + inversion H3; subst.
      rewrite H10. rewrite H11. reflexivity.

  - match goal with
    | Hfind: find_label_in_component _ _ _ = _ |- _ =>
      rewrite Hfind
    end.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8, H9. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite Hregs_value, Hsame_component, Pos.eqb_refl
    end.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H9, H10. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hfind: find_label_in_procedure _ _ _ = _ |- _ =>
      rewrite Hregs_value, Hfind
    end.
    destruct val;
      try contradiction;
      try (eexists; split; [ reflexivity | ]).
    + constructor; try reflexivity.
      * rewrite H10, H11. reflexivity.
    + constructor; try reflexivity.
      * rewrite H10, H11. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite Hregs_value
    end.
    eexists; split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H8, H9. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hpositive_size: size > 0 |- _ =>
      rewrite Hregs_value;
      apply Zgt_not_le in Hpositive_size; apply Z.leb_nle in Hpositive_size;
      rewrite Hpositive_size
    end.
    unfold Memory.alloc in *.
    rewrite <- H11 in *.
    destruct (PMap.find (Pointer.component pc) mem1); try discriminate.
    destruct (ComponentMemory.alloc t (Z.to_nat size)); try discriminate.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + inversion H3; subst.
      rewrite H10. rewrite H11. reflexivity.
    + inversion H3; subst; reflexivity.

  - match goal with
    | Hentrypoint: EntryPoint.get _ _ _ = _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite Hentrypoint, Hregs_value
    end.
    destruct (imported_procedure_iff (genv_interface G) (Pointer.component pc) C' P)
      as [H' H''].
    rewrite H'; auto.
    destruct (Pos.eqb (Pointer.component pc) C') eqn:Hpc_eq_C'.
    + apply Pos.eqb_eq in Hpc_eq_C'.
      rewrite <- Hpc_eq_C' in H1.
      contradiction.
    + simpl. eexists. split; [ reflexivity | ].
      constructor;
        try reflexivity.
      * rewrite H11, H12. reflexivity.

  - match goal with
    | Hdifferent_target: Pointer.component _ <> Pointer.component _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      apply Pos.eqb_neq in Hdifferent_target; rewrite Hdifferent_target;
      rewrite Hregs_value; simpl
    end.
    eexists. split; [ reflexivity | ].
    constructor;
      try reflexivity.
    + rewrite H9, H10. reflexivity.
Qed.

Theorem eval_step_sound:
  forall G st t st',
    eval_step G st = Some (t, st') -> step G st t st'.
Proof.
  intros G st t st' Heval_step.
  repeat unfold_states.
  destruct (PMap.find (Pointer.component pc0) (genv_procedures G))
    as [C_procs | ] eqn:HC_procs.
  - destruct (PMap.find (Pointer.block pc0) C_procs)
      as [P_code | ] eqn:HP_code.
    + destruct (Pointer.offset pc0 >=? 0) eqn:Hpc.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
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

           *** eapply Nop;
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

           *** destruct (Register.get r regs0) eqn:Hreg.
               **** rewrite H in H2. discriminate.
               **** destruct (Memory.load mem0 t0) eqn:Hmem.
                    ***** rewrite H in H2.
                          destruct (Pos.eqb (Pointer.component t0)
                                            (Pointer.component pc0))%positive
                                   eqn:Hsame_comp.
                          ****** inversion H2. subst.
                                 eapply Load with (ptr:=t0);
                                   try reflexivity.
                                 ******* eexists. eexists. eauto.
                                 ******* assumption.
                                 ******* apply Pos.eqb_eq. assumption.
                                 ******* assumption.
                          ****** discriminate.
                    ***** rewrite H in H2.
                          destruct (Pos.eqb (Pointer.component t0)
                                            (Pointer.component pc0))%positive
                                   eqn:Hsame_comp;
                            discriminate.
               **** rewrite H in H2. discriminate.

           *** destruct (Register.get r regs0) eqn:Hreg.
               **** rewrite H in H2. discriminate.
               **** destruct (Pos.eqb (Pointer.component t0) (Pointer.component pc0))
                             eqn:Hcompcheck.
                    ***** rewrite H in H2.
                    destruct (Memory.store mem0 t0 (Register.get r0 regs0)) eqn:Hmem.
                    ****** inversion H2. subst.
                           eapply Store with (ptr:=t0);
                             try reflexivity.
                           ******* eexists. eexists. eauto.
                           ******* assumption.
                           ******* apply Pos.eqb_eq. assumption.
                           ******* assumption.
                    ****** discriminate.
                    ***** rewrite H in H2. discriminate.
               **** rewrite H in H2. discriminate.

           *** rewrite H in H2.
               destruct (Register.get r0 regs0) eqn:Hreg.
               **** destruct (z <=? 0) eqn:Hzpos.
                    ***** discriminate.
                    ***** destruct (Memory.alloc mem0 (Pointer.component pc0) (Z.to_nat z)) eqn:Hmem.
                    ****** destruct p. inversion H2. subst.
                           eapply Alloc;
                             try reflexivity.
                           ******* eexists. eexists. eauto.
                           ******* eassumption.
                           ******* apply Z.lt_gt. apply Z.leb_gt. assumption.
                           ******* assumption.
                    ****** discriminate.
               **** discriminate.
               **** discriminate.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) = false,
                 Hcond: (if Pointer.offset _ <? 0 then None else _) = Some _ |- _ =>
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
                    ***** auto.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H2. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ****** eexists. eexists. eauto.
                    ****** eassumption.
                    ****** auto.
                    ****** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) = false,
                 Hcond: (if Pointer.offset _ <? 0 then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Pos.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcompcheck;
                 try discriminate.
               inversion H2; subst.
               eapply Jump with (pc':=pc);
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.
               **** apply Pos.eqb_eq. assumption.

           *** match goal with
               | Hpositive_offset: Pointer.offset _ <? 0 = false |- _ =>
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
               | Hpositive_offset: Pointer.offset _ <? 0 = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               destruct (Pos.eqb (Pointer.component pc0) i) eqn:Hcomp;
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
               **** apply Pos.eqb_neq. assumption.
               **** apply imported_procedure_iff. auto.
               **** assumption.
               **** assumption.

           *** match goal with
               | Hpositive_offset: Pointer.offset _ <? 0 = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               destruct s0;
                 try discriminate.
               destruct (Pos.eqb (Pointer.component pc0) (Pointer.component t0))
                        eqn:Hcomp;
                 try discriminate.
               simpl in *.
               destruct (Register.get R_COM regs0) eqn:Hreg;
                 try discriminate.
               inversion H2. subst.
               eapply Return;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Pos.eqb_neq. assumption.
               **** assumption.

           *** match goal with
               | Hpositive_offset: Pointer.offset _ <? 0 = false |- _ =>
                 rewrite Hpositive_offset in *
               end.
               discriminate.

        ** simpl in Heval_step. unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct (Pointer.offset pc0 <? 0); discriminate.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs, HP_code, Hinstr in Heval_step.
           destruct (Pointer.offset pc0 <? 0) eqn:Hpc';
             try discriminate.
           exfalso. unfold Z.geb in Hpc.
           destruct (Pointer.offset pc0);
             try discriminate.
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
    step G st t st' <->
    (exists st'', state_eq st' st'' /\ eval_step G st = Some (t, st'')).
Proof.
  split.
  - intros Hstep.
    destruct (eval_step_complete G st t st' Hstep) as [st'' []].
    exists st''.
    repeat split; eauto.
  - intros H.
    destruct H as [st'' [Heq Hstep]].
    apply eval_step_sound in Hstep.
    eapply equal_states_step.
    + apply Hstep.
    + reflexivity.
    + symmetry. assumption.
Qed.

(* complete semantics and some properties *)

Corollary step_deterministic:
  forall G st t st1 st2,
    step G st t st1 -> step G st t st2 -> state_eq st1 st2.
Proof.
  intros G st t st1 st2 Hstep1 Hstep2.
  apply eval_step_correct in Hstep1.
  apply eval_step_correct in Hstep2.
  destruct Hstep1 as [st1' [Heq1 Heval_step1]].
  destruct Hstep2 as [st2' [Heq2 Heval_step2]].
  rewrite Heq1, Heq2.
  rewrite Heval_step1 in Heval_step2.
  inversion Heval_step2.
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
      match_traces t1 t2 /\ (t1 = t2 -> state_eq s1 s2).
  Proof.
    (* TODO think about this, it's admitted because coq is too slow in checking the proof *)
  Admitted.
    (*
    intros s t1 s1 t2 s2 Hstep1 Hstep2.

    inversion Hstep1; subst;
    inversion Hstep2; subst;

      (* extract information about states *)
      match goal with
        Heq1: state_eq ?S1 _, Heq2: state_eq ?S1' _,
        Heq3: state_eq ?S2 _, Heq4: state_eq ?S2' _ |- _ =>
        inversion Heq1; subst; clear Heq1; inversion Heq2; subst; clear Heq2;
        inversion Heq3; subst; clear Heq3; inversion Heq4; subst; clear Heq4
      end;

      (* extract information about the instruction we are executing *)
      match goal with
        Hexec1: executing ?G ?PC ?INSTR1,
        Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
        destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
        destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
        rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
        rewrite HP_code in HP_code'; inversion HP_code'; subst;
        rewrite Hinstr in Hinstr'; inversion Hinstr'; subst
      end;

      (* remove consider silly cases *)
      try (exfalso; discriminate Hinstr');

      (* solve simple cases *)
      try (split;
           [ apply match_traces_E0
           | intro; eapply step_deterministic; eauto ]).

    (* call *)
    - split.
      + match goal with
          Hrcom1: Register.get R_COM _ = Int _,
          Hrcom2: Register.get R_COM _ = Int _ |- _ =>
          rewrite Hrcom1 in Hrcom2; inversion Hrcom2; subst
        end.
        constructor.
      + intro.
        constructor;
          try reflexivity.
        * match goal with
            Hmem_eq1: PMap.Equal ?MEM1 ?MEM,
            Hmem_eq2: PMap.Equal ?MEM2 ?MEM,
            Hmem_eq3: PMap.Equal ?MEM1 ?MEM0,
            Hmem_eq4: PMap.Equal ?MEM3 ?MEM0 |- _ =>
            rewrite Hmem_eq2; rewrite Hmem_eq4; rewrite <- Hmem_eq3;
            symmetry; apply Hmem_eq1
          end.
        * match goal with
            Hentrypoint1: EntryPoint.get _ _ _ = _,
            Hentrypoint2: EntryPoint.get _ _ _ = _ |- _ =>
            rewrite Hentrypoint1 in Hentrypoint2; inversion Hentrypoint2; subst
          end.
          reflexivity.

    (* return *)
    - match goal with
        Hstack: ?PC :: _ = ?PC' :: _ |- _ =>
        inversion Hstack; subst
      end.
      match goal with
        Hrcom1: Register.get R_COM _ = Int _,
        Hrcom2: Register.get R_COM _ = Int _ |- _ =>
        rewrite Hrcom1 in Hrcom2; inversion Hrcom2; subst
      end.
      split.
      + constructor.
      + intro.
        constructor;
          try reflexivity.
        * match goal with
            Hmem_eq1: PMap.Equal ?MEM1 ?MEM,
            Hmem_eq2: PMap.Equal ?MEM2 ?MEM,
            Hmem_eq3: PMap.Equal ?MEM1 ?MEM0,
            Hmem_eq4: PMap.Equal ?MEM3 ?MEM0 |- _ =>
            rewrite Hmem_eq2; rewrite Hmem_eq4; rewrite <- Hmem_eq3;
            symmetry; apply Hmem_eq1
          end.
  Qed.
  *)

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; simpl; auto.
  Qed.

  (*
  Lemma determinate_initial_states:
    forall s1 s2,
      initial_state p s1 -> initial_state p s2 ->
      s1 = s2.
  Proof.
    unfold initial_state.
    intros s1 s2 Hs1_init Hs2_init.
    repeat unfold_states.
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
   *)

  (*
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
   *)

  (*
  Lemma determinacy:
    determinate sem.
  Proof.
    constructor.
    - apply determinate_step.
    - apply singleton_traces.
    - apply determinate_initial_states.
    - apply final_states_stuckness.
  Qed.
   *)
End Semantics.
End CS.
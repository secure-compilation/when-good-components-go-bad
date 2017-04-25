Require Import Common.
Require Import Machine.
Require Import Events.
Require Import Smallstep.

Module LTT.

Import AbstractMachine.

Definition stack:= list (Component.id * Memory.address).

Definition state : Type := 
  Component.id * stack * Memory.data * Register.data * Memory.address.

Record global_env := mkGlobalEnv {
  get_interfaces : Program.interface;
  get_entrypoints : EntryPoint.data;
  entrypoints_exist :
    forall CI C,
      In CI get_interfaces ->
      Component.name CI = C ->
      M.In C get_entrypoints /\
      exists addrs, M.MapsTo C addrs get_entrypoints;
}.

Definition initial_state_for (p : program) : state :=
  match p with (Is, mem, E) =>
    (0, [], mem, Register.empty, EntryPoint.get 0 0 E)
  end.

Definition initial_state G (s : state) : Prop :=
  match s with (C, d, mem, regs, pc) =>
    C = 0 /\ d = [] /\ regs = Register.empty /\
    pc = EntryPoint.get 0 0 (get_entrypoints G)
  end.

Definition final_state (s : state) : Prop :=
  match s with (C, d, mem, regs, pc) =>
    d = [] /\ executing Halt C mem pc
  end.

Definition eval_binop (e : binop) (a b : nat) : nat :=
  match e with
  | Add   => a + b
  | Minus => a - b
  | Mul   => a * b
  | Eq    => if a  =? b then 1 else 0
  | Leq   => if a <=? b then 1 else 0
  end.

Reserved Notation "G |-LTT s1 '=>[' t ']' s2" (at level 40).

Inductive step (G : global_env)
  : state -> trace -> state -> Prop :=
| Nop: forall mem C pc d regs,
    executing Nop C mem pc ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+1)

| Const: forall mem C pc r cval d regs regs',
    executing (Const cval r) C mem pc ->
    regs' = Register.set r cval regs ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

| Mov: forall mem C pc r1 r2 regs regs' d,
    executing (Mov r1 r2) C mem pc ->
    regs' = Register.set r2 (Register.get r1 regs) regs ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

| BinOp: forall mem C pc r1 r1val r2 r2val r3 regs regs' d op,
    executing (BinOp op r1 r2 r3) C mem pc ->
    r1val = Register.get r1 regs ->
    r2val = Register.get r2 regs ->
    regs' = Register.set r3 (eval_binop op r1val r2val) regs ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

| Load: forall mem C pc r1 r2 regs regs' d addr memval,
    executing (Load r1 r2) C mem pc ->
    addr = Register.get r1 regs ->
    Some memval = Memory.get mem C addr ->
    regs' = Register.set r2 memval regs ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

| Store: forall mem C pc r1 r2 regs d addr value mem',
    executing (Store r1 r2) C mem pc->
    addr = Register.get r1 regs ->
    value = Register.get r2 regs ->
    mem' = Memory.set mem C addr value ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem',regs,pc+1)

| Jal: forall mem C pc val r regs regs' d,
    executing (Jal r) C mem pc->
    val = Register.get r regs ->
    regs' = Register.set r (pc+1) regs ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',val)

| Jump: forall mem C pc addr r regs d,
    executing (Jump r) C mem pc->
    Register.get r regs = addr ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,addr)

| BnzNZ: forall mem C pc offset r regs d,
    executing (Bnz r offset) C mem pc ->
    Register.get r regs <> 0 ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+offset)

| BnzZ: forall mem C pc offset r regs d,
    executing (Bnz r offset) C mem pc ->
    Register.get r regs = 0 ->
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+1)

| Call: forall mem C pc regs d d' C' P,
    executing (Call C' P) C mem pc ->
    call_is_public_and_exists (get_interfaces G) C' P ->
    call_is_in_imports (get_interfaces G) C C' P ->
    C' <> C ->
    d' = (C,pc+1) :: d ->
    let t := [ECall C P (Register.get Register.R_COM regs) C'] in
    let E := get_entrypoints G in
    G |-LTT (C,d,mem,regs,pc) =>[t]
            (C',d',mem,regs,EntryPoint.get C' P E)

| Return: forall mem C pc pc' d' regs d C',
    executing Return C mem pc ->
    d = (C',pc') :: d' ->
    C <> C' ->
    let t := [ERet C (Register.get Register.R_COM regs) C'] in
    G |-LTT (C,d,mem,regs,pc) =>[t] (C',d',mem,regs,pc')

where "G |-LTT s1 '=>[' t ']' s2" := (step G s1 t s2).

Definition mem_of (s : state) : Memory.data :=
  match s with (_,_,mem,_,_) => mem end.

Definition comp_of (s : state) : Component.id :=
  match s with (C,_,_,_,_) => C end.

Lemma step_implies_memory_existence:
  forall G s t s',
    G |-LTT s =>[t] s' ->
  exists Cmem, M.MapsTo (comp_of s) Cmem (mem_of s).
Proof.
  intros G s t s'.
  intros Hstep.
  destruct s
    as [[[[C d] mem] regs] pc] eqn:Hstate_s.
  inversion Hstep; subst;
    match goal with
    | Hexec : executing ?INSTR C mem ?PC |- _ =>
      unfold executing, Memory.get in Hexec;
        destruct (M.find (elt:=list nat) C mem)
          as [Cmem | ] eqn:HCmem;
        [ exists Cmem; simpl;
          apply (M.find_2 HCmem)
        | rewrite EncDec.decode_nothing in Hexec;
          inversion Hexec
        ]
    end.
Qed.

(* probably useless *)
Lemma epsilon_step_preserves_component_and_stack:
  forall G C d mem regs pc C' d' mem' regs' pc',
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C',d',mem',regs',pc') ->
    C' = C /\ d' = d.
Proof.
  intros G C d mem regs pc C' d' mem' regs' pc' Hstep.
  inversion Hstep; subst;
    split; trivial.
Qed.

(* probably useless *)
Lemma epsilon_step_weakening:
  forall Is E EWF C d1 mem mem' cmem cmem' regs regs' pc pc',
    let G := mkGlobalEnv Is E EWF in
    M.MapsTo C cmem  mem ->
    M.MapsTo C cmem' mem' ->
    G |-LTT (C,d1,mem,regs,pc) =>[E0] (C,d1,mem',regs',pc') ->
  forall E' E'WF d2 wmem,
    let G' := mkGlobalEnv Is E' E'WF in
    M.MapsTo C cmem wmem ->
    exists wmem',
      M.MapsTo C cmem' wmem' ->
      G' |-LTT (C,d2,wmem,regs,pc) =>[E0] (C,d2,wmem',regs',pc').
Proof.
  intros Is E EWF C d1 mem mem' cmem cmem' regs regs' pc pc'.
  intros G HCmem HCmem' Hstep.
  intros E' E'WF d2 wmem G' HCwmem.
  inversion Hstep; subst.
  - exists wmem. intro HCwmem'.
    apply Nop;
      assumption.
  - exists wmem. intro HCwmem'.
    apply Const with r cval;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    apply Mov with r1 r2;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    eapply BinOp;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    eapply Load;
      try reflexivity.
    + assert (Hexec': executing (AbstractMachine.Load r1 r2) C wmem pc). {
        unfold executing. unfold executing in H5.
        unfold Memory.get. unfold Memory.get in H5.
        rewrite (M.find_1 HCwmem).
        rewrite (M.find_1 HCmem') in H5.
        apply H5.
      }
      apply Hexec'.
    + assert (cmem = cmem'). {
        apply (F.MapsTo_fun HCmem HCmem').
      }
      unfold Memory.get. unfold Memory.get in H9.
      rewrite (M.find_1 HCwmem').
      rewrite (M.find_1 HCmem') in H9.
      apply H9.
  - remember (Register.get r1 regs') as r1val.
    remember (Register.get r2 regs') as r2val.
    exists (Memory.set wmem C r1val r2val). intro HCwmem'.
    apply Store with r1 r2 r1val r2val;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    eapply Jal;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    eapply Jump;
      try reflexivity;
      try assumption.
  - exists wmem. intro HCwmem'.
    eapply BnzNZ.
    + assert (executing (AbstractMachine.Bnz r offset) C wmem pc). {
        unfold executing. unfold executing in H1.
        unfold Memory.get. unfold Memory.get in H1.
        rewrite (M.find_1 HCwmem).
        rewrite (M.find_1 HCmem') in H1.
        apply H1.
      }
      apply H.
    + assumption.
  - exists wmem. intro HCwmem'.
    eapply BnzZ.
    + assert (executing (AbstractMachine.Bnz r offset) C wmem pc). {
        unfold executing. unfold executing in H1.
        unfold Memory.get. unfold Memory.get in H1.
        rewrite (M.find_1 HCwmem).
        rewrite (M.find_1 HCmem') in H1.
        apply H1.
      }
      apply H.
    + assumption.
Qed.

Theorem LTT_determinism :
  forall G s t s1 s2,
    G |-LTT s =>[t] s1 ->
    G |-LTT s =>[t] s2 ->
    s1 = s2.
Proof.
  intros G s t s1 s2 E1 E2.
  inversion E1; subst; inversion E2; subst;
    (* trivial cases *)
    try reflexivity;
    (* contradiction: different instructions at the same address *)
    try (match goal with
         | Hexec : executing _ ?COMP ?MEM ?PC,
           Hexec' : executing _ ?COMP ?MEM ?PC |- _ =>
           unfold executing in Hexec, Hexec';
           rewrite Hexec in Hexec';
           inversion Hexec'; subst; auto
         end);
    (* contradiction: different values in the same register *)
    try (match goal with
         | Hreg_neq : Register.get _ _ <> 0,
           Hreg_eq : Register.get _ _ = 0 |- _ =>
           exfalso; apply Hreg_neq; apply Hreg_eq
         end).
  (* load from the same memory address *)
  - match goal with
    | Hmemget1 : Some _ = Memory.get mem _ _,
      Hmemget2 : Some _ = Memory.get mem _ _ |- _ =>
      rewrite <- Hmemget1 in Hmemget2;
        inversion Hmemget2; subst; auto
    end.
  (* return exactly to same component and address *)
  - match goal with
    | Hstack : (C', pc') :: d' = (_, _) :: _
      |- _ =>
      inversion Hstack; subst; auto
    end.
Qed.

Section SEMANTICS.
  Variable G : global_env.

  Definition semantics :=
    Semantics_gen step (initial_state G) final_state G.
End SEMANTICS.
End LTT.

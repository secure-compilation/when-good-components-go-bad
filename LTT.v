Require Import Common.
Require Import Machine.
Require Import Traces.

Module LTT.

Import AbstractMachine.

Definition stack:= list (Component.id * Memory.address).

Definition state : Type := 
  (Component.id * stack * Memory.data * Register.data * Memory.address).

Record global_env := mkGlobalEnv {
  get_interfaces : Program.interface;
  get_entrypoints : EntryPoint.data;
}.

Record global_env_wf (G : global_env) := mkGlobalEnvWF {
  entrypoints_exist :
    forall CI C,
      In CI (get_interfaces G) ->
      Component.name CI = C ->
      M.In C (get_entrypoints G) /\
      exists addrs, M.MapsTo C addrs (get_entrypoints G);
}.

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

Lemma epsilon_step_preserves_component_and_stack:
  forall G C d mem regs pc C' d' mem' regs' pc',
    G |-LTT (C,d,mem,regs,pc) =>[E0] (C',d',mem',regs',pc') ->
    C' = C /\ d' = d.
Proof.
  intros G C d mem regs pc C' d' mem' regs' pc' Hstep.
  inversion Hstep; subst;
    split; trivial.
Qed.

Lemma epsilon_step_weakening:
  forall Is E C d1 mem mem' cmem cmem' regs regs' pc pc',
    M.MapsTo C cmem  mem ->
    M.MapsTo C cmem' mem' ->
    (mkGlobalEnv Is E) |-LTT (C,d1,mem,regs,pc) =>[E0] (C,d1,mem',regs',pc') ->
  forall E' d2 wmem,
    M.MapsTo C cmem wmem ->
    exists wmem',
      M.MapsTo C cmem' wmem' ->
      (mkGlobalEnv Is E') |-LTT (C,d2,wmem,regs,pc) =>[E0] (C,d2,wmem',regs',pc').
Proof.
  intros Is E C d1 mem mem' cmem cmem' regs regs' pc pc'.
  intros HCmem HCmem' Hstep.
  intros E' d2 wmem HCwmem.
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
  inversion E1 as [ ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? Hexec |
                    ? ? ? ? ? ? ? ? Hexec ];
    subst;
      inversion E2 as [ ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? Hexec' |
                        ? ? ? ? ? ? ? ? Hexec' ];
    subst;
    (* same step *)
    try reflexivity;
    (* different instructions *)
    try (unfold executing in Hexec, Hexec';
         rewrite Hexec in Hexec'; inversion Hexec'; subst; trivial).
  (* load from the same memory address *)
  - rewrite <- H0 in H1. inversion H1. subst. trivial.
  (* conditional jumps take different branches *) 
  - exfalso. apply H. apply H0.
  - exfalso. apply H0. apply H.
  (* return exactly to same component and address *)
  - inversion H. subst. trivial.
Qed.

End LTT.
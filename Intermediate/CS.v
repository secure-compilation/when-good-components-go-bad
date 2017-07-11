Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Events.
Require Import Common.Smallstep.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.

Module CS.
  Import Intermediate.

  Definition stack : Type := list Pointer.t.

  Definition state : Type := stack * Memory.t * Register.t * Pointer.t.

  Inductive step (G : global_env) : state -> trace -> state -> Prop :=
  | Nop: forall gps mem regs pc,
      executing G pc Nop ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc)

  | Const: forall gps mem regs regs' pc r v,
      executing G pc (Const v r) ->
      Register.set r (imm_to_val v) regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

  | Mov: forall gps mem regs regs' pc r1 r2,
      executing G pc (Mov r1 r2) ->
      Register.set r2 (Register.get r1 regs) regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

  | BinOp: forall gps mem regs regs' pc r1 r2 r3 op,
      executing G pc (BinOp op r1 r2 r3) ->
      Register.set r3
                   (eval_binop op (Register.get r1 regs) (Register.get r2 regs))
                   regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

  | Load: forall gps mem regs regs' pc r1 r2 ptr v,
      executing G pc (Load r1 r2) ->
      Register.get r1 regs = Ptr ptr ->
      Memory.load mem ptr = Some v ->
      Register.set r2 v regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs', Pointer.inc pc)

  | Store: forall gps mem regs pc ptr r1 r2 mem',
      executing G pc (Store r1 r2) ->
      Register.get r1 regs = Ptr ptr ->
      Pointer.component ptr = Pointer.component pc ->
      Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
      step G (gps, mem, regs, pc) E0 (gps, mem', regs, Pointer.inc pc)

  | Jal: forall gps mem regs regs' pc pc' l,
      executing G pc (Jal l) ->
      find_label_in_component G pc l = Some pc' ->
      Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs', pc')

  | Jump: forall gps mem regs pc pc' r,
      executing G pc (Jump r) ->
      Register.get r regs = Ptr pc' ->
      Pointer.component pc' = Pointer.component pc ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc')

  | BnzNZ: forall gps mem regs pc pc' r l val,
      executing G pc (Bnz r l) ->
      Register.get r regs = Int val ->
      val <> 0 ->
      find_label_in_procedure G pc l = Some pc' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc')

  | BnzZ: forall gps mem regs pc pc' r l,
      executing G pc (Bnz r l) ->
      Register.get r regs = Int 0 ->
      find_label_in_procedure G pc l = Some pc' ->
      step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc')

  | Alloc: forall gps mem mem' regs regs' pc rsize rptr size ptr,
      executing G pc (Alloc rptr rsize) ->
      Register.get rsize regs = Int size ->
      Memory.alloc mem (Pointer.component pc) size = Some (mem', ptr) ->
      Register.set rptr (Ptr ptr) regs = regs' ->
      step G (gps, mem, regs, pc) E0 (gps, mem', regs', Pointer.inc pc)

  | Call: forall gps gps' mem regs pc b C' P rcomval,
      executing G pc (Call C' P) ->
      Pointer.component pc <> C' ->
      imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
      gps' = Pointer.inc pc :: gps ->
      EntryPoint.get C' P (genv_entrypoints G) = Some b ->
      let pc' := (C', b, 0) in
      Register.get R_COM regs = Int rcomval ->
      let t := [ECall (Pointer.component pc) P rcomval C'] in
      step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc')

  | Return: forall gps gps' mem regs pc pc' rcomval,
      executing G pc Return ->
      gps = pc' :: gps' ->
      Pointer.component pc <> Pointer.component pc' ->
      Register.get R_COM regs = Int rcomval ->
      let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
      step G (gps, mem, regs, pc) t (gps', mem, Register.invalidate regs, pc').

  Theorem determinism:
    forall G s t s1 s2,
      step G s t s1 -> step G s t s2 -> s1 = s2.
  Proof.
  Admitted.
End CS.
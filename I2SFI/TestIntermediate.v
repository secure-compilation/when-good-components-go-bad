Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Common.Maps.
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.

Require Import CompCert.Events.

Require Export Lib.Monads.
Require Import FunctionalExtensionality.

Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Import MonadNotations.
Open Scope monad_scope.

Inductive ExecutionError :=
| MissingComponentId : Pointer.t -> ExecutionError
| NegativePointerOffset : Pointer.t -> ExecutionError
| LoadOutsideComponent : ExecutionError
| LoadNotAddressInReg : ExecutionError
| StoreOutsideComponent : ExecutionError
| StoreNotAddressInReg : ExecutionError
| JumpOutsideComponent : ExecutionError
| JumpNotAddressInReg : ExecutionError
| MissingJalLabel: ExecutionError
| MissingLabel : ExecutionError
| MissingBlock : Pointer.t -> ExecutionError
| OffsetTooBig : Pointer.t -> ExecutionError
| MemoryError : Pointer.t -> Pointer.t -> ExecutionError
| StoreMemoryError : Pointer.t -> Pointer.t -> ExecutionError
| NotIntInReg : ExecutionError
| AllocNegativeBlockSize : ExecutionError
| InvalidEnv : ExecutionError
| NoInfo: ExecutionError
.

Inductive execution_state {A:Type} :=
| Running : A -> execution_state
| OutOfFuel : A -> execution_state
| Halted : trace -> execution_state
| Wrong : trace -> string -> ExecutionError -> execution_state.

Instance exec_monad : Monad (@execution_state)
  := {      
      ret := fun {A:Type} (x:A) => @Running A x;
      
      bind := fun {A B:Type} (x : @execution_state A) (f : A -> @execution_state B) => 
                match x with
                | Running y => f y
                | Wrong tr m err => Wrong tr m err
                | Halted tr => Halted tr
                | OutOfFuel y => f y
                end
    }.
(* Not a real monad. Does not have right identity. *)

Definition t : Type :=  (trace*CS.state).

Definition lift {A} (x: option A) (msg : string) (err : ExecutionError) :=
  match x with
  | None  => (@Wrong A E0 msg err)
  | Some v => (@Running A v)
  end.
    
Definition fail {A} (msg : string) (err : ExecutionError) :=
  (@Wrong A E0 msg err).


Definition eval_step (G: global_env) (s: CS.state)  : (@execution_state t) :=
  let '(gps, mem, regs, pc) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- lift (getm (genv_procedures G) (Pointer.component pc) )
        "Missing component"%string (MissingComponentId pc);
    match (getm C_procs (Pointer.block pc)) with
    | None => fail "Missing block"%string (MissingBlock pc)
    | Some P_code => 
      if ((Pointer.offset pc) <? 0)%Z then
        fail "Negative offset"%string (NegativePointerOffset pc)
      else
        match nth_error P_code (Z.to_nat (Pointer.offset pc)) with
        | None => fail "Offset too big"%string (OffsetTooBig pc)
        | Some instr =>
          (* decode and execute the instruction *)
          match instr with
          | ILabel l =>
            ret (E0, (gps, mem, regs, Pointer.inc pc))
          | INop =>
            ret (E0, (gps, mem, regs, Pointer.inc pc))
          | IConst v r =>
            let regs' := Intermediate.Register.set r (imm_to_val v) regs in
            ret (E0, (gps, mem, regs', Pointer.inc pc))
          | IMov r1 r2 =>
            let regs' := Intermediate.Register.set r2 (Intermediate.Register.get r1 regs) regs in
            ret (E0, (gps, mem, regs', Pointer.inc pc))
          | IBinOp op r1 r2 r3 =>
            let regs' := Intermediate.Register.set
                           r3 (eval_binop op (Intermediate.Register.get r1 regs)
                                          (Intermediate.Register.get r2 regs))
                           regs in
            ret (E0, (gps, mem, regs', Pointer.inc pc))
          | ILoad r1 r2 =>
            match Intermediate.Register.get r1 regs with
            | Ptr ptr =>
              if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
                do v <- lift (Memory.load mem ptr) "Memory load error" (MemoryError ptr pc);
                  let regs' := Intermediate.Register.set r2 v regs in
                  ret (E0, (gps, mem, regs', Pointer.inc pc))
              else
                fail "Load outside component"%string LoadOutsideComponent
            | _ => fail "Not a pointer value in address register"%string LoadNotAddressInReg
            end
          | IStore r1 r2 =>
            match Intermediate.Register.get r1 regs with
            | Ptr ptr =>
              if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
                do mem' <- lift (Memory.store mem ptr (Intermediate.Register.get r2 regs))
                "Memory store error"%string (StoreMemoryError ptr pc);
                  ret (E0, (gps, mem', regs, Pointer.inc pc))
              else
                fail "Store outside component"%string StoreOutsideComponent
            | _ => fail "Not a pointer value in address register"%string StoreNotAddressInReg
            end
          | IJal l =>
            do pc' <- lift (find_label_in_component G pc l)
              "Missing Jal label"%string MissingJalLabel;
              let regs' :=  Intermediate.Register.set R_RA (Ptr (Pointer.inc pc)) regs in
              ret (E0, (gps, mem, regs', pc'))
          | IJump r =>
            match Intermediate.Register.get r regs with
            | Ptr pc' =>
              if Component.eqb (Pointer.component pc') (Pointer.component pc) then
                ret (E0, (gps, mem, regs, pc'))
              else
                fail "Jump outside component"%string JumpOutsideComponent
            | _ => fail "Not a pointer value in address register"%string JumpNotAddressInReg
            end
          | IBnz r l =>
            match Intermediate.Register.get r regs with
            | Int 0 =>
              ret (E0, (gps, mem, regs, Pointer.inc pc))
            | Int val =>
              do pc' <- lift (find_label_in_procedure G pc l)
                  "Missing Bnz label"%string MissingLabel;
                ret (E0, (gps, mem, regs, pc'))
            | _ => fail  "Bnz::Not int"%string NotIntInReg
            end
          | IAlloc rptr rsize =>
            match Intermediate.Register.get rsize regs with
            | Int size =>
              if (size <=? 0)%Z then
                fail  "Negative block size"%string AllocNegativeBlockSize
              else
                do (mem', ptr) <- lift (Memory.alloc mem (Pointer.component pc) (Z.to_nat size))
                   "Alloc failed"%string (MemoryError pc pc);
                let regs' := Intermediate.Register.set rptr (Ptr ptr) regs in
                ret (E0, (gps, mem', regs', Pointer.inc pc))
            | _ => fail  "Alloc::Not int"%string NotIntInReg
            end
          | ICall C' P =>
            if negb (Component.eqb (Pointer.component pc) C') then
              if imported_procedure_b (genv_interface G) (Pointer.component pc) C' P then
                do b <- lift (Intermediate.EntryPoint.get C' P (genv_entrypoints G))
                    "Call::Incorrect environment"%string InvalidEnv;
                  match Intermediate.Register.get R_COM regs with
                  | Int rcomval =>
                    let pc' := (C', b, 0%Z) in
                    let tr := [ECall (Pointer.component pc) P rcomval C'] in
                    let res : t := (tr, (Pointer.inc pc :: gps,
                                         mem,
                                         Intermediate.Register.invalidate regs,
                                         pc')) in
                    ret res
                  | Ptr _ => fail "Call::Ptr in register R_COM"%string NoInfo
                  | Undef => fail "Call::Undef in register R_COM"%string NoInfo
                  end
              else
                fail  "Call::procedure not imported"%string InvalidEnv
            else
              fail  "Call::same component"%string InvalidEnv
          | IReturn =>
            match gps with
            | pc' :: gps' =>
              if negb (Component.eqb (Pointer.component pc) (Pointer.component pc')) then
                match Intermediate.Register.get R_COM regs with
                | Int rcomval =>
                  let tr := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
                  ret (tr, (gps', mem, Intermediate.Register.invalidate regs, pc'))
                | Ptr _ => fail "Return::Ptr in register R_COM"%string NoInfo
                | Undef => fail "Return::Undef in register R_COM"%string NoInfo
                end
              else
                fail  "Return::same component"%string InvalidEnv
            | _ => fail "Empty Stack"%string InvalidEnv
            end
          | IHalt =>  Halted E0
          end
        end
    end
.

Fixpoint execN (n: nat) (G: global_env) (tr:trace) (st: CS.state) : execution_state :=
  match n with
  | O => OutOfFuel (tr,st)
  | S n' =>
    match eval_step G st with
    | Halted _ => Halted tr
    | OutOfFuel s => OutOfFuel s
    | Wrong _ msg err => Wrong tr msg err
    | Running (ntr,nst) => execN n' G (tr++ntr) nst
    end
  end.

Definition runp (n : nat) (p : Intermediate.program) : execution_state :=
  let G := prepare_global_env p in
  let st := CS.initial_machine_state p in
  execN n G nil st.


Close Scope monad_scope.
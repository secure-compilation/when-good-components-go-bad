(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Logic.
Require Import Coq.Structures.Equalities.

From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype.

Require Import CompCert.Events.
Require Import Common.Definitions.
Require Import TargetSFI.Machine.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.EitherMonad.

Require Export Lib.Monads.
Export MonadNotations.
Open Scope monad_scope.

Module CS.

  Import RiscMachine.
  Import RiscMachine.ISA.
  Import RiscMachine.Memory.
  Import SFI.
  Import Env.
  Import MachineState.

  (* Set Printing Implicit. *)
  (* Set Typeclasses Debug. *)

  Import MonadNotations.
  Open Scope monad_scope.

  
  Definition ret_trace (G : Env.t) (pc pc' : RiscMachine.pc)
             (gen_regs : RiscMachine.RegisterFile.t) :option trace :=
    do rcomval <- RegisterFile.get_register Register.R_COM gen_regs;
      do cpc <- Env.get_component_name_from_id (SFI.C_SFI pc) G;
      do cpc' <- Env.get_component_name_from_id (SFI.C_SFI pc') G;
      Some [ERet cpc rcomval cpc'].

  
  Definition call_trace (G : Env.t) (pc pc' : RiscMachine.pc)
             (gen_regs : RiscMachine.RegisterFile.t) : option trace :=
    do rcomval <- RegisterFile.get_register Register.R_COM gen_regs;
      do cpc <- Env.get_component_name_from_id (SFI.C_SFI pc) G;
      do cpc' <- Env.get_component_name_from_id (SFI.C_SFI pc') G;
      do p <- Env.get_procedure pc' G;
      Some [ECall cpc p rcomval cpc'].

  
  Inductive step (G : Env.t) :
    MachineState.t -> trace-> MachineState.t -> Prop :=
  | Nop : forall mem mem' pc gen_regs,      
      executing mem pc INop ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem', inc_pc pc,gen_regs)
           
  | Const : forall mem mem' pc gen_regs gen_regs' val reg,
      executing mem pc (IConst val reg) ->
      RegisterFile.set_register reg val gen_regs = gen_regs' ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem', inc_pc pc,gen_regs')

  | Mov : forall mem mem' pc gen_regs gen_regs' reg_src reg_dst val,
      executing mem pc (IMov reg_src reg_dst) ->
      Some val = RegisterFile.get_register reg_src gen_regs ->
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem', inc_pc pc,gen_regs')

  | BinOp : forall mem mem' pc gen_regs gen_regs' op reg_src1 reg_src2 reg_dst val1 val2,
      executing mem pc (IBinOp op reg_src1 reg_src2 reg_dst) ->
      Some val1 = RegisterFile.get_register reg_src1 gen_regs ->
      Some val2 = RegisterFile.get_register reg_src2 gen_regs ->
      let result := eval_binop op val1 val2 in
      RegisterFile.set_register reg_dst result gen_regs = gen_regs' ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',inc_pc pc,gen_regs')

  | Load : forall mem mem' pc gen_regs gen_regs' rptr rd ptr val,
      executing mem pc (ILoad rptr rd) ->
      Some ptr = RegisterFile.get_register rptr gen_regs ->
      let addr := Memory.to_address (ptr) in
      Some val = Memory.get_value mem addr ->
      RegisterFile.set_register rd val gen_regs = gen_regs' ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',inc_pc pc,gen_regs')
           
  | Store: forall mem mem' pc gen_regs rptr rs ptr val,
      executing mem pc (IStore rptr rs) ->
      Some ptr = RegisterFile.get_register rptr gen_regs ->
      Some val = RegisterFile.get_register rs gen_regs ->
      Memory.Equal (Memory.set_value mem (Memory.to_address ptr) val) mem' ->
      step G (mem,pc,gen_regs) E0 (mem',inc_pc pc,gen_regs)

  | BnzNZ: forall mem mem' pc gen_regs reg offset val,
      executing mem pc (IBnz reg offset) ->
      Some val = RegisterFile.get_register reg gen_regs ->
      val <> Z0 ->
      let pc' := Z.to_N( Z.add (Z.of_N pc) offset ) in
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',pc',gen_regs)
           
  | BnzZ: forall mem mem' pc gen_regs reg offset,
      executing mem pc (IBnz reg offset) ->
      Some Z0 = RegisterFile.get_register reg gen_regs ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',inc_pc pc,gen_regs)
           
  | Return: forall mem mem' pc gen_regs reg t addr,
      executing mem pc (IJump reg) ->
      Some addr = RegisterFile.get_register reg gen_regs ->
      let pc' := Memory.to_address addr in
      Some t = ret_trace G pc pc' gen_regs ->
      ~SFI.is_same_component pc pc' ->
      ~SFI.is_same_component pc' SFI.MONITOR_COMPONENT_ID ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) t (mem',pc',gen_regs)

  | Jump: forall mem mem' pc gen_regs reg addr,
      executing mem pc (IJump reg) ->
      Some addr = RegisterFile.get_register reg gen_regs ->
      let pc' := Memory.to_address addr in
      (SFI.is_same_component pc pc') \/ (SFI.is_same_component pc' SFI.MONITOR_COMPONENT_ID) ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',pc',gen_regs)
           
  | Jal: forall mem mem' pc gen_regs gen_regs' addr,      
      executing mem pc (IJal addr) ->
      let ra := Z.of_N (inc_pc pc) in
      RegisterFile.set_register Register.R_RA ra gen_regs = gen_regs'->
      let pc' := addr in
      (SFI.is_same_component pc pc') \/ (SFI.is_same_component pc SFI.MONITOR_COMPONENT_ID) ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) E0 (mem',pc',gen_regs')
           
  | Call: forall mem mem' pc gen_regs gen_regs' addr t,
      executing mem pc (IJal addr) ->
      let ra := Z.of_N (inc_pc pc) in
      RegisterFile.set_register Register.R_RA ra gen_regs = gen_regs'->
      let pc' := addr in
      Some t = call_trace G pc pc' gen_regs ->
      ~SFI.is_same_component pc pc'->
       ~SFI.is_same_component pc SFI.MONITOR_COMPONENT_ID ->
      Memory.Equal mem mem' -> 
      step G (mem,pc,gen_regs) t (mem',pc',gen_regs').

  Open Scope string_scope.
  Section FunctionalRepresentation.

    Variable state_records : Type.

    Variable update_state_records :
      Env.t
      -> MachineState.t
      -> trace
      -> MachineState.t
      -> state_records
      -> state_records.

    Notation STATE := (StateMonad.t state_records).
    Notation lift := (StateMonad.lift state_records).
    Notation get := (StateMonad.get state_records).
    Notation put := (StateMonad.put state_records).
    Notation modify := (StateMonad.modify state_records).
    Notation fail := (StateMonad.fail state_records).
    Notation run := (StateMonad.run state_records).

    Definition DEBUG := false.
    
    Definition eval_step_with_state (G : Env.t) (s : MachineState.t)
      : STATE (trace * MachineState.t) :=
      
      let '(mem,pc,gen_regs) := s in
      let get_reg r := 
          (lift (RegisterFile.get_register r gen_regs)
               "Unknown register" (RegisterNotFound s r)) in
      match Memory.get_word mem pc with
      | Some (Instruction instr) =>
        match instr with
        | INop => ret (Right (E0, (mem,inc_pc pc,gen_regs)))
        | IConst val reg =>
          let gen_regs' :=  RegisterFile.set_register reg val gen_regs in
          ret (E0, (mem,inc_pc pc,gen_regs'))
        | IMov reg_src reg_dst =>
          do val <- get_reg reg_src;
            let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in
            ret (E0, (mem,inc_pc pc,gen_regs'))
        | ISA.IBinOp op reg_src1 reg_src2 reg_dst =>
          do val1 <- get_reg reg_src1;
            do val2 <- get_reg reg_src2;
            let result : value := RiscMachine.eval_binop op val1 val2 in
            let gen_regs':= RegisterFile.set_register reg_dst result gen_regs in
            ret (E0, (mem,inc_pc pc,gen_regs'))
        | ILoad rptr rd =>
          do ptr <- get_reg rptr;
            if (DEBUG)
            then
              let addr := Memory.to_address ptr in
              do word <- lift (Memory.get_word mem addr)
                 "Uninitialized mem(ILoad) " (UninitializedMemory s addr);
                match word with
                | Data val =>
                  let gen_regs' := RegisterFile.set_register rd val gen_regs in
                  ret (E0, (mem,inc_pc pc,gen_regs'))
                | Instruction i => (fail "ILoad from code memory " (CodeMemoryException s addr i))
                end
            else
              let addr := Memory.to_address ptr in
              let val :=
                  match Memory.get_word mem addr with
                  | None => Z0
                  | Some word =>
                    match word with 
                    | Data val => val
                    | _ => Z0
                    end
                  end in
              let gen_regs' := RegisterFile.set_register rd val gen_regs in
              ret (E0, (mem,inc_pc pc,gen_regs'))
        | IStore rptr rs =>
          do ptr <- get_reg rptr;
            let addr := Memory.to_address ptr in
            if (SFI.is_code_address addr)
            then
              fail "IStore in code memory" (CodeMemoryException s addr instr)
            else
              do val <- get_reg rs;
              let mem': Memory.t := Memory.set_value mem addr val  in
              ret (E0, (mem',inc_pc pc,gen_regs))
        | IBnz reg offset =>
          do val <- get_reg reg;
            let pc': address :=  if Z.eqb val Z0 then inc_pc pc
                                 else (Z.to_N (Z.add (Z.of_N pc) offset)) in
            ret  (E0, (mem,pc',gen_regs))
        | IJump reg =>
          do addr <- get_reg reg;
            let pc' := Memory.to_address addr in
            if SFI.is_same_component_bool pc pc' then
              ret (E0, (mem,pc',gen_regs))
            else
              (* if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID) *)
              (* then *)
              (*   fail "Jump" (IllegalJumpFromZeroComponent s) *)
              (* else *)
                if (N.eqb (SFI.C_SFI pc') SFI.MONITOR_COMPONENT_ID)
                then
                  ret (E0, (mem,pc',gen_regs))
                else
                  do rcomval <- get_reg Register.R_COM;
              do cpc <- lift (Env.get_component_name_from_id (SFI.C_SFI pc) G)
                 "No intermediate component id" 
                 (MissingComponentId s  (SFI.C_SFI pc) (fst G));
                do cpc' <- lift (Env.get_component_name_from_id (SFI.C_SFI pc') G)
                   "No intermediate component id" 
                   (MissingComponentId s  (SFI.C_SFI pc') (fst G));
                ret ([ERet cpc rcomval cpc'], (mem,pc',gen_regs))
        | IJal addr =>
          let ra := Z.of_N (pc+1) in
          let gen_regs' := RegisterFile.set_register Register.R_RA ra gen_regs in
          let pc' := addr in
          if SFI.is_same_component_bool pc pc' then ret (E0, (mem,pc',gen_regs'))
          else
            (* if (N.eqb (SFI.C_SFI pc') SFI.MONITOR_COMPONENT_ID) *)
            (* then *)
            (*      fail "Jal" (IllegalJalToZeroComponent s) *)
            (* else *)
              if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
              then
                ret (E0, (mem,pc',gen_regs')) 
              else
                let ot := call_trace G pc pc' gen_regs in
                match ot with
                | None => fail "Call trace error"
                              (CallEventError s (SFI.C_SFI pc) (SFI.C_SFI pc')
                                              (fst G) (snd G))
                | Some t => ret (t, (mem,pc',gen_regs'))
                end
        | IHalt => ret (E0,(mem,pc,gen_regs))
        end
      | Some (Data val) => fail "Pc in data memory" (DataMemoryException s pc val)
      | None =>
        if (DEBUG)
        then 
          fail "Pc address not initialized" (UninitializedMemory s pc)
        else
          if (SFI.last_address_in_slot pc) 
          then            
            ret (E0, (Memory.set_instr mem pc IHalt,pc,gen_regs)) (* IHalt *)
          else
            if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
            then
              fail "Pc address not initialized" (UninitializedMemory s pc)
            else
              ret (E0, (mem,inc_pc pc,gen_regs)) (* INop *)
            
      end.

    Close Scope string_scope.

    Fixpoint eval_steps_with_state (n : nat) (G : Env.t) (s : MachineState.t)
      : STATE (trace * MachineState.t * nat) :=
      match n with
      | O => ret (E0,s,0%nat)
      | S n' => do (t',s') <- eval_step_with_state G s;
                 do! modify (update_state_records G s t' s');
                 (* check if a Halt was executed *)
                  let '(mem,pc,gen_regs) := s in
                  match Memory.get_word mem pc with
                  | Some (Instruction instr) =>
                    match instr with
                    | IHalt => ret (t',s',n')                   
                    | _ =>  
                      do (t'',s'',n'') <- eval_steps_with_state n' G s';
                        ret (t'++t'',s'',n'')
                    end
                  | _ =>
                    if (DEBUG)
                    then 
                      fail "eval_steps_with_state: Impossible branch" NoInfo
                    else
                      do (t'',s'',n'') <- eval_steps_with_state n' G s';
                      ret (t'++t'',s'',n'')
                  end
      end.

    Fixpoint eval_program_with_state (fuel : nat) (p : sfi_program) (regs : RegisterFile.t)
      : STATE (trace * MachineState.t * nat) :=
      let st0 := ((TargetSFI.Machine.mem p), RiscMachine.PC0, regs) in
      let g := ((TargetSFI.Machine.cn p),(TargetSFI.Machine.e p)) in
      do res <- eval_steps_with_state fuel g st0;
        let '((t,s),n) := res in
        ret (t,s,(fuel-n)%nat)
    .

  End FunctionalRepresentation.

  Definition update_empty_records (_ : Env.t) (_ : MachineState.t) (_ : trace)
             (_ : MachineState.t) (_ : unit) : unit := tt.
  
  Definition eval_step (G : Env.t) (s : MachineState.t)
    : @Either (trace * MachineState.t) :=
    fst ((eval_step_with_state unit G s) tt).

  Definition eval_program (fuel : nat) (p : sfi_program) (regs : RegisterFile.t)
      : @Either (trace * MachineState.t) :=
    do res <- fst ((eval_program_with_state unit update_empty_records fuel p regs) tt);
      ret (fst res).

  Definition initial_state (p : sfi_program) (s0 : MachineState.t) : bool :=
    MachineState.eqb
      ((TargetSFI.Machine.mem p), RiscMachine.PC0, RiscMachine.RegisterFile.reset_all)
      s0
  .

  Definition final_state (G : Env.t) (s : MachineState.t) : bool :=
    let '(mem,pc,regs) := s in
    is_executing mem pc IHalt.
  
  Conjecture eval_step_complete :
    forall (G : Env.t)  (st : MachineState.t) (t : trace) (st' : MachineState.t),
      (step G st t st') -> (eval_step G st = Right (t, st')).
  
  
  Conjecture eval_step_sound:
    forall (G : Env.t)  (st : MachineState.t) (t : trace) (st' : MachineState.t),
      eval_step G st = Right (t, st') -> step G st t st'.
  
  Close Scope monad_scope.

End CS.
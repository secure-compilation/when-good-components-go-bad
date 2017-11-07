(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.MachineGen.

Require Import Intermediate.Machine.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Instance show_intermediate_program : Show Intermediate.program :=
  {|
    show := fun _ => Coq.Strings.String.EmptyString (* TODO *)
  |}.

(* TODO implement this *)
Definition genIntermediateProgram : G Intermediate.program :=
  let COMP1_ID : positive := 1%positive in
  let PROC1_ID : positive := 1%positive in
  let BLOCK1_ID : positive := 1%positive in
  let component1_interface : Component.interface :=
      (Component.mkCompInterface [PROC1_ID] []) in
  let program_interface : Program.interface :=
      PMap.add COMP1_ID component1_interface (PMap.empty Component.interface) in
  let buffers := PMap.add COMP1_ID [(BLOCK1_ID,10%nat)] (PMap.empty (list (Block.id * nat))) in
  let proc1_code := (PMap.add PROC1_ID
                              ([
                                  Intermediate.Machine.IConst
                                    (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 
                                  ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2 
                                  ; Intermediate.Machine.IStore R_AUX1 R_AUX2
                                  ; Intermediate.Machine.IReturn])
                              (PMap.empty Intermediate.Machine.code) ) in
  let procs := PMap.add COMP1_ID proc1_code
                        (PMap.empty (PMap.t Intermediate.Machine.code)) in
  returnGen {|
        Intermediate.prog_interface := program_interface;
        Intermediate.prog_procedures := procs;
        Intermediate.prog_buffers := buffers;
        Intermediate.prog_main := (COMP1_ID,PROC1_ID)
      |}.


(* This is how I would like to write the property to test *)
(* TODO check it later *)
Conjecture correct_data_compartmentalized:

  forall (sfi_p : sfi_program) (ip : Intermediate.program)
    (n : nat) (mem : RiscMachine.Memory.t) (pc : RiscMachine.address)
    (gen_regs : RiscMachine.RegisterFile.t)
    (rp rs : RiscMachine.Register.t)
    (t : CompCert.Events.trace) 
    (ptr sfi_sp_val: RiscMachine.value ),

    TargetSFI.EitherMonad.Right sfi_p = compile_program ip /\
    TargetSFI.EitherMonad.Right (t, (mem,pc,gen_regs)) = (CS.eval_program n sfi_p RiscMachine.RegisterFile.reset_all) /\
    RiscMachine.Memory.get_word mem pc = Some (RiscMachine.Instruction (RiscMachine.ISA.IStore rp rs)) ->
    (* Write at the top of SFI stack (from a pc that is in the list of push sfi ??) *)
    (
      rp = RiscMachine.Register.R_AUX1 /\
      rs = RiscMachine.Register.R_RA /\
      Some ptr = RiscMachine.RegisterFile.get_register rp gen_regs /\
      Some sfi_sp_val = RiscMachine.RegisterFile.get_register
                          RiscMachine.Register.R_SFI_SP gen_regs /\
      RiscMachine.Memory.to_address ptr = SFI.address_of SFI.MONITOR_COMPONENT_ID
                                                  (2*(Z.to_N sfi_sp_val))%N N0 
    )
    \/ (* same component write into a data block *)
    ( Some ptr = RiscMachine.RegisterFile.get_register rp gen_regs /\
      (Z0 <= ptr)%Z /\    
      SFI.is_same_component pc (RiscMachine.Memory.to_address ptr) /\
      (SFI.is_data_address (RiscMachine.Memory.to_address ptr)) = true
    ).

    
(************************************************
 * No writes outside it's own memory, 
 * except for push sfi.
 *************************************************)

Definition store_log_entry := RiscMachine.pc * RiscMachine.address * RiscMachine.value.

Definition store_log := list store_log_entry.

Definition update_store_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : store_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IStore rptr rs =>
      match RiscMachine.RegisterFile.get_register rptr regs with
      | Some ptr =>
        let addr := RiscMachine.Memory.to_address ptr in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_SFI_SP regs with
        | Some sp => (log ++ [(pc,addr,sp)])%list
        | _ => log
        end
      | _ => log
      end
    | _ => log
    end
  | _ => log
  end.
            
Definition show_log_entry (entry : store_log_entry) : string :=
  let '(pc,addr,sfi_sp) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " sfi sp: " ++ (show sfi_sp).

Definition eval_store_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t) * store_log) :=
  ((CS.eval_program_with_state     
     store_log
     update_store_log
     (100%nat)
     p
     (RiscMachine.RegisterFile.reset_all)) nil).
  
Definition store_checker (log : store_log) : Checker :=
  conjoin (List.map (fun '(pc,addr,sfi_sp) =>
                       if (SFI.is_same_component_bool pc addr)
                       then checker true
                       else
                         if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                         then
                           whenFail ("Failed at: " ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                    (N.eqb addr (SFI.address_of
                                                   SFI.MONITOR_COMPONENT_ID
                                                   (Z.to_N (2 * sfi_sp +1))
                                                   0))
                         else
                           whenFail ("Failed at: " ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                    false
                    ) log).

Definition store_correct : Checker :=
  forAll genIntermediateProgram
  ( fun ip =>
      match compile_program ip with
      | TargetSFI.EitherMonad.Left msg => checker false
      | TargetSFI.EitherMonad.Right p =>
        let (res,log) := eval_store_program p in
        store_checker log (* check the log even if the program fails *)
      end
  ).

(********************************************
 * Jumps
 ************************************************)

Definition jump_log_entry := RiscMachine.pc * RiscMachine.address * CompCert.Events.trace.

Definition jump_log := list (@Either jump_log_entry).

Definition update_jump_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : jump_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
      if (N.eqb r RiscMachine.Register.R_RA) || (N.eqb r RiscMachine.Register.R_T)
      then
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => (log ++ [TargetSFI.EitherMonad.Right (pc, RiscMachine.Memory.to_address ptr,t)])%list
        | _ => log
        end
      else
        (log ++ [TargetSFI.EitherMonad.Left ("Illegal target register: " ++ (show_N r))%string])%list
    | RiscMachine.ISA.IJal addr => (log ++ [TargetSFI.EitherMonad.Right (pc,addr,t)])%list
    | _ => log
    end
  | Some (RiscMachine.Data _) => (log ++ [TargetSFI.EitherMonad.Left ("Data found at address: " ++ (show pc))%string])%list
  | _ => log
  end.
            
Definition show_jump_log_entry (entry : jump_log_entry) : string :=
  let '(pc,addr,t) := entry in
   "pc: " ++ (show pc)
          ++ " ptr: "
          ++ (show addr)
          ++ " trace: " ++ (show t).

Definition eval_jump_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t) * jump_log) :=
  ((CS.eval_program_with_state     
     jump_log
     update_jump_log
     (100%nat)
     p
     (RiscMachine.RegisterFile.reset_all)) nil).
  
Definition jump_checker (log : jump_log) : Checker :=
  conjoin (List.map (fun elt =>
                       match elt with
                       | TargetSFI.EitherMonad.Left msg => whenFail msg false
                       | TargetSFI.EitherMonad.Right (pc,addr,t) =>
                         if (SFI.is_same_component_bool pc addr)
                            || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                            || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                         then
                           match t with
                           | nil => checker true
                           | _ => whenFail ("Unexpectected event at log entry:" ++ (show_jump_log_entry (pc,addr,t)))
                                          false
                           end
                         else
                           match t with
                           | _::_ => checker true
                           | nill => whenFail ("Unexpectected empty event at log entry:" ++ (show_jump_log_entry (pc,addr,t)))
                                             false
                           end
                       end
                    ) log). (* TODO check the event too *)

Definition jump_correct : Checker :=
  forAll genIntermediateProgram
         ( fun ip =>
             match compile_program ip with
             | TargetSFI.EitherMonad.Left msg => checker false
             | TargetSFI.EitherMonad.Right p =>
               let (res,log) := eval_jump_program p in
               jump_checker log (* check the log even if the program fails *)
             end
         ).


(*******************************************************
 * Control Stack
 **********************************************************)
Inductive stack_op := Push
                    | Pop.

Definition show_op op :=
  match op with
  | Push => "Push"
  | Pop => "Pop"
  end.

Definition cs_log_entry := RiscMachine.pc * RiscMachine.address * stack_op * RiscMachine.ISA.instr.

Definition cs_log := list (@Either cs_log_entry).

Definition update_cs_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : cs_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => let addr := RiscMachine.Memory.to_address ptr in
                     if SFI.is_same_component_bool pc addr
                     then (* intra-component jump *)
                       if (N.eqb r RiscMachine.Register.R_T)
                       then log
                       else
                         (log ++ [TargetSFI.EitherMonad.Left ("Illegal target register: " ++ (show_N r))%string])%list  
                     else (* cross-component return *)
                       if (N.eqb r RiscMachine.Register.R_RA)
                       then
                         (log ++ [TargetSFI.EitherMonad.Right (pc, addr, Pop, instr)])%list
                       else
                         (log ++ [TargetSFI.EitherMonad.Left ("Illegal target register: " ++ (show_N r))%string])%list
        | _ => (log ++ [TargetSFI.EitherMonad.Left ("Can't find R_RA in general registers " ++ (show regs))%string])%list
        end
    | RiscMachine.ISA.IJal addr =>
      if SFI.is_same_component_bool pc addr
      then log
      else
        let '(mem',pc',regs') := st' in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_RA regs' with
        | Some addr => (log ++ [TargetSFI.EitherMonad.Right (pc, RiscMachine.Memory.to_address addr,Push, instr)])%list
        | _ => (log ++ [TargetSFI.EitherMonad.Left ("Can't find R_RA in general registers " ++ (show regs'))%string])%list
        end
    | _ => log
    end
  | Some (RiscMachine.Data _) => (log ++ [TargetSFI.EitherMonad.Left ("Data found at address: " ++ (show pc))%string])%list
  | _ => log
  end.
            
Definition show_cs_log_entry (entry : cs_log_entry) : string :=
  let '(pc,addr,t, instr) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " stack op: " ++ (show_op t)
          ++ "instr " ++ (show instr). 

Definition eval_cs_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t) * cs_log) :=
  ((CS.eval_program_with_state     
     cs_log
     update_cs_log
     (100%nat)
     p
     (RiscMachine.RegisterFile.reset_all)) nil).
  
Definition cs_checker (log : cs_log) : Checker :=
  let fix aux l s :=
      match l with
      | nil => checker true
      | elt::xs =>
        match elt with
        | TargetSFI.EitherMonad.Left msg => whenFail msg false
        | TargetSFI.EitherMonad.Right (pc,addr,op,instr) =>
          match op with
          | Push => aux xs (addr::s)
          | Pop =>
            match s with
            | nil => whenFail ("Attemting to pop from empty stack at address" ++ (show pc))%string false
            | a::s' => if (N.eqb a addr)
                      then aux xs s'
                      else whenFail ("Attemting address on the stack: "
                                       ++ (show_addr a)
                                       ++ " address in register: "
                                       ++ (show_addr addr)
                                       ++ "at pc: "
                                       ++ (show_addr pc)
                                       ++ " instr: "
                                       ++ (show instr)
                                    )%string
                                    false
            end
          end
        end
      end
  in aux log [].

Definition cs_correct : Checker :=
  forAll genIntermediateProgram
         ( fun ip =>
             match compile_program ip with
             | TargetSFI.EitherMonad.Left msg => checker false
             | TargetSFI.EitherMonad.Right p =>
               let (res,log) := eval_cs_program p in
               match res with
               | TargetSFI.EitherMonad.Left msg => whenFail msg (cs_checker log)
               | TargetSFI.EitherMonad.Right (t,(mem,_,regs)) => 
                 (whenFail ("memory of failed program: " ++ (show_mem  mem))%string
                        (cs_checker log) (* check the log even if the program fails *))
               end
             end
         ).

(****************** QUICK CHECKS ***************************)
QuickChick store_correct.
QuickChick jump_correct.
QuickChick cs_correct.

(* test compile correctness *)

(* Conjecture robust_compilation : *)
(*   forall (ip : Intermediate.program) (sp : sfi_program) *)
(*     (sc : sfi_program) (b : trace) *)

(*     eval  *)
(* . *)
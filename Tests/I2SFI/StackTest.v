(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.
Require Import TargetSFI.Machine.

Require Import TargetSFI.ExecutionError.
Require Import Tests.TargetSFI.SFITestUtil.
Require Import Tests.IntermediateProgramGeneration.
Require Import Tests.CompilerPBTests.

Require Import Tests.I2SFI.SFIPBTests.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Inductive stack_op := Push | Pop.
Definition stack_log_entry := (RiscMachine.pc
                           * RiscMachine.address
                           * stack_op * RiscMachine.ISA.instr)%type.

Definition show_op op :=
  match op with
  | Push => "Push"
  | Pop => "Pop"
  end.

Definition show_stack_log_entry (entry : stack_log_entry) : string :=
  let '(pc,addr,t, instr) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " stack op: " ++ (show_op t)
          ++ "instr " ++ (show instr). 

Instance show_cs_log_entry_i : Show stack_log_entry :=
  {| show := show_stack_log_entry |}.


Definition update_stack_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t)
           (log : (log_type stack_log_entry)) :=
  let '(mem,pc,regs) := st in
  let '(cs_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ pc::nil)%list
      else addr_log
  in
  let '(mem,pc,regs) := st in
  let '(cs_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ pc::nil)%list
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => let addr := RiscMachine.Memory.to_address ptr in
                     if SFI.is_same_component_bool pc addr
                     then (cs_log,nlog)
                     else (* cross-component return *)
                         ((cs_log ++ (pc, addr, Pop, instr)::nil)%list,nlog)
        | _ => (cs_log,nlog)
        end
          
    | RiscMachine.ISA.IJal addr =>
      if SFI.is_same_component_bool pc addr
      then (cs_log,nlog)
      else
        let '(mem',pc',regs') := st' in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_RA regs' with
        | Some addr => ((cs_log
                          ++
                          (pc, RiscMachine.Memory.to_address addr,Push, instr)::nil)%list
                       ,nlog)
        | _ => (cs_log,nlog)
        end
    | _ => (cs_log,nlog)
    end
  | _ => (cs_log,nlog)
  end.

(* 1. number of instr exec, 
   2. number of internal jump, 
   3. number of cross component jumps 
   5. number of static instructions executed
*)
Definition stack_stat := (nat * nat * nat)%type.

(* dynamic instr, static instr, 
   # of operations, 
   intermediate execution result *)
Instance show_stack_stat : Show stack_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, op, si) := ss in
        (show  steps)
          ++ "," ++ (show si)
          ++ "," ++ (show op)
  |}.

Definition stack_stats (log : (log_type stack_log_entry))
           (steps : nat) : stack_stat :=
  let '(l1,l2) := log in
  (steps, (List.length l1), List.length l2).

Fixpoint stack_mem_checker s mem : Checker :=
  match s with
  | nil => checker true
  | addr::xs =>
    let stack_address := SFI.address_of SFI.MONITOR_COMPONENT_ID
                                        (N.of_nat ((List.length s) - 1)%nat)
                                        0%N
    in
    match RiscMachine.Memory.get_word mem stack_address with
    | Some (RiscMachine.Data v) => 
      if (N.eqb addr (Z.to_N v))
      then stack_mem_checker xs mem
      else whenFail ("stack_mem_checker s=" ++ (show s))%string (checker false)
    | _ => whenFail ("stack_mem_checker stack_address="
                      ++ (show_addr stack_address))%string
                   (checker false)
    end
  end.

Fixpoint stack_step_checker (l : list stack_log_entry) s  mem :=
  match l with
  | nil => (* check s against memory *)
    stack_mem_checker s mem
  | (pc,addr,op,instr)::xs => 
    match op with
    | Push => stack_step_checker xs (addr::s) mem
    | Pop =>
      match s with
      | nil => whenFail ("Attemting to pop from empty stack at address"
                          ++ (show pc))%string false
      | a::s' => if (N.eqb a addr)
                then stack_step_checker xs s' mem
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
  end.


Definition stack_log_checker (log : (log_type stack_log_entry))
           (res : CompCert.Events.trace*MachineState.t*nat) : Checker :=
  let '(_,st,steps) := res in
  let mem := MachineState.getMemory st in
  let (l1,l2) := log in
  collect
    (stack_stats log steps)
    match steps with
    | O => whenFail "Impossible, no instructions executed!" (checker false)
    | _ =>
      match l1 with
      | nil => checker tt
      | _ =>
        if DEBUG
        then
          (stack_step_checker l1 nil mem)
        else
          let ostack :=
              List.fold_left
                (fun acc '(pc,addr,op,instr) =>
                   match acc with
                   | None => None
                   | Some s =>
                     match op with
                     | Push => Some (addr::s)
                     | Pop =>
                       match s with 
                       | nil => None
                       | a::s' =>
                         if (N.eqb a addr)
                         then Some s'
                         else None
                       end             
                     end
                   end
                ) l1 (Some nil) in
                   match ostack with
          | None => whenFail
                     ( "Address didn't match: log=" ++ (show l1) )
                     (checker false)
          | Some stack =>           
              (* the last address may have not yet been written in memory *)
              (* I record the log entry at Jal *)
              (* the memory is updated at push_sfi *)
              match stack with
              | nil
              | _::nil => checker true
              | _::xs =>
                let sl := List.rev (List.seq 0%nat (List.length xs)) in
                conjoin
                  (List.map
                     (fun '(addr,p) =>
                        let stack_address := SFI.address_of
                                               SFI.MONITOR_COMPONENT_ID
                                               (2*(N.of_nat p)+1)%N
                                               0%N
                        in
                        match RiscMachine.Memory.get_word mem stack_address with
                        | Some (RiscMachine.Data v) =>
                          if (N.eqb addr (Z.to_N v))
                          then checker true
                          else
                            whenFail ("Address from leftoverstack doesn't match ="
                                        ++ (show_addr addr) ++ "stack address:"
                                        ++ (show_addr stack_address)
                                     )%string
                                     (checker false)
                        | _ => whenFail ("Not valid data ar address: "
                                           ++ (show_addr stack_address)
                                        )%string
                                        (checker false)
                        end
                     )
                     (List.combine xs sl)
                  )
              end
          end
      end
    end.

Definition stack_log_checker_error
           (log : log_type stack_log_entry) err :=
  match err with
  | DataMemoryException _ _ _
  | UninitializedMemory _ _ =>
    whenFail "DataMemoryException or UninitializedMemory error"
             (checker false)
  | _ =>
    whenFail
      ("TargetExecutionError:" ++ (show err))
      (* TODO add trace *)
      (stack_log_checker log ((nil,get_state err),0%nat))
  end.

Definition stack_correct (fuel : nat) :=
  sfi_check_correct TestSpecific CStack update_stack_log
                stack_log_checker_error stack_log_checker fuel.
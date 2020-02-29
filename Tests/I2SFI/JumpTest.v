(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNat.
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
Import QcDefaultNotation QcNotation.
Open Scope qc_scope.
Open Scope string_scope.
Import GenLow GenHigh.

Inductive jump_type :=
| Indirect : RiscMachine.Register.t -> jump_type
| Direct : jump_type.
Definition jump_log_entry := (RiscMachine.pc * RiscMachine.address
                              * jump_type * CompCert.Events.trace)%type.


Instance show_jump_type : Show jump_type :=
  {|
    show :=
      fun t =>
        match t with
        | Indirect r => "Jmp " ++ (show r)
        | Direct => "Jal"
        end
  |}.

Definition show_jump_log_entry (entry : jump_log_entry) : string :=
  let '(pc,addr,type,t) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " type: "
          ++ ( match type with
               | Indirect r => "Jmp " ++ (show r)
               | Direct => "Jal"
               end)
          ++ " trace: " ++ (show t).


Definition update_jump_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t)
           log :=
  let '(mem,pc,regs) := st in
  let '(j_log,addr_log) := log in
  let nlog :=
      (if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ pc::nil)%list
      else addr_log)
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
      if (N.eqb r RiscMachine.Register.R_RA) || (N.eqb r RiscMachine.Register.R_T)
      then
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr =>
          ( (j_log ++ (pc, RiscMachine.Memory.to_address ptr,Indirect r,t)::nil)%list,
           nlog)
        | _ => (j_log,nlog)
        end
      else (j_log,nlog)
    | RiscMachine.ISA.IJal addr => ((j_log ++ (pc,addr,Direct,t)::nil)%list,nlog)
    | _ => (j_log,nlog)
    end
  | _ => (j_log,nlog)
  end.

(* 1. number of instr exec,
   2. number of internal jumps,
   3. number of cross component jumps
   5. number of static instructions executed
*)
Definition jump_stat := (nat * nat * nat * nat)%type.

(* dynamic instr, static instr,
   # of internal jump instr executed,
   # of cross-component jumps,
 *)
Instance show_jump_stat : Show jump_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e, si) := ss in
        (show  steps)
           ++ "," ++ (show si)
           ++ "," ++ (show i )
           ++ "," ++ (show e)
  |}.

Definition jump_stats
           (log : (log_type jump_log_entry))
           (steps : nat) : jump_stat :=
  let '(l1,l2) := log in
  let i := (List.length
              (List.filter
                 (fun '(pc,addr,type,t) =>
                    (SFI.is_same_component_bool pc addr)
                    || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                    || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                 ) l1
              )
           ) in
  let e := (List.length
              (List.filter
                 (fun  '(pc,addr,type,t) =>
                    negb (
                        (SFI.is_same_component_bool pc addr)
                        || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                        || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                      )
                 ) l1
              )
           ) in
  ((steps,i), e, List.length l2).

Definition entry_checker (entry : jump_log_entry) : Checker :=
  let '(pc,addr,type,t) := entry in
  if (SFI.is_same_component_bool pc addr)
  then
    match t with
    | nil =>  whenFail (  "Register R_T expected in internal jumps "
                          ++ (show_jump_log_entry (pc,addr,type,t)))
                      (match type with
                       | Indirect r => RiscMachine.Register.eqb
                                        RiscMachine.Register.R_T r
                       | Direct => true
                       end)
    | _ => whenFail (  "Unexpectected event at log entry:"
                        ++ (show_jump_log_entry (pc,addr,type,t)))
                   false
    end
  else
    match t with
    | _::_ =>  whenFail ( (show_addr pc)
                          ++ ": Register R_A expected in internal jumps "
                          ++ (show type))
                       (match type with
                        | Indirect r => RiscMachine.Register.eqb
                                         RiscMachine.Register.R_RA r
                        | Direct => true
                        end)
    | nill => whenFail ("Unexpectected empty event at log entry:"
                         ++ (show_jump_log_entry (pc,addr,type,t)))
                      false
    end.

Fixpoint entries_checker (l : list jump_log_entry) : Checker :=
  match l with
  | nil => checker true
  | (pc,addr,type,t)::nil =>
    if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
    then checker true
    else entry_checker (pc,addr,type,t)
  | e::xs => conjoin ((entry_checker e)::(entries_checker xs)::nil)
  end.

Definition jump_log_checker
           (log :(log_type jump_log_entry))
           (res : CompCert.Events.trace*MachineState.t*nat) : Checker :=
  let (_,steps) := res in
  let (l1,l2) := log in
  collect
    (jump_stats log steps)
    match l1 with
    | nil => checker tt
    | (pc,addr,type,t)::xsl1 =>
      if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
      then
        entries_checker xsl1
      else
        whenFail "jump_checker:"
                 (checker false)
    end.

Definition jump_log_checker_error
           (log : log_type jump_log_entry) err :=
  match err with
  | DataMemoryException _ _ _
  | UninitializedMemory _ _ =>
    whenFail "jump_correct:Datamemoryexception or Uninitializedmemory"
             (checker false)
  | _ =>
    whenFail
      ("TargetExecutionError:" ++ (show err))
      (* TODO get the trace here *)
      (jump_log_checker log ((nil,get_state err),0%nat))
  end.

Definition jump_correct (fuel : nat) :=
  sfi_check_correct NoUndef CJump update_jump_log jump_log_checker_error jump_log_checker fuel.

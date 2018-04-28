(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.Bool.Bool.
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

Definition store_log_entry := (RiscMachine.pc * RiscMachine.address * RiscMachine.value)%type.

Definition show_log_entry (entry : store_log_entry) : string :=
  let '(pc,addr,sfi_sp) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " sfi sp: " ++ (show sfi_sp).

Definition update_store_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t)
           (log : (log_type store_log_entry)) :=
  let '(mem,pc,regs) := st in
  let '(st_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ pc::nil)%list
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IStore rptr rs =>
      match RiscMachine.RegisterFile.get_register rptr regs with
      | Some ptr =>
        let addr := RiscMachine.Memory.to_address ptr in
        match RiscMachine.RegisterFile.get_register
                RiscMachine.Register.R_SFI_SP regs with
        | Some sp => ((st_log ++ (pc,addr,sp)::nil)%list,nlog)
        | _ => (st_log,nlog)
        end
      | _ => (st_log,nlog)
      end
    | _ => (st_log,nlog)
    end
  | _ => (st_log,nlog)
  end.

(* 1. number of instr exec, 
   2. number of internal writes, 
   3. number of push sfi, 
   5. number of static instructions executed
*)
Definition store_stat := (nat * nat * nat * nat)%type.

(* dynamic instr, static instr, #of internal store instr executed, # of push sfi *)
Instance show_store_stat : Show store_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e,  si) := ss in
        (show  steps) (* dynamic instructions *)
          ++ "," ++ (show si) (* static instructions *)
           ++ "," ++ (show i ) (* internal stores *)
           ++ "," ++ (show e) (* push SFI *)
  |}.

Definition store_stats (log : log_type store_log_entry)
           (steps : nat) : store_stat :=
  let '(l1,l2) := log in
  let i := (List.length (List.filter (fun '(pc,addr,sfi_sp) =>
                                        (SFI.is_same_component_bool pc addr)
                                     ) l1
                        )
           ) in
  ( steps, i, ((List.length l1) - i)%nat, List.length l2).

Definition store_log_checker (log : log_type store_log_entry)
           (res : CompCert.Events.trace*MachineState.t*nat) : Checker :=
  let (_,steps) := res in
  let (l1,l2) := log in
  collect (store_stats log steps)
    match l1 with
    | nil => checker tt
    | _ =>
      conjoin (List.map (fun '(pc,addr,sfi_sp) =>
                           if (SFI.is_same_component_bool pc addr)
                           then checker true
                           else
                             if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                             then
                               whenFail ("Failed at: "
                                           ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                        (N.eqb addr (SFI.address_of
                                                       SFI.MONITOR_COMPONENT_ID
                                                       (Z.to_N (2 * sfi_sp +1))
                                                       0))
                             else
                               whenFail ("Failed at: "
                                           ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                        false
                        ) l1)
    end.

Definition store_log_checker_error
           (log : log_type store_log_entry) err :=
  match err with
  | CodeMemoryException _ _ _ =>
    whenFail "store_correct:CodeMemoryException"
             (checker false)
  | _ => 
    whenFail
      ("TargetExecutionError:"++(show err))
      (store_log_checker log ((nil,get_state err),0%nat))
  end.

(*! Section prop_store_correct *) (*! extends fault_store_test *)
Definition store_correct (fuel : nat) :=
  sfi_check_correct TestSpecific
                CStore
                update_store_log
                store_log_checker_error
                store_log_checker fuel.

Extract Constant Test.defNumTests => "10".
(*! QuickChick (store_correct 100%nat). *)

(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import Common.Definitions.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.

Require Import Intermediate.Machine.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

(* Definition in_memory (start : RiscMachine.address) *)
(*            (code : list RiscMachine.ISA.instr) *)
(*            (mem : RiscMachine.Memory.t) : Prop := *)
(*   fst (List.fold_left *)
(*          (fun '(p,index) i => *)
(*             match RiscMachine.Memory.get_instr mem (start + (N.of_nat index))%N with *)
(*             | Some i' => (p /\ (i = i'),index+1) *)
(*             | None => (False,index+1) *)
(*             end) *)
(*          code (True,0)). *)

(* Definition sfi_registers_correct (regs : RiscMachine.RegisterFile.t) : Prop := True. (* TODO *) *)

(* Definition address_in_same_component (st : MachineState.t) (r : RiscMachine.Register.t) : Prop := *)
(*   let regs := MachineState.getRegs st in *)
(*   let pc := MachineState.getPC st in *)
(*   match RiscMachine.RegisterFile.get_register r regs with *)
(*   | None => False *)
(*   | Some v => SFI.is_same_component pc (RiscMachine.Memory.to_address v) *)
(*   end. *)

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
 * No writes outside it's own memory
 *************************************************)

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

Definition store_log := list (RiscMachine.pc * RiscMachine.address * RiscMachine.value).

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
        | Some sp => log ++ [(pc,addr,sp)]
        | _ => log
        end
      | _ => log
      end
    | _ => log
    end
  | _ => log
  end.
            

Definition eval_store_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t) * store_log) :=
  ((CS.eval_program_with_state     
     store_log
     update_store_log
     (100%nat)
     p
     (RiscMachine.RegisterFile.reset_all)) nil).
  
Definition store_checker (log : store_log) : Checker := 
  checker (
       true (* TODO implement this *)
    ). 

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
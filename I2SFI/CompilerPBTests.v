(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import I2SFI.Compiler.
Require Import I2SFI.CompMonad.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.


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
    (t : trace) 
    (ptr sfi_sp_val: RiscMachine.value ),

    Right (sfi_program) sfi_p = compile_program ip /\
    Some (t, (mem,pc,gen_regs)) = (CS.eval_program n sfi_p RiscMachine.RegisterFile.reset_all) /\
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

    

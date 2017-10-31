(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.


Definition in_memory (start : RiscMachine.address)
           (code : list RiscMachine.ISA.instr)
           (mem : RiscMachine.Memory.t) : Prop :=
  fst (List.fold_left
         (fun '(p,index) i =>
            match RiscMachine.Memory.get_instr mem (start + (N.of_nat index))%N with
            | Some i' => (p /\ (i = i'),index+1)
            | None => (False,index+1)
            end)
         code (True,0)).

Definition sfi_registers_correct (regs : RiscMachine.RegisterFile.t) : Prop := True. (* TODO *)

Definition address_in_same_component (st : MachineState.t) (r : RiscMachine.Register.t) : Prop :=
  let regs := MachineState.getRegs st in
  let pc := MachineState.getPC st in
  match RiscMachine.RegisterFile.get_register r regs with
  | None => False
  | Some v => SFI.is_same_component pc (RiscMachine.Memory.to_address v)
  end.


(* for all adresses in the current component the 
   address transformation is identity and the 
   memory access is performed at the same address *)
(* Conjecture correct_execute_IStore_id_same_component:  *)
(*   forall (regs : RiscMachine.RegisterFile.t) *)
(*     (mem : RiscMachine.Memory.t) (addr : RiscMachine.address) *)
(*     (rp rs : Intermediate.Machine.register) (g : Env.t) *)
(*     (st st' : MachineState.t) (t : trace), *)
    
(*     let instrs :=  (compile_IStore rp rs) in *)

(*     sfi_registers_correct regs /\ *)
(*     in_memory addr instrs /\ *)
(*     (t,st') = CS.eval_steps (List.length instrs) g st /\ *)
(*     (* rp address in current component *) *)
(*     address_in_same_component st rp *)
(*     -> *)
(*     ( t = E0 /\ *)
(*       RiscMachine.RegisterFile.get_register rp (MachineState.getRegs st) = *)
(*            RiscMachine.RegisterFile.get_register RiscMachine.Register.R_D (MachineState.getRegs st') /\ *)
(*       RiscMachine.RegisterFile.get_register rp (MachineState.getRegs st) = *)
(*            RiscMachine.RegisterFile.get_register rp (MachineState.getRegs st')). *)
      
              
    
    (* the sfi masking registers have proper values 
       regs[RiscMachine.Register.R_AND_CODE_MASK] = ....
       .....
     *)
    (* with the 3 instruction somewhere in memory
       there exists address addr, ...
       st. ...
     *)
    (* if regs[rp] is an address in current component 
       
       eval compile_Istore ??? regs'[rd]=regs'[rp]=regs[rp]
     *)
    
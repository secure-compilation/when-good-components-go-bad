Require Import TargetSFI.Machine.

Module CS.

  Import SFI.

  (* Global Env: (C,CN,E) *)
  Definition global_env : Set := C * CN * E.

  Definition sp : Set := nat.

  Definition pc : Set := address.

(* Machine State:

  (mem, sp, pc, reg) where 
  - mem is a total function from addresses to words
  - reg is a total function from general registers to words
  - pc is the program counter register
  - sp is the control stack register

 *)
  Definition state : Set := Memory * sp * pc * RegisterFile.t.

  (* Let P₁=(CN,E,mem,ψ) be a complete compartmentalized program.
  Let S₁=(mem,reg,pc) be a complete state. 
  The predicate initial(P₁,S₁) is true iff 
  1. mem is the same map 
  2. registers are all set to 0 (including sp)
  3. pc is set to 0
  *)(*
  Definition initial_state (progr : program) (st :state) : Prop :=
    let '(mem,sp_reg,pc_reg,gen_regs) := st in
    progr.mem = mem /\
    sp_reg = 0 /\
    pc_reg = 0 /\
    RegisterFile.is_zero gen_regs.
*)
End CS.
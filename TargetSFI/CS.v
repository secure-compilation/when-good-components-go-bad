Require Import CompCert.Events.

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
  *)
  Definition initial_state (progr : program) (st : state) : Prop :=
    let '(mem,sp_reg,pc_reg,gen_regs) := st in
    (SFI.mem progr) = mem /\
    sp_reg = 0 /\
    pc_reg = 0 /\
    RegisterFile.is_zero gen_regs.

  Definition final_state (st : state) (r : value) : Prop :=
    let '(mem,sp_reg,pc_reg,gen_regs) := st in
    executing mem pc_reg IHalt.

  Inductive step (G : global_env) : state -> trace -> state -> Prop :=
  | Nop : forall mem sp_reg pc_reg gen_regs,
      executing mem pc_reg INop ->
      step G (mem,sp_reg,pc_reg,gen_regs) E0 (mem,sp_reg,pc_reg+1,gen_regs)
  | Const : forall mem sp_reg pc_reg gen_regs gen_regs' val reg,
      executing mem pc_reg (IConst val reg) ->
      RegisterFile.set_register reg val gen_regs = gen_regs' ->
      step G (mem,sp_reg,pc_reg,gen_regs) E0 (mem,sp_reg,pc_reg+1,gen_regs)
           
  (* mem[pc] = i *)
  (* decode i = Mov r₁ → r₂ *)
  (* reg' = reg[r₂ ↦ reg[r₁]] *)
  (* —————————————————————————————————————————————————— CS_Mov *)
  (*                              ε *)
  (* (C,CN,E) ⊢CS (mem,sp,pc,reg) → (mem,sp,pc+1,reg') *)

  | Mov : forall mem sp_reg pc_reg gen_regs gen_regs' reg_src reg_dst,
      executing mem pc_reg (IMov reg_src reg_dst) ->
      let val := RegisterFile.get_register reg_src gen_regs in
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      step G (mem,sp_reg,pc_reg,gen_regs) E0 (mem,sp_reg,pc_reg+1,gen_regs)
  .
      
(* (* register operations *) *)
(* | IMov : register -> register -> instr *)
(* | IBinOp : binop -> register -> register -> register -> instr *)
(* (* memory operations *) *)
(* | ILoad : register -> register -> instr *)
(* | IStore : register -> register -> instr *)
(* (* conditional and unconditional jumps *) *)
(* | IBnz : register -> immediate -> instr *)
(* | IJump : register -> instr *)
(* | IJal : address -> instr *)
(* (* termination *) *)
(* | IHalt : instr. *)
    
End CS.
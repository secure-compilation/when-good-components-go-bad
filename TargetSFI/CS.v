Require Import ZArith.
Require Import List.

Require Import CompCert.Events.

Require Import Lib.Monads.

Require Import TargetSFI.Machine.

Module CS.

  Import SFI.
  Import SFI.Memory.
  
  (* Global Env: (C,CN,E) *)
  Definition global_env : Set := C * CN * E.

(* Machine State:

  (mem, sp, pc, reg) where 
  - mem is a total function from addresses to words
  - reg is a total function from general registers to words
  - pc is the program counter register
  - sp is the control stack register

  I will keep sp in the general registers (reg) for ease of 
  the implementation. The extraction in code is easy, but harder 
  to explain in the file.

 *)
  Definition state : Type :=  Memory.t * RegisterFile.pc * RegisterFile.general_registers.

  (* Let P₁=(CN,E,mem,ψ) be a complete compartmentalized program.
  Let S₁=(mem,reg,pc) be a complete state. 
  The predicate initial(P₁,S₁) is true iff 
  1. mem is the same map 
  2. registers are all set to 0 (including sp)
  3. pc is set to 0
  *)
  Definition initial_state (progr : program) (st : state) : Prop :=
    let '(mem,pc,gen_regs) := st in
    (SFI.mem progr) = mem /\
    pc = Z.to_N 0 /\
    RegisterFile.is_zero gen_regs.

  Definition final_state (st : state) (r : value) : Prop :=
    let '(mem,pc,gen_regs) := st in
    executing mem pc IHalt.

  Open Scope N_scope.
  
  Inductive step (G : global_env) : state -> trace -> state -> Prop :=
  | Nop : forall mem pc gen_regs,
      executing mem pc INop ->
      step G (mem,pc,gen_regs) E0 (mem,pc + 1,gen_regs)
           
  | Const : forall mem pc gen_regs gen_regs' val reg,
      executing mem pc (IConst val reg) ->
      RegisterFile.set_register reg val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs)
           
  (* mem[pc] = i *)
  (* decode i = Mov r₁ → r₂ *)
  (* reg' = reg[r₂ ↦ reg[r₁]] *)
  (* —————————————————————————————————————————————————— CS_Mov *)
  (*                              ε *)
  (* (C,CN,E) ⊢CS (mem,sp,pc,reg) → (mem,sp,pc+1,reg') *)

  | Mov : forall mem pc gen_regs gen_regs' reg_src reg_dst,
      executing mem pc (IMov reg_src reg_dst) ->
      let val := RegisterFile.get_register reg_src gen_regs in
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs')

  (* mem[pc] = i *)
  (* decode i = BinOp r₁ ⊗ r₂ → r₃ *)
  (* reg' = reg[r₃ ↦ reg[r₁] ⊗ reg[r₂]] *)
  (* —————————————————————————————————————————————————— CS_BinOp *)
  (*                              ε *)
  (* (C,CN,E) ⊢CS (mem,sp,pc,reg) → (mem,sp,pc+1,reg') *)
  | BinOp : forall mem pc gen_regs gen_regs' op reg_src1 reg_src2 reg_dst,
      (* This is a bit more permisive than the written semantics *)
      executing mem pc (IBinOp op reg_src1 reg_src2 reg_dst) ->
      IS_NOT_SFI_REGISTER reg_dst ->
      let val1 := RegisterFile.get_register reg_src1 gen_regs in
      let val2 := RegisterFile.get_register reg_src2 gen_regs in
      let result := executing_binop op val1 val2 in
      RegisterFile.set_register reg_dst result gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs')
           
  | BinOpToSp : forall mem pc gen_regs gen_regs' op reg_src1 reg_src2 reg_dst,
      (* This is a bit more permisive than the written semantics *)
      executing mem pc (IBinOp op reg_src1 reg_src2 reg_dst) ->
      IS_SFI_SP_REGISTER reg_dst ->
      let val1 := RegisterFile.get_register reg_src1 gen_regs in
      let val2 := RegisterFile.get_register reg_src2 gen_regs in
      let result := executing_binop op val1 val2 in
      RegisterFile.set_register reg_dst result gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs')
  (* (* memory operations *) *)
  (* | ILoad : register -> register -> instr *)           
  (* mem[pc] = i *)
  (* decode i = Load *r₁ → r₂ *)
  (* reg[r₁] = p *)
  (* reg' = reg[r₂ ↦ mem[p]] *)
  (* —————————————————————————————————————————————————— CS_Load *)
  (*                              ε *)
  (* (C,CN,E) ⊢CS (mem,sp,pc,reg) → (mem,sp,pc+1,reg') *)
  | Load : forall mem pc gen_regs gen_regs' reg_src reg_dst,
      executing mem pc (ILoad reg_src reg_dst) ->
      let ptr := Memory.to_address (RegisterFile.get_register reg_src gen_regs) in
      let val := Memory.get_value mem ptr in
      Memory.is_same_component ptr pc ->
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs')
  | LoadExtern : forall mem pc gen_regs gen_regs' reg_src reg_dst,
      executing mem pc (ILoad reg_src reg_dst) ->
      let ptr := Memory.to_address (RegisterFile.get_register reg_src gen_regs) in
      let val := Memory.get_value mem ptr in
      ~Memory.is_same_component ptr pc ->
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      let cn := snd G in
      let cpc := cn pc in
      let cptr := cn ptr in
      (* TODO Fix this when the rest changes from nat to Z *)
      let t := (ELoad cpc (Z.to_nat val) cptr)::nil in
      step G (mem,pc,gen_regs) t (mem,pc+1,gen_regs')           
  (* | IStore : register -> register -> instr *)
  (* mem[pc] = i *)
  (* decode i = Store *r₁ ← r₂ *)
  (* reg[r₁] = p *)
  (* reg[r₂] = w *)
  (* mem' = mem[p ↦ w] *)
  (* —————————————————————————————————————————————————— CS_Store *)
  (*                              ε *)
  (* (C,CN,E) ⊢CS (mem,sp,pc,reg) → (mem',sp,pc+1,reg) *)

  | Store: forall mem mem' pc gen_regs reg_dst reg_src,
      executing mem pc (IStore reg_src reg_dst) ->
      let ptr := RegisterFile.get_register reg_dst gen_regs in
      let val := RegisterFile.get_register reg_src gen_regs in
      Memory.set_value mem (Memory.to_address ptr) val = mem' ->
      step G (mem,pc,gen_regs) E0 (mem',pc+1,gen_regs)
  (* (* conditional and unconditional jumps *) *)
  (* | IBnz : register -> immediate -> instr *)
  | BnzNZ: forall mem pc gen_regs reg offset,
      executing mem pc (IBnz reg offset) ->
      let val := RegisterFile.get_register reg gen_regs in
      val <> ZERO_VALUE ->
      let pc' := Z.to_N( Z.add (Z.of_N pc) offset ) in
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs)
  | IBnzZ: forall mem pc gen_regs reg offset,
      executing mem pc (IBnz reg offset) ->
      let val := RegisterFile.get_register reg gen_regs in
      val = ZERO_VALUE ->
      step G (mem,pc,gen_regs) E0 (mem,pc+1,gen_regs)
  (* | IJump : register -> instr *)
  | Return: forall mem pc gen_regs reg,
      executing mem pc (IJump reg) ->
      let pc' := Memory.to_address (RegisterFile.get_register reg gen_regs) in
      ~Memory.is_same_component pc pc'->
      let cn := snd (fst G) in
      let cpc := cn pc in
      let cpc' := cn pc' in
      (* TODO Fix this when the rest changes from nat to Z *)
      let rcomval :=  Z.to_nat (RegisterFile.get_register R_COM gen_regs) in 
      let t := (ERet cpc rcomval cpc')::nil in
      step G (mem,pc,gen_regs) t (mem,pc',gen_regs)
  | Jump: forall mem pc gen_regs reg,
      executing mem pc (IJump reg) ->
      let pc' := Memory.to_address (RegisterFile.get_register reg gen_regs) in
      Memory.is_same_component pc pc'->
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs)
  (* | IJal : address -> instr *)
  | Jal: forall mem pc gen_regs gen_regs' addr,
      executing mem pc (IJal addr) ->
      RegisterFile.set_register R_RA (Z.of_N (pc+1)) gen_regs = gen_regs'->
      let pc' := addr in
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs')
  | Call: forall mem pc gen_regs gen_regs' addr,
      executing mem pc (IJal addr) ->
      RegisterFile.set_register R_RA (Z.of_N (pc+1)) gen_regs = gen_regs'->
      let pc' := addr in
      ~Memory.is_same_component pc pc'->
      let cn := snd G in
      let cpc := cn pc in
      let cpc' := cn pc' in
      let p := (snd G) pc' in
      (* TODO Fix this when the rest changes from nat to Z *)
      let rcomval := Z.to_nat (RegisterFile.get_register R_COM gen_regs) in 
      let t := (ECall cpc p rcomval cpc')::nil in
      step G (mem,pc,gen_regs) t (mem,pc',gen_regs').   
  Close Scope N_scope.


  (* Import MonadNotations. *)
  (* Open Scope monad_scope. *)
  (* Open Scope N_scope. *)

  (* Definition eval_step (G: global_env) (s: state) : option (trace * state) := *)
  (*   let '(mem,pc,gen_regs) := s in *)
  (*   match Memory.get_word mem pc with *)
  (*   | Some (Instruction instr) => *)
  (*     match instr with *)
  (*     | INop => ret (E0, (mem,gen_regs,pc+1)) *)
  (*     | IConst val reg => *)
  (*       let gen_regs' :=  RegisterFile.set_register reg val gen_regs in *)
  (*       ret (E0, (mem,gen_regs',pc+1)) *)
  (*     | IMov reg_src reg_dst => *)
  (*       let val := RegisterFile.get_register reg_src gen_regs in *)
  (*       let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in *)
  (*       ret (E0, (mem,gen_regs',pc+1)) *)
  (*     | IBinOp op reg_src1 reg_src2 reg_dst => *)
  (*       if orb (is_not_sfi_reg_bool reg_dst) (is_sfi_sp_register_bool reg_dst) *)
  (*       then *)
  (*         let val1 := RegisterFile.get_register reg_src1 gen_regs in *)
  (*         let val2 := RegisterFile.get_register reg_src2 gen_regs in *)
  (*         let result := executing_binop op val1 val2 in *)
  (*         let gen_regs' := RegisterFile.set_register reg_dst result gen_regs in *)
  (*         ret (E0, (mem,gen_regs',pc+1)) *)
  (*       else *)
  (*         None *)
  (*     | ILoad reg_src reg_dst => *)
  (*       let ptr := Memory.to_address (RegisterFile.get_register reg_src gen_regs) in *)
  (*       let val := Memory.get_value mem ptr in *)
  (*       let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in *)
  (*       let t := if (Memory.is_same_component_bool ptr pc) then E0 *)
  (*                else let cn := snd G in *)
  (*                     let cpc := cn pc in *)
  (*                     let cptr := cn ptr in *)
  (*                     (* TODO Fix this when the rest changes from nat to Z *) *)
  (*                     (ELoad cpc (Z.to_nat val) cptr)::nil in *)
  (*       ret (t, (mem,gen_regs',pc+1)) *)
  (*     | IStore reg_src reg_dst => *)
  (*       let ptr := RegisterFile.get_register reg_dst gen_regs in *)
  (*       let val := RegisterFile.get_register reg_src gen_regs in *)
  (*       let mem' := Memory.set_value mem (Memory.to_address ptr) val in *)
  (*       ret (E0, (mem',gen_regs,pc+1)) *)
  (*     | IBnz reg offset => *)
  (*       let val := RegisterFile.get_register reg gen_regs in *)
  (*       let pc' := if Z.eqb val 0 then pc + 1 *)
  (*                  else  Z.to_N( Z.add (Z.of_N pc) offset ) in *)
  (*       ret (E0, (mem,gen_regs,pc')) *)
  (*     | IJump reg => *)
  (*       let pc' := Memory.to_address (RegisterFile.get_register reg gen_regs) in *)
  (*       let t := if Memory.is_same_component_bool pc pc' then E0 *)
  (*                else *)
  (*                  let cn := snd (fst G) in *)
  (*                  let cpc := cn pc in *)
  (*                  let cpc' := cn pc' in *)
  (*                  (* TODO Fix this when the rest changes from nat to Z *) *)
  (*                  let rcomval :=  Z.to_nat (RegisterFile.get_register R_COM gen_regs) in  *)
  (*                  (ERet cpc rcomval cpc')::nil in *)
  (*       ret (t, (mem,gen_regs,pc')) *)
  (*     | IJal addr => *)
  (*       let gen_regs' := RegisterFile.set_register R_RA (Z.of_N (pc+1)) gen_regs in *)
  (*       let pc' := addr in *)
  (*       let t := if Memory.is_same_component_bool pc pc' then E0 *)
  (*                else *)
  (*                  let cn := snd G in *)
  (*                  let cpc := cn pc in *)
  (*                  let cpc' := cn pc' in *)
  (*                  let p := (snd G) pc' in *)
  (*                  (* TODO Fix this when the rest changes from nat to Z *) *)
  (*                  let rcomval := Z.to_nat (RegisterFile.get_register R_COM gen_regs) in  *)
  (*                  (ECall cpc p rcomval cpc')::nil in *)
  (*       ret (t, (mem,gen_regs',pc')) *)
  (*     | IHalt => None *)
  (*     end *)
  (*   | Some (Data val) => None *)
  (*   | None => None *)
  (*   end. *)
  (* Close Scope N_scope. *)
  (* Close Scope monad_scope. *)

End CS.
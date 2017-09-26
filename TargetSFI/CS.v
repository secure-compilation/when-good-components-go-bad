Require Import ZArith.
Require Import List.

(* From QuickChick Require Import QuickChick Tactics. *)
(* Import QcDefaultNotation. Open Scope qc_scope. *)

(* Require Import Coq.Classes.EquivDec. *)

Require Import CompCert.Events.
Require Import Lib.Monads.
Require Import Common.Definitions.
Require Import TargetSFI.Machine.

Module CS.

  Import SFI.
  Import SFI.Memory.
  
  (* Global Env: (CN,E) *)
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
  (* POSTPONED *)         
  (* | LoadExtern : forall mem pc gen_regs gen_regs' reg_src reg_dst, *)
  (*     executing mem pc (ILoad reg_src reg_dst) -> *)
  (*     let ptr := Memory.to_address (RegisterFile.get_register reg_src gen_regs) in *)
  (*     let val := Memory.get_value mem ptr in *)
  (*     ~Memory.is_same_component ptr pc -> *)
  (*     RegisterFile.set_register reg_dst val gen_regs = gen_regs' -> *)
  (*     let '(_,cn,_) := G in *)
  (*     let cpc := cn pc in *)
  (*     let cptr := cn ptr in *)
  (*     let t := (ELoad cpc (Z.to_nat val) cptr)::nil in *)
  (*     step G (mem,pc,gen_regs) t (mem,pc+1,gen_regs')            *)

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
      let cn := snd (fst G) in
      let cpc := cn pc in
      let cpc' := cn pc' in
      let rcomval :=  RegisterFile.get_register R_COM gen_regs in
      let t:trace := [ERet cpc rcomval cpc'] in
      ~Memory.is_same_component pc pc'->
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
  | Call: forall mem pc gen_regs
                 (gen_regs': RegisterFile.general_registers)
                 (addr:address),
      executing mem pc (IJal addr) ->
      RegisterFile.set_register R_RA (Z.of_N (pc+1)) gen_regs = gen_regs'->
      let pc' := addr in
      let cn := snd (fst G) in
      let cpc := cn pc in
      let cpc' := cn pc' in
      let e := snd G in
      let p := e pc' in
      let rcomval := RegisterFile.get_register R_COM gen_regs in
      let t := [ECall cpc p rcomval cpc'] in
       ~Memory.is_same_component pc pc'->
      step G (mem,pc,gen_regs) t (mem,pc',gen_regs').   
  Close Scope N_scope.


  Import MonadNotations.
  Open Scope monad_scope.
  Open Scope N_scope.

   Definition eval_step (G: global_env) (s: state) : option (trace * state) :=
    let '(mem,pc,gen_regs) := s in
    match Memory.get_word mem pc with
    | Some (Instruction instr) =>
      match instr with
      | INop => ret (E0, (mem,pc+1,gen_regs))
      | IConst val reg =>
        let gen_regs' :=  RegisterFile.set_register reg val gen_regs in
        ret (E0, (mem,pc+1,gen_regs'))
      | IMov reg_src reg_dst =>
        let val: value := RegisterFile.get_register reg_src gen_regs in
        let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in
        ret (E0, (mem,pc+1,gen_regs'))
      | IBinOp op reg_src1 reg_src2 reg_dst =>
        if orb (is_not_sfi_reg_bool reg_dst) (is_sfi_sp_register_bool reg_dst)
        then
          let val1 := RegisterFile.get_register reg_src1 gen_regs in
          let val2 := RegisterFile.get_register reg_src2 gen_regs in
          let result := executing_binop op val1 val2 in
          let gen_regs' := RegisterFile.set_register reg_dst result gen_regs in
          ret (E0, (mem,pc+1,gen_regs'))
        else
          None
      | ILoad reg_src reg_dst =>
        let ptr: address
            := Memory.to_address (RegisterFile.get_register reg_src gen_regs) in
        let val: value := Memory.get_value mem ptr in
        let gen_regs': RegisterFile.general_registers
            := RegisterFile.set_register reg_dst val gen_regs in
        let c_sfi_ptr: SFIComponent.id := C_SFI ptr in
        let c_sfi_pc: SFIComponent.id := C_SFI pc in
        let same_comp: bool := c_sfi_pc =? c_sfi_ptr in
        let t := E0 in 
        (* POSTPONED *)
        (* let t: trace := if same_comp then E0 *)
        (*          else let '(_,cn,_) := G in *)
        (*               let cpc: Component.id := cn pc in *)
        (*               let cptr: Component.id := cn ptr in *)
        (*               [ELoad cpc val     cptr] in *)
        ret (t, (mem,pc+1,gen_regs'))
      | IStore reg_src reg_dst =>
        let ptr_val: value := RegisterFile.get_register reg_dst gen_regs in 
        let ptr: address := Memory.to_address ptr_val in
        let val: value := RegisterFile.get_register reg_src gen_regs in
        let mem': Memory.t := Memory.set_value mem ptr val in
        ret (E0, (mem',pc+1,gen_regs))
      | IBnz reg offset =>
        let val := RegisterFile.get_register reg gen_regs in
        let is_zero: bool := Z.eqb val Z0 in
        let pc': address :=  if is_zero then pc + 1
                   else  Z.to_N( Z.add (Z.of_N pc) offset ) in
        ret (E0, (mem,pc',gen_regs))
      | IJump reg =>
        let pc' := Memory.to_address (RegisterFile.get_register reg gen_regs) in
        let t := if Memory.is_same_component_bool pc pc' then E0
                 else
                   let '(_,cn,_) := G in
                   let cpc := cn pc in
                   let cpc' := cn pc' in
                   let rcomval :=  RegisterFile.get_register R_COM gen_regs in
                   (ERet cpc rcomval cpc')::nil in
        ret (t, (mem,pc',gen_regs))
      | IJal addr =>
        let gen_regs': RegisterFile.general_registers
            := RegisterFile.set_register R_RA (Z.of_N (pc+1)) gen_regs in
        let pc': address := addr in
        let t: trace := if Memory.is_same_component_bool pc pc' then E0
                 else
                   let '(_,cn,e) := G in
                   let cpc : Component.id := cn pc in
                   let cpc' : Component.id := cn pc' in
                   let p : Procedure.id := e pc' in
                   let rcomval := RegisterFile.get_register R_COM gen_regs in
                   [ECall cpc p rcomval cpc'] in
        ret (t, (mem,pc',gen_regs'))
      | IHalt => None
      end
    | Some (Data val) => None
    | None => None
    end.

   (* NOT NEEDED NOW *)
   (* Import MonadNotations. *)
   (* Open Scope monad_scope. *)
   (* Set Typeclasses Debug. *)

   (* Check C_SFI. *)
   
   (* (* Global Env: (C,CN,E) *) *)
   (* (* State : Memory.t * RegisterFile.pc * RegisterFile.general_registers. *) *)
   (*  (*  Record program := *) *)
   (*  (* { *) *)
   (*  (*   cn : CN; *) *)
   (*  (*   e : E; *) *)
   (*  (*   mem : Memory.t; *) *)
   (*  (*   prog_interface : Program.interface *) *)
   (* (* }. *) *)
   (* Definition init_genv_and_state (p : SFI.program) : global_env * state := *)
   (*   let gcn : CN := (SFI.cn p) in *)
   (*   let ge : E := (SFI.e p) in *)
   (*   let G := (C_SFI, gcn, ge) in *)
   (*   let smem : SFI.Memory.t := (SFI.mem p) in *)
   (*   let st0 : state := (smem, N0, SFI.RegisterFile.zero) in *)
   (*   (G, st0). *)


   (* Fixpoint execN (n: nat) (G: global_env) (st: state) : option value := *)
   (*   match n with *)
   (*   | O => None *)
   (*   | S n' => *)
   (*     match eval_step G st with *)
   (*     | None => *)
   (*       let '(_, _, regs) := st in *)
   (*       Some (RegisterFile.get_register R_COM regs) *)
   (*     | Some (_, st') => execN n' G st' *)
   (*     end *)
   (*   end. *)

   (* Definition run (p: SFI.program) (fuel: nat) : option value := *)
   (*   let (G, st) := (init_genv_and_state p) in *)
   (*    (* TODO do something about the input *) *)
   (*     execN fuel G st. *)
  
  Close Scope N_scope.


  (* Conjecture eval_step_complete : forall G st t st', *)
  (*     step G st t st' -> eval_step G st = Some (t, st'). *)

  (* Instance dec_eval_step_complete (G : global_env) (st : state) *)
  (*          (t : trace) (st' : state) : Dec (eval_step_complete G st t st'). *)
  (* Proof. Amitted. *)

  Close Scope monad_scope.
End CS.
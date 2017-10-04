Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Logic.

Require Import CompCert.Events.
Require Import Common.Definitions.
Require Import TargetSFI.Machine.

Require Import TargetSFI.MachineGen.
Require Import QuickChick.Decidability.

Require Export Lib.Monads.
Export MonadNotations.
Open Scope monad_scope.

Module CS.

  Import RiscMachine.
  Import RiscMachine.ISA.
  Import RiscMachine.Memory.
  Import SFI.
  Import Env.
  Import MachineState.

  (* Set Printing Implicit. *)
  (* Set Typeclasses Debug. *)

  Import MonadNotations.
  Open Scope monad_scope.
  
  Definition ret_trace (G : Env.t) (pc pc' : RiscMachine.pc)
             (gen_regs : RiscMachine.RegisterFile.t) : option trace :=
    do rcomval <-  RegisterFile.get_register Register.R_COM gen_regs;
    do cpc <-  Env.get_component_name_from_id (SFI.C_SFI pc) G;
    do cpc' <- Env.get_component_name_from_id (SFI.C_SFI pc') G;
    Some [ERet cpc rcomval cpc'].

  Definition call_trace (G : Env.t) (pc pc' : RiscMachine.pc)
             (gen_regs : RiscMachine.RegisterFile.t) : option trace :=
    do rcomval <- RegisterFile.get_register  Register.R_COM gen_regs;
    do cpc <-  Env.get_component_name_from_id (SFI.C_SFI pc) G;
    do cpc' <- Env.get_component_name_from_id (SFI.C_SFI pc') G;
    do p <- Env.get_procedure pc' G;
    Some [ECall cpc p rcomval cpc'].
  
  Inductive step (G : Env.t) :
    MachineState.t -> trace-> MachineState.t -> Prop :=
  | Nop : forall mem pc gen_regs,
      executing mem pc INop ->
      step G (mem,pc,gen_regs) E0 (mem, inc_pc pc,gen_regs)
           
  | Const : forall mem pc gen_regs gen_regs' val reg,
      executing mem pc (IConst val reg) ->
      RegisterFile.set_register reg val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem, inc_pc pc,gen_regs)

  | Mov : forall mem pc gen_regs gen_regs' reg_src reg_dst val,
      executing mem pc (IMov reg_src reg_dst) ->
      Some val = RegisterFile.get_register reg_src gen_regs ->
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem, inc_pc pc,gen_regs')

  | BinOp : forall mem pc gen_regs gen_regs' op reg_src1 reg_src2 reg_dst val1 val2,
      executing mem pc (IBinOp op reg_src1 reg_src2 reg_dst) ->
      Some val1 = RegisterFile.get_register reg_src1 gen_regs ->
      Some val2 = RegisterFile.get_register reg_src2 gen_regs ->
      let result := executing_binop op val1 val2 in
      RegisterFile.set_register reg_dst result gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,inc_pc pc,gen_regs')

  | Load : forall mem pc gen_regs gen_regs' reg_src reg_dst addr val,
      executing mem pc (ILoad reg_src reg_dst) ->
      Some addr = RegisterFile.get_register reg_src gen_regs ->
      let ptr := Memory.to_address (addr) in
      Some val = Memory.get_value mem ptr ->
      RegisterFile.set_register reg_dst val gen_regs = gen_regs' ->
      step G (mem,pc,gen_regs) E0 (mem,inc_pc pc,gen_regs')
           
  | Store: forall mem mem' pc gen_regs reg_dst reg_src ptr val,
      executing mem pc (IStore reg_src reg_dst) ->
      Some ptr = RegisterFile.get_register reg_dst gen_regs ->
      Some val = RegisterFile.get_register reg_src gen_regs ->
      Memory.set_value mem (Memory.to_address ptr) val = mem' ->
      step G (mem,pc,gen_regs) E0 (mem',inc_pc pc,gen_regs)

  | BnzNZ: forall mem pc gen_regs reg offset val,
      executing mem pc (IBnz reg offset) ->
      Some val = RegisterFile.get_register reg gen_regs ->
      val <> Z0 ->
      let pc' := Z.to_N( Z.add (Z.of_N pc) offset ) in
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs)
           
  | IBnzZ: forall mem pc gen_regs reg offset val,
      executing mem pc (IBnz reg offset) ->
      Some val = RegisterFile.get_register reg gen_regs ->
      val = Z0 ->
      step G (mem,pc,gen_regs) E0 (mem,inc_pc pc,gen_regs)
           
  | Return: forall mem pc gen_regs reg t addr,
      executing mem pc (IJump reg) ->
      Some addr = RegisterFile.get_register reg gen_regs ->
      let pc' := Memory.to_address addr in
      Some t = ret_trace G pc pc' gen_regs ->
      ~SFI.is_same_component pc pc'->
      step G (mem,pc,gen_regs) t (mem,pc',gen_regs)

  | Jump: forall mem pc gen_regs reg addr,
      executing mem pc (IJump reg) ->
      Some addr = RegisterFile.get_register reg gen_regs ->
      let pc' := Memory.to_address addr in
      SFI.is_same_component pc pc'->
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs)
           
  | Jal: forall mem pc gen_regs gen_regs' addr,      
      executing mem pc (IJal addr) ->
      let ra := Z.of_N (inc_pc pc) in
      RegisterFile.set_register Register.R_RA ra gen_regs = gen_regs'->
      let pc' := addr in
      step G (mem,pc,gen_regs) E0 (mem,pc',gen_regs')
           
  | Call: forall mem pc gen_regs gen_regs' addr t,
      executing mem pc (IJal addr) ->
      let ra := Z.of_N (inc_pc pc) in
      RegisterFile.set_register Register.R_RA ra gen_regs = gen_regs'->
      let pc' := addr in
      Some t = call_trace G pc pc' gen_regs ->
      ~SFI.is_same_component pc pc'->
      step G (mem,pc,gen_regs) t (mem,pc',gen_regs').


  Definition eval_step (G : Env.t) (s : MachineState.t)
    : option (trace * MachineState.t) :=
    
    let '(mem,pc,gen_regs) := s in
    match Memory.get_word mem pc with
    | Some (Instruction instr) =>
      match instr with
      | INop => Some (E0, (mem,inc_pc pc,gen_regs))
      | IConst val reg =>
        let gen_regs' :=  RegisterFile.set_register reg val gen_regs in
        Some (E0, (mem,inc_pc pc,gen_regs'))
      | IMov reg_src reg_dst =>
        do val <- RegisterFile.get_register reg_src gen_regs;
        let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in
        Some (E0, (mem,inc_pc pc,gen_regs'))
      | ISA.IBinOp op reg_src1 reg_src2 reg_dst =>
        do val1 <- RegisterFile.get_register reg_src1 gen_regs;
        do val2 <- RegisterFile.get_register reg_src2 gen_regs;
        let result : value := RiscMachine.executing_binop op val1 val2 in
        let gen_regs':= RegisterFile.set_register reg_dst result gen_regs in
        Some (E0, (mem,inc_pc pc,gen_regs'))
      | ILoad reg_src reg_dst =>
        do addr <- RegisterFile.get_register reg_src gen_regs;
        let ptr := Memory.to_address addr in
        do val <- Memory.get_value mem ptr;
        let gen_regs' := RegisterFile.set_register reg_dst val gen_regs in
        Some (E0, (mem,inc_pc pc,gen_regs'))
      | IStore reg_src reg_dst =>
        do ptr_val <- RegisterFile.get_register reg_dst gen_regs;
        let ptr := Memory.to_address ptr_val in
        do val <- RegisterFile.get_register reg_src gen_regs;
        let mem': Memory.t := Memory.set_value mem ptr val  in
        Some (E0, (mem',inc_pc pc,gen_regs))
      | IBnz reg offset =>
        do val <- RegisterFile.get_register reg gen_regs;
        let pc': address :=  if Z.eqb val Z0 then inc_pc pc
                             else N.add pc (Z.to_N offset) in
        Some (E0, (mem,pc',gen_regs))
      | IJump reg =>
        do addr <- RegisterFile.get_register reg gen_regs;
        let pc' := Memory.to_address addr in
        if SFI.is_same_component_bool pc pc' then
          Some (E0, (mem,pc',gen_regs))
        else
          let ot := ret_trace G pc pc' gen_regs in
          match ot with
          | None => None
          | Some t => ret (t, (mem,pc',gen_regs))
          end
      | IJal addr =>
        let ra := Z.of_N (pc+1) in
        let gen_regs' := RegisterFile.set_register Register.R_RA ra gen_regs in
        let pc' := addr in
        if SFI.is_same_component_bool pc pc' then Some (E0, (mem,pc',gen_regs'))
        else
          let ot := call_trace G pc pc' gen_regs in
          match ot with
          | None => None
          | Some t => Some (t, (mem,pc',gen_regs'))
          end
      | IHalt => None
      end
    | Some (Data val) => None
    | None => None
    end.

  Conjecture eval_step_complete :
    forall (G : Env.t)  (st : MachineState.t) (t : trace) (st' : MachineState.t),
      (step G st t st') -> (eval_step G st = Some (t, st')).

  Conjecture eval_step_sound:
    forall (G : Env.t)  (st : MachineState.t) (t : trace) (st' : MachineState.t),
      eval_step G st = Some (t, st') -> step G st t st'.
  
  Close Scope monad_scope.


  (* Unused code for now *)
(* Let P₁=(CN,E,mem,ψ) be a complete compartmentalized program.
  Let S₁=(mem,reg,pc) be a complete state. 
  The predicate initial(P₁,S₁) is true iff 
  1. mem is the same map 
  2. registers are all set to 0 (including sp)
  3. pc is set to 0
 *)
  (* Definition initial_state (progr : program) (st : state) : Prop := *)
  (*   let '(mem,pc,gen_regs) := st in *)
  (*   (SFI.mem progr) = mem /\ *)
  (*   pc = Z.to_N 0 /\ *)
  (*   RegisterFile.is_zero gen_regs. *)

  (* Definition final_state (st : state) (r : value) : Prop := *)
  (*   let '(mem,pc,gen_regs) := st in *)
  (*   executing mem pc IHalt. *)

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
  

  
End CS.
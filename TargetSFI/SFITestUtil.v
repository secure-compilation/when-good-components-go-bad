Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import CompCert.Events.

Require Import Common.Definitions.

Require Import TargetSFI.Machine.
Require Import TargetSFI.EitherMonad.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Open Scope char_scope.

Definition hexDigitToNat (c : ascii) : option N :=
  match c with
    | "0" => Some 0%N
    | "1" => Some 1%N
    | "2" => Some 2%N
    | "3" => Some 3%N
    | "4" => Some 4%N
    | "5" => Some 5%N
    | "6" => Some 6%N
    | "7" => Some 7%N
    | "8" => Some 8%N
    | "9" => Some 9%N
    | "a" | "A" => Some 10%N
    | "b" | "B" => Some 11%N
    | "c" | "C" => Some 12%N
    | "d" | "D" => Some 13%N
    | "e" | "E" => Some 14%N
    | "f" | "F" => Some 15%N
    | _ => None
  end.

Open Scope string_scope.

Definition hex2N (s : string) : N :=
  let fix aux (s : string) (acc : N) : option N :=
  match s with
    | "" => Some acc
    | String c s' =>
      match hexDigitToNat c with
        | Some n => aux s' (16 * acc + n)%N
        | None => None
      end
  end in
  match aux s 0%N with
  | None => 0%N
  | Some n => n
  end.
  
Definition show_pos (p : positive) := show_nat (Pos.to_nat p).

Definition show_value (v : RiscMachine.value) := show_int v.

Definition show_N ( n : N ) := show_nat (N.to_nat n).

Instance show_Component_id : Show Component.id :=
  {|
    show := show_pos
  |}.

Instance show_sfi_id : Show SFIComponent.id :=
  {|
    show := show_N
  |}.

Instance show_CN : Show Env.CN := showList.

Definition show_addr (addr : RiscMachine.address) :=
  let '(c,s,o) := SFI.convert_address addr in
  "(c=" ++ (show_N c) ++ ", s=" ++ (show s)
        ++ ", o=" ++ (show o) ++ ")".

Instance show_addr_i : Show  RiscMachine.address :=
  {|
    show := show_addr
  |}.

Instance show_Addr_Proc : Show (RiscMachine.address * Procedure.id) := showPair.

Instance show_E : Show Env.E := showList.

Instance show_env : Show Env.t :=
  {
    show := fun (G : Env.t) =>
              let (cn,e) := G in 
              (show cn) ++ (show e)
  }.

Instance show_event : Show event :=
  {|
    show := fun (e : event) =>
              match e with
              | ECall c1 pid arg c2 => "[ECall " ++ (show c1) ++ " "
                                                 ++ (show pid) ++ " "
                                                 ++ (show_int arg) ++ " "
                                                 ++ (show c2) ++ "]"
              |  ERet c1 arg c2 => "[ERet " ++ (show c1) ++ " "
                                                 ++ (show_int arg) ++ " "
                                                 ++ (show c2) ++ "]"
              end
  |}.



Definition show_op_f (op : RiscMachine.ISA.binop) :=
  match op with 
  | RiscMachine.ISA.Addition => "+"
  | RiscMachine.ISA.Subtraction => "-"
  | RiscMachine.ISA.Multiplication => "*"
  | RiscMachine.ISA.Equality => "="
  | RiscMachine.ISA.Leq => "<="
  | RiscMachine.ISA.BitwiseOr => "|"
  | RiscMachine.ISA.BitwiseAnd => "&"
  | RiscMachine.ISA.ShiftLeft => "<<"
  end.

Instance show_op : Show RiscMachine.ISA.binop :=
  {|
    show := show_op_f
  |}.

Instance show_reg : Show RiscMachine.Register.t :=
  {|
    show :=
      fun r =>
        if (N.eqb r RiscMachine.Register.R_ONE)
        then "R_ONE"
        else
          if (N.eqb r RiscMachine.Register.R_COM) then "R_COM"
          else
            if (N.eqb r RiscMachine.Register.R_AUX1) then "R_AUX1"
            else
              if (N.eqb r RiscMachine.Register.R_AND_CODE_MASK) then "R_AND_CODE_MASK"
              else
                if (N.eqb r RiscMachine.Register.R_AND_DATA_MASK) then "R_AND_DATA_MASK"
                else
                  if (N.eqb r RiscMachine.Register.R_OR_CODE_MASK) then "R_OR_CODE_MASK"
                  else
                    if (N.eqb r RiscMachine.Register.R_OR_DATA_MASK) then "R_OR_DATA_MASK"
                    else
                      if (N.eqb r RiscMachine.Register.R_AUX2) then "R_AUX2"
                      else
                        if (N.eqb r RiscMachine.Register.R_RA) then "RA"
                        else
                          if (N.eqb r RiscMachine.Register.R_SP) then "SP"
                          else
                            if (N.eqb r RiscMachine.Register.R_SFI_SP) then "SFI_SP"
                            else
                              if (N.eqb r RiscMachine.Register.R_T) then "R_T"
                              else
                                if (N.eqb r RiscMachine.Register.R_D) then "R_D"
                                else (show_N r)
  |}.

Instance show_instr : Show RiscMachine.ISA.instr :=
  {|
    show := fun i =>
              match i with
              | RiscMachine.ISA.INop => "Nop"                         
              (* register operations *)
              | RiscMachine.ISA.IConst v r =>
                ("Const " ++ (show v) ++ " " ++ (show r))%string
              | RiscMachine.ISA.IMov r1 r2  =>
                ("Mov " ++ (show r1) ++ " " ++ (show r2))%string
              | RiscMachine.ISA.IBinOp op r1 r2 r3 =>
                ("BinOP " ++ (show op) ++ " "
                          ++ (show r1) ++ " "
                          ++ (show r2) ++ " "
                          ++ (show r3))%string
              (* memory operations *)
              | RiscMachine.ISA.ILoad r1 r2 =>
                ("Load " ++ (show r1) ++ " " ++ (show r2))%string
              | RiscMachine.ISA.IStore r1 r2 =>
                ("Store " ++ (show r1) ++ " " ++ (show r2))%string
              (* conditional and unconditional jumps *)
              | RiscMachine.ISA.IBnz r imm =>
                ("BnZ " ++ (show r) ++ " " ++ (show imm))%string
              | RiscMachine.ISA.IJump r =>
                ("Jump " ++ (show r))%string
              | RiscMachine.ISA.IJal addr=>
                ("Jal " ++ (show_addr addr))%string
              (* termination *)
              | RiscMachine.ISA.IHalt => "Halt"
              end
  |}.

Definition newline := String "010" ""%string.


Instance show_trace : Show CompCert.Events.trace := showList.

Definition show_mem (mem : RiscMachine.Memory.t) : string :=
  List.fold_left (fun acc '(a,val) =>
                    match val with
                    | RiscMachine.Data v => acc++((show_addr a) ++ ":" ++ (show_value v) ++ newline)%string
                    | RiscMachine.Instruction i => acc++((show_addr a) ++ ":" ++ (show i) ++ newline)%string
                    end
                 ) (BinNatMap.elements mem) ""%string.
     

Instance show_mem_i : Show RiscMachine.Memory.t :=
  {|
    show := show_mem
  |}.


Instance show_state : Show MachineState.t :=
  {|
    show := fun (st : MachineState.t) =>
              let '(mem,pc,gen_regs) := st in
              "PC: " ++ (show_addr pc) ++ newline
                     ++ "registers: " ++ (show gen_regs) ++ newline
                     ++ "memory: " ++ newline ++ (show mem) 
  |}.

Instance show_exec_error : Show ExecutionError :=
  {|
    show :=
      fun err =>
        match err with
        | RegisterNotFound st reg => (show reg)
        | NoInfo => EmptyString
        | UninitializedMemory st addr =>
          "PC=" ++ (show_addr (MachineState.getPC st))               
                ++ " address=" ++ (show_addr addr) ++ newline
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        | CodeMemoryException st addr i =>
          "PC=" ++ (show_addr (MachineState.getPC st))
                ++ " address in data memory=" ++ (show_addr addr)
                ++ " contains instruction "
                ++ (show i)
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        | DataMemoryException st addr val  =>
          "PC=" ++ (show_addr (MachineState.getPC st))
                ++ " address in code memory=" ++ (show_addr addr)
                ++ " contains value "
                ++ (show_value val)
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        | MissingComponentId st cid cn =>
          "PC=" ++ (show_addr (MachineState.getPC st))
                ++ " cid=" ++ (show cid)
                ++ " CN=" ++ (show cn)
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        | CallEventError st cid cid' cn e =>
          "PC=" ++ (show_addr (MachineState.getPC st))
                ++ " cid=" ++ (show cid)
                ++ " cid'=" ++ (show cid')
                ++ " CN=" ++ (show cn)
                ++ " E=" ++ (show e)
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        | RetEventError st cid cid' cn =>
          "PC=" ++ (show_addr (MachineState.getPC st))
                ++ " cid=" ++ (show cid)
                ++ " cid'=" ++ (show cid')
                ++ " CN=" ++ (show cn)
                ++ " memory:" ++ newline
                ++ (show_mem (MachineState.getMemory st))
                ++ " registers:" ++ newline
                ++ (show (MachineState.getRegs st))
        end                 
  |}.

Close Scope string_scope.

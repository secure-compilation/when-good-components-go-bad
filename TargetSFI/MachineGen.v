(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.omega.Omega.
Require Coq.Bool.Bool.
Require Import Coq.Lists.List. Import ListNotations.
Require Import List ZArith.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Coq.Strings.String.
Local Open Scope string.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.

Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import TargetSFI.EitherMonad.

Require Import CompCert.Events.

Import Env.
Import SFIComponent.
Import RiscMachine.
Import CS.

Module DoNotation.
Import ssrfun.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.

(*******************************
 * Env.CN Generator
 *******************************)

Theorem decComponentId: forall x y : Component.id, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Theorem decRegisterFile: forall regs1 regs2 : RiscMachine.RegisterFile.t,
    {regs1 = regs2} + {regs1 <> regs2}.
Proof.
  apply List.list_eq_dec. apply Z.eq_dec.
Defined.
      
Definition cut_list (l : list Component.id) : list Component.id :=
  let fix gen_seq len :=
      match len with
      | O => [ 1%nat ]
      | S len' => List.app (gen_seq len') [ (len+1) ]
      end
  in
  let len:nat := (N.to_nat SFI.COMP_MAX) in
  let l' : (list Component.id) := (List.nodup decComponentId l) in 
  if (  Nat.leb len (List.length l') )
  then (List.firstn len l') 
  else (gen_seq len).

Instance genCN : Gen Env.CN :=
  {
    arbitrary :=
      let len := N.to_nat SFI.COMP_MAX in
      let double := len * 2 in
      liftGen cut_list (vectorOf double arbitrary )
  }.


(*******************************
 * Addresses Generator
 *******************************)
Definition genSFIComponentId : G SFIComponent.id :=
  do! n <- choose (O,N.to_nat SFI.COMP_MAX);
  returnGen (N.of_nat n).

Definition even_gen : G N :=
  do! x <- arbitrary;
    returnGen ((2*(N.of_nat x))%N). 

Definition odd_gen : G N :=
  do! x <- arbitrary;
    returnGen ((2*(N.of_nat x)+1)%N). 

Definition odd_even_frecv_gen (even_freq : nat) (odd_freq : nat) : G N :=
  freq [
      (even_freq, even_gen);
        (odd_freq, odd_gen)
    ].

Definition genBlockIds (frecv_code : nat) (frecv_data : nat) : G (list N) :=
  let how_many : nat := plus frecv_code frecv_data in
  vectorOf how_many (odd_even_frecv_gen frecv_code frecv_data).

Definition genOffset : G N :=
  liftGen N.of_nat (choose (O,N.to_nat (SFI.SLOT_SIZE - 1))).

Definition genBlockOffsetPairs (frecv_code : nat) (frecv_data : nat) : G (list (N*N)) :=
  let how_many : nat := plus frecv_code frecv_data in
  do! blockIds <- genBlockIds frecv_code frecv_data;
    do! offsets <- vectorOf how_many genOffset;
    returnGen (List.combine blockIds offsets). 

Definition genAbstractAddresses (frecv_code : nat) (frecv_data : nat) :
  G (list (SFIComponent.id*(N*N))) :=
  let how_many := plus frecv_code frecv_data in
  (* generator of pairs of lists cid * block id * offset *)
  do! cids <- vectorOf how_many genSFIComponentId;
    do! bl_off <- genBlockOffsetPairs frecv_code frecv_data;
    returnGen (List.combine cids bl_off).

Definition genAddresses (frecv_code : nat) (frecv_data : nat) :
  G (list RiscMachine.address) :=
  do! addresses <- genAbstractAddresses frecv_code frecv_data;
  returnGen
    (
      List.map (fun '(cid,(bid,off)) => SFI.address_of cid bid off)
               addresses
    ).

(* frecv_code = number of addresses in code slots
   frecv_data = number of addresses in data slots
   cid = the component id of all addresses generated *)
Definition genAddressesForCid (frecv_code : nat) (frecv_data : nat) cid :
  G (list RiscMachine.address) :=
  let how_many : nat := plus frecv_code frecv_data in
  (* generate a 1ist of how_many addresses with generated block id and offset and given cid *)
  do! bl_off <- genBlockOffsetPairs frecv_code frecv_data;
  returnGen
    (List.map
       (fun '(bid,off) => SFI.address_of cid bid off)
       bl_off
    ).
   

(*******************************
 * Env.E Generator
 *******************************)
Definition genEForCid cid : G Env.E :=
  do! addresses <- genAddressesForCid 10 0 cid;
    do! pids <- vectorOf 10 (choose (1,100));
    returnGen (List.combine addresses pids).

Instance genE : Gen Env.E :=
  {
    arbitrary := 
      let cids := List.map N.of_nat (List.seq 0 (N.to_nat SFI.COMP_MAX)) in
      foldGen (fun (acc : Env.E) cid =>
                 do! addrs <- genAddressesForCid 10 0 cid;
                   do! pids <- vectorOf 10 (choose (1,100));
                   returnGen (acc ++ (List.combine addrs pids))%list
              ) cids nil 
  }.

(*******************************
 * Env Generator
 *******************************)

Definition genEnv : G Env.t := liftGen2 pair arbitrary arbitrary.

Instance genEnvInst : Gen Env.t :=
  {
    arbitrary := genEnv
  }.

(*******************************
 * MachineState Generator
 *******************************)
Import RiscMachine.ISA.

Instance genReg : Gen RiscMachine.Register.t :=
  {
    arbitrary := elems [ RiscMachine.Register.R_ONE
                         ; RiscMachine.Register.R_COM
                         ; RiscMachine.Register.R_AUX1
                         ; RiscMachine.Register.R_AUX2
                         ; RiscMachine.Register.R_RA
                         ; RiscMachine.Register.R_SP
                         ; RiscMachine.Register.R_SFI_SP
                         ; RiscMachine.Register.R_AND_CODE_MASK
                         ; RiscMachine.Register.R_AND_DATA_MASK
                         ; RiscMachine.Register.R_OR_CODE_MASK
                         ; RiscMachine.Register.R_OR_DATA_MASK
                         ; RiscMachine.Register.R_T
                         ; RiscMachine.Register.R_D ]
  }.

Instance genValue : Gen RiscMachine.value :=
  {
    arbitrary := arbitrary
  }.

Instance genImmediate : Gen RiscMachine.immediate :=
  {
    arbitrary := arbitrary
  }.

Instance genOp : Gen RiscMachine.ISA.binop :=
  {
    arbitrary := elems [ Addition
                         ; Subtraction
                         ; Multiplication
                         ; Equality
                         ; Leq
                         ; BitwiseOr
                         ; BitwiseAnd
                         ; ShiftLeft
                       ]
  }.

Definition genIConst : G instr :=
  do! val <- arbitrary;
    do! reg <- arbitrary;
    returnGen (IConst val reg).

Definition gen2Reg (it :  RiscMachine.Register.t -> RiscMachine.Register.t -> instr) : G instr :=
  do! r1 <- arbitrary;
    do! r2 <- arbitrary;
    returnGen (it r1 r2).

Definition genIBinOp : G instr :=
  do! op <- arbitrary;
    do! r1 <- arbitrary;
    do! r2 <- arbitrary;
    do! r3 <- arbitrary;
    returnGen (IBinOp op r1 r2 r3).

Definition genIBnz : G instr :=
  do! reg <- arbitrary;
    do! imm <- arbitrary;
    returnGen (IBnz reg imm).

Definition genIJump : G instr :=
  do! reg <- arbitrary;
  returnGen (IJump reg).

Definition genIJal (addresses : list RiscMachine.address) : G instr :=
  elements INop (List.map
                   (fun addr => IJal addr)
                   addresses
                ).

Definition genInstr (addresses : list RiscMachine.address) : G instr :=
  oneOf [ (returnGen INop)
          ; genIConst
          ; gen2Reg IMov
          ; genIBinOp
          ; gen2Reg ILoad
          ; gen2Reg IStore
          ; genIBnz
          ; genIJump
          ; genIJal addresses
          ; (returnGen IHalt)
        ].
                         
Definition genMemForAddresses (g : Env.t)
           (addresses : list RiscMachine.address) : G RiscMachine.Memory.t :=
  let env_addresses := List.map fst (snd g) in (* add env addresses to the memory *)
  do! res <- sequenceGen
       (List.map
          ( fun addr =>
              if ( SFI.is_code_address addr )
              then
                do! i <- genInstr addresses;
                  returnGen (addr, RiscMachine.Instruction i)
              else
                do! v <- arbitrary;
                returnGen (addr, RiscMachine.Data v)
          ) (env_addresses++addresses));
    returnGen
      (RiscMachine.Memory.of_list res)
.


Definition genMem (g : Env.t) : G RiscMachine.Memory.t :=
  let frecv_code := 50%nat in
  let frecv_data := 50%nat in
  let how_many : nat := (frecv_code + frecv_data)%nat in
  do! addresses <- genAddresses frecv_code frecv_data;
    genMemForAddresses g addresses.


Definition genPCFromMem (mem : RiscMachine.Memory.t) : G RiscMachine.pc :=
  (* pc is a random code address *)
  elements N0 (RiscMachine.Memory.filter_used_addresses mem SFI.is_code_address).


Definition genRegsAddress (mem : RiscMachine.Memory.t)
           (rptr : RiscMachine.Register.t) (code : bool) : G RiscMachine.RegisterFile.t :=
  do! l1 <- vectorOf ((N.to_nat rptr) - 1)%nat arbitrary;
    do! l2 <- vectorOf (RiscMachine.Register.NO_REGISTERS - (N.to_nat rptr))%nat arbitrary;
  do! addr <- 
  (if code
  then
    elements Z0 (List.map
                   Z.of_N
                   (RiscMachine.Memory.filter_used_addresses mem SFI.is_code_address))
  else
    elements Z0 (List.map
                   Z.of_N 

                   (RiscMachine.Memory.filter_used_addresses mem SFI.is_data_address)));

    returnGen
      (
        l1 ++ [addr] ++ l2
      )%list.

Definition genRegsFromMemPC (mem : RiscMachine.Memory.t) (pc : RiscMachine.pc)
  : G RiscMachine.RegisterFile.t :=
  (* the register values are random with some care for the cases when I need valid addresses *)
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction (ILoad rptr rs)) => genRegsAddress mem rptr false
  | Some (RiscMachine.Instruction (IStore rptr rd)) => genRegsAddress mem rptr false
  | Some (RiscMachine.Instruction (IJump rt)) => genRegsAddress mem rt true
  | _ => vectorOf RiscMachine.Register.NO_REGISTERS arbitrary
  end.


Definition genStateForEnv (g : Env.t) : G MachineState.t :=
  (*  (RiscMachine.Memory.t * RiscMachine.pc) * RiscMachine.RegisterFile.t. *)
  do! mem <- genMem g;
    do! pc <- genPCFromMem mem;
    do! regs <- genRegsFromMemPC mem pc;
    returnGen (mem,pc,regs).
  

Definition genTrace (g : Env.t) (st : MachineState.t): G trace :=
  let mem :=  MachineState.getMemory st in
  let pc := MachineState.getPC st in
  let regs := MachineState.getRegs st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction (IJump rt)) => (* possible ret event *)
    match RegisterFile.get_register rt regs with
    | Some addr =>
      let pc' := Memory.to_address addr in
      if (SFI.is_same_component_bool pc pc') 
      then returnGen E0
      else
        match (ret_trace g pc pc' regs) with
        | Some t => returnGen t
        | _ => returnGen E0 (* TODO this is actually error *)
        end
    | None => (* TODO this is actually error *) returnGen E0
    end
  | Some (RiscMachine.Instruction (IJal imm)) => (* possible call event *)
      if (SFI.is_same_component_bool pc imm)
      then returnGen E0
      else
        match (call_trace g pc imm regs) with
        | Some t => returnGen t
        | _ => returnGen E0 (* TODO this is actually error *)
        end
  | _ => returnGen E0
  end.


Definition update_mem (mem : Memory.t) (instr : ISA.instr) (regs : RegisterFile.t) : Memory.t :=
  match instr with
  | IStore reg_src reg_dst =>
    match RegisterFile.get_register reg_src regs with
    | Some addr => let ptr :=  Memory.to_address addr in
      match  RegisterFile.get_register reg_src regs with
      | Some val => Memory.set_value mem ptr val
      | _ => mem (* TODO this is actually error *)
      end
    | _ => mem  (* TODO this is actually error *)
    end
  | _ => mem
  end.

Definition update_pc (mem : Memory.t) (instr : ISA.instr) (pc : RiscMachine.pc)
           (regs : RegisterFile.t) : RiscMachine.pc :=
  match instr with
  | IJump rt =>
    match RegisterFile.get_register rt regs with
    | Some addr => Memory.to_address addr 
    | _ => pc  (* TODO this is actually error *)
    end
  | IJal imm => imm
  | IBnz reg offset =>
    match RegisterFile.get_register reg regs with
    | Some flag =>
      if (Z.eqb flag Z0) then pc
      else Memory.to_address ((Z.of_N pc) + offset)%Z
    | _ => pc
    end
  | _ => pc
  end.


Definition update_regs (mem : Memory.t) (instr : ISA.instr)  (pc : RiscMachine.pc)
           (regs : RegisterFile.t) : RegisterFile.t :=
  match instr with
  | IConst val reg =>  RegisterFile.set_register reg val regs
  | ILoad rptr rd =>
    match RegisterFile.get_register rptr regs with
    | Some addr =>
      let ptr :=  Memory.to_address addr in
      match Memory.get_value mem ptr with
      | Some val => RegisterFile.set_register rd val regs
      | _ => regs
      end
    | _ => regs  (* TODO this is actually error *)
    end
  | IMov rs rd =>
    match (RegisterFile.get_register rs regs) with
    | Some v => RegisterFile.set_register rd v regs
    | _ => regs
    end
  | IBinOp op r1 r2 rd =>
    match (RegisterFile.get_register r1 regs,
           RegisterFile.get_register r2 regs) with
    | (Some v1, Some v2) => RegisterFile.set_register
                             rd (RiscMachine.eval_binop op v1 v2) regs
    | _ => regs
    end
  | IJal imm => RegisterFile.set_register RiscMachine.Register.R_RA ((Z.of_N pc)+1)%Z regs
  | _ => regs
  end.


Definition genNextState (g : Env.t) (st : MachineState.t) (t : trace) : G MachineState.t :=
  let mem :=  MachineState.getMemory st in
  let pc := MachineState.getPC st in
  let regs := MachineState.getRegs st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (Instruction instr) =>
    returnGen ( (update_mem mem instr regs,
                 update_pc mem instr pc regs), update_regs mem instr pc regs)
  | _ => returnGen ( (mem,pc), regs)  (* TODO this is actually error *)
  end.
           
  
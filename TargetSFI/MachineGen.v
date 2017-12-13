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

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

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
(* TODO Use UPenn MetaLibrary *)

(*******************************
 * Env.CN Generator
 *******************************)

Theorem decComponentId: forall x y : Component.id, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Theorem decRegisterFile: forall regs1 regs2 : RiscMachine.RegisterFile.t,
    {regs1 = regs2} + {regs1 <> regs2}.
Proof.
  apply List.list_eq_dec. apply Z.eq_dec.
  (* induction regs1. *)
  (* - destruct regs2. *)
  (*   + auto. *)
  (*   + right. intro H. inversion H. *)
  (* - destruct regs2. *)
  (*   + right. intro H. inversion H. *)
  (*   + destruct (Z.eqb a v) eqn:Hh. *)
  (*     * rewrite Z.eqb_eq in Hh. rewrite Hh. *)
  (*       destruct IHregs1 with (regs2:=regs2). *)
  (*       left. apply f_equal. apply e. *)
  (*       right. intro H. apply n. inversion H. reflexivity. *)
  (*     * right. intro H. inversion H. rewrite <- Z.eqb_eq in H1. *)
  (*       rewrite Hh in H1. inversion H1. *)
Defined.
      
Definition cut_list (l : list Component.id) : list Component.id :=
  let fix gen_seq len :=
      match len with
      | O => [ (Pos.of_nat 1) ]
      | S len' => List.app (gen_seq len') [ Pos.of_nat (len+1) ]
      end
  in
  let len:nat := (N.to_nat SFI.COMP_MAX) in
  let l' : (list Component.id) := (List.nodup decComponentId l) in 
  if (  Nat.leb len (List.length l') )
  then (List.firstn len l') 
  else (gen_seq len).

Open Scope nat_scope.
Instance genCN : Gen Env.CN :=
  {
    arbitrary :=
      let len := N.to_nat SFI.COMP_MAX in
      let double := len * 2 in
      liftGen cut_list (liftGen (map Pos.of_nat) (vectorOf double arbitrary ))
  }.
Close Scope nat_scope.


(*******************************
 * Addresses Generator
 *******************************)
Definition genSFIComponentId : G SFIComponent.id :=
  liftGen N.of_nat (choose (O,N.to_nat SFI.COMP_MAX)).

Open Scope N_scope.
Definition odd_even_frecv_gen (even_freq : nat) (odd_freq : nat) : G N :=
  freq [
      (even_freq, liftGen (fun x => 2*(N.of_nat x)) arbitrary);
        (odd_freq, liftGen (fun x => 2*(N.of_nat x)+1) arbitrary)
    ].
Close Scope N_scope.

Definition genBlockIds (frecv_code : nat) (frecv_data : nat) : G (list N) :=
  let how_many : nat := plus frecv_code frecv_data in
  vectorOf how_many (odd_even_frecv_gen frecv_code frecv_data).

Definition genOffset : G N :=
  liftGen N.of_nat (choose (O,N.to_nat (SFI.SLOT_SIZE - 1))).

Definition genBlockOffsetPairs (frecv_code : nat) (frecv_data : nat) : G (list (N*N)) :=
  let how_many : nat := plus frecv_code frecv_data in
  liftGen (fun '(l1,l2) => List.combine l1 l2)
          (liftGen2 pair
                    (genBlockIds frecv_code frecv_data)
                    (vectorOf how_many genOffset)).

Definition genAbstractAddresses (frecv_code : nat) (frecv_data : nat) :
  G (list (SFIComponent.id*(N*N))) :=
  let how_many := plus frecv_code frecv_data in
  (* generator of pairs of lists cid * block id * offset *)
  liftGen (fun '(l1,l2) => List.combine l1 l2)
          (liftGen2 pair
                    (vectorOf how_many genSFIComponentId)
                    (* generator of pair of lists block id * offset *)
                    (genBlockOffsetPairs frecv_code frecv_data)).

Definition genAddresses (frecv_code : nat) (frecv_data : nat) :
  G (list RiscMachine.address) :=
  liftGen
    (List.map (fun '(cid,(bid,off)) => SFI.address_of cid bid off))
    (genAbstractAddresses frecv_code frecv_data).

(* frecv_code = number of addresses in code slots
   frecv_data = number of addresses in data slots
   cid = the component id of all addresses generated *)
Definition genAddressesForCid (frecv_code : nat) (frecv_data : nat) cid :
  G (list RiscMachine.address) :=
  let how_many : nat := plus frecv_code frecv_data in
  (* generate a 1ist of how_many addresses with generated block id and offset and given cid *)
  liftGen
    (List.map (fun '(bid,off) => SFI.address_of cid bid off))
    (genBlockOffsetPairs frecv_code frecv_data).
   

(*******************************
 * Env.E Generator
 *******************************)

Open Scope nat_scope.
Definition genEForCid cid : G Env.E :=
  liftGen (fun '(l1,l2) => List.combine l1 l2)
          (liftGen2 pair
                    (genAddressesForCid 10 0 cid)
                    (* Procedure.id *)
                    (liftGen (List.map Pos.of_nat) (vectorOf 10 (choose (0,100))))).
Close Scope nat_scope.

Definition foldE (ll : list Env.E) : Env.E :=
  List.fold_left (fun l1 l2 => List.app l1 l2) ll nil.

(* Q: How can I do the recursion on N, avoiding the strange 
conversion to nat? *)
Instance genE : Gen Env.E :=
  {
    arbitrary := 
      let cids := List.map N.of_nat (List.seq 0 (N.to_nat SFI.COMP_MAX)) in
      let generators := List.map genEForCid cids in
      liftGen foldE (sequenceGen generators)
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
  liftGen2 (fun (val : RiscMachine.value)
                (reg : RiscMachine.Register.t) =>
              IConst val reg ) arbitrary arbitrary.

Definition gen2Reg (it :  RiscMachine.Register.t -> RiscMachine.Register.t -> instr) : G instr :=
  liftGen2 (fun (r1 : RiscMachine.Register.t)
                (r2 : RiscMachine.Register.t) =>
              it r1 r2 ) arbitrary arbitrary.

Definition genIBinOp : G instr :=
  liftGen4 (fun (op : RiscMachine.ISA.binop)
                (r1 : RiscMachine.Register.t)
                (r2 : RiscMachine.Register.t)
                (r3 : RiscMachine.Register.t) =>
              IBinOp op r1 r2 r3) arbitrary arbitrary arbitrary arbitrary.

Definition genIBnz : G instr :=
  liftGen2 (fun (reg : RiscMachine.Register.t)
                (imm : RiscMachine.immediate) =>
              IBnz reg imm) arbitrary arbitrary.

Definition genIJump : G instr :=
  liftGen (fun (reg : RiscMachine.Register.t) => IJump reg) arbitrary.

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
  let how_many : nat := List.length (addresses++env_addresses) in
  liftGen (fun (lst : list (RiscMachine.address*(RiscMachine.value*RiscMachine.ISA.instr))) =>
             List.fold_left
                       (fun mem '(address, (val, i)) =>
                          if ( SFI.is_code_address address)
                          then RiscMachine.Memory.set_instr mem
                                                            address
                                                            i
                          else RiscMachine.Memory.set_value mem
                                                            address
                                                            val)
                       lst
                       RiscMachine.Memory.empty
                    )
          (* list address*(val*instr) *)
          ( liftGen (fun '(l1,l2) => List.combine addresses (List.combine l1 l2))
                    (liftGen2 pair
                              (vectorOf how_many arbitrary)
                              (vectorOf how_many (genInstr addresses)))).

Open Scope nat_scope.
Definition genMem (g : Env.t) : G RiscMachine.Memory.t :=
  let frecv_code := 50 in
  let frecv_data := 50 in
  let how_many : nat := frecv_code + frecv_data in
  bindGen (genAddresses frecv_code frecv_data) (genMemForAddresses g).
Close Scope nat_scope.

Definition genPCFromMem (mem : RiscMachine.Memory.t) : G RiscMachine.pc :=
  (* pc is a random code address *)
  elements N0 (RiscMachine.Memory.filter_used_addresses mem SFI.is_code_address).

Definition genRegsAddress (mem : RiscMachine.Memory.t)
           (rptr : RiscMachine.Register.t) (code : bool) : G RiscMachine.RegisterFile.t :=
  let genVal : G RiscMachine.value := arbitrary in
  let rptr_nat := N.to_nat rptr in
  liftGen3 (fun l1 l2 l3 => l1 ++ l2 ++ l3)%list
           (vectorOf (rptr_nat - 1) genVal)
           (vectorOf 1 (if code
           then
             elements Z0 (List.map
                            Z.of_N
                            (RiscMachine.Memory.filter_used_addresses mem SFI.is_code_address))
           else
             elements Z0 (List.map
                            Z.of_N 
                            (RiscMachine.Memory.filter_used_addresses mem SFI.is_data_address))))
           (vectorOf (RiscMachine.Register.NO_REGISTERS - rptr_nat) genVal). 

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
  let memGen := (genMem g) in
  let pcGen := 
      bindGen memGen (fun mem => genPCFromMem mem) in
  let regsGen := 
      bindGen (liftGen2 pair memGen pcGen)
              (fun '(mem,pc) => genRegsFromMemPC mem pc) in
  (liftGen2 pair
            (liftGen2 pair memGen pcGen)
            regsGen).
  

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

Open Scope Z_scope.
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
      else Memory.to_address ((Z.of_N pc) + offset)
    | _ => pc
    end
  | _ => pc
  end.
Close Scope Z_scope.

Open Scope Z_scope.
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
  | IJal imm => RegisterFile.set_register RiscMachine.Register.R_RA ((Z.of_N pc)+1) regs
  | _ => regs
  end.
Close Scope Z_scope.



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
           
  
(*
Sample arbitrary.
Check arbitrary.
*)
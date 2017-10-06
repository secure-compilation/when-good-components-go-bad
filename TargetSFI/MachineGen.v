Set Implicit Arguments.

Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Notations.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.

Require Import TargetSFI.Machine.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.
Local Open Scope string.

Require Import CompCert.Events.

Import Env.
Import SFIComponent.

Definition show_pos (p : positive) := show_nat (Pos.to_nat p).

Definition show_N ( n : N ) := show_nat (N.to_nat n).

Instance show_Component_id : Show Component.id :=
  {|
    show := show_pos
  |}.

Instance show_CN : Show Env.CN := showList.

Instance show_addr : Show  RiscMachine.address :=
  {|
    show := show_N
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

Instance show_trace : Show trace := showList.

Instance show_state : Show MachineState.t :=
  {|
    show := fun (st : MachineState.t) =>
              let '(mem,pc,gen_regs) := st in
              "PC: " ++ (show pc) ++ " "
                     ++ "registers: " ++ (show gen_regs)
                     (* TODO print memory *)                     
  |}.


(* TODO Use UPenn MetaLibrary *)

(*******************************
 * Env.CN Generator
 *******************************)

Theorem decComponentId: forall x y : Component.id, {x = y} + {x <> y}.
Proof. decide equality. Defined.

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
  liftGen N.of_nat (choose (O,N.to_nat SFI.get_max_offset)).

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
  (* generate a 1ist of 10 addresses with generated block id and offset and given cid *)
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
Instance genEnv : Gen Env.t :=
  {
    arbitrary := liftGen2 pair arbitrary arbitrary
  }.

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


(*******************************
 * MachineState Generator
 *******************************)
Import RiscMachine.ISA.

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
                         
Definition genMemForAddresses (addresses : list RiscMachine.address) : G RiscMachine.Memory.t :=
  let how_many : nat := List.length addresses in
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
  (* returnGen RiscMachine.Memory.empty. *)
  

Open Scope nat_scope.
Instance genMem : Gen RiscMachine.Memory.t :=
  {
    arbitrary := 
      let frecv_code := 50 in
      let frecv_data := 50 in
      let how_many : nat := frecv_code + frecv_data in
      bindGen (genAddresses frecv_code frecv_data) genMemForAddresses
  }.
Close Scope nat_scope.
                    
(*
Sample arbitrary.
Check arbitrary.
*)
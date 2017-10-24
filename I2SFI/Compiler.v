(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import Common.Maps.
Require Import Common.Definitions.
Require Import Intermediate.Machine.
Require Import TargetSFI.Machine.
Require Import I2SFI.CompMonad.
Require Import I2SFI.AbstractMachine.

Import MonadNotations.
Open Scope monad_scope.

Record compiler_env : Type := 
  {
    current_component : Component.id;
    next_label : Intermediate.Machine.label;
    cid2SFIid : PMap.t N;
    (* intermediate component id -> block is -> sfi slot id *)
    (* this is especially needed for static buffers *)
    block_id2slot : PMap.t (PMap.t N)
  }.

Notation COMP := (Comp.t compiler_env).
Notation get := (Comp.get compiler_env).
Notation put := (Comp.put compiler_env).
Notation modify := (Comp.modify compiler_env).
Notation lift := (Comp.lift compiler_env).
Notation fail := (Comp.fail compiler_env).
Notation run := (Comp.run compiler_env).

Definition gen_cn (pi : Program.interface) : list Component.id :=
  List.map (fun '(key,_) => key) (PMap.elements pi).

Definition with_current_component (cid : Component.id)
           (env : compiler_env) :  compiler_env :=
  {|
    current_component := cid;
    next_label := next_label env;
    cid2SFIid := cid2SFIid env;
    block_id2slot :=  block_id2slot env
  |}.

Definition env_add_blocks (cid : Component.id) (blocks : PMap.t N)
           (env : compiler_env) :  compiler_env :=
  {|
    current_component := current_component env;
    next_label := next_label env;
    cid2SFIid := cid2SFIid env;
    block_id2slot :=  PMap.add cid blocks (block_id2slot env)
  |}.

Definition with_fresh_label (lbl :  Intermediate.Machine.label)
           (env : compiler_env) :  compiler_env :=
   {|
    current_component := current_component env;
    block_id2slot :=  block_id2slot env;
    cid2SFIid := cid2SFIid env;
    next_label := (lbl + 1)%positive
   |}.

Definition with_cid2SFIid (m : PMap.t N)
          (env : compiler_env) :  compiler_env :=
  {|
    current_component := current_component env;
    next_label := next_label env;
    block_id2slot := block_id2slot env;
    cid2SFIid := m
  |}.


Definition gen_push_sfi (cid : Component.id) : AbstractMachine.code :=
  [
    AbstractMachine.IConst (RiscMachine.to_value (SFI.OFFSET_BITS_NO + SFI.COMP_BITS_NO + 1%N))
                           RiscMachine.Register.R_AUX1
    ; AbstractMachine.IBinOp (RiscMachine.ISA.ShiftLeft) RiscMachine.Register.R_AUX1
                             RiscMachine.Register.R_SFI_SP RiscMachine.Register.R_AUX1
    ; AbstractMachine.IBinOp (RiscMachine.ISA.BitwiseOr) RiscMachine.Register.R_AUX1
                             RiscMachine.Register.R_OR_DATA_MASK RiscMachine.Register.R_AUX1
    ; AbstractMachine.IStore RiscMachine.Register.R_AUX1 RiscMachine.Register.R_RA
    ; AbstractMachine.IConst (1%Z) RiscMachine.Register.R_AUX1
    ; AbstractMachine.IBinOp (RiscMachine.ISA.Addition) RiscMachine.Register.R_SFI_SP
                             RiscMachine.Register.R_AUX1 RiscMachine.Register.R_SFI_SP
  ]. 
(* # form address (s=2*r_SFI_sp+1,c,o=0) in r₁ *)
(*   Const r₁ <- N+S+1 *)
(*   Binop r₁ <- r₁ SL r_SFI_sp  *)
(*   Binop r₁ <- r₁ | r_or_data_mask *)
(* # Store ra at the top of the stack *)
(*   Store *r₁ <- ra *)
(* # increment stack pointer *)
(*   Const r₁ <- 1 *)
(*   Binop r_SFI_sp <- r_SFI_sp + r₁  *)


Definition gen_set_sfi_registers (cid : SFIComponent.id) : AbstractMachine.code :=
  let data_mask := RiscMachine.to_value (SFI.or_data_mask cid) in
  let code_mask := RiscMachine.to_value (SFI.or_code_mask cid) in
  [
      AbstractMachine.IConst data_mask RiscMachine.Register.R_OR_DATA_MASK
    ; AbstractMachine.IConst code_mask RiscMachine.Register.R_OR_CODE_MASK
    ; AbstractMachine.IConst data_mask RiscMachine.Register.R_D
    ; AbstractMachine.IConst code_mask RiscMachine.Register.R_T
  ].

Definition get_address (cid : Component.id) (bid : Block.id)
           (offset : Block.offset): COMP (RiscMachine.address) :=
  do cenv <- get;
    do cmap <- lift (PMap.find cid (block_id2slot cenv));
    do slotid <- lift (PMap.find bid cmap);
    if (Z.ltb offset 0%Z) then fail
    else if (Z.leb (Z.of_N SFI.SLOT_SIZE) offset) then fail
         else                                 
           do sfiId <- lift (PMap.find cid (cid2SFIid cenv));
           ret (SFI.address_of sfiId slotid (Z.to_N offset)).
  

Definition compile_IConst 
           (imval : Intermediate.Machine.imvalue)
           (reg : Intermediate.Machine.register)
  : COMP (AbstractMachine.code) :=
  let reg' := map_register reg in
  match imval with
  | Intermediate.Machine.IInt n => ret [AbstractMachine.IConst n reg']
  | Intermediate.Machine.IPtr p =>
    let cid := Pointer.component p in
    let bid := Pointer.block p in
    let offset := Pointer.offset p in
    do address <- get_address cid bid offset;
      ret  [AbstractMachine.IConst (RiscMachine.to_value address) reg']
  end.

Definition compile_IStore (rp : Intermediate.Machine.register)
           (rs : Intermediate.Machine.register) : COMP (AbstractMachine.code) :=
  ret [
      AbstractMachine.IBinOp (RiscMachine.ISA.BitwiseAnd)
                             (map_register rp) (RiscMachine.Register.R_AND_DATA_MASK)
                             (RiscMachine.Register.R_D)
      ; AbstractMachine.IBinOp (RiscMachine.ISA.BitwiseOr)
                             (RiscMachine.Register.R_D) (RiscMachine.Register.R_OR_DATA_MASK)
                             (RiscMachine.Register.R_D)
      ; AbstractMachine.IStore (RiscMachine.Register.R_D) (map_register rs)
    ].
  (* Binop r_d <- r_p & r_and_data_mask  *)
  (* Binop r_d <- r_d | r_or_data_mask(cid) *)
  (* Store *r_d <- r_s *)

(* TODO: Either use R_ONE or get rid of it *)
Definition compile_IAlloc (rp : Intermediate.Machine.register)
           (rs : Intermediate.Machine.register) : COMP (AbstractMachine.code) :=
  do cenv <- get;
    do cid <- lift (PMap.find (current_component cenv) (cid2SFIid cenv));
    let rp' := (map_register rp) in
    let rs' := (map_register rs) in
    let (r1,r2) :=
        if (RiscMachine.Register.eqb rp' rs')
        then
          if (RiscMachine.Register.eqb rp' RiscMachine.Register.R_AUX1)
          then (RiscMachine.Register.R_AUX1,RiscMachine.Register.R_AUX2)
          else (rp',RiscMachine.Register.R_AUX1)
        else (rp',rs') in  ret
    [
    (* # save register r₂ at location (s=1,c,o=1) *)
    (*   Const r₁ <- Address of (s=1,cid,o=1)  *)
      AbstractMachine.IConst (RiscMachine.to_value (SFI.address_of cid 1%N 1%N))
                             RiscMachine.Register.R_AUX1
      (*   Store *r₁ <- r₂ *)
      ; AbstractMachine.IStore RiscMachine.Register.R_AUX1 RiscMachine.Register.R_AUX2
      (*   Const r₂ <- Address of (s=1,cid,o=0)  *)
      ; AbstractMachine.IConst (RiscMachine.to_value (SFI.address_of cid 1%N 0%N))
                             RiscMachine.Register.R_AUX2
      (*   Load *r₂ -> r₁ *)
      ; AbstractMachine.ILoad  RiscMachine.Register.R_AUX2  RiscMachine.Register.R_AUX1
                             
      (*   Const r₂ <- 1 *)
      ; AbstractMachine.IConst (1%Z) RiscMachine.Register.R_AUX2

      (*   Binop r₁ <- r₁ + r₂ *)
      ; AbstractMachine.IBinOp (RiscMachine.ISA.Addition) RiscMachine.Register.R_AUX1
                               RiscMachine.Register.R_AUX2 RiscMachine.Register.R_AUX1
                             
      (*   Const r₂ <- Address of (s=1,cid,o=0)  *)
      ; AbstractMachine.IConst (RiscMachine.to_value (SFI.address_of cid 1%N 0%N))
                             RiscMachine.Register.R_AUX2
      (*   Store *r₂ <- r₁ *)
      ; AbstractMachine.IStore RiscMachine.Register.R_AUX2 RiscMachine.Register.R_AUX1
    
      (*   Const r₂ <- 1 *)
      ; AbstractMachine.IConst (1%Z) RiscMachine.Register.R_AUX2

      (*   Binop r₁ <- r₁ - r₂ *)
      ;  AbstractMachine.IBinOp (RiscMachine.ISA.Subtraction) RiscMachine.Register.R_AUX1
                               RiscMachine.Register.R_AUX2 RiscMachine.Register.R_AUX1
      (* # calculate address (s=2*k+1,c,o=0) in r₁ *)      
      (*   Const r₂ <- N+S+1 *)
      ; AbstractMachine.IConst (RiscMachine.to_value (SFI.OFFSET_BITS_NO + SFI.COMP_BITS_NO + 1%N))
                           RiscMachine.Register.R_AUX2
      (*   Binop r₁ <- r₁ << r₂ # k shift left (N+S+1) *)
      ; AbstractMachine.IBinOp (RiscMachine.ISA.ShiftLeft) RiscMachine.Register.R_AUX1
                             RiscMachine.Register.R_AUX2 RiscMachine.Register.R_AUX1
      (*   Binop r₁ <- r₁ |  r_or_data_mask  *)
      ;  AbstractMachine.IBinOp (RiscMachine.ISA.BitwiseOr) RiscMachine.Register.R_AUX1
                             RiscMachine.Register.R_OR_DATA_MASK RiscMachine.Register.R_AUX1
      (* # restore r₂ *)
      (*   Const r₂ <- Address of (s=1,cid,o=1)  *)
      ; AbstractMachine.IConst (RiscMachine.to_value (SFI.address_of cid 1%N 1%N))
                               RiscMachine.Register.R_AUX1
      (*   Load *r₂ -> r₂ *)
      ;  AbstractMachine.ILoad  RiscMachine.Register.R_AUX2  RiscMachine.Register.R_AUX2
                               
  ]. 


Definition compile_instruction 
           (i : Intermediate.Machine.instr)
  : COMP (AbstractMachine.code) :=
  do cenv <- get;
    let cid := (current_component cenv) in
  match i with
  | Intermediate.Machine.INop => ret [AbstractMachine.INop]
  | Intermediate.Machine.ILabel lbl => ret [AbstractMachine.ILabel (cid,lbl)]
  | Intermediate.Machine.IConst imval reg => (compile_IConst imval reg)
  | Intermediate.Machine.IMov rs rd => ret [AbstractMachine.IMov
                                             (map_register rs) (map_register rd)]
  | Intermediate.Machine.IBinOp op r1 r2 rd => ret [AbstractMachine.IBinOp
                                                     (map_binop op)
                                                     (map_register r1) (map_register r2)
                                                     (map_register rd)]
  | Intermediate.Machine.ILoad rp rd => ret [AbstractMachine.ILoad (map_register rp)
                                                                  (map_register rd)]
  | Intermediate.Machine.IStore rp rs => (compile_IStore rp rs)
  | Intermediate.Machine.IAlloc rp rs => (compile_IAlloc rp rs)
  | Intermediate.Machine.IBnz r lbl => ret [AbstractMachine.IBnz (map_register r) (cid,lbl)]
  | _ => ret [AbstractMachine.INop]
  end.


Fixpoint compile_instructions 
         (ilist : Intermediate.Machine.code)
  : COMP (AbstractMachine.code) :=
  match (ilist) with
  | [] => ret []
  | i::xs =>
    do ai <- compile_instruction i;
    do res <- compile_instructions xs;
    ret (ai ++ res)
  end.

Definition compile_procedure 
           (pid : Procedure.id)
           (code : Intermediate.Machine.code)
           (interface : Program.interface) 
  : COMP (AbstractMachine.code) :=
  (* if the procedure is exported then must add the sfi stuff*)
  do cenv <- get;
    let cid := (current_component cenv) in
    do comp_interface <- lift (PMap.find cid interface);
    let proc_label := next_label cenv in
    let exported_procs := Component.export comp_interface in
    let is_exported := List.existsb (Pos.eqb pid) exported_procs in
    do acode <- compile_instructions code;     
      if is_exported then
        do sfiId <- lift (PMap.find cid (cid2SFIid cenv));
          ret (
              [AbstractMachine.IHalt; AbstractMachine.ILabel (cid,proc_label)]
                ++ (gen_push_sfi cid)
                ++ (gen_set_sfi_registers sfiId)
                ++ acode )
      else
        ret acode
.

Definition max_label (procs : list (Procedure.id * Intermediate.Machine.code))
  : Intermediate.Machine.label :=
  List.fold_left
    Pos.max
    (List.map
       (fun i =>
          match i with
          | Intermediate.Machine.ILabel lbl => lbl
          | _ => 1%positive (* impossible because of the filter *)
          end
       )
       (List.filter (fun i =>
                       match i with
                       | Intermediate.Machine.ILabel _ => true
                       | _ => false
                       end
                    )
                    (List.flat_map snd procs)))
    1%positive.

Fixpoint compile_procedures (procs : list (Procedure.id * Intermediate.Machine.code))
         (interface : Program.interface)
  : COMP (list (Procedure.id * AbstractMachine.code)) :=
  match procs with
    | [] => ret []
    | (pid,code) :: xs =>
      do! modify (with_fresh_label (max_label procs));
      do compiled_proc <- compile_procedure pid code interface;
        do res <- compile_procedures xs interface;
        ret ((pid, compiled_proc)::res)
  end.
  
Fixpoint compile_components (components : list (Component.id * PMap.t Intermediate.Machine.code))
         (interface : Program.interface)
  : COMP (list (Component.id * PMap.t AbstractMachine.code)) :=
  match components with
  | [] => ret []
  | (cid,procs)::xs =>
    do! modify (with_current_component cid);
    do procs <- compile_procedures (PMap.elements procs) interface;
    do res <- compile_components xs interface;
    ret ((cid, PMapExtra.of_list procs)::res)
  end.
  
(* In slot 1 of each component store allocator data:
for each component at address (s=1,cid,0) write number of buffers +1 
*)
Fixpoint allocate_buffers (buffs :  (list (Component.id * (list (Block.id * nat)))))
           (cid2SFIid : PMap.t N) : COMP (RiscMachine.Memory.t) :=
  match buffs with
  | [] => ret RiscMachine.Memory.empty
  | (cid,lst) :: xs =>
    do mem <- allocate_buffers xs cid2SFIid;
      match PMap.find cid cid2SFIid with
      | None => fail
      | Some sfi_cid =>
        match List.find (fun '(_,size) => Nat.ltb (N.to_nat SFI.SLOT_SIZE) size) lst with
        | None => 
          let blocks := PMapExtra.of_list
                          (List.combine (fst (List.split lst))
                                        (SFI.Allocator.allocate_slots (List.length lst))) in
          do! modify (env_add_blocks cid blocks); 
            ret (RiscMachine.Memory.set_value
                   mem
                   (SFI.address_of sfi_cid (SFI.Allocator.allocator_data_slot) 0%N)
                   (SFI.Allocator.initial_allocator_value (List.length lst)))
        |_ => fail
        end
      end
  end.

Definition init_env : compiler_env :=
  {| current_component := 1%positive;
     next_label := 1%positive;
     block_id2slot := PMap.empty (PMap.t N);
     cid2SFIid := PMap.empty N
  |}.

Definition compile_abstract_program (ip : Intermediate.program) :
  option (abstract_program) :=
    (* cn maps sfi component id to intermediate component id *)
    let cn := gen_cn (Intermediate.prog_interface ip) in
    run init_env (
          (* cid2SFIid maps intermediate component id to sfi id *)
          let cid2SFIid := List.fold_left
                             (fun acc '(cid,i)  =>
                                PMap.add cid (Env.index2SFIid i) acc)
                             (List.combine cn (List.seq 0 ((List.length cn) - 1)))
                             (PMap.empty SFIComponent.id) in
          do! modify (with_cid2SFIid cid2SFIid);
          do mem <- allocate_buffers
             (PMap.elements (Intermediate.prog_buffers ip))
             cid2SFIid;
            
            do acode <- compile_components
               (PMap.elements (Intermediate.prog_procedures ip) )
               (Intermediate.prog_interface ip);

            ret {| AbstractMachine.cn := cn;
                   data_mem := mem;
                   prog_code := PMapExtra.of_list acode;
                   AbstractMachine.prog_interface := Intermediate.prog_interface ip;
                   AbstractMachine.prog_main := Intermediate.prog_main ip
                |}
            
    ).

Definition compile_program (ip : Intermediate.program) :
  option (sfi_program) := None.
(* layout code in memory *)
(* replace labels with addresses *)
              (* generate code for component 0
       push address of halt on sfi stack
       call main === changes mem *)
(* generate E *)
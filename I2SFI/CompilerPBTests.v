(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.CS.
Require Import CompEitherMonad.
Require Import CompStateMonad.
Require Import TestIntermediate.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import CompTestUtil.
Require Import TargetSFI.SFITestUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Module DoNotation.
Import ssrfun.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.


Theorem label_eq_dec:
  forall l1 l2 : Intermediate.Machine.label,  {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality.
Defined.

(***************************************************************************
 * Intermediate program generation
 ***************************************************************************)

Definition MAX_PROC_PER_COMP := 10%nat.

Definition MAX_NO_BUFFERS_PER_COMP := 10%nat.

Definition MAX_BUFFER_SIZE := 10%nat.

Definition MAX_PROC_LENGTH := 100%nat.
    
Inductive test_type : Type :=
| TStore : test_type
| TJump : test_type
| TStack : test_type.

Inductive instr_type :=
| Nop : instr_type
| Label : instr_type
| Const : instr_type
| Mov : instr_type
| BinOp : instr_type
| Load : instr_type
| Store : instr_type
| Alloc : instr_type
| Bnz : instr_type
| Jump : instr_type
| Jal : instr_type
| Call : instr_type
| Return : instr_type
| Halt : instr_type.

Definition get_freq (t : test_type) (i:instr_type) : nat :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store =>
      match t with
      | TStore => 20%nat
      | _ => 4
      end
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump =>
      match t with
      | TJump => 20%nat
      | _ => 1%nat
      end
  | Jal => 1%nat
  | Call =>
      match t with
      | TStack => 30%nat
      | _ => 4%nat
      end
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition choose_pos ( p : positive * positive) :=
  let Z_to_pos z := (* TODO figure out the proper function to call here *)
      match z with
      | Z0 => 1%positive
      | Zpos p => p
      | Zneg p => p
      end in
  let (lo,hi) := p in 
  do! p' <- choose (Zpos lo, Zpos hi);
    returnGen (Z_to_pos p').

Definition pos_list (l : nat) : list positive :=
  List.map Pos.of_nat (List.seq 1 l).

Definition gen_pair_list {A B : Type} (ga : G (list A)) (gb : G (list B)) : G (list (A*B)) :=
  liftGen (fun '(la,lb) => List.combine la lb) 
          (liftGen2 pair ga gb).

Definition gen_sublist {A : Type} ( default : A ) ( all : list A ) : G (list A) :=
  match all with
  | [] => returnGen []
  | _ => 
    do! n <- (choose (1%nat,(List.length all)));
      (vectorOf n (elements default all))
  end.
    
Definition gen_program_interface (cids : list Component.id) : G Program.interface :=
  let proc_ids := do! n <- choose(1%nat,MAX_PROC_PER_COMP); returnGen (pos_list n) in
  do! exported_procs <- (vectorOf (List.length cids) proc_ids);
  let all_procs := List.flat_map
                     (fun '(cid,lp) => List.map (fun pid => (cid,pid)) lp)
                     (List.combine cids exported_procs) in
  do! imported_procs <-  
    sequenceGen (
      List.map (fun cid =>
                  do! import_procs <- (gen_sublist (1%positive,1%positive) all_procs);
                    returnGen (List.filter (fun '(cid',_) =>
                                              negb (Pos.eqb cid cid'))
                                           (List.nodup procs_eqdec import_procs))  
               ) cids);
  returnGen (PMapExtra.of_list
               (List.combine
                  cids 
                  (List.map
                     (fun '(e,i) => (Component.mkCompInterface e i))
                     (List.combine exported_procs imported_procs)
                  )
               )
            ).

Definition gen_value (buffers : list (Component.id*(list (Block.id * nat))))
  : G value :=
  freq [ (3%nat, (do! i <- arbitrary; returnGen (Int i)))
         ; (1%nat, (match buffers with
                  | nil => (do! i <- arbitrary; returnGen (Int i))
                  | p::xs =>
                    let (cid,blocks) := p in 
                      do! p' <- elements p xs;
                        let (cid',blocks') := p' in 
                        (match blocks' with
                         | nil => (do! i <- arbitrary; returnGen (Int i))
                         | b::xs' =>
                           let (bid,s) := b in
                           do! b' <- elements (bid,s) xs';
                             let (bid',s') := b' in
                             do! off <- choose (0%nat, (s'-1)%nat);
                               returnGen (Ptr (cid',bid',Z.of_nat off))
                         end)
                  end
                 )
           )
       ].
                 

Definition gen_sum bsize (buffers : list (Component.id * list (Block.id * nat)))
  : G ( nat+ list value) :=
  freq [ (3%nat, returnGen (inl bsize))
         ; (1%nat,
             (do! vals <- vectorOf bsize (gen_value buffers);
                returnGen (inr vals)))
       ].

Definition gen_buffers (cids : list Component.id)
  : G (PMap.t (list (Block.id * (nat + list value)))) :=
  let gen_n_buffers : G (list (Block.id * nat)) :=
      do! n <- choose (1%nat,MAX_NO_BUFFERS_PER_COMP); 
        let ids := pos_list n in
        do! sizes <- vectorOf n (choose (1%nat, MAX_BUFFER_SIZE));
           returnGen (List.combine ids sizes) in
  do! buffers <- (vectorOf (List.length cids) gen_n_buffers);
    let comp_buffers := (List.combine cids buffers) in
    do! init_buffers <- sequenceGen
      (List.map
         (fun '(cid,bl_lst) =>
            do! bvals <- sequenceGen 
              (List.map (fun '(bid,bsize) =>
                          gen_sum bsize comp_buffers
                        )
                        bl_lst
              );
              returnGen (List.combine (List.map fst bl_lst) bvals)
         )
         comp_buffers
      );
    returnGen (PMapExtra.of_list (List.combine cids init_buffers)).

  
  Instance genOp : Gen Common.Values.binop :=
    {
      arbitrary := elems [
                       Common.Values.Add 
                       ; Common.Values.Minus 
                       ; Common.Values.Mul 
                       ; Common.Values.Eq 
                       ; Common.Values.Leq 
                     ]
    }.

  Instance genRegs : Gen Intermediate.Machine.register :=
    {
      arbitrary := elems [
                       R_ONE
                       ; R_COM
                       ; R_AUX1
                       ; R_AUX2
                       ; R_RA
                       ; R_SP
                     ]
    }.

 
  Definition genPtrImVal
             (pi : Program.interface)
              (buffers : PMap.t (list (Block.id * (nat+list value))))
             (cid : Component.id)
    : G (option Intermediate.Machine.imvalue) :=
    let  genPointer (id : Component.id) :=
         match PMap.find id buffers with
         | None => returnGen None
         | Some lst =>
           match lst with 
           | nil => returnGen None
           | b::xs =>
             do! b' <- elements b xs;
               let '(bid,bs) := b in
               match bs with
               | inl size =>
                 do! offset <- choose (Z0,Z.of_nat size);
                   returnGen (Some (Intermediate.Machine.IPtr ((cid,bid),offset) ))
               | inr lst =>
                 do! offset <- choose (Z0,Z.of_nat (List.length lst));
                   returnGen (Some (Intermediate.Machine.IPtr ((cid,bid),offset) ))
               end
           end
         end in    
    backtrack [
        ( 4%nat, (genPointer cid) )
        ; ( 1%nat,
            (do! id <- (elements (1%positive) (List.map fst (PMap.elements pi)));
               (genPointer id)))
      ].

   
  Definition genIntImVal : G Intermediate.Machine.imvalue :=
    do! n<-arbitrary; returnGen (Intermediate.Machine.IInt n).
  

  Definition genImVal (pi : Program.interface)
             (buffers : PMap.t (list (Block.id * (nat+list value))))
             (cid : Component.id)  : G imvalue :=
    let genImValAux : G Intermediate.Machine.imvalue :=    
        do! res <- genPtrImVal pi buffers cid;
          match res with
          | None => genIntImVal
          | Some ptr => returnGen ptr
          end in 
    freq
      [ (4%nat, genIntImVal)
        ; (1%nat, genImValAux) ].

  Definition genIConst
             (pi : Program.interface)
             (buffers : PMap.t (list (Block.id * (nat+list value))))
             (cid : Component.id) : G instr :=
    do! v <- genImVal pi buffers cid;
      do! r <- arbitrary;
      returnGen (IConst v r).

  Definition gen2Reg (it :  register -> register -> instr) : G instr :=
    do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      returnGen (it r1 r2).

  Definition genIBinOp : G instr :=
    do! op <- arbitrary;
      do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      do! r3 <- arbitrary;
      returnGen (IBinOp op r1 r2 r3).


  Definition genIJump : G instr :=
    do! r <- arbitrary;
      returnGen (IJump r).

  Definition genICall (pi : Program.interface)
             (cid : Component.id)
             (pid : Procedure.id) : G instr :=
    match PMap.find cid pi with
    | None => returnGen INop (* This should not happen *)
    | Some comp_interface =>
      let imports := (Component.import comp_interface) in
      match imports with
      | nil => returnGen INop (* no imports; can't generate ICall *)
      | (cid1,pid1)::xs =>
        do! p <- elements (cid1,pid1) imports;
          let (cid',pid') := p in
          returnGen (ICall cid' pid')
      end
    end.

  Definition genIJal : G instr :=
    do! l <- choose_pos (1%positive,20%positive);
      returnGen (IJal l).
  
  Definition genIBnz (first_label : positive) (lbl : positive) : G instr :=
    do! r <- arbitrary;
      if (Pos.ltb first_label (lbl+3))%positive
      then
        do! target <- choose_pos (first_label,(lbl+3)%positive);
          returnGen (IBnz r target)
      else
        do! target <- choose_pos (lbl,(lbl+3)%positive);
          returnGen (IBnz r target).
      
  Definition genILabel (lbl : positive) : G instr :=
    returnGen (ILabel lbl).


  Definition delared_labels_in_proc (proc : code) :=
     List.map (fun i =>
                 match i with
                 | ILabel l => l
                 | _ => 1%positive (* this is not happening *)
                 end
              )
              (List.filter (fun i => match i with
                                  | ILabel _ => true
                                  | _ => false
                                  end ) proc ).


  Definition gen_procedure
             (t : test_type)
             (pi : Program.interface)
             (buffers : PMap.t (list (Block.id * (nat+list value))))
             (cid : Component.id)
             (pid : Procedure.id)
             (next_label : positive) : G code :=
    let get_missing_labels proc :=
        let decl := delared_labels_in_proc proc in
        let uses :=  List.map (fun i =>
                                match i with
                                | IBnz _ l => l
                                | _ => 1%positive (* this is not happening *)
                                end
                             )
                             (List.filter (fun i => match i with
                                                 | IBnz _ _ => true
                                                 | _ => false
                                                 end ) proc ) in
        List.nodup label_eq_dec
                   (List.filter (fun l => Nat.eqb 0%nat (List.count_occ label_eq_dec decl l))
                                uses)
    in

    let fix gen_proc_with_labels proc missing_labels :=
        match missing_labels with
        | nil => returnGen proc
        | lbl::xs =>          
          do! pos <- choose (0%nat,((List.length missing_labels)-1)%nat);
            let new_proc := ((List.firstn pos proc)
                              ++ [ILabel lbl]
                              ++ (List.skipn pos proc))%list in
            gen_proc_with_labels new_proc xs
        end in
    
    let gen_instr  (first_label : positive)  (next_label : positive) :=
      freq [
          ( (get_freq t Nop) ,(returnGen INop))
          ; ( (get_freq t Const), genIConst pi buffers cid)
          ; ( (get_freq t Label) , genILabel next_label) 
          ; ( (get_freq t Mov), gen2Reg IMov)
          ; ( (get_freq t BinOp), genIBinOp)
          ; ( (get_freq t Load) , gen2Reg ILoad)
          ; ( (get_freq t Store), gen2Reg IStore)
          ; ( (get_freq t Bnz), genIBnz first_label next_label)
          ; ( (get_freq t Jump), genIJump)
          ; ( (get_freq t Jal), genIJal)
          ; ( (get_freq t Call), genICall pi cid pid)
          ; ( (get_freq t Alloc), gen2Reg IAlloc)
          ; ( (get_freq t Halt), (returnGen IHalt))
          ; ( (get_freq t Return), (returnGen IReturn))
        ] in
  let fix gen_proc_rec proc len first_lbl lbl :=
      match len with
      | O =>
        do! p <- gen_proc_with_labels proc (get_missing_labels proc);
          returnGen (p ++ [IReturn])%list
        (* returnGen (proc *)
        (*              (* generate missing labels *)  *)
        (*              ++ (List.map (fun l => ILabel l) (get_missing_labels proc)) *)
        (*              ++ [IReturn])%list *)
      | S len' =>
        do! i <- gen_instr first_lbl lbl;
          match i with
          | ILabel _ => gen_proc_rec (proc ++ [i])%list len' first_lbl (lbl+1)%positive
          | IReturn | IHalt =>
                      do! p <- gen_proc_with_labels proc (get_missing_labels proc);
                        returnGen (p ++ [i])%list
                      (* returnGen (proc *)
                      (*              (* generate missing labels *)  *)
                      (*              ++ (List.map (fun l => ILabel l) (get_missing_labels proc)) *)
                      (*              ++ [i])%list *)
          | _ => gen_proc_rec (proc ++ [i])%list len' first_lbl lbl
          end
      end in
  gen_proc_rec [] MAX_PROC_LENGTH next_label next_label.
    

  Definition gen_procs (t : test_type)
             (pi : Program.interface)
           (buffers : PMap.t (list (Block.id * (nat+list value))))
  : G (PMap.t (PMap.t code)) :=
  let max_label (procs : PMap.t code) :=
      PMap.fold (fun _ proc acc =>
                   (List.fold_left (fun acc' i =>
                                match i with
                                | ILabel l => if (Pos.ltb acc' l) then l else acc'
                                | _ => acc'
                                end
                             ) proc acc)
                ) procs 1%positive
  in
  foldGen
    (fun acc '(cid,comp_interface) =>
       do! proc_map <- (
           foldGen
             (fun acc pid =>
                do! proc <- gen_procedure t  pi buffers cid pid ((max_label acc) + 1)%positive;
                returnGen (PMap.add pid proc acc)
             ) (Component.export comp_interface) (PMap.empty code));
         (* check add labels as needed for IJal *)
         let all_decl_labels := List.fold_left
                                  (fun acc elt => (acc ++ elt)%list )
                                  (List.map (fun p => delared_labels_in_proc (snd p))
                                            (PMap.elements proc_map))
                                  (@nil positive) in
         let uses := List.fold_left
                       (fun acc elt => (acc ++ elt)%list )
                       (List.map (fun p => 
                                    List.map (fun i =>
                                                match i with
                                                | IJal l => l
                                                | _ => 1%positive (* this is not happening *)
                                                end
                                             )
                                             (List.filter (fun i => match i with
                                                                 | IJal _  => true
                                                                 | _ => false
                                                                 end )
                                                          (snd p) ))
                                 (PMap.elements proc_map))
                       (@nil positive) in
         let lbls := List.nodup label_eq_dec
                                (List.filter (fun l =>
                                                Nat.eqb 0%nat
                                                        (List.count_occ
                                                           label_eq_dec
                                                           all_decl_labels
                                                           l
                                                        )
                                             )
                                             uses
                                ) in
         (* TODO do something smarter *)
         match PMap.elements proc_map with
         | nil => returnGen (PMap.add cid proc_map acc)
         | (pid,code)::_ => returnGen (PMap.add cid
                                               (PMap.add
                                                  pid
                                                  (
                                                    (
                                                      List.map
                                                        (fun l => ILabel l)
                                                        lbls
                                                    )++code
                                                  )%list
                                                  proc_map) 
                                               acc)
         end        
    ) (PMap.elements pi)
    (PMap.empty (PMap.t code))
.

Definition gen_main (pi : Program.interface) : G (Component.id * Procedure.id) :=
  do! cid <- elements 1%positive (List.map fst (PMap.elements pi));
    match PMap.find cid pi with
    | None => returnGen (cid,1%positive)
    | Some cint => do! pid <- elements 1%positive (Component.export cint);
                   returnGen (cid,pid)
    end.
  

Definition genIntermediateProgram (t : test_type) : G Intermediate.program :=
    do! n <- choose (1%nat, (N.to_nat (SFI.COMP_MAX-1)%N));
      let cids : list Component.id := pos_list n in
  
  do! program_interface <- (gen_program_interface cids);
  do! buffers <- (gen_buffers cids);
  do! procs <- gen_procs t program_interface buffers;
  do! main <- gen_main program_interface;
  returnGen {|
        Intermediate.prog_interface := program_interface;
        Intermediate.prog_procedures := procs;
        Intermediate.prog_buffers := buffers;
        Intermediate.prog_main := main
      |}.


(* This is how I would like to write the property to test *)
(* TODO check it later *)
Conjecture correct_data_compartmentalized:

  forall (sfi_p : sfi_program) (ip : Intermediate.program)
    (n : nat) (mem : RiscMachine.Memory.t) (pc : RiscMachine.address)
    (gen_regs : RiscMachine.RegisterFile.t)
    (rp rs : RiscMachine.Register.t)
    (t : CompCert.Events.trace) 
    (ptr sfi_sp_val: RiscMachine.value ),

    CompEitherMonad.Right sfi_p = compile_program ip /\
    EitherMonad.Right (t, (mem,pc,gen_regs)) =
    (CS.eval_program n sfi_p RiscMachine.RegisterFile.reset_all) /\
    RiscMachine.Memory.get_word mem pc =
    Some (RiscMachine.Instruction (RiscMachine.ISA.IStore rp rs)) ->
    (* Write at the top of SFI stack (from a pc that is in the list of push sfi ??) *)
    (
      rp = RiscMachine.Register.R_AUX1 /\
      rs = RiscMachine.Register.R_RA /\
      Some ptr = RiscMachine.RegisterFile.get_register rp gen_regs /\
      Some sfi_sp_val = RiscMachine.RegisterFile.get_register
                          RiscMachine.Register.R_SFI_SP gen_regs /\
      RiscMachine.Memory.to_address ptr = SFI.address_of SFI.MONITOR_COMPONENT_ID
                                                  (2*(Z.to_N sfi_sp_val))%N N0 
    )
    \/ (* same component write into a data block *)
    ( Some ptr = RiscMachine.RegisterFile.get_register rp gen_regs /\
      (Z0 <= ptr)%Z /\    
      SFI.is_same_component pc (RiscMachine.Memory.to_address ptr) /\
      (SFI.is_data_address (RiscMachine.Memory.to_address ptr)) = true
    ).


Definition FUEL := 500%nat.

Instance show_ip_exec_state : Show (@execution_state (Events.trace*(CS.state))) :=
  {|
    show := fun es =>
              match es with
              | Running _ => "Running"
              | OutOfFuel _ => "OutOfFuel"
              | Halted => "Halted"
              | Wrong msg err  =>
                "Wrong "
                  ++ match err with
                     | MissingComponentId _ => "MissingComponentId" 
                     | NegativePointerOffset _ => "NegativePointerOffset"
                     | LoadOutsideComponent => "LoadOutsideComponent"
                     | LoadNotAddressInReg => "LoadNotAddressInReg"
                     | StoreOutsideComponent => "StoreOutsideComponent"
                     | StoreNotAddressInReg => "StoreNotAddressInReg"
                     | JumpOutsideComponent => "JumpOutsideComponent"
                     | JumpNotAddressInReg => "JumpNotAddressInReg"
                     | MissingJalLabel => "MissingJalLabel"
                     | MissingLabel => "MissingLabel"
                     | MissingBlock _ => "MissingBlock"
                     | OffsetTooBig _ => "OffsetTooBig"
                     | MemoryError _ => "MemoryError"
                     | NotIntInReg => "MemoryError"
                     | AllocNegativeBlockSize => "AllocNegativeBlockSize"
                     | InvalidEnv => "InvalidEnv(" ++ msg ++")"
                     | NoInfo => msg
                     end
              end
  |}.

Definition run_intermediate_program (ip : Intermediate.program) :=
  runp ip (Int Z0) FUEL.

(************************************************
 * No writes outside its own memory, 
 * except for push sfi.
 *************************************************)

Definition store_log_entry := RiscMachine.pc * RiscMachine.address * RiscMachine.value.

Definition store_log := (list store_log_entry) * (list RiscMachine.address).

Definition update_store_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : store_log) :=
  let '(mem,pc,regs) := st in
  let '(st_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ [pc])%list
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IStore rptr rs =>
      match RiscMachine.RegisterFile.get_register rptr regs with
      | Some ptr =>
        let addr := RiscMachine.Memory.to_address ptr in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_SFI_SP regs with
        | Some sp => ((st_log ++ [(pc,addr,sp)])%list,nlog)
        | _ => (st_log,nlog)
        end
      | _ => (st_log,nlog)
      end
    | _ => (st_log,nlog)
    end
  | _ => (st_log,nlog)
  end.
            
Definition show_log_entry (entry : store_log_entry) : string :=
  let '(pc,addr,sfi_sp) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " sfi sp: " ++ (show sfi_sp).


(* 1. number of instr exec, 
   2. number of internal writes, 
   3. number of push sfi, 
   4. result of intermediate program
   5. number of static instructions executed
*)
Definition store_stat := nat * nat * nat * (@execution_state (CompCert.Events.trace*CS.state)) * nat.

Instance show_store_stat : Show store_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e, es, si) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Internal: "
           ++ (show i )
           ++ " Push SFI: "
           ++ (show e)
           ++ " Intermediate Execution: "
           ++ (show es)
           ++ " Static instructions: "
           ++ (show si)
  |}.
             
Definition store_stats (log : store_log) (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))) : store_stat :=
  let '(l1,l2) := log in
  let i := (List.length (List.filter (fun '(pc,addr,sfi_sp) =>
                                        (SFI.is_same_component_bool pc addr)
                                     ) l1
                        )
           ) in
  ( steps, i, ((List.length l1) - i)%nat, es, List.length l2).


Definition eval_store_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * store_log ) :=
  ((CS.eval_program_with_state     
     store_log
     update_store_log
     FUEL
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).

Definition store_checker (log : store_log) (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))): Checker :=
  let (l1,l2) := log in
  collect
    (store_stats log steps es)
    match l1 with
    | nil => checker tt
    | _ =>
      conjoin (List.map (fun '(pc,addr,sfi_sp) =>
                           if (SFI.is_same_component_bool pc addr)
                           then checker true
                           else
                             if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                             then
                               whenFail ("Failed at: "
                                           ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                        (N.eqb addr (SFI.address_of
                                                       SFI.MONITOR_COMPONENT_ID
                                                       (Z.to_N (2 * sfi_sp +1))
                                                       0))
                             else
                               whenFail ("Failed at: "
                                           ++ (show_log_entry (pc,addr,sfi_sp)) )%string
                                        false
                        ) l1)
    end.

Definition store_correct : Checker :=
  forAll (genIntermediateProgram TStore)
  ( fun ip =>
      match compile_program ip with
      | CompEitherMonad.Left msg err =>
        whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
      | CompEitherMonad.Right p =>
        let '(res,log) := eval_store_program p in
        let es := run_intermediate_program ip in
        match es with
        | Wrong msg InvalidEnv => whenFail ((show es) ++ (show ip))%string false
        | _ =>
          match res with
          | TargetSFI.EitherMonad.Left msg err => whenFail
                                                   (msg ++ (show err))
                                                   (store_checker log 0%nat es)
          | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => 
            (whenFail ("memory of failed program: " ++ (show_mem  mem))%string
                      (store_checker log steps es))
          end
        end
      end
  ).

(********************************************
 * Jumps
 ************************************************)

Inductive jump_type :=
| Indirect : RiscMachine.Register.t -> jump_type
| Direct : jump_type
.

Instance show_jump_type : Show jump_type :=
  {|
    show :=
      fun t =>
        match t with
        | Indirect r => "Jmp " ++ (show r)
        | Direct => "Jal"
        end
  |}.

Definition jump_log_entry := RiscMachine.pc * RiscMachine.address
                             * jump_type * CompCert.Events.trace.

Definition jump_log := (list jump_log_entry) * (list RiscMachine.address).

Definition update_jump_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : jump_log) :=
  let '(mem,pc,regs) := st in
  let '(j_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ [pc])%list
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
      if (N.eqb r RiscMachine.Register.R_RA) || (N.eqb r RiscMachine.Register.R_T)
      then
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => ((j_log ++ [(pc, RiscMachine.Memory.to_address ptr,Indirect r,t)])%list,nlog)
        | _ => (j_log,nlog)
        end
      else (j_log,nlog)
    | RiscMachine.ISA.IJal addr => ((j_log ++ [(pc,addr,Direct,t)])%list,nlog)
    | _ => (j_log,nlog)
    end
  | _ => (j_log,nlog)
  end.
            
Definition show_jump_log_entry (entry : jump_log_entry) : string :=
  let '(pc,addr,type,t) := entry in
   "pc: " ++ (show pc)
          ++ " ptr: "
          ++ (show addr)
          ++ " type: "
          ++ ( match type with
               | Indirect r => "Jmp " ++ (show r)
               | Direct => "Jal"
               end)
          ++ " trace: " ++ (show t).

Definition eval_jump_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * jump_log) :=
  ((CS.eval_program_with_state     
     jump_log
     update_jump_log
     FUEL
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).

(* 1. number of instr exec, 
   2. number of internal jumps, 
   3. number of cross component jumps 
   4. result of intermediate program
   5. number of static instructions executed
*)
Definition jump_stat := nat * nat * nat * (@execution_state (CompCert.Events.trace*CS.state)) * nat.

Instance show_jump_stat : Show jump_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e, es,si) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Internal: "
           ++ (show i )
           ++ " Cross Component: "
           ++ (show e)
           ++ " Intermediate Execution: "
           ++ (show es)
           ++ " Static instructions: "
           ++ (show si)
  |}.

Definition jump_stats (log : jump_log) (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))) : jump_stat :=
  let '(l1,l2) := log in
  let i := (List.length
              (List.filter
                 (fun '(pc,addr,type,t) =>                  
                    (SFI.is_same_component_bool pc addr)
                    || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                    || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID) 
                 ) l1
              )
           ) in
  let e := (List.length
              (List.filter
                 (fun  '(pc,addr,type,t) =>
                    negb (
                        (SFI.is_same_component_bool pc addr)
                        || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                        || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                      )
                 ) l1
              )
           ) in
  ((steps,i), e,es,List.length l2).

Definition jump_checker (log : jump_log) (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))) : Checker :=
  let (l1,l2) := log in
   collect
     (jump_stats log steps es)
      match l1 with
      | nil => checker tt
      | _ =>
        conjoin (
            List.map
              (fun '(pc,addr,type,t) =>
                 if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                 then checker true
                 else
                   if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                   then checker true
                   else
                     if (SFI.is_same_component_bool pc addr)                      
                     then
                       match t with
                       | nil =>  whenFail ("Register R_T expected in internal jumps "
                                            ++ (show type))
                                         (match type with
                                          | Indirect r => RiscMachine.Register.eqb
                                                           RiscMachine.Register.R_T r
                                          | Direct => true
                                          end)     
                       | _ => whenFail ("Unexpectected event at log entry:"
                                         ++ (show_jump_log_entry (pc,addr,type,t)))
                                      false
                       end
                     else
                         match t with
                         | _::_ =>  whenFail ("Register R_A expected in internal jumps "
                                               ++ (show type))
                                            (match type with
                                             | Indirect r => RiscMachine.Register.eqb
                                                              RiscMachine.Register.R_RA r
                                             | Direct => true
                                             end)
                         | nill => whenFail ("Unexpectected empty event at log entry:"
                                              ++ (show_jump_log_entry (pc,addr,type,t)))
                                           false
                         end
              ) l1)
      end. (* TODO check the event too *)

Definition jump_correct : Checker :=
  forAll (genIntermediateProgram TJump)
         ( fun ip =>
             match compile_program ip with
             | CompEitherMonad.Left msg err =>
               whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
             | CompEitherMonad.Right p =>
               let (res,log) := eval_jump_program p in
               let es := run_intermediate_program ip in
               match es with
               | Wrong msg InvalidEnv => whenFail ((show es) ++ (show ip))%string false
               | _ =>
                 match res with
                 | TargetSFI.EitherMonad.Left msg err => whenFail
                                                          (msg ++ (show err))
                                                          (jump_checker log 0%nat es)
                 | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => 
                   jump_checker log steps es
                 end
               end
             end
         ).


(*******************************************************
 * Control Stack
 **********************************************************)
Inductive stack_op := Push
                    | Pop.

Definition show_op op :=
  match op with
  | Push => "Push"
  | Pop => "Pop"
  end.

Definition cs_log_entry := RiscMachine.pc
                           * RiscMachine.address
                           * stack_op * RiscMachine.ISA.instr.

Definition cs_log := (list cs_log_entry) * (list RiscMachine.address).

Definition update_cs_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : cs_log) :=
  let '(mem,pc,regs) := st in
  let '(cs_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ [pc])%list
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => let addr := RiscMachine.Memory.to_address ptr in
                     if SFI.is_same_component_bool pc addr
                     then (cs_log,nlog)
                     else (* cross-component return *)
                         ((cs_log ++ [(pc, addr, Pop, instr)])%list,nlog)
        | _ => (cs_log,nlog)
        end
          
    | RiscMachine.ISA.IJal addr =>
      if SFI.is_same_component_bool pc addr
      then (cs_log,nlog)
      else
        let '(mem',pc',regs') := st' in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_RA regs' with
        | Some addr => ((cs_log
                          ++
                          [(pc, RiscMachine.Memory.to_address addr,Push, instr)])%list
                       ,nlog)
        | _ => (cs_log,nlog)
        end
    | _ => (cs_log,nlog)
    end
  | _ => (cs_log,nlog)
  end.
            
Definition show_cs_log_entry (entry : cs_log_entry) : string :=
  let '(pc,addr,t, instr) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " stack op: " ++ (show_op t)
          ++ "instr " ++ (show instr). 

Definition eval_cs_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * cs_log) :=
  ((CS.eval_program_with_state     
     cs_log
     update_cs_log
     FUEL
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).

(* 1. number of instr exec, 
   2. number of internal jump, 
   3. number of cross component jumps 
   4. result of intermediate program
   5. number of static instructions executed
*)
Definition cs_stat := nat * nat  * (@execution_state (CompCert.Events.trace*CS.state)) * nat.

Instance show_cs_stat : Show cs_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, op, es, si) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Operations no: "
           ++ (show op )
           ++ " Intermediate Execution: "
           ++ (show es)
           ++ " Intermediate Execution: "
           ++ (show es)
           ++ " Static instructions: "
           ++ (show si)
  |}.

Definition cs_stats (log : cs_log) (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))) : cs_stat :=
  let '(l1,l2) := log in
  (steps, (List.length l1), es, List.length l2).
  
Definition cs_checker (log : cs_log)  (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state))) : Checker :=
  let (l1,l2) := log in
  let fix aux l s :=
      match l with
      | nil => checker true
      |  (pc,addr,op,instr)::xs =>
         match op with
         | Push => aux xs (addr::s)
         | Pop =>
           match s with
           | nil => whenFail ("Attemting to pop from empty stack at address"
                               ++ (show pc))%string false
           | a::s' => if (N.eqb a addr)
                     then aux xs s'
                     else whenFail ("Attemting address on the stack: "
                                      ++ (show_addr a)
                                      ++ " address in register: "
                                      ++ (show_addr addr)
                                      ++ "at pc: "
                                      ++ (show_addr pc)
                                      ++ " instr: "
                                      ++ (show instr)
                                   )%string
                                   false
           end         
        end
      end
  in

  collect
    (cs_stats log steps es)
    match steps with
    | O => checker false
    | _ => 
      match l1 with
      | nil => checker tt
      | _ => aux l1 []
      end
    end.

Definition cs_correct : Checker :=
  forAll (genIntermediateProgram TStack)
         ( fun ip =>
             match compile_program ip with
             | CompEitherMonad.Left msg err =>
               whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
             | CompEitherMonad.Right p =>
               let (res,log) := eval_cs_program p in
               let es := run_intermediate_program ip in
                match es with
                | Wrong msg InvalidEnv => whenFail ((show es) ++ (show ip))%string false
                | _ =>
                  match res with
                  | TargetSFI.EitherMonad.Left msg err => whenFail
                                                           (msg ++ (show err))
                                                           (cs_checker log 0%nat es)
                  | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) =>
                    (whenFail ("memory of failed program: " ++ (show_mem  mem))%string
                              (cs_checker log steps es))
                  end
               end
             end
         ).

(****************** QUICK CHECKS ***************************)
Extract Constant Test.defNumTests => "20".

QuickChick store_correct.
QuickChick jump_correct.
QuickChick cs_correct.

(* TODO test compile correctness *)

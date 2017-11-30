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
Require Import TargetSFI.CS.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.MachineGen.

Require Import Intermediate.Machine.

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

Definition newline := String "010" ""%string.

Definition show_map { A :Type} `{_ : Show A} (m : (PMap.t A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (PMap.elements m)
    Coq.Strings.String.EmptyString.

Instance show_map_i  { A :Type} `{_ : Show A} : Show (PMap.t A) :=
  {| show := show_map |}.

Instance show_component_interface : Show Component.interface :=
  {|
    show := fun ci =>
              ("Export: ") 
                ++ (show (Component.export ci)) ++ newline
                ++ "Import:"
                ++ (show (Component.import ci)) ++ newline
  |}.

Instance show_program_interface : Show Program.interface :=
  {| show := fun pi => show_map pi |}.

Instance show_ptr : Show Pointer.t :=
  {| show :=
       fun p => "( cid=" ++ (show (Pointer.component p))
                      ++ ",bid=" ++ (show (Pointer.block p))
                      ++ ",off=" ++ (show (Pointer.offset p))
                      ++ ")"
  |}.

Instance show_immv : Show imvalue :=
  {|
    show :=
      fun iv =>
        match iv with
        | IInt n => "IInt " ++ (show n)
        | IPtr p => "IPtr " ++ (show p)
        end
  |}.

Instance show_register : Show register :=
  {|
    show :=
      fun r =>
        match r with
        | R_ONE => "R_ONE"
        | R_COM => "R_COM"
        | R_AUX1 => "R_AUX1"
        | R_AUX2 => "R_AUX2"
        | R_RA => "R_RA"
        | R_SP => "R_SP"
        end
  |}.

Instance show_binop : Show Common.Values.binop :=
  {|
    show :=
      fun op =>
        match op with
        | Common.Values.Add => "+"
        | Common.Values.Minus => "-"
        | Common.Values.Mul => "*"
        | Common.Values.Eq => "="
        | Common.Values.Leq => "<="
        end
  |}.

Instance show_instr : Show Intermediate.Machine.instr :=
  {| show :=
       fun i =>
         match i with
           | INop => "INop"
           | ILabel lbl => "ILabel " ++ (show lbl)
           | IConst v r => "IConst " ++ (show v) ++ " " ++ (show r)
           | IMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
           | IBinOp op r1 r2 r3 => "IBinop " ++ (show op)
                                            ++ " " ++ (show r1)
                                            ++ " " ++ (show r2)
                                            ++ " " ++ (show r3)
           | ILoad r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
           | IStore r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
           | IAlloc r1 r2 => "IAlloc " ++ (show r1) ++ " " ++ (show r2)
           | IBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
           | IJump r => "IJump " ++ (show r)
           | IJal l => "IJal " ++ (show l) 
           | ICall cid pid => "ICall " ++ (show cid) ++ " " ++ (show pid)
           | IReturn => "IReturn"
           | IHalt => "IHalt"
         end
  |}.

Instance show_value : Show Common.Values.value :=
  {|
    show := fun val =>
              match val with
              | Int i => (show i)
              | Ptr p => (show p)
              | Undef => "Undef"
              end
  |}.

Instance show_buffers : Show (Block.id * (nat + list value)) :=
  {|
    show := fun p =>
              match p with
              | (bid, inl n) => (show bid) ++ "[" ++ (show n) ++"]"
              | (bid, inr lst) => (show bid) ++ ":" ++ (show lst)
              end             
  |}.

Instance show_intermediate_program : Show Intermediate.program :=
  {|
    show := fun ip =>
              ("Interface: ") ++ newline
                ++ (show (Intermediate.prog_interface ip))
                ++ ("Buffers: ") ++ newline
                ++ (show_map (Intermediate.prog_buffers ip))
                ++ ("Code: ") ++ newline
                ++ (show (Intermediate.prog_procedures ip))
                ++ ("Main: ") ++ newline
                ++ (show (Intermediate.prog_main ip))
                         
  |}.

Theorem label_eq_dec:
      forall l1 l2 : Intermediate.Machine.label,  {l1 = l2} + {l1 <> l2}.
    Proof.
      repeat decide equality. Defined.

(***************************************************************************
 * Intermediate program generation
 ***************************************************************************)

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
  let proc_ids := do! n <- choose(1%nat,5%nat); returnGen (pos_list n) in
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
      do! n <- choose (1%nat,5%nat); 
        let ids := pos_list n in
        do! sizes <- vectorOf n (choose (1%nat, N.to_nat (10)%N));
        (* do! sizes <- vectorOf n (choose (1%nat, N.to_nat (SFI.SLOT_SIZE-1)%N)); *)
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
        
    let gen_instr  (first_label : positive)  (next_label : positive) :=
      freq [
          (1%nat,(returnGen INop))
          ; (4%nat, genIConst pi buffers cid)
          ; (4%nat, genILabel next_label) 
          ; (4%nat, gen2Reg IMov)
          ; (7%nat, genIBinOp)
          ; (6%nat, gen2Reg ILoad)
          ; (4%nat, gen2Reg IStore)
          ; (4%nat, genIBnz first_label next_label)
          ; (8%nat, genIJump)
          ; (8%nat, genIJal)
          ; (6%nat, genICall pi cid pid)
          ; (4%nat, gen2Reg IAlloc)
          ; (1%nat, (returnGen IHalt))
          ; (1%nat, (returnGen IReturn))
        ] in
  let fix aux proc len first_lbl lbl :=
      match len with
      | O => 
        returnGen (proc
                     (* generate missing labels *) 
                     ++ (List.map (fun l => ILabel l) (get_missing_labels proc))
                     ++ [IReturn])%list
      | S len' =>
        do! i <- gen_instr first_lbl lbl;
          match i with
          | ILabel _ => aux (proc ++ [i])%list len' first_lbl (lbl+1)%positive
          | IReturn | IHalt =>
                      returnGen (proc
                                   (* generate missing labels *) 
                                   ++ (List.map (fun l => ILabel l) (get_missing_labels proc))
                                   ++ [i])%list
          | _ => aux (proc ++ [i])%list len' first_lbl lbl
          end
      end in
  aux [] 10%nat next_label next_label.
    

Definition gen_procs (pi : Program.interface)
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
                do! proc <- gen_procedure pi buffers cid pid ((max_label acc) + 1)%positive;
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
  

Definition genIntermediateProgram : G Intermediate.program :=
    do! n <- choose (1%nat, (N.to_nat (SFI.COMP_MAX-1)%N));
      let cids : list Component.id := pos_list n in
  
  do! program_interface <- (gen_program_interface cids);
  do! buffers <- (gen_buffers cids);
  do! procs <- gen_procs program_interface buffers;
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

    TargetSFI.EitherMonad.Right sfi_p = compile_program ip /\
    TargetSFI.EitherMonad.Right (t, (mem,pc,gen_regs)) = (CS.eval_program n sfi_p RiscMachine.RegisterFile.reset_all) /\
    RiscMachine.Memory.get_word mem pc = Some (RiscMachine.Instruction (RiscMachine.ISA.IStore rp rs)) ->
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

(************************************************
 * No writes outside its own memory, 
 * except for push sfi.
 *************************************************)

Definition store_log_entry := RiscMachine.pc * RiscMachine.address * RiscMachine.value.

Definition store_log := list store_log_entry.

Definition update_store_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : store_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IStore rptr rs =>
      match RiscMachine.RegisterFile.get_register rptr regs with
      | Some ptr =>
        let addr := RiscMachine.Memory.to_address ptr in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_SFI_SP regs with
        | Some sp => (log ++ [(pc,addr,sp)])%list
        | _ => log
        end
      | _ => log
      end
    | _ => log
    end
  | _ => log
  end.
            
Definition show_log_entry (entry : store_log_entry) : string :=
  let '(pc,addr,sfi_sp) := entry in
   "pc: " ++ (show_addr pc)
          ++ " ptr: "
          ++ (show_addr addr)
          ++ " sfi sp: " ++ (show sfi_sp).

Definition eval_store_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * store_log ) :=
  ((CS.eval_program_with_state     
     store_log
     update_store_log
     FUEL
     p
     (RiscMachine.RegisterFile.reset_all)) nil).


(* number of instr exec, number of internal writes, number 0f push sfi *)
Definition store_stat := nat * nat * nat.

Instance show_store_stat : Show store_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Internal: "
           ++ (show i )
           ++ " Push SFI: "
           ++ (show e)
  |}.
             
Definition store_stats (log : store_log) (steps : nat) : store_stat :=
  let i := (List.length (List.filter (fun '(pc,addr,sfi_sp) =>
                                        (SFI.is_same_component_bool pc addr)
                                     ) log
                        )
           ) in
  ((steps,i), ((List.length log) - i)%nat).

Definition store_checker (log : store_log) (steps : nat) : Checker :=
  collect
    (store_stats log steps)
    match log with
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
                        ) log)
    end.

Definition store_correct : Checker :=
  forAll genIntermediateProgram
  ( fun ip =>
      match compile_program ip with
      | TargetSFI.EitherMonad.Left msg =>
        whenFail ("Compilation error: " ++ msg) false
      | TargetSFI.EitherMonad.Right p =>
        let '(res,log) := eval_store_program p in
        match res with
        | TargetSFI.EitherMonad.Left msg => whenFail msg (store_checker log 0%nat)
        | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => 
          (whenFail ("memory of failed program: " ++ (show_mem  mem))%string
                    (store_checker log steps) (* check the log even if the program fails *))
        end
      end
  ).

(********************************************
 * Jumps
 ************************************************)

Definition jump_log_entry := RiscMachine.pc * RiscMachine.address * CompCert.Events.trace.

Definition jump_log := list (@Either jump_log_entry).

Definition update_jump_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : jump_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
      if (N.eqb r RiscMachine.Register.R_RA) || (N.eqb r RiscMachine.Register.R_T)
      then
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => (log ++ [TargetSFI.EitherMonad.Right
                                (pc, RiscMachine.Memory.to_address ptr,t)])%list
        | _ => log
        end
      else
        (log ++ [TargetSFI.EitherMonad.Left
                   ("Illegal target register: " ++ (show_N r))%string])%list
    | RiscMachine.ISA.IJal addr => (log ++ [TargetSFI.EitherMonad.Right (pc,addr,t)])%list
    | _ => log
    end
  | Some (RiscMachine.Data _) => (log ++
                                     [TargetSFI.EitherMonad.Left
                                        ("Data found at address: " ++ (show pc))%string])%list
  | _ => log
  end.
            
Definition show_jump_log_entry (entry : jump_log_entry) : string :=
  let '(pc,addr,t) := entry in
   "pc: " ++ (show pc)
          ++ " ptr: "
          ++ (show addr)
          ++ " trace: " ++ (show t).

Definition eval_jump_program (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * jump_log) :=
  ((CS.eval_program_with_state     
     jump_log
     update_jump_log
     FUEL
     p
     (RiscMachine.RegisterFile.reset_all)) nil).

(* number of instr exec, number of internal jump, number of cross component jumps *)
Definition jump_stat := nat * nat * nat.

Instance show_jump_stat : Show jump_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, e) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Internal: "
           ++ (show i )
           ++ " Cross Component: "
           ++ (show e)
  |}.

Definition jump_stats (log : jump_log) (steps : nat) : jump_stat :=
  let i := (List.length
              (List.filter
                 (fun elt =>
                    match elt with
                    | TargetSFI.EitherMonad.Left msg => false
                    | TargetSFI.EitherMonad.Right (pc,addr,t) =>
                      (SFI.is_same_component_bool pc addr)
                      || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                      || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                    end
                 ) log
              )
           ) in
  let e := (List.length
              (List.filter
                 (fun elt =>
                    match elt with
                    | TargetSFI.EitherMonad.Left msg => false
                    | TargetSFI.EitherMonad.Right (pc,addr,t) =>
                      negb (
                          (SFI.is_same_component_bool pc addr)
                          || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                          || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                        )
                    end
                 ) log
              )
           ) in
  ((steps,i), e).

Definition jump_checker (log : jump_log) (steps : nat) : Checker :=
   collect
     (jump_stats log steps)
      match log with
      | nil => checker tt
      | _ =>
        conjoin (List.map (fun elt =>
                             match elt with
                             | TargetSFI.EitherMonad.Left msg => whenFail msg false
                             | TargetSFI.EitherMonad.Right (pc,addr,t) =>
                               if (SFI.is_same_component_bool pc addr)
                                  || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID)
                                  || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
                               then
                                 match t with
                                 | nil => checker true
                                 | _ => whenFail ("Unexpectected event at log entry:"
                                                   ++ (show_jump_log_entry (pc,addr,t)))
                                                false
                                 end
                               else
                                 match t with
                                 | _::_ => checker true
                                 | nill => whenFail ("Unexpectected empty event at log entry:"
                                                      ++ (show_jump_log_entry (pc,addr,t)))
                                                   false
                                 end
                             end
                          ) log)
      end. (* TODO check the event too *)

Definition jump_correct : Checker :=
  forAll genIntermediateProgram
         ( fun ip =>
             match compile_program ip with
             | TargetSFI.EitherMonad.Left msg =>
               whenFail ("Compilation error: " ++ msg) false
             | TargetSFI.EitherMonad.Right p =>
               let (res,log) := eval_jump_program p in
               match res with
               | TargetSFI.EitherMonad.Left msg => whenFail msg (jump_checker log 0%nat)
               | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => 
                 jump_checker log steps
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

Definition cs_log_entry := RiscMachine.pc * RiscMachine.address
                           * stack_op * RiscMachine.ISA.instr.

Definition cs_log := list (@Either cs_log_entry).

Definition update_cs_log (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : cs_log) :=
  let '(mem,pc,regs) := st in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump r  =>
        match RiscMachine.RegisterFile.get_register r regs with
        | Some ptr => let addr := RiscMachine.Memory.to_address ptr in
                     if SFI.is_same_component_bool pc addr
                     then (* intra-component jump *)
                       if (N.eqb r RiscMachine.Register.R_T)
                       then log
                       else
                         (log ++ [TargetSFI.EitherMonad.Left
                                    ("Illegal target register: " ++ (show_N r))%string])%list  
                     else (* cross-component return *)
                       if (N.eqb r RiscMachine.Register.R_RA)
                       then
                         (log ++ [TargetSFI.EitherMonad.Right (pc, addr, Pop, instr)])%list
                       else
                         (log ++ [TargetSFI.EitherMonad.Left
                                    ("Illegal target register: " ++ (show_N r))%string])%list
        | _ => (log ++ [TargetSFI.EitherMonad.Left ("Can't find R_RA in general registers "
                                                     ++ (show regs))%string])%list
        end
    | RiscMachine.ISA.IJal addr =>
      if SFI.is_same_component_bool pc addr
      then log
      else
        let '(mem',pc',regs') := st' in
        match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_RA regs' with
        | Some addr => (log ++ [TargetSFI.EitherMonad.Right
                                 (pc, RiscMachine.Memory.to_address addr,Push, instr)])%list
        | _ => (log ++ [TargetSFI.EitherMonad.Left ("Can't find R_RA in general registers "
                                                     ++ (show regs'))%string])%list
        end
    | _ => log
    end
  | Some (RiscMachine.Data _) => (log ++ [TargetSFI.EitherMonad.Left
                                           ("Data found at address: " ++ (show pc))%string])%list
  | _ => log
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
     (RiscMachine.RegisterFile.reset_all)) nil).

(* number of instr exec, number of internal jump, number of cross component jumps *)
Definition cs_stat := nat * nat .

Instance show_cs_stat : Show cs_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, op) := ss in
         "Steps: "
           ++ (show  steps)
           ++ " Operations no: "
           ++ (show op )
  |}.

Definition cs_stats (log : cs_log) (steps : nat) : cs_stat :=
  (steps, (List.length log)).
  
Definition cs_checker (log : cs_log)  (steps : nat) : Checker :=
  let fix aux l s :=
      match l with
      | nil => checker true
      | elt::xs =>
        match elt with
        | TargetSFI.EitherMonad.Left msg => whenFail msg false
        | TargetSFI.EitherMonad.Right (pc,addr,op,instr) =>
          match op with
          | Push => aux xs (addr::s)
          | Pop =>
            match s with
            | nil => whenFail ("Attemting to pop from empty stack at address" ++ (show pc))%string false
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
      end
  in

  collect
    (cs_stats log steps)
    match steps with
    | O => checker false
    | _ => 
      match log with
      | nil => checker tt
      | _ => aux log []
      end
    end.

Definition cs_correct : Checker :=
  forAll genIntermediateProgram
         ( fun ip =>
             match compile_program ip with
             | TargetSFI.EitherMonad.Left msg =>
               whenFail ("Compilation error: "
                           ++ msg
                           ++ newline
                           ++ (show ip) ) false
             | TargetSFI.EitherMonad.Right p =>
               let (res,log) := eval_cs_program p in
               match res with
               | TargetSFI.EitherMonad.Left msg => whenFail msg (cs_checker log 0%nat)
               | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) =>
                 (whenFail ("memory of failed program: " ++ (show_mem  mem))%string
                        (cs_checker log steps) (* check the log even if the program fails *))
               end
             end
         ).

(****************** QUICK CHECKS ***************************)
Extract Constant Test.defNumTests => "20".

(* Definition test5 *)
(*   : @Either (sfi_program) := *)
(*   (* : @Either (trace*MachineState.t) := *) *)
(*   let component1_interface : Component.interface := *)
(*       (Component.mkCompInterface [1%positive *)
(*                                   ; 2%positive *)
(*                                   ; 3%positive *)
(*                                   ; 4%positive *)
(*                                  ] [(2%positive, 3%positive)]) in *)
(*   let component2_interface : Component.interface := *)
(*       (Component.mkCompInterface [1%positive *)
(*                                   ; 2%positive *)
(*                                   ; 3%positive *)
(*                                   ; 4%positive *)
(*                                   ; 5%positive *)
(*                                  ] [ *)
(*                                    (1%positive, 3%positive) *)
(*                                    ; (1%positive, 2%positive) *)
(*                                    ; (3%positive, 1%positive) *)
(*                                  ] *)
(*       ) in *)
(*     let component3_interface : Component.interface := *)
(*       (Component.mkCompInterface [1%positive *)
(*                                  ] [ *)
(*                                    (1%positive, 3%positive) *)
(*                                    ; (2%positive, 3%positive) *)
(*                                    ; (2%positive, 5%positive) *)
(*                                    ; (2%positive, 4%positive) *)
(*                                  ] *)
(*       ) in *)
  
(*     let program_interface : Program.interface := *)
(*         PMap.add 3%positive component3_interface ( *)
(*                    PMap.add 2%positive component2_interface ( *)
(*                               PMap.add 1%positive *)
(*                                        component1_interface *)
(*                                        (PMap.empty Component.interface))) in *)
(*   let buffers := *)
(*       PMap.add 1%positive [(1%positive, (inl 3258%nat)) *)
(*                          ; (2%positive,(inl 1689%nat)) *)
(*                          ; (3%positive,(inl 1074%nat)) *)
(*                          ; (4%positive,(inl 946%nat)) *)
(*                          ; (5%positive,(inl 110%nat)) *)
(*                         ] *)
(*                (PMap.empty (list (Block.id * (nat + list value)))) in *)

(*   let proc1 := *)
(*       PMap.add *)
(*          4%positive *)
(*          [ IBinOp Common.Values.Eq R_AUX2 R_AUX2 R_AUX1 *)
(*            ; IBinOp Common.Values.Leq R_AUX2 R_SP R_AUX2 *)
(*            ; ICall 2%positive 3%positive *)
(*            ; ILabel 10%positive *)
(*            ; ILoad R_RA R_AUX1 *)
(*            ; IJal 3%positive *)
(*            ; IAlloc R_SP R_COM *)
(*            ; IJal 19%positive *)
(*            ; IJump R_SP *)
(*            ; IJump R_SP *)
(*            ; IReturn *)
(*          ]  *)
(*          (PMap.add *)
(*             3%positive *)
(*             [IJump R_AUX1 *)
(*              ; IStore R_COM R_AUX1 *)
(*              ; IBinOp Common.Values.Eq R_COM R_AUX1 R_AUX2 *)
(*              ; ILabel 4%positive *)
(*              ; IStore R_AUX2 R_SP *)
(*              ; IBnz R_SP 4%positive *)
(*              ; ILabel 5%positive *)
(*              ; IBnz R_AUX1 9%positive *)
(*              ; IMov R_AUX1 R_COM *)
(*              ; IBinOp Common.Values.Minus R_AUX1 R_ONE R_AUX1 *)
(*              ; ILabel 9%positive *)
(*              ; IReturn *)
(*             ] *)
(*             (PMap.add *)
(*                2%positive *)
(*                [ILoad R_AUX1 R_COM *)
(*                 ; IJal 20%positive *)
(*                 ; IBinOp Common.Values.Minus R_ONE R_ONE R_COM *)
(*                 ; ICall 2%positive 3%positive *)
(*                 ; ILabel 2%positive *)
(*                 ; ILabel 3%positive *)
(*                 ; IJal 6%positive *)
(*                 ; IJump R_AUX1 *)
(*                 ; IBinOp Common.Values.Leq R_SP R_SP R_ONE *)
(*                 ; ICall 2%positive 3%positive *)
(*                 ; IReturn] *)
(*                (PMap.add *)
(*                   1%positive *)
(*                   [ *)
(*                     ILabel 17%positive *)
(*                     ; ILabel 20%positive *)
(*                     ; ILabel 6%positive *)
(*                     ; ILabel 19%positive *)
(*                     ; ILoad R_SP R_AUX1 *)
(*                     ; IAlloc R_ONE R_COM *)
(*                     ; IMov R_SP R_ONE *)
(*                     ; ICall 2%positive 3%positive *)
(*                     ; ILoad R_AUX1 R_ONE *)
(*                     ; ILoad R_RA R_AUX1 *)
(*                     ; ILoad R_ONE R_AUX2 *)
(*                     ; IJal 17%positive *)
(*                     ; IJump R_SP *)
(*                     ; ICall 2%positive 3%positive *)
(*                     ; IReturn *)
(*                   ] *)
(*                   (PMap.empty Intermediate.Machine.code)))) in *)
(*   let proc2 := *)
(*       PMap.add *)
(*         5%positive *)
(*         [ *)
(*           ICall 3%positive 1%positive *)
(*           ; ICall 1%positive 2%positive *)
(*           ; ILabel 9%positive *)
(*           ; ILoad R_ONE R_COM *)
(*           ; IJal 20%positive *)
(*           ; ICall 1%positive 3%positive *)
(*           ; IJump R_AUX2 *)
(*           ; IBinOp Common.Values.Mul R_AUX2 R_SP R_AUX2 *)
(*           ; IBinOp Common.Values.Eq R_AUX2 R_ONE R_COM *)
(*           ; ICall 3%positive 1%positive *)
(*           ; IReturn *)
(*         ] *)
(*         ( PMap.add *)
(*          4%positive *)
(*          [ *)
(*            IMov R_SP R_COM *)
(*            ; ICall 3%positive 1%positive *)
(*            ; IJal 4%positive *)
(*            ; IBnz R_AUX1 8%positive *)
(*            ; ILabel 8%positive *)
(*            ; IJump R_AUX1 *)
(*            ; ICall 1%positive 3%positive *)
(*            ; IConst (IInt 4%Z) R_COM *)
(*            ; IJal 15%positive *)
(*            ; ILoad R_SP R_AUX2 *)
(*            ; IReturn *)
(*          ]  *)
(*          (PMap.add *)
(*             3%positive *)
(*             [ *)
(*               ICall 3%positive 1%positive *)
(*               ; IJal 3%positive *)
(*               ; ILoad R_AUX1 R_SP *)
(*               ; IBnz R_COM 7%positive *)
(*               ; ICall 3%positive 1%positive *)
(*               ; ILabel 5%positive *)
(*               ; ILoad R_ONE R_SP *)
(*               ; ILoad R_AUX2 R_COM *)
(*               ; IMov R_RA R_SP *)
(*               ; IMov R_RA R_AUX2 *)
(*               ; ILabel 7%positive *)
(*               ; IReturn *)
(*             ] *)
(*             (PMap.add *)
(*                2%positive *)
(*                [ *)
(*                  IStore R_SP R_COM *)
(*                  ; IConst (IInt 3%Z) R_AUX2 *)
(*                  ; IJal 5%positive *)
(*                  ; IJump R_AUX2 *)
(*                  ; IConst (IInt 1%Z) R_AUX2 *)
(*                  ; ILoad R_AUX2 R_SP *)
(*                  ; ICall 3%positive 1%positive *)
(*                  ; IJal 2%positive *)
(*                  ; ILoad R_SP R_ONE *)
(*                  ; ICall 1%positive 2%positive *)
(*                  ; IReturn] *)
(*                (PMap.add *)
(*                   1%positive *)
(*                   [ *)
(*                     ILabel 15%positive *)
(*                     ; ILabel 20%positive *)
(*                     ; ICall 1%positive 2%positive *)
(*                     ; ICall 3%positive 1%positive *)
(*                     ; IConst (IInt (-3)%Z) R_ONE *)
(*                     ; ICall 3%positive 1%positive *)
(*                     ; ILabel 2%positive *)
(*                     ; IBnz R_COM 4%positive *)
(*                     ; IBinOp Common.Values.Eq R_AUX1 R_ONE R_ONE *)
(*                     ; ILabel 3%positive *)
(*                     ; IMov R_AUX1 R_AUX2 *)
(*                     ; INop *)
(*                     ; ILabel 4%positive *)
(*                     ; IReturn *)
(*                   ] *)
(*                   (PMap.empty Intermediate.Machine.code))))) in *)
(*   let proc3 := PMap.add *)
(*                   1%positive *)
(*                   [ *)
(*                     IJump R_SP *)
(*                     ; IConst (IInt 3%Z) R_AUX1 *)
(*                     ; IMov R_SP R_AUX1 *)
(*                     ; IJump R_AUX2 *)
(*                     ; IJump R_SP *)
(*                     ; IAlloc R_COM R_COM *)
(*                     ; ICall 2%positive 4%positive *)
(*                     ; IBnz R_AUX1 4%positive *)
(*                     ; ICall 2%positive 3%positive *)
(*                     ; IBinOp Common.Values.Leq R_ONE R_AUX2 R_AUX2 *)
(*                     ; ILabel 4%positive *)
(*                     ; IReturn *)
(*                   ] *)
(*                   (PMap.empty Intermediate.Machine.code) in *)
    
(*   let procs := *)
(*       PMap.add 1%positive proc1 *)
(*                ( PMap.add 2%positive proc2 *)
(*                           (PMap.add 3%positive proc3 *)
(*                                     (PMap.empty (PMap.t Intermediate.Machine.code)))) in *)
(*   let program : Intermediate.program := {| *)
(*         Intermediate.prog_interface := program_interface; *)
(*         Intermediate.prog_procedures := procs; *)
(*         Intermediate.prog_buffers := buffers; *)
(*         Intermediate.prog_main := (2%positive,5%positive) *)
(*       |} in *)
(*   compile_program program. *)
(*   (* match compile_program program with *) *)
(*   (* | TargetSFI.EitherMonad.Left msg => Left msg *) *)
(*   (* | TargetSFI.EitherMonad.Right p => *) *)
(*   (*   CS.eval_program (100%nat) p RiscMachine.RegisterFile.reset_all *) *)
(*   (* end. *) *)

(* QuickChick *)
(*   ( let x :=  test5 in *)
(*     match x with *)
(*     | TargetSFI.EitherMonad.Left msg => whenFail ("Compilation failed:" *)
(*                                                    ++ msg) *)
(*                                                 (checker false) *)
(*     | TargetSFI.EitherMonad.Right tp => *)
(*       whenFail (show (mem tp) ++ "Env: " ++ (show (e tp))) (checker false) *)
(*     end ). *)


QuickChick store_correct.
QuickChick jump_correct.
QuickChick cs_correct.

(* TODO test compile correctness *)

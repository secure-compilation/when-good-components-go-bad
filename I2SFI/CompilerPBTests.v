(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.
Require Import Common.Maps.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.CS.
Require Import TargetSFI.SFIUtil.
Require Import CompEitherMonad.
Require Import CompStateMonad.
Require Import TestIntermediate.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import CompTestUtil.
Require Import I2SFI.Shrinkers.
Require Import TargetSFI.SFITestUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import CoqUtils.ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Theorem procs_eqdec:
  forall p1 p2 : (positive*positive), {p1 = p2} + {p1 <> p2}. Proof.
  repeat decide equality.
Defined.

(***************************************************************************
 * Intermediate program generation
 ***************************************************************************)

Definition DEBUG := false.

Definition MAX_PROC_PER_COMP := 10%nat.

Definition MAX_NO_BUFFERS_PER_COMP := 10%nat.

Definition MAX_BUFFER_SIZE := 10%nat.

Definition MAX_PROC_LENGTH := 10%nat.

Inductive test_type : Type :=
| TInstrEqual : test_type
| TInstrEqualUndef : test_type
| TStore : test_type
| TJump : test_type
| TStack : test_type
| TStackAllUndefElim : test_type
| TCompilerCorrect : test_type.

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

Definition get_freq_store i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 0%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 1%nat
  | Jal => 1%nat
  | Call => 4%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition get_freq_jump i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 4%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 20%nat
  | Jal => 1%nat
  | Call => 4%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition get_freq_call i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 4%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 1%nat
  | Jal => 1%nat
  | Call => 30%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition get_freq (t : test_type) (i:instr_type) : nat :=
  match t with
  | TInstrEqual => 1%nat
  | TInstrEqualUndef => 1%nat
  | TStore => get_freq_store i
  | TJump => get_freq_jump i
  | TStack => get_freq_call i
  | TCompilerCorrect => get_freq_call i
  | TStackAllUndefElim => get_freq_call i
  end.

Definition jump_undef (t : test_type) : bool :=
  match t with
  | TInstrEqualUndef
  | TJump => true
  | _ => false
  end.

Definition bnz_undef (t : test_type) : bool :=
  match t with
  | TInstrEqualUndef
  | TStack => true
  | _ => false
  end.

Definition load_undef (t : test_type) : bool :=
  match t with
  | TInstrEqualUndef => true
  | _ => false
  end.

Definition store_undef (t : test_type) : bool :=
  match t with
  | TInstrEqualUndef
  | TStore => true
  | _ => false
  end.

Definition alloc_undef (t : test_type) : bool :=
  match t with
  | TInstrEqualUndef => true
  | _ => false
  end.



Definition choose_pos ( p : positive * positive) :=
  let (lo,hi) := p in
  do! p <- choose (Pos.to_nat lo, Pos.to_nat hi);
    returnGen (Pos.of_nat p).

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

Definition prog_int := PMap.t ((list positive) * (list (positive*positive))).

Definition gen_program_interface (cids : list positive) : G prog_int :=
  
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
                  (List.combine exported_procs
                                imported_procs
                  )                  
               )
            ).

Definition gen_value
           (cid : positive)
           (all_buffers : list (positive*(list (positive * nat))))
  : G value :=
  let buffers := List.filter (fun '(cid',_) => Pos.eqb cid cid') all_buffers in
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
                               returnGen (Ptr (Pos.to_nat cid'
                                               , Pos.to_nat bid'
                                               , Z.of_nat off))
                         end)
                  end
                 )
           )
       ].
                 

Definition gen_sum (cid : positive) (bsize : nat) (buffers : list (positive * list (positive * nat)))
  : G ( nat+ list value) :=
  freq [ (3%nat, returnGen (inl bsize))
         ; (1%nat,
             (do! vals <- vectorOf bsize (gen_value cid buffers);
                returnGen (inr vals)))
       ].

Definition gen_buffers (cids : list positive)
  : G (PMap.t (list (positive * (nat + list value)))) :=
  
  let gen_n_buffers : G (list (positive * nat)) :=
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
                          gen_sum cid bsize comp_buffers
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


  Definition genPointer (cid : positive)
             (buffers : PMap.t (list (positive * (nat+list value)))) :=
    let nat_cid := Pos.to_nat cid in
    match PMap.find cid buffers with
    | None => returnGen None
    | Some lst =>
      match lst with 
      | nil => returnGen None
      | b::xs =>
        do! b' <- elements b xs;
          let '(bid,bs) := b in
          let nat_bid := Pos.to_nat bid in
          match bs with
          | inl sz =>
            if Nat.eqb sz 0%nat
            then returnGen None
            else
              if Nat.eqb sz 1%nat
              then
                returnGen
                  (Some (Intermediate.Machine.IPtr
                           ((nat_cid, nat_bid), 0%Z)))
              else
                let up := (sz-1)%nat in
                do! offset <- choose (0%nat, up);
                  returnGen (Some (Intermediate.Machine.IPtr
                                     ((nat_cid, nat_bid), Z.of_nat offset)))
          | inr lst =>
            if (Nat.eqb (List.length lst) 1%nat)
            then
              returnGen (Some (Intermediate.Machine.IPtr
                                 ((nat_cid, nat_bid), Z0) ))
            else
              do! offset <- choose (0%nat,((List.length lst) - 1)%nat);
              returnGen (Some (Intermediate.Machine.IPtr
                                 ((nat_cid, nat_bid), Z.of_nat offset)))
          end
      end
    end.

  
  Definition genPtrImVal
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
             (sameComponent : bool)
    : G (option Intermediate.Machine.imvalue) :=
    if sameComponent
    then
      genPointer cid buffers
    else
      backtrack [
          ( 4%nat, (genPointer cid buffers) )
          ; ( 1%nat,
              (do! id <- (elements (1%positive) (List.map fst (PMap.elements pi)));
                 (genPointer id buffers)))
        ].

   
  Definition genIntImVal : G Intermediate.Machine.imvalue :=
    do! n<-arbitrary; returnGen (Intermediate.Machine.IInt n).
  
  Definition genImVal
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)  : G imvalue :=
    let genImValAux : G Intermediate.Machine.imvalue :=    
        do! res <- genPtrImVal pi buffers cid false;
          match res with
          | None => genIntImVal
          | Some ptr => returnGen ptr
          end in 
    freq
      [ (4%nat, genIntImVal)
        ; (1%nat, genImValAux) ].

  Definition genIConst
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive) : G (list instr) :=
    do! v <- genImVal pi buffers cid;
      do! r <- arbitrary;
      returnGen ([IConst v r]).

  Definition gen2Reg (it :  register -> register -> instr) : G (list instr) :=
    do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      returnGen ([it r1 r2]).

  Definition genMemReg
             (it :  register -> register -> instr)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
    : G (list instr) :=
    do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      do! res <- genPtrImVal pi buffers cid true;
      match res with
      | None => returnGen [it r1 r2]
      | Some ptr =>
        returnGen [IConst ptr r1; it r1 r2]
      end.

  Definition genIAlloc (t : test_type) : G (list instr) :=    
    do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      match (alloc_undef t) with
      | true => returnGen [IAlloc r1 r2]
      | _ =>
        do! v <- choose (0%nat,((N.to_nat SFI.SLOT_SIZE) - 1)%nat);
          returnGen [IConst (IInt (Z.of_nat v)) r2; IAlloc r1 r2]
      end.

  Definition genILoad
             (t : test_type)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
    : G (list instr) :=
    match (load_undef t) with
    | true => gen2Reg ILoad
    | _ => genMemReg ILoad pi buffers cid
    end.
  
  Definition genIStore
             (t : test_type)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
    : G (list instr) :=
    match (store_undef t) with
    | true => gen2Reg IStore
    | _ => genMemReg IStore pi buffers cid
    end.   
    
  Definition genIBinOp : G (list instr) :=
    do! op <- arbitrary;
      do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      do! r3 <- arbitrary;
      returnGen ([IBinOp op r1 r2 r3]).

  Definition genIJump : G (list instr) :=
    do! r <- arbitrary;
      returnGen ([IJump r]).

  Definition genICall
             (pi : prog_int)
             (cid : positive)
             (pid : positive) : G (list instr) :=
    match PMap.find cid pi with
    | None => returnGen [INop] (* This should not happen *)
    | Some comp_interface =>
      let imports := (snd comp_interface) in
      match imports with
      | nil => returnGen [INop] (* no imports; can't generate ICall *)
      | (cid1,pid1)::xs =>
        do! p <- elements (cid1,pid1) imports;
          do! v <- arbitrary;
          let (cid',pid') := p in
          let call_instr := ICall (Pos.to_nat cid') (Pos.to_nat pid') in
          let const_instr := IConst (Intermediate.Machine.IInt v) R_COM in
          returnGen ([const_instr;call_instr])
      end
    end.

  Definition genIJal : G (list instr) :=
    do! l <- choose (1%nat,20%nat);
      returnGen ([IJal l]).
  
  Definition genIBnz (first_label : nat) (lbl : nat) : G (list instr) :=
    do! r <- arbitrary;
      do! v <- arbitrary;
      if (Nat.ltb first_label (lbl+3))%nat
      then
        do! target <- choose (first_label,(lbl+3)%nat);
          returnGen ([IConst (IInt v) r; IBnz r target])
      else
        do! target <- choose (lbl,(lbl+3)%nat);
          returnGen ([IConst (IInt v) r; IBnz r target]).
      
  Definition genILabel (lbl : nat) : G (list instr) :=
    returnGen ([ILabel lbl]).


  Definition delared_labels_in_proc (proc : Intermediate.Machine.code) :=
     List.map (fun i =>
                 match i with
                 | ILabel l => l
                 | _ => 1%nat (* this is not happening *)
                 end
              )
              (List.filter (fun i => match i with
                                  | ILabel _ => true
                                  | _ => false
                                  end ) proc ).

  (************ gen procedure *********************)

  Definition get_missing_labels proc :=
    let decl := delared_labels_in_proc proc in
    let uses :=  List.map
                   (fun i =>
                      match i with
                      | IBnz _ l => l
                      | _ => 1%nat (* this is not happening *)
                      end
                   )
                   (List.filter (fun i => match i with
                                       | IBnz _ _ => true
                                       | _ => false
                                       end ) proc ) in
    List.nodup label_eq_dec
               (List.filter (fun l => Nat.eqb 0%nat (List.count_occ label_eq_dec decl l))
                            uses).

  Fixpoint gen_proc_with_labels proc missing_labels :=
    match missing_labels with
    | nil => returnGen proc
    | lbl::xs =>          
      do! pos <- choose (0%nat,((List.length missing_labels)-1)%nat);
        let new_proc := ((List.firstn pos proc)
                           ++ [ILabel lbl]
                           ++ (List.skipn pos proc))%list in
        gen_proc_with_labels new_proc xs
    end.


  Definition gen_instr
             (first_label : nat)
             (next_label : nat)
             (t : test_type)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
             (pid : positive)
    :=
    freq [
        ( (get_freq t Nop) ,(returnGen [INop]))
        ; ( (get_freq t Const), genIConst pi buffers cid)
        ; ( (get_freq t Label) , genILabel next_label) 
        ; ( (get_freq t Mov), gen2Reg IMov)
        ; ( (get_freq t BinOp), genIBinOp)
        ; ( (get_freq t Load) , genILoad t pi buffers cid)
        ; ( (get_freq t Store), genIStore t pi buffers cid)
        ; ( (get_freq t Bnz), genIBnz first_label next_label)
        ; ( (get_freq t Jump), genIJump)
        ; ( (get_freq t Jal), genIJal)
        ; ( (get_freq t Call), genICall pi cid pid)
        ; ( (get_freq t Alloc), genIAlloc t)
        ; ( (get_freq t Halt), (returnGen [IHalt]))
        ; ( (get_freq t Return), (returnGen [IReturn]))
      ].
  
  Definition gen_procedure
             (t : test_type)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
             (cid : positive)
             (pid : positive)
             (next_label : nat) : G Intermediate.Machine.code :=
   
  let fix gen_proc_rec proc len first_lbl lbl :=
      match len with
      | O =>
        do! p <- gen_proc_with_labels proc (get_missing_labels proc);
          returnGen (p ++ [IReturn])%list
      | S len' =>
        do! il <- gen_instr first_lbl lbl t pi buffers cid pid;
          match il with
          | [ILabel _] => gen_proc_rec (proc ++ il)%list len' first_lbl (lbl+1)%nat
          | [IReturn] | [IHalt] =>
                      do! p <- gen_proc_with_labels proc (get_missing_labels proc);
                        returnGen (p ++ il)%list
          | _ => gen_proc_rec (proc ++ il)%list len' first_lbl lbl
          end
      end in
  gen_proc_rec [] MAX_PROC_LENGTH next_label next_label.


  (****************** Done gen_procedure (split to avoid stack overflow) *******)

  Definition max_label (procs : PMap.t Intermediate.Machine.code) :=
    List.fold_left
      (fun acc '(_,proc)  =>
         (List.fold_left (fun acc' i =>
                            match i with
                            | ILabel l => if (Nat.ltb acc' l) then l else acc'
                            | _ => acc'
                            end
                         ) proc acc)
      ) (PMap.elements procs) 1%nat.
  
  Definition gen_procedures
             (t : test_type)
             (pi : prog_int)
             (buffers : PMap.t (list (positive * (nat+list value))))
    : G (PMap.t (PMap.t Intermediate.Machine.code)) :=

   foldGen
     (fun acc '(cid, comp_interface)  =>
        do! proc_map <- (
            let '(lexp,limp) := comp_interface in
            foldGen
              (fun acc pid =>
                 do! proc <- gen_procedure t  pi buffers cid pid ((max_label acc) + 1)%nat;
                        returnGen (PMap.add pid proc acc)
              ) lexp (PMap.empty Intermediate.Machine.code));
          
          (* check add labels as needed for IJal *)
          let all_decl_labels := List.fold_left
                                   (fun acc elt => (acc ++ elt)%list )
                                   (List.map (fun p => delared_labels_in_proc (snd p))
                                             (PMap.elements proc_map))
                                   (@nil nat) in
          let uses := List.fold_left
                        (fun acc elt => (acc ++ elt)%list )
                        (List.map (fun p => 
                                     List.map (fun i =>
                                                 match i with
                                                 | IJal l => l
                                                 | _ => 1%nat (* this is not happening *)
                                                 end
                                              )
                                              (List.filter (fun i => match i with
                                                                  | IJal _  => true
                                                                  | _ => false
                                                                  end )
                                                           (snd p) ))
                                  (PMap.elements proc_map))
                        (@nil nat) in
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
                                                     proc_map
                                                  )
                                                  acc
                                      )
          end 
          ) (PMap.elements  pi)
          (PMap.empty (PMap.t Intermediate.Machine.code))
.

Definition gen_main (pi : prog_int) : G (positive * positive) :=
  do! cid <- elements 1%positive (List.map fst (PMap.elements pi));
    match PMap.find cid pi with
    | None => returnGen (cid,1%positive)
    | Some cint => do! pid <- elements 1%positive (fst cint);
                    returnGen (cid,pid)
    end.

Definition convert_program_interface (pi : prog_int) : Program.interface :=
  PMap.fold
    (fun cid cint acc =>
       let '(lexp,limp) := cint in
       setm acc (Pos.to_nat cid) (Component.mkCompInterface
                                    (list2fset (List.map Pos.to_nat lexp))
                                    (list2fset (List.map
                                                  (fun '(c,p) => (Pos.to_nat c,Pos.to_nat p))
                                                  limp)))
    ) pi (emptym).

Definition convert_procedures (all : PMap.t (PMap.t Intermediate.Machine.code))
  : NMap (NMap Intermediate.Machine.code) :=
  PMap.fold
    (fun cid pm (acc : NMap ( NMap Intermediate.Machine.code ) ) =>
       setm acc (Pos.to_nat cid)
            (
              PMap.fold
                (fun pid pcode (acc1 : NMap Intermediate.Machine.code) =>
                   setm acc1 (Pos.to_nat pid) pcode)
                pm (emptym)
            )
    ) all (emptym).

Definition convert_buffers (buffs : PMap.t  (list (positive * (nat+list value)))) :=
  PMap.fold
    (fun cid b acc => setm acc (Pos.to_nat cid)
                        (List.map (fun '(id,s)=>(Pos.to_nat id,s)) b))
    buffs emptym.

(* TODO Check with Arthur and G. *) 
Definition fix_main (all : PMap.t (PMap.t Intermediate.Machine.code))
           (cid : Component_id) (pid : Procedure_id) :=
  match PMap.find cid all with
  | None => all
  | Some pmap =>
    match PMap.find pid pmap with
    | None => all
    | Some l =>
      PMap.add cid
               ( PMap.add
                   pid
                   ( List.map
                       (fun i => match i with
                              | IReturn => IHalt
                              | _ => i
                              end
                       ) l
                   )
                   pmap
               )
               all
    end
  end.

Definition genIntermediateProgram (t : test_type) : G Intermediate.program :=
  
  do! n <- choose (1%nat, (N.to_nat (SFI.COMP_MAX-1)%N));
    let cids := pos_list n in
  
    do! pi <- (gen_program_interface cids);
      
      do! buffers <- gen_buffers cids;
      do! procs <- gen_procedures t pi buffers;      
      do! main <- gen_main pi;
      let (mc,mp) := main in
      let fixed_procs := fix_main procs mc mp in
      
  returnGen {|
        Intermediate.prog_interface := convert_program_interface pi;
        Intermediate.prog_procedures := convert_procedures fixed_procs;
        Intermediate.prog_buffers := convert_buffers buffers;
        Intermediate.prog_main := Some (Pos.to_nat mc,Pos.to_nat mp)
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


Definition FUEL := 100%nat.

Definition run_intermediate_program (ip : Intermediate.program) :=
  runp FUEL ip.

(************************************************
 * No writes outside its own memory, 
 * except for push sfi.
 *************************************************)

Definition store_log_entry := (RiscMachine.pc * RiscMachine.address * RiscMachine.value)%type.

Definition store_log := ((list store_log_entry) * (list RiscMachine.address))%type.

Definition update_store_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
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
Definition store_stat := (nat * nat * nat
                          * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type.

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

Definition store_correct  (t : test_type) : Checker :=
  forAllShrink (genIntermediateProgram t) shrink
  ( fun ip =>
      match compile_program ip with
      | CompEitherMonad.Left msg err =>
        whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
      | CompEitherMonad.Right p =>
        let '(res,log) := eval_store_program p in
        let es := run_intermediate_program ip in
        match es with
        | Wrong _ msg InvalidEnv
        | Wrong _ msg (NegativePointerOffset _)
        | Wrong _ msg MissingJalLabel
        | Wrong _ msg MissingLabel
        | Wrong _ msg (MissingBlock _)
        | Wrong _ msg (OffsetTooBig _)
        | Wrong _ msg (MemoryError _ _)
        | Wrong _ msg AllocNegativeBlockSize
        | Wrong _ msg NoInfo
        | Wrong _ msg (MissingComponentId _) =>
          if DEBUG
          then 
            whenFail ((show es) ++ (show ip))%string false
          else
            checker tt
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

Definition jump_log_entry := (RiscMachine.pc * RiscMachine.address
                             * jump_type * CompCert.Events.trace)%type.

Definition jump_log := ((list jump_log_entry) * (list RiscMachine.address))%type.

Definition update_jump_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
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
Definition jump_stat := (nat * nat * nat
                         * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type.

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
      end. 

Definition jump_correct  (t : test_type) : Checker :=
  forAllShrink (genIntermediateProgram TJump) shrink
         ( fun ip =>
             match compile_program ip with
             | CompEitherMonad.Left msg err =>
               whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
             | CompEitherMonad.Right p =>
               let (res,log) := eval_jump_program p in
               let es := run_intermediate_program ip in
               match es with
               | Wrong _ msg InvalidEnv
               | Wrong _ msg (NegativePointerOffset _)
               | Wrong _ msg MissingJalLabel
               | Wrong _ msg MissingLabel
               | Wrong _ msg (MissingBlock _)
               | Wrong _ msg (OffsetTooBig _)
               | Wrong _ msg (MemoryError _ _)
               | Wrong _ msg (StoreMemoryError _ _)
               | Wrong _ msg AllocNegativeBlockSize
               | Wrong _ msg NoInfo
               | Wrong _ msg (MissingComponentId _) =>
                 if DEBUG
                 then 
                   whenFail ((show es) ++ (show ip))%string false
                 else
                   checker tt
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

Definition cs_log_entry := (RiscMachine.pc
                           * RiscMachine.address
                           * stack_op * RiscMachine.ISA.instr)%type.

Definition cs_log := ((list cs_log_entry) * (list RiscMachine.address))%type.

Definition update_cs_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
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
Definition cs_stat := (nat * nat
                       * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type.

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

Definition cs_correct (t : test_type) : Checker :=
  forAllShrink (genIntermediateProgram t) shrink
         ( fun ip =>
             match compile_program ip with
             | CompEitherMonad.Left msg err =>
               whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
             | CompEitherMonad.Right p =>
               let (res,log) := eval_cs_program p in
               let es := run_intermediate_program ip in
                match es with
                | Wrong _ msg InvalidEnv
                | Wrong _ msg (NegativePointerOffset _)
                | Wrong _ msg MissingJalLabel
                | Wrong _ msg MissingLabel
                | Wrong _ msg (MissingBlock _)
                | Wrong _ msg (OffsetTooBig _)
                | Wrong _ msg (MemoryError _ _)
                | Wrong _ msg (StoreMemoryError _ _)
                | Wrong _ msg AllocNegativeBlockSize
                | Wrong _ msg NoInfo
                | Wrong _ msg (MissingComponentId _) =>
                  if DEBUG
                  then 
                    whenFail ((show es) ++ (show ip))%string false
                  else
                    checker tt
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
Extract Constant Test.defNumTests => "10000". 

(* QuickChick store_correct TStore. *)
(* QuickChick jump_correct TJump. *)
(* QuickChick cs_correct TStack. *)



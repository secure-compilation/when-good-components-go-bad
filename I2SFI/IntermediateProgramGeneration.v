(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.

Require Import Common.Definitions.
Require Import Common.Maps.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import CompTestUtil.
Require Import TargetSFI.SFIUtil.
Require Import TargetSFI.Machine.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Import Common.Values.

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

Definition Component_id := N.
Definition Procedure_id := N.
Definition Block_id := N.
Definition prog_int := BinNatMap.t ((list Procedure_id) * (list (Component_id*Procedure_id))).

Inductive instr_gen : Type :=
| EqualUndefAllowed : instr_gen
| EqualNoUndef : instr_gen
| TestSpecific : instr_gen.


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

Definition instr_weight := instr_type -> nat.
Definition code_address_const_instr := 
             Intermediate.Machine.register -> 
             prog_int ->
             Component_id -> G (list instr).
Definition data_address_const_instr :=
  Intermediate.Machine.register ->
  Intermediate.Machine.register ->
  prog_int -> BinNatMap.t (list (Block_id * (nat+list value))) ->
  Component_id -> G (list instr).


Theorem label_eq_dec:
  forall l1 l2 : Intermediate.Machine.label,  {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality.
Defined.

Theorem procs_eqdec:
  forall p1 p2 : (N*N), {p1 = p2} + {p1 <> p2}. Proof.
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

Definition choose_N ( p : N * N) :=
  let (lo,hi) := p in
  do! p <- choose (N.to_nat lo, N.to_nat hi);
    returnGen (N.of_nat p).

Definition N_list (l : nat) : list N :=
  List.map N.of_nat (List.seq 0 l).

Definition arbitrary_N : G N :=
  do! z <- arbitrary;
    returnGen (Z.abs_N z).

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

Definition get_freq (t : instr_gen) (wf : instr_weight) (i:instr_type) : nat :=
  match t with
  | EqualUndefAllowed => 1%nat
  | EqualNoUndef => 1%nat
  | TestSpecific =>
    wf i
  end.

Definition gen_program_interface (cids : list N) : G prog_int :=

  let proc_ids := do! n <- choose(0%nat,MAX_PROC_PER_COMP); returnGen (N_list n) in
  do! exported_procs <- (vectorOf (List.length cids) proc_ids);
    let all_procs := List.flat_map
                       (fun '(cid,lp) => List.map (fun pid => (cid,pid)) lp)
                       (List.combine cids exported_procs) in
    do! imported_procs <-
      sequenceGen (
        List.map (fun cid =>
                    do! import_procs <- (gen_sublist
                                           (N.of_nat Component.main,
                                            N.of_nat Procedure.main) all_procs);
                      returnGen (List.filter (fun '(cid',_) =>
                                                negb (N.eqb cid cid'))
                                             (List.nodup procs_eqdec import_procs))
                 ) cids);
      returnGen (BinNatMapExtra.of_list
                   (List.combine
                      cids
                      (List.combine exported_procs
                                    imported_procs
                      )
                   )
                ).

Definition gen_value
           (cid : N)
           (all_buffers : list (N*(list (N * nat))))
  : G value :=
  let buffers := List.filter (fun '(cid',_) => N.eqb cid cid') all_buffers in
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
                             returnGen (Ptr (N.to_nat cid'
                                             , N.to_nat bid'
                                             , Z.of_nat off))
                       end)
                  end
                 )
           )
       ].

Definition gen_sum (cid : N) (bsize : nat) (buffers : list (N * list (N * nat)))
  : G ( nat+ list value) :=
  freq [ (3%nat, returnGen (inl bsize))
         ; (1%nat,
            (do! vals <- vectorOf bsize (gen_value cid buffers);
               returnGen (inr vals)))
       ].

Definition gen_buffers (cids : list N)
  : G (BinNatMap.t (list (N * (nat + list value)))) :=

  let gen_n_buffers : G (list (N * nat)) :=
      do! n <- choose (1%nat,MAX_NO_BUFFERS_PER_COMP);
        let ids := N_list n in
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
      returnGen (BinNatMapExtra.of_list (List.combine cids init_buffers)).

Derive Arbitrary for Common.Values.binop.
Derive Arbitrary for Intermediate.Machine.register.

(* Instance genRegs : Gen Intermediate.Machine.register := *)
(*   { *)
(*     arbitrary := elems [ *)
(*                      R_ONE *)
(*                      ; R_COM *)
(*                      ; R_AUX1 *)
(*                      ; R_AUX2 *)
(*                      ; R_RA *)
(*                      ; R_SP *)
(*                    ] *)
(*   }. *)

Definition genPointer (cid : N)
           (buffers : BinNatMap.t (list (N * (nat+list value)))) :=
  let nat_cid := N.to_nat cid in
  match BinNatMap.find cid buffers with
  | None => returnGen None
  | Some lst =>
    match lst with 
    | nil => returnGen None
    | b::xs =>
      do! b' <- elements b xs;
        let '(bid,bs) := b in
        let nat_bid := N.to_nat bid in
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
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (cid : N)
           (sameComponent : bool)
  : G (option Intermediate.Machine.imvalue) :=
  if sameComponent
  then
    genPointer cid buffers
  else
    backtrack [
        ( 4%nat, (genPointer cid buffers) )
        ; ( 1%nat,
            (do! id <- (elements (1%N) (List.map fst (BinNatMap.elements pi)));
               (genPointer id buffers)))
      ].

Definition genIntImVal : G Intermediate.Machine.imvalue :=
  do! n<-arbitrary; returnGen (Intermediate.Machine.IInt n).


Definition genImVal
           (pi : prog_int)
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (cid : N)  : G imvalue :=
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
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (cid : N) : G (list instr) :=
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
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (cid : N)
  : G (list instr) :=
  do! r1 <- arbitrary;
    do! r2 <- arbitrary;
    do! res <- genPtrImVal pi buffers cid true;
    match res with
    | None => returnGen [it r1 r2]
    | Some ptr =>
      returnGen [IConst ptr r1; it r1 r2]
    end.

Definition genIAlloc (t : instr_gen) : G (list instr) :=    
  do! r1 <- arbitrary;
    do! r2 <- arbitrary;
    match t with
    | EqualUndefAllowed => returnGen [IAlloc r1 r2]
    | _ =>
      do! v <- choose (1%nat,10%nat);
        returnGen [IConst (IInt (Z.of_nat v)) r2; IAlloc r1 r2]
    end.

Definition genILoad
           (t : instr_gen)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
  : G (list instr) :=
  match t with
  | EqualUndefAllowed => gen2Reg ILoad
  | _ => genMemReg ILoad pi buffers cid
  end.

Definition genIStore
           (t : instr_gen)
           (addr_gen : data_address_const_instr)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
  : G (list instr) :=
  match t with
  | EqualUndefAllowed =>
    gen2Reg IStore
  | _ =>
    do! r1 <- arbitrary;
      do! r2 <- arbitrary;
      do! constInstr <- addr_gen r1 r2 pi buffers cid;
      returnGen (constInstr++[IStore r1 r2])%list
  end.

Definition genIBinOp : G (list instr) :=
  do! op <- arbitrary;
    do! r1 <- arbitrary;
    do! r2 <- arbitrary;
    do! r3 <- arbitrary;
    returnGen ([IBinOp op r1 r2 r3]).

Definition genIJump
           (t : instr_gen)
           (cag : code_address_const_instr)
           (pi : prog_int)
           (cid : Component_id)
  : G (list instr) :=
  match t with
  | EqualUndefAllowed  =>
    do! r <- arbitrary;
      returnGen ([IJump r])
  | _ =>
    do! r <- arbitrary;
      do! li <- cag r pi cid;
      returnGen (li ++ [IJump r])%list
  end.

Definition genICall
           (pi : prog_int)
           (cid : N)
           (pid : N) : G (list instr) :=
  match BinNatMap.find cid pi with
  | None => returnGen [INop] (* This should not happen *)
  | Some comp_interface =>
    let imports := (snd comp_interface) in
    match imports with
    | nil => returnGen [INop] (* no imports; can't generate ICall *)
    | (cid1,pid1)::xs =>
      do! p <- elements (cid1,pid1) imports;
        do! v <- arbitrary;
        let (cid',pid') := p in
        let call_instr := ICall (N.to_nat cid') (N.to_nat pid') in
        let const_instr := IConst (Intermediate.Machine.IInt v) R_COM in
        returnGen ([const_instr;call_instr])
    end
  end.

Definition genIJal : G (list instr) :=
  do! l <- choose (1%nat,20%nat);
    returnGen ([IJal l]).

Definition genIBnz (t : instr_gen)
           (first_label : nat) (lbl : nat) : G (list instr) :=
  match t with
  | EqualUndefAllowed =>
    do! r <- arbitrary;
      if (Nat.ltb first_label (lbl+3))%nat
      then
        do! target <- choose (first_label,(lbl+3)%nat);
          returnGen ([IBnz r target])
      else
        do! target <- choose (lbl,(lbl+3)%nat);
      returnGen ([IBnz r target])
  | _ => 
    do! r <- arbitrary;
      do! v <- arbitrary;
      if (Nat.ltb first_label (lbl+3))%nat
      then
        do! target <- choose (first_label,(lbl+3)%nat);
          returnGen ([IConst (IInt v) r; IBnz r target])
      else
        do! target <- choose (lbl,(lbl+3)%nat);
      returnGen ([IConst (IInt v) r; IBnz r target])
  end.

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
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (first_label : nat)
           (next_label : nat)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (cid : N)
           (pid : N)
  :=
    freq [
        ( (get_freq t wf Call), genICall pi cid pid)
        ; ( (get_freq t wf Const), genIConst pi buffers cid)
        ; ( (get_freq t wf Label) , genILabel next_label) 
        ; ( (get_freq t wf Mov), gen2Reg IMov)
        ; ( (get_freq t wf BinOp), genIBinOp)
        ; ( (get_freq t wf Load) , genILoad t pi buffers cid)
        ; ( (get_freq t wf Store), genIStore t dag pi buffers cid)
        ; ( (get_freq t wf Bnz), genIBnz t first_label next_label)
        ; ( (get_freq t wf Jump), genIJump t cag pi cid)
        ; ( (get_freq t wf Jal), genIJal)
        ; ( (get_freq t wf Alloc), genIAlloc t)
        ; ( (get_freq t wf Halt), (returnGen [IHalt]))
        ; ( (get_freq t wf Return), (returnGen [IReturn]))
        ; ( (get_freq t wf Nop) ,(returnGen [INop]))
      ].

Definition gen_procedure
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
           (pid : Procedure_id)
           (next_label : nat) : G Intermediate.Machine.code :=
  
  let fix gen_proc_rec proc len first_lbl lbl :=
      match len with
      | O =>
        do! p <- gen_proc_with_labels proc (get_missing_labels proc);
          returnGen (p ++ [IReturn])%list
      | S len' =>
        do! il <- gen_instr t wf cag dag first_lbl lbl pi buffers cid pid;
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

Definition max_label (procs : BinNatMap.t Intermediate.Machine.code) :=
  List.fold_left
    (fun acc '(_,proc)  =>
       (List.fold_left (fun acc' i =>
                          match i with
                          | ILabel l => if (Nat.ltb acc' l) then l else acc'
                          | _ => acc'
                          end
                       ) proc acc)
    ) (BinNatMap.elements procs) 1%nat.

Definition gen_procedures
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (N * (nat+list value))))
  : G (BinNatMap.t (BinNatMap.t Intermediate.Machine.code)) :=

  foldGen
    (fun acc '(cid, comp_interface)  =>
       do! proc_map <- (
           let '(lexp,limp) := comp_interface in
           foldGen
             (fun acc pid =>
                do! proc <- gen_procedure t wf cag dag pi buffers cid pid ((max_label acc) + 1)%nat;
                  returnGen (BinNatMap.add pid proc acc)
             ) lexp (BinNatMap.empty Intermediate.Machine.code));
         
         (* check add labels as needed for IJal *)
         let all_decl_labels := List.fold_left
                                  (fun acc elt => (acc ++ elt)%list )
                                  (List.map (fun p => delared_labels_in_proc (snd p))
                                            (BinNatMap.elements proc_map))
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
                                 (BinNatMap.elements proc_map))
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
         match BinNatMap.elements proc_map with
         | nil => returnGen (BinNatMap.add cid proc_map acc)
         | (pid,code)::_ => returnGen (BinNatMap.add cid
                                                    (BinNatMap.add
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
    ) (BinNatMap.elements  pi)
    (BinNatMap.empty (BinNatMap.t Intermediate.Machine.code))
.

Definition gen_main_pid (pi : prog_int) : G (N) :=
  match BinNatMap.find (N.of_nat Component.main) pi with
  | None => returnGen (N.of_nat Procedure.main)
  | Some cint =>    
    returnGen
      ((List.fold_left
          (fun acc elt => if (N.leb acc elt) then elt else acc)
          (fst cint)
          (N.of_nat Procedure.main))+1)%N
  end.

Definition convert_program_interface (pi : prog_int) : Program.interface :=
  BinNatMap.fold
    (fun cid cint acc =>
       let '(lexp,limp) := cint in
       setm acc (N.to_nat cid) (Component.mkCompInterface
                                  (list2fset (List.map N.to_nat lexp))
                                  (list2fset (List.map
                                                (fun '(c,p) => (N.to_nat c,N.to_nat p))
                                                limp)))
    ) pi (emptym).

Definition convert_procedures (all : BinNatMap.t (BinNatMap.t Intermediate.Machine.code))
  : NMap (NMap Intermediate.Machine.code) :=
  BinNatMap.fold
    (fun cid pm (acc : NMap ( NMap Intermediate.Machine.code ) ) =>
       setm acc (N.to_nat cid)
            (
              BinNatMap.fold
                (fun pid pcode (acc1 : NMap Intermediate.Machine.code) =>
                   setm acc1 (N.to_nat pid) pcode)
                pm (emptym)
            )
    ) all (emptym).

Definition convert_buffers (buffs : BinNatMap.t  (list (N * (nat+list value))))
  : NMap {fmap Block.id -> nat + list value} :=
  BinNatMap.fold
    (fun cid b acc =>
       setm acc (N.to_nat cid)
            (list2fmap
               (
                 List.map (fun '(bid,v) => (N.to_nat bid,v) ) b
               )
            )
    (* (List.map (fun '(id,s)=>(N.to_nat id,s)) b)) *)
    )
    buffs emptym.

Definition gen_main_code
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (N * (nat+list value))))
           (all : BinNatMap.t (BinNatMap.t Intermediate.Machine.code))
           (pid : Procedure_id) :=

  do! p' <-
    match BinNatMap.find (N.of_nat Component.main) all with
    | None =>
      gen_procedure t wf cag dag pi buffers (N.of_nat Component.main) pid 1%nat
    | Some pmap =>
      match BinNatMap.find pid pmap with
      | None => (* must generate code for this procedure *)
        gen_procedure t wf cag dag pi buffers
                      (N.of_nat Component.main)
                      pid (max_label pmap )
      | Some l => returnGen l
      end
    end;
        (* check add labels as needed for IJal *)
    let all_decl_labels := delared_labels_in_proc p' in
    let uses := List.map
                  (fun i =>
                     match i with
                     | IJal l => l
                     | _ => 1%nat (* this is not happening *)
                     end
                  )
                  (List.filter (fun i => match i with
                                         | IJal _  => true
                                         | _ => false
                                         end )
                               p' ) in
    let lbls := List.nodup label_eq_dec
                           (List.fold_left (fun acc elt =>
                                              (List.remove label_eq_dec elt acc))
                                           all_decl_labels uses) in
    let pmap := match BinNatMap.find (N.of_nat Component.main) all with
                | None => BinNatMap.empty (code)
                | Some m => m
                end in
    let p := List.map
               (fun i => match i with
                         | IReturn => IHalt
                         | _ => i
                         end
               ) p' in
    returnGen 
      ( match BinNatMap.elements pmap with
        | nil =>
          (BinNatMap.add
             (N.of_nat Component.main)
             (BinNatMap.add
                pid
                ((List.map (fun l => ILabel l) lbls) ++ p)%list
                pmap)
             all)
        | (pid',code)::_ =>
          let code' := ((List.map (fun l => ILabel l) lbls) ++ code)%list in
          BinNatMap.add (N.of_nat Component.main)
                        (BinNatMap.add
                           pid
                           p
                           (BinNatMap.add pid' code' pmap)
                        ) all
        end).


Definition genIntermediateProgram
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (max_components : bool)
  : G Intermediate.program :=

  do! n <-
      (if max_components
      then returnGen (N.to_nat (SFI.COMP_MAX-1)%N)
      else choose (1%nat, (N.to_nat (SFI.COMP_MAX-1)%N)));
    let cids := N_list n in

    do! pi <- (gen_program_interface cids);

      do! buffers <- gen_buffers cids;
      do! procs <- gen_procedures t wf cag dag pi buffers;
      do! main <- gen_main_pid pi;
      do! all_procs <- gen_main_code t wf cag dag pi buffers procs main;
      returnGen {|
          Intermediate.prog_interface := convert_program_interface pi;
          Intermediate.prog_procedures := convert_procedures all_procs;
          Intermediate.prog_buffers := convert_buffers buffers;
          Intermediate.prog_main := Some (N.to_nat main)
        |}.
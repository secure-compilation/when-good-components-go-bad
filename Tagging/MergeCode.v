Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Traces.
(* TL TODO: Ariths Export is a pain *)
Require Import I2MP.Tmp.
Require Import Util.

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From extructures Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import MicroPolicies.LRC.
Require Import Linearize.
Require Import Tags.
Require Import Tagging.Language.
Require Import Tagging.LinearizeCompartments.
Import Tags.Register.
Import Tagging.Memory.Memory.

Require Import Lib.Extra.
Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


Section Tags.

Inductive cell_tag := Data : Component.id -> cell_tag | Code : Component.id -> code_tag -> cell_tag.

Definition def_code_tag c : cell_tag := Code c None.

End Tags.


Section Values.


  Inductive value : Type :=
  | Int : Z -> value
  | Ptr : Pointer.t -> value
  | Undef : value
  | Instr : instr -> value.

  Record tvalue := MCVal
   { vtag : value_tag;
     val : value }.

  Definition to_tvalue (v : value) : tvalue := MCVal Other v.

  Definition tUndef := to_tvalue Undef.

  Record mem_cell := MCell
   { tval : tvalue ;
     ctag : cell_tag }.

Definition val_to_ival (v : Tags.value) : value := match v with
  | Tags.Int Z => Int Z
  | Tags.Ptr p => Ptr p
  | Tags.Undef => Undef
end.


  Definition to_tagged_cell (c : Component.id) (v : value) : mem_cell := MCell (to_tvalue v) (Data c).

  Definition to_tagged_block (c : Component.id) (l : list value) : list mem_cell := 
    map (to_tagged_cell c) l.

Definition eval_binop (op : binop) (v1 v2 : value) : value :=
  match op, v1, v2 with
  (* natural numbers *)
  | Add,   Int n1, Int n2 => Int (n1 + n2)
  | Minus, Int n1, Int n2 => Int (n1 - n2)
  | Mul,   Int n1, Int n2 => Int (n1 * n2)
  | Eq,    Int n1, Int n2 => Int (Util.Z.of_bool (n1  =? n2)%Z)
  | Leq,   Int n1, Int n2 => Int (Util.Z.of_bool (n1 <=? n2)%Z)
  (* pointer arithmetic *)
  | Add,   Ptr p,  Int n  => Ptr (Pointer.add p n)
  | Add,   Int n,  Ptr p  => Ptr (Pointer.add p n)
  | Minus, Ptr p1, Ptr p2 => let '(b1, o1) := p1 in
                             let '(b2, o2) := p2 in
                             if (Nat.eqb b1 b2) then
                               Int (o1 - o2)
                             else
                               Undef
  | Minus, Ptr p,  Int n  => Ptr (Pointer.sub p n)
  | Eq,    Ptr p1, Ptr p2 => Int (Util.Z.of_bool (Pointer.eq p1 p2))
  | Leq,   Ptr p1, Ptr p2 => match Pointer.leq p1 p2 with
                             | Some res => Int (Util.Z.of_bool res)
                             | None     => Undef
                             end
  (* undefined operations *)
  | _,     _,       _       => Undef
  end.

End Values.


Module Register.
  Definition t : Type := NMap tvalue.

  Definition to_nat (r : register) : nat :=
    match r with
    | R_ONE  => 0
    | R_COM  => 1
    | R_AUX1 => 2
    | R_AUX2 => 3
    | R_RA   => 4
    | R_SP   => 5
    | R_ARG  => 6
    end.




  Definition init :=
    mkfmap [(to_nat R_ONE, tUndef);
            (to_nat R_COM, tUndef);
            (to_nat R_AUX1, tUndef);
            (to_nat R_AUX2, tUndef);
            (to_nat R_RA, tUndef);
            (to_nat R_SP, tUndef);
            (to_nat R_ARG, tUndef)].

  Definition get (r : register) (regs : t) : tvalue :=
    match getm regs (to_nat r) with
    | Some v => v
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => tUndef
    end.

  Definition get_value (r : register) (regs : t) : value :=
    match getm regs (to_nat r) with
    | Some tv => val tv
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition get_tag (r : register) (regs : t) : option value_tag :=
    match getm regs (to_nat r) with
    | Some tv => Some (vtag tv)
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => None
    end.

  Definition set (r : register) (val : value) (vt : value_tag) (regs : t) : t :=
    setm regs (to_nat r) (MCVal vt val).

  Definition tset (r : register) (tval : tvalue) (regs : t) : t :=
    setm regs (to_nat r) tval.

Definition invalidate regs := 
[fmap (Register.to_nat R_ONE, tUndef);(Register.to_nat R_COM, Register.get R_COM regs);
      (Register.to_nat R_AUX1, tUndef);(Register.to_nat R_AUX2, tUndef);(Register.to_nat R_RA, Register.get R_RA regs);
      (Register.to_nat R_SP, tUndef);(Register.to_nat R_ARG, tUndef)].

  Lemma invalidate_eq : forall regs1 regs2,
    get R_COM regs1 = get R_COM regs2 ->
    get R_RA regs1 = get R_RA regs2 ->
    invalidate regs1 = invalidate regs2.
  Proof.
    intros regs1 regs2 Hregs Hregs'.
    unfold invalidate.
     congruence.
  Qed.
End Register.




Module Memory. (* : AbstractComponentMemory.*)
  Definition block := list mem_cell.

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := mem.


  Definition prealloc (bufs: {fmap Block.id -> (Component.id * (nat + list value))}) : t :=
    let init_block x := match x with
                        | (c,inl size) => repeat (to_tagged_cell c Undef) size
                        | (c,inr chunk) => to_tagged_block c chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (extructures.fmap.domm bufs) 0) |}.


  Definition prealloc_c C (bufs: {fmap Block.id -> ((nat + list value))}) : t :=
    let init_block x := match x with
                        | inl size => repeat (to_tagged_cell C Undef) size
                        | inr chunk => to_tagged_block C chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (extructures.fmap.domm bufs) 0) |}.


  Definition empty :=
    {| content := emptym; nextblock := 0 |}.

  Definition reserve_block (m: t) : t * Block.id :=
    ({| content := content m; nextblock := (1 + nextblock m)%nat |},
     nextblock m).

  Definition alloc (c : Component.id) m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat (to_tagged_cell c Undef) size in
    ({| content := setm (content m) fresh_block chunk;
        nextblock := (1 + nextblock m) |},
     fresh_block).



  Definition load_b m b i : option mem_cell :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then nth_error chunk (Z.to_nat i)
      else None
    | None => None
    end.

  Definition load m ptr : option mem_cell := load_b m (Pointer.block ptr) (Pointer.offset ptr).

  Definition store_b m b i mcl : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then
        match list_upd chunk (Z.to_nat i) mcl with
        | Some chunk' =>
          Some {| content := setm (content m) b chunk';
                  nextblock := nextblock m |}
        | _ => None
        end
      else None
    | None => None
    end.

Check store_b.

  Definition store m ptr v : option mem := store_b m (Pointer.block ptr) (Pointer.offset ptr) v.

End Memory.


Definition codeless : Type := Memory.t * Register.t * Pointer.t * pc_tag.

Fixpoint find_label (chunk : Memory.block) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | {| tval := {| val := Instr (TrLabel l') |} |} :: c' =>
        if Nat.eqb l (label_of l') then
          Some o
        else
          aux c' (1 + o)%Z
      | _ :: c' =>
        aux c' (1 + o)%Z
      end
  in aux chunk 0%Z.


Definition find_label_in_block (m : Memory.t) (b : Block.id) (l : label) : option Pointer.t :=
  match (Memory.content m) b with
  | Some chunk =>
      match find_label chunk l with
      | Some offset => Some (b, offset)
      | None => None
      end
  | None => None
end.

Fixpoint find_label_in_mem_helper
         (blocks : seq Block.id) (m : Memory.t) (l: label) : option Pointer.t :=
  match blocks with
   | [] => None
   | block_id :: blocks' => match find_label_in_block m block_id l with
      | None => find_label_in_mem_helper blocks' m l
      | x => x
    end
  end.

Definition find_label_in_mem (m : Memory.t) (l : label) : option Pointer.t :=
  find_label_in_mem_helper (extructures.fmap.domm (Memory.content m)) m l.


Fixpoint find_plabel (chunk : Memory.block) (c : Component.id) (p : Procedure.id) : option Z :=
  let fix aux chunk o :=
      match chunk with
      | [] => None
      | {| tval := {| val := Instr (TrLabel (_,Some (c',p'))) |} |} :: chunk' =>
        if Nat.eqb c c' && Nat.eqb p p' then
          Some o
        else
          aux chunk' (1 + o)%Z
      | _ :: chunk' =>
        aux chunk' (1 + o)%Z
      end
  in aux chunk 0%Z.




Fixpoint find_plabel_in_mem_helper (m : Memory.t) (blocks : seq Block.id) (c : Component.id) (p : Procedure.id) : option Pointer.t :=
  match blocks with
   | [] => None
   | block_id :: blocks' => 
          match (Memory.content m) block_id with
            | None => find_plabel_in_mem_helper m blocks' c p
            | Some b => 
              match find_plabel b c p with
              | None => find_plabel_in_mem_helper m blocks' c p
              | Some z => Some (block_id,z)
              end
          end
  end.


Definition find_plabel_in_mem (m : Memory.t) (c : Component.id) (p : Procedure.id) : option Pointer.t :=
  find_plabel_in_mem_helper m (extructures.fmap.domm (Memory.content m)) c p.






Open Scope monad_scope.
(* remove locality of labels LATER *)


Definition get_instr (mc : mem_cell) : option (instr * Component.id) := 
 match ctag mc, val (tval mc) with
  | Code c _, Instr i => Some (i,c)
  | _, _ => None
 end.

Definition pc_fall (pc : Pointer.t) (mem : Memory.t) (c : Component.id) := 
 do mc <- Memory.load mem (Pointer.add pc 1);
 match ctag mc with
    | Code c' _ => if Nat.eqb c c' then ret (Pointer.add pc 1)
                    else None
    | _ => None
 end.

Print Register.t.

Definition eval_step (s: codeless) : option (trace * codeless) :=
  let '(mem, regs, pc, pct) := s in
  (* fetch the next instruction to execute *)
  do mc <- Memory.load mem pc;
  do (instr,comp) <- get_instr mc;
    match instr with
    | TrLabel _ => do pc' <- pc_fall pc mem comp;
      ret (E0, (mem, regs, pc', pct))
    | TrNop => do pc' <- pc_fall pc mem comp;
      ret (E0, (mem, regs, pc', pct))
    | TrConst v r => do pc' <- pc_fall pc mem comp;
      let regs' := Register.set r (val_to_ival v) Other regs in
      ret (E0, (mem, regs', pc', pct))
    | TrMov r1 r2 => do pc' <- pc_fall pc mem comp;
      let tval := Register.get r1 regs in
      let regs' := Register.tset r2 tval regs in
      ret (E0, (mem, regs', pc', pct))
    | TrBinOp op r1 r2 r3 => do pc' <- pc_fall pc mem comp;
      let tv1 := Register.get r1 regs in
      let tv2 := Register.get r2 regs in
      let result := eval_binop op (val tv1) (val tv2) in
      let regs' := Register.set r3 result Other regs in
      (* Check to ensure that the value is not protected (return adress) *)
      match (vtag tv1,vtag tv2) with
        | (Other,Other) => ret (E0, (mem, regs', pc', pct))
        | (_,_) => None
      end
    | TrLoad r1 r2 => do pc' <- pc_fall pc mem comp;
      let tv := Register.get r1 regs in
      match (val tv, vtag tv) with
      | (Ptr ptr,Other) =>
          do (v,c) <- Memory.load mem ptr;
        if Component.eqb c comp then
          match (vtag v) with
            | Other =>
              let regs' := Register.tset r2 v regs in
              ret (E0, (mem, regs', pc', pct))
            | Ret n => 
              let regs' := Register.tset r2 v regs in
              do mem' <- Memory.store mem ptr (MCell tUndef (Data comp));
              ret (E0, (mem', regs', pc', pct))
          end
        else
          None
      | _ => None
      end
    | TrStore r1 r2 => do pc' <- pc_fall pc mem comp;
      let tv := Register.get r1 regs in
      match (val tv,vtag tv) with
      | (Ptr ptr,Other) => 
          do (_,tag) <- Memory.load mem ptr;
          if Component.eqb tag (comp) then 
            let tv2 := Register.get r2 regs in
            match (vtag tv2) with
            | Other =>
              do mem' <- Memory.store mem ptr (MCell (Register.get r2 regs) (Data comp));
              ret (E0, (mem', regs, pc', pct))
            | Ret n => 
              do mem' <- Memory.store mem ptr (MCell (Register.get r2 regs) (Data comp));
              let regs' := Register.tset r2 tUndef regs in
              ret (E0, (mem', regs', pc', pct))
            end
          else
            None
      | _ => None
      end
    | TrAlloc rptr rsize => do pc' <- pc_fall pc mem comp;
      let tv := Register.get rsize regs in
      match (val tv, vtag tv) with
      | (Int size,Other) =>
        if (size <=? 0) % Z then
          None
        else
          let (mem', block) := Memory.alloc (comp) mem (Z.to_nat size) in
          let regs' := Register.set rptr (Ptr (block,0%Z)) Other regs in
          ret (E0, (mem', regs', pc', pct))
      | _ => None
      end
 | _ => None end.
    | TrBnz r l => let tv := Register.get r regs in
      match (val tv, vtag tv) with
      | (Int 0,Other) => do pc' <- pc_fall pc mem comp;
        ret (E0, (mem, regs, pc', pct))
      | (Int val,Other) =>
        do pc' <- find_label_in_code cde l;
        if Component.eqb (comp) (?????Pointer.block pc') then 
          ret (E0, (mem, regs, pc', pct))
        else
          None
      | _ => None
      end
    | TrJump r => let tv := Register.get r regs in
      match (val tv, vtag tv) with
      | (Ptr pc',Other) =>
        if Component.eqb (????Pointer.block pc') (comp) then
          ret (E0, (mem, regs, pc', pct))
        else
          None
      | (Ptr pc', Ret n) => 
        do pctag' <- check_dec_pc_tag pct n;
        if  (Component.eqb (Pointer.block pc') (Pointer.block pc)) then
          None
        else
         if (Pointer.offset pc' <? 0) % Z then
            None
         else
            do C_code' <- cde (Pointer.block pc');
            do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
            let tvcom := Register.get R_COM regs in
            match (val tvcom,vtag tvcom) with
            | (Int rcomval,Other) =>
              let t := [ERet (Pointer.block pc) rcomval (Pointer.block pc')] in
              ret (t, (mem, invalidate regs, pc', pctag'))
            | _ => None
            end
      | _ => None
      end
    | TrJalNat l => 
      do pc' <- find_label_in_comp cde (Pointer.block pc) l;
      if Component.eqb (Pointer.block pc) (Pointer.block pc') then 
        let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) Other regs in
        ret (E0, (mem, regs', pc', pct))
      else
        None
    | TrJalProc (c',pid) =>
      match find_plabel_in_code cde c' pid with 
      | Some pc' => 
       if (Pointer.offset pc' <? 0) % Z then
         None
       else
       if negb (Component.eqb c' (Pointer.block pc')) then
        None
       else
        if Component.eqb c' (Pointer.block pc) then
          let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) Other regs in
          ret (E0, (mem, regs', pc', pct))
        else 
           do C_code' <- cde (Pointer.block pc');
           do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
           match tni with
            | Some (pid',lc) => 
              if Procedure.eqb pid pid' then 
               if check_comp_belongs_b (Pointer.block pc) lc then
                 let tvrcom := Register.get R_COM regs in
                 match (val tvrcom,vtag tvrcom) with
                 | (Int rcomval,Other) =>
                     let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) (inc_ret pct) regs in
                     let t := [ECall (Pointer.block pc) pid rcomval (Pointer.block pc')] in
                     ret (t, (mem, invalidate regs', pc', inc_pc_tag pct))
                 | _ => None
                 end
               else None
              else None
             | _ => None
            end
       | None => None
      end
    | _ => None
end.



Fixpoint execN (n: nat) (cde: code) (st: stackless) : option Z + nat :=
  match n with
  | O => inr 3
  | S n' =>
    match eval_step cde st with
    | None =>
      let '(_, regs, _, _) := st in
      let tvrcom := Register.get R_COM regs in
      match (val tvrcom,vtag tvrcom) with
      | (Int i,Other) => inl (Some i)
      | (_,Other) => inr 4
      | _ => inr 77
      end
    | Some (_, st') => execN n' cde st'
    end
  end.


Record program : Type := mkProg {
    prog_interface : Program.interface;
    prog_code : code;
    prog_buffers : {fmap Block.id -> Component.id * (nat + seq value)};
    prog_main : bool }.









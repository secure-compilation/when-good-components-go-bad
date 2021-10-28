Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Common.Traces.
(* TL TODO: Ariths Export is a pain *)
Require Import I2MP.Tmp.

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From extructures Require Import fmap fset.

Require Import Intermediate.Machine.
(* Require Import Intermediate.GlobalEnv.
Require Import MicroPolicies.LRC.
Require Import Tmp.
Require Import Linearize. *)
Require Import Tags.
Import Tags.Register.
Require Import Tagging.Memory.
Import Tagging.Memory.Memory.

Require Import Lib.Extra.
Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.

Definition proc_label : Set := Component.id * Procedure.id.

Definition plabel : Set := label * option proc_label.

Definition label_of (pl : plabel) : label := let (n,_) := pl in n.

Variant instr :=
| TrNop : instr
| TrLabel : plabel -> instr
(* register operations *)
| TrConst : value -> register -> instr
| TrMov : register -> register -> instr
| TrBinOp : binop -> register -> register -> register -> instr
(* memory operations *)
| TrLoad : register -> register -> instr
| TrStore : register -> register -> instr
| TrAlloc : register -> register -> instr
(* conditional and unconditional jumps *)
| TrBnz : register -> label -> instr
| TrJump : register -> instr
| TrJalNat : label -> instr
| TrJalProc : proc_label -> instr
(* termination *)
| TrHalt : instr.

Definition code := NMap (seq (instr * code_tag)).



(* 
Definition executing (cde : code) (pc : Pointer.t) (i : instr) (tg : code_tag) (c : Component.id)  : Prop := 
    exists C_code,
    Pointer.component pc = c /\
    cde c = Some C_code /\
    (Pointer.offset pc >= 0) % Z /\
    nth_error C_code (Z.to_nat (Pointer.offset pc)) = Some (i,tg). *)


Fixpoint check_comp_belongs (c : Component.id) (l : seq Component.id) : Prop := match l with 
 | nil => False
 | c' :: l' => c = c' \/ check_comp_belongs c l'
end.

Fixpoint check_comp_belongs_b (c : Component.id) (l : seq Component.id) : bool := match l with 
 | nil => false
 | c' :: l' => if Nat.eqb c c' then true else check_comp_belongs_b c l'
end.


(* Stackless state *)

Notation BigPointer := Common.Values.Pointer.t.

Definition stackless : Type := Memory.t * Register.t * Pointer.t * pc_tag.

Fixpoint find_label (cd : seq (instr * code_tag)) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | (TrLabel l',_) :: c' =>
        if Nat.eqb l (label_of l') then
          Some o
        else
          aux c' (1 + o)%Z
      | _ :: c' =>
        aux c' (1 + o)%Z
      end
  in aux cd 0%Z.



Definition find_label_in_comp (cde : code) (c : Component.id) (l : label) : option Pointer.t :=
  match cde c with
  | Some C_comp =>
      match find_label C_comp l with
      | Some offset => Some (c, offset)
      | None => None
      end
  | None => None
end.

Fixpoint find_label_in_code_helper
         (cde : code) (comps: list (Component.id * (seq (instr * code_tag))))
         (l: label) : option Pointer.t :=
  match comps with
   | [] => None
   | (comp_id,comp_code) :: comps' => match find_label_in_comp cde comp_id l with
      | None => find_label_in_code_helper cde comps' l
      | x => x
    end
  end.

Definition find_label_in_code (cde : code) (l : label) : option Pointer.t :=
  find_label_in_code_helper cde (elementsm cde) l.


Fixpoint find_plabel (cd : seq (instr * code_tag)) (c : Component.id) (p : Procedure.id) : option Z :=
  let fix aux cd o :=
      match cd with
      | [] => None
      | (TrLabel (_,Some (c',p')),_) :: cd' =>
        if Nat.eqb c c' && Nat.eqb p p' then
          Some o
        else
          aux cd' (1 + o)%Z
      | _ :: cd' =>
        aux cd' (1 + o)%Z
      end
  in aux cd 0%Z.


Definition find_plabel_in_code (cde : code) (c : Component.id) (p : Procedure.id) : option Pointer.t :=
  match cde c with
  | Some C_comp =>
      match find_plabel C_comp c p with
      | Some offset => Some (c, offset)
      | None => None
      end
  | None => None
end.



(* 
Inductive check_pc : code -> Pointer.t -> code_tag -> Prop :=
| PcFall : forall cde pc tg i tni c, 
    executing cde (Pointer.inc pc) i tni c ->
    (* color tg = c -> *) check_pc cde pc tg.


Inductive check_pc_jump : code -> mem_tag -> Pointer.t -> Component.id -> Prop :=
 |PcJump : forall cde tg pc' i tni c c0,
    executing cde (pc') i tni c ->
    Pointer.component pc' = c0 -> check_pc_jump cde tg pc' c0.

Inductive check_pc_call : Component.id -> code_tag -> Procedure.id -> Prop := 
 | PcCall : forall c tni pid l, (* color ti = c ->  *)
  tni = Some (pid,l) -> 
  check_comp_belongs c l -> check_pc_call c tni pid.


(* missing stuff *)
Inductive check_pc_ret : Component.id -> code_tag -> Prop := 
 | PcRet : forall c tni pid l, (* color ti = c ->  *)
  tni = Some (pid,l) -> 
  check_comp_belongs c l -> check_pc_ret c tni. *)


(*** !IMPORTANT: PROTECT Return Adress registers with tags in a 'linear' way,
                 so that they can't be copied ***)
(* well-formedness & interfaces *)
(* TODO Add Jal for (c,pid) type (TrJalProc), but intra compartment ?? 
todo? (in order to reduce UB), allow TrJalNat to different components *)




Open Scope monad_scope.
(* remove locality of labels LATER *)


Definition eval_step (cde: code) (s: stackless) : option (trace * stackless) :=
  let '(mem, regs, pc, pct) := s in
  (* fetch the next instruction to execute *)
  if (Pointer.offset pc <? 0) % Z then
    None
  else
      do C_code <- cde (Pointer.block pc);
      do (instr,tag) <- nth_error C_code (Z.to_nat (Pointer.offset pc));
    (* HERE, are we ok enforcing this this way?*)
    let comp := Pointer.block pc in
    match instr with
    | TrLabel _ =>
      ret (E0, (mem, regs, Pointer.inc pc, pct))
    | TrNop =>
      ret (E0, (mem, regs, Pointer.inc pc, pct))
    | TrConst v r =>
      let regs' := Register.set r v Other regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrMov r1 r2 => 
      let tval := Register.get r1 regs in
      let regs' := Register.tset r2 tval regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrBinOp op r1 r2 r3 =>
      let tv1 := Register.get r1 regs in
      let tv2 := Register.get r2 regs in
      let result := eval_binop op (val tv1) (val tv2) in
      let regs' := Register.set r3 result Other regs in
      (* Check to ensure that the value is not protected (return adress) *)
      match (vtag tv1,vtag tv2) with
        | (Other,Other) => ret (E0, (mem, regs', Pointer.inc pc, pct))
        | (_,_) => None
      end
    | TrLoad r1 r2 => let tv := Register.get r1 regs in
      match (val tv, vtag tv) with
      | (Ptr ptr,Other) =>
          do (v,c) <- Memory.load mem ptr;
        if Component.eqb c comp then
          match (vtag v) with
            | Other =>
              let regs' := Register.tset r2 v regs in
              ret (E0, (mem, regs', Pointer.inc pc, pct))
            | Ret n => 
              let regs' := Register.tset r2 v regs in
              do mem' <- Memory.store mem ptr (tUndef,Pointer.block pc);
              ret (E0, (mem', regs', Pointer.inc pc, pct))
          end
        else
          None
      | _ => None
      end
    | TrStore r1 r2 => let tv := Register.get r1 regs in
      match (val tv,vtag tv) with
      | (Ptr ptr,Other) => 
          do (_,tag) <- Memory.load mem ptr;
          if Component.eqb tag (Pointer.block pc) then 
            let tv2 := Register.get r2 regs in
            match (vtag tv2) with
            | Other =>
              do mem' <- Memory.store mem ptr (Register.get r2 regs,comp);
              ret (E0, (mem', regs, Pointer.inc pc, pct))
            | Ret n => 
              do mem' <- Memory.store mem ptr (Register.get r2 regs,comp);
              let regs' := Register.tset r2 tUndef regs in
              ret (E0, (mem', regs', Pointer.inc pc, pct))
            end
          else
            None
      | _ => None
      end
    | TrAlloc rptr rsize => let tv := Register.get rsize regs in
      match (val tv, vtag tv) with
      | (Int size,Other) =>
        if (size <=? 0) % Z then
          None
        else
          let (mem', block) := Memory.alloc (Pointer.block pc) mem (Z.to_nat size) in
          let regs' := Register.set rptr (Ptr (block,0%Z)) Other regs in
          ret (E0, (mem', regs', Pointer.inc pc, pct))
      | _ => None
      end
    | TrBnz r l => let tv := Register.get r regs in
      match (val tv, vtag tv) with
      | (Int 0,Other) =>
        ret (E0, (mem, regs, Pointer.inc pc, pct))
      | (Int val,Other) =>
        do pc' <- find_label_in_code cde l;
        if Component.eqb (Pointer.block pc) (Pointer.block pc') then 
          ret (E0, (mem, regs, pc', pct))
        else
          None
      | _ => None
      end
    | TrJump r => let tv := Register.get r regs in
      match (val tv, vtag tv) with
      | (Ptr pc',Other) =>
        if Component.eqb (Pointer.block pc') (Pointer.block pc) then
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


(* Compile buffers *)

Definition old_val := Common.Values.value.

Definition inter_bufs := NMap {fmap Block.id -> nat + seq old_val}.


Definition tag_buffers (pb : NMap {fmap Block.id -> nat + seq old_val}) : NMap {fmap Block.id -> Component.id * (nat + seq old_val)}:=
 mapim (fun C f => mapim (fun b k => (C,k)) f) pb.

Fixpoint clean_seq {T} (l : seq (option T)) : seq T := match l with
 | [] => []
 | None :: ls => clean_seq ls
 | (Some x) :: ls => x :: clean_seq ls
end.


Definition fmap_rekeying {T : ordType} {T' : ordType} {S : Type} (f : {fmap T -> S}) (r : {fmap T -> T'}) : {fmap T' -> S} := 
 let dom := clean_seq (map r (extructures.fmap.domm f)) in
 let fn := fun x => match ((invm r) x) with None => None | Some y => f y end in
mkfmapfp fn dom.

Definition re_block_id C (pb : NMap {fmap Block.id -> Component.id * (nat + seq old_val)}) (block_renum : {fmap (Component.id * Block.id) -> Block.id})  : option {fmap Block.id -> Component.id * (nat + seq old_val)}:= 
match pb C with
 | None => None
 | Some f => match ((currym block_renum) C) with None => None | Some g => Some (fmap_rekeying f g) end
end.


Fixpoint union_mem {T : ordType} {T' : ordType} {S : Type} l (f : T -> option {fmap T' -> S}) := match l with [] => emptym | x :: xs => 
match (f x) with None => (union_mem xs f)
 | Some y => unionm y (union_mem xs f) end
end.

Definition compile_buffs_renum (pb: NMap {fmap Block.id -> Component.id * (nat + seq old_val)}) (block_renum : {fmap (Component.id * Block.id) -> Block.id}) :=
union_mem (extructures.fmap.domm pb) (fun C => re_block_id C pb block_renum).


Fixpoint add_key_aux {S} {T} (x : S) (l: seq T) : seq (S * T) := match l with [] => [] | y :: ys => (x,y) :: (add_key_aux x ys) end.

Definition domm_to_seq {S} {T : ordType} {T' : ordType} (f : {fmap T' -> {fmap T -> S}}) (x : T') : seq T := match (f x) with None => [] | Some g => extructures.fmap.domm g end.

Definition make_block_renum_fmap (pb: NMap {fmap Block.id -> nat + seq old_val}) (block_renum : Component.id -> Block.id -> Block.id) :=
mkfmapf (fun x => match x with (C,b) => block_renum C b end) (foldr (fun C l => (add_key_aux C (domm_to_seq pb C)) ++ l) [] (extructures.fmap.domm pb)) .


Definition max_block (m: NMap {fmap Block.id -> nat + seq old_val}) := let component_max_block map := foldl Nat.max 0 (extructures.fmap.domm map) in 
 let max_block_ids := [seq component_max_block i | i <- codomm' m] in
foldl Init.Nat.max 0 max_block_ids + 1.



Definition fun_renum_block (m: NMap {fmap Block.id -> nat + seq old_val}) C b := C*(max_block m)+b.




Definition ptr_to_ptr (ptr : BigPointer) (block_renum : Component.id -> Block.id -> Block.id) : Pointer.t := let '(c,b,o) := ptr in (block_renum c b,o).

Definition val_to_val m (v : Common.Values.value) : value := match v with
  | Common.Values.Int z => Int z
  | Common.Values.Ptr ptr => Ptr (ptr_to_ptr ptr ((fun_renum_block m)))
  | Common.Values.Undef => Undef
end.

Definition compile_buffs_aux (m: NMap {fmap Block.id -> nat + seq old_val}) := compile_buffs_renum (tag_buffers m) (make_block_renum_fmap m (fun_renum_block m)).

Definition compile_buffs (m: NMap {fmap Block.id -> nat + seq old_val}) := mapm (fun x => match x with
 | (C,inl n) => (C,inl n)
 | (C,inr l) => (C,inr (map (val_to_val m) l))
  end) (compile_buffs_aux m).




(* Alloc initial memory *)



Definition alloc_static_buffers p := prealloc (prog_buffers p).
Definition prepare_initial_memory := alloc_static_buffers.

Definition run_transitional fuel p :=
    let mem := prepare_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code (prog_code p) Component.main Procedure.main) with
    | Some pc =>
      execN fuel (prog_code p) (mem,regs, pc, Level 0)
    | None => inr 5
end.








Section Semantics.
  Variable p: program.

Inductive step (cde : code) (s: stackless) ( t :trace) ( s' : stackless) : Prop :=  By_def.

(*  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p. *)

  Definition sem :=
    @Semantics_gen stackless code step (fun _ => True) (fun _ => True) (prog_code p).
End Semantics.
(* 
Check Semantics_gen.


Print RobustImp.CompCert.Smallstep.initial_state.
Locate prepare_global_env.
  Let G := prepare_global_env p.

  Definition sem :=
    @Semantics_gen state global_env step (initial_state p) (final_state G) G.

!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)


(* temporarily removed
Inductive step (cde : code) : stackless -> trace -> stackless -> Prop :=
| Nop: forall st mem regs pc tg c pct,
    executing cde pc TrNop tg c ->
    check_pc cde pc tg ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, Pointer.inc pc, pct)

| Label: forall st mem regs pc tg c pct l,
    executing cde pc (TrLabel l) tg c ->
    check_pc cde pc tg ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, Pointer.inc pc, pct)

| Const: forall st mem regs regs' pc tg c pct r v,
    executing cde pc (TrConst  v r) tg c ->
    check_pc cde pc tg ->
    Register.set r (imm_to_val v) regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| Mov: forall st mem regs regs' pc tg c pct r1 r2,
    executing cde pc (TrMov r1 r2) tg c ->
    check_pc cde pc tg ->
    Register.set r2 (Register.get r1 regs) regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| BinOp: forall st mem regs regs' pc tg c pct r1 r2 r3 op,
    executing cde pc (TrBinOp op r1 r2 r3) tg c ->
    check_pc cde pc tg ->
    let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
    Register.set r3 result regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| Load: forall st mem regs regs' pc tg c pct r1 r2 ptr v,
    executing cde pc (TrLoad r1 r2) tg c ->
    check_pc cde pc tg ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr = c ->
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| Store: forall st mem mem' regs pc tg c pct ptr r1 r2,
    executing cde pc (TrStore r1 r2) tg c ->
    check_pc cde pc tg ->
    Register.get r1 regs = Ptr ptr ->
    Pointer.component ptr =  c ->
    Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem', regs, Pointer.inc pc, pct)

| Jal: forall st mem regs regs' pc tg c pct pc' l,
    executing cde pc (TrJalNat l) tg c ->
(*   check_pc cde pc tg ->*)
(*    find_label_in_component G pc l = Some pc' -> *)
    find_label_in_code cde l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', pc', pct)

| Jump: forall st mem regs pc tg c pct pc' r,
    executing cde pc (TrJump r) tg c ->
(*    check_pc cde pc tg ->*)
    Register.get r regs = Ptr pc' ->
(*    Pointer.component pc' = Pointer.component pc -> *)
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, pc', pct)

| BnzNZ: forall st mem regs pc tg c pct pc' r l val,
    executing cde pc (TrBnz r l) tg c ->
(*    check_pc cde pc tg ->*)
    Register.get r regs = Int val ->
    (val <> 0) % Z ->
    find_label_in_code cde l = Some pc' ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, pc', pct)

| BnzZ: forall st mem regs pc tg c pct r l,
    executing cde pc (TrBnz r l) tg c ->
    check_pc cde pc tg ->
    Register.get r regs = Int 0 ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, Pointer.inc pc, pct)

| Alloc: forall st mem mem' regs regs' pc tg c pct rsize rptr size ptr,
    executing cde pc (TrAlloc rptr rsize) tg c ->
    check_pc cde pc tg ->
    Register.get rsize regs = Int size ->
    (size > 0) % Z ->
    Memory.alloc mem c (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem', regs', Pointer.inc pc, pct)

| Call: forall st mem regs regs' pc tg c pct pc' i tni c' pid call_arg,
    executing cde pc (TrJalProc (c',pid)) tg c ->
(*   check_pc cde pc tg ->*)
(*    find_label_in_component G pc l = Some pc' -> *)
    find_plabel_in_code cde c' pid = Some pc' ->
    executing cde pc' i tni c' ->
    c <> c' ->
    check_pc_call c tni pid ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    Register.get R_COM regs = Int call_arg ->
    step cde (st, mem, regs, pc, pct) [ECall c pid call_arg c']
           (Pointer.inc pc :: st, mem, invalidate regs', pc', inc_pc_tag pct). *)




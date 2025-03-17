Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Common.Traces.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From extructures Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import MicroPolicies.LRC.
Require Import Tmp.
Require Import Linearize.

Require Import Lib.Extra.
Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.
Import Intermediate.

Require Import Source.Language.

(*
Record mem_tag : Type := MTag
  { vtag : value_tag;
    entry : option (Procedure.id * seq Component.id) }.



Definition def_mem_tag (c : Component.id) := MTag Other None.
*)
Definition proc_label : Set := Component.id * Procedure.id.

Definition plabel : Set := label +  proc_label.

Variant instr :=
| TrNop : instr
| TrLabel : plabel -> instr
(* register operations *)
| TrConst : imvalue -> register -> instr
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


Section Tags.


(* Value tags and tags for code *)


Notation value_tag := LRC.value_tag. (* Ret : nat -> value_tag | Other : value_tag. *)

Definition code_tag : Type := option (Procedure.id * seq Component.id).


(* Tag of Memory cell *)

(* Record mem_tag : Type := MTag
  { vtag : value_tag;
    color : Component.id }.*)
(*
Record mem_tag : Type := MTag { vtag : value_tag ;
                                color : Component.id ;
                                entry : option (Procedure.id * seq Component.id) }.
(* TODO : is this right? |} *)
Definition def_mem_tag c : mem_tag := {| vtag := Other ; color := c ; entry := None |}. 
*)
End Tags.





Definition code := NMap (seq (instr * mem_tag)).



Definition instr_to_transitional (c : Component.id) (i : Machine.instr) : (instr * mem_tag) :=
  match i with
  | ICall c' P => if beq_nat c c' then ((TrJalProc (c',P)), def_mem_tag c)
    else ((TrJalProc (c',P)), def_mem_tag c)
  | IReturn => ((TrJump R_RA), def_mem_tag c)
  | INop => (TrNop, def_mem_tag c)
  | ILabel l =>  (TrLabel (inl l), def_mem_tag c)
  | IConst v r =>  (TrConst v r, def_mem_tag c)
  | IMov r r' => (TrMov r r', def_mem_tag c)
  | IBinOp op r r' r'' => (TrBinOp op r r' r'', def_mem_tag c)
  | ILoad r r' => (TrLoad r r', def_mem_tag c)
  | IStore r r' => (TrStore r r', def_mem_tag c)
  | IAlloc r r' => (TrAlloc r r', def_mem_tag c)
  | IBnz r l => (TrBnz r l, def_mem_tag c)
  | IJump => (TrJump R_RA, def_mem_tag c)
  | IJal l => (TrJalNat l, def_mem_tag c)
  | IHalt => (TrHalt, def_mem_tag c)
  end.


Definition executing (cde : code) (pc : Pointer.t) (i : instr) (tg : mem_tag) (c : Component.id)  : Prop := 
    exists C_code,
    Pointer.component pc = c /\
    cde c = Some C_code /\
    (Pointer.offset pc >= 0) % Z /\
    nth_error C_code (Z.to_nat (Pointer.offset pc)) = Some (i,tg).


(* Inductive F := FallThrough | Jumped.

Definition pc_tag : Type := F * Component.id.


Inductive check_pc : pc_tag -> mem_tag -> Prop := 
 | PcFall : forall c mt, color mt = c -> check_pc (FallThrough,c) mt
 | PcJump : forall c mt pid l, entry mt = Some (pid,l) -> check_comp_belongs c l -> check_pc (Jumped,c) mt. *)


Inductive pc_tag : Type := Level : nat -> pc_tag.

Definition level (pct : pc_tag) : nat := match pct with Level n => n end.

Definition inc_pc_tag (pct : pc_tag) : pc_tag := Level (level pct + 1).

(* Here: rather do an option thing? *)
Definition dec_pc_tag (pct : pc_tag) : pc_tag := Level (level pct - 1).

(* Definition level (pct : pc_tag) : nat := match pct with (n,c) => n end. *)

Fixpoint check_comp_belongs (c : Component.id) (l : seq Component.id) : Prop := match l with 
 | nil => False
 | c' :: l' => c = c' \/ check_comp_belongs c l'
end.

Fixpoint check_comp_belongs_b (c : Component.id) (l : seq Component.id) : bool := match l with 
 | nil => false
 | c' :: l' => if Nat.eqb c c' then true else check_comp_belongs_b c l'
end.


(* 
Inductive check_pc_samec : mem_tag -> mem_tag -> Prop := 
 | PcFall : forall c ti tni, color ti = c -> color tni = c -> check_pc_samec ti tni.

Inductive check_pc_callret : mem_tag -> mem_tag -> Prop := 
 | PcJump : forall c ti tni pid l, color ti = c -> entry tni = Some (pid,l) -> 
check_comp_belongs c l -> check_pc_callret ti tni. *)



Section Values.
  Record tvalue := MVal
   { tvtag : value_tag;
     val : value }.

  Definition to_tvalue (v : value) : tvalue := MVal Other v.

  Definition tUndef := to_tvalue Undef.

  Definition to_tagged_cell (c : Component.id) (v : value) : tvalue * mem_tag := (to_tvalue v,def_mem_tag c).

  Definition to_tagged_block (c : Component.id) (l : list value) : list (tvalue * mem_tag) := 
    map (to_tagged_cell c) l.
End Values.

Definition value_to_pc_tag (vt : value_tag) : option pc_tag :=
  match vt with
  | Ret n => Some (Level (S n))
  | _ => None
  end.

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
    | Some tv => Some (tvtag tv)
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => None
    end.

  Definition set (r : register) (val : value) (vt : value_tag) (regs : t) : t :=
    setm regs (to_nat r) (MVal vt val).

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


Require Import Common.Memory.

Module Memory. (* : AbstractComponentMemory.*)
  Definition block := list (tvalue * mem_tag).

  Implicit Types (b : Block.id).

  Record mem := mkMemT {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := NMap mem.

  Definition prealloc (bufs: {fmap Block.id -> (Component.id * (nat + list value))}) : mem :=
    let init_block x := match x with
                        | (c,inl size) => repeat (tUndef, def_mem_tag c) size
                        | (c,inr chunk) => (to_tagged_block c chunk)
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (domm bufs) 0) |}.


  Definition prealloc_c C (bufs: {fmap Block.id -> ((nat + list value))}) : mem :=
    let init_block x := match x with
                        | inl size => repeat (tUndef, def_mem_tag C) size
                        | inr chunk => to_tagged_block C chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (domm bufs) 0) |}.


  Definition empty :=
    {| content := emptym; nextblock := 0 |}.

  Definition reserve_block (m: mem) : (mem * Block.id) :=
    ({| content := content (m); nextblock := (1 + nextblock m)%nat |},
     nextblock m).

  Definition alloc_bis (c : Component.id) m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat (tUndef, def_mem_tag c) size in
    ({| content := setm (content m) fresh_block chunk;
        nextblock := (1 + nextblock m) |},
     fresh_block).

  Definition alloc (m : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    do mem <- m C;
    let '(mem', b) := alloc_bis C mem size in
      Some (setm m C mem', (C, b, 0%Z)).

  Definition load_b m b i : option (tvalue * mem_tag) :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then nth_error chunk (Z.to_nat i)
      else None
    | None => None
    end.

  Definition load (m:t) ptr : option (tvalue * mem_tag) :=
    obind (fun m =>
    load_b m (Pointer.block ptr) (Pointer.offset ptr)) (m (Pointer.component ptr)).

  Definition store_b m b i v : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then
        match list_upd chunk (Z.to_nat i) v with
        | Some chunk' =>
          Some {| content := setm (content m) b chunk';
                  nextblock := nextblock m |}
        | _ => None
        end
      else None
    | None => None
    end.

  Definition store (m:t) ptr v : option t :=
    let c := (Pointer.component ptr) in
    obind (fun mem =>
           obind (fun mem => Some (setm m c mem)) (store_b mem (Pointer.block ptr) (Pointer.offset ptr) v)) (m c).

  Definition domm_mem (m : t) c := obind (fun mem => Some (@domm nat_ordType block (content mem))) (m c).

  

  (* all functions below are used to initialize the memory *)
  
  Definition reserve_blocks (m : mem) (n : nat) : (mem * list Block.id) :=
    let acc '(_, bs) :=
      let (mem', b) := (reserve_block m) in
      (mem', bs ++ [b])  in
    ssrnat.iter n (acc)  ((m, [])).
  
Definition reserve_component_blocks p C Cmem procs_code
  : (mem * NMap Machine.code * NMap Block.id) :=
  let is_main_proc comp_id proc_id :=
      match prog_main p with
      | true =>
        (Component.main =? comp_id) && (Procedure.main =? proc_id)
      | false => false
      end in
  (* if P is exported or is the main procedure, add an external entrypoint *)
  let map_entrypoint '(P, b) :=
      match getm (prog_interface p) C with
      | Some Ciface =>
        if (P \in Component.export Ciface) || is_main_proc C P then Some (P, b)
        else None
      | None => None (* this case shouldn't happen for well formed p *)
      end in
  let (Cmem', bs) := reserve_blocks Cmem (length procs_code) in
  let (procs, code) := (unzip1 procs_code, unzip2 procs_code) in
  let Cprocs := mkfmap (zip bs code) in
  let Centrypoints := mkfmap (pmap map_entrypoint (zip procs bs)) in
  (Cmem', Cprocs, Centrypoints).

  Definition prepare_procedures_initial_memory_aux (p: Intermediate.program) :=
    mkfmapf
      (fun C =>
         let Cprocs := odflt emptym ((prog_procedures p) C) in
         let Cmem := prealloc (mapm (fun a => (C, a)) (odflt emptym ((prog_buffers p) C))) in
         reserve_component_blocks p C Cmem (elementsm Cprocs))
      (domm (prog_interface p)).

  Definition prepare_procedures_initial_memory (p: Intermediate.program)
    : Memory.t :=
    let m := prepare_procedures_initial_memory_aux p in
    (mapm (fun x => x.1.1) m).
End Memory.

Definition state : Type := list Pointer.t * Memory.t * Register.t * Pointer.t * pc_tag.

Definition stackless : Type := Memory.t * Register.t * Pointer.t * pc_tag.


Fixpoint find_label (cd : seq (instr * mem_tag)) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | (TrLabel (inl l'),_) :: c' =>
        if Nat.eqb l l' then
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
      | Some offset => Some (c, 0, offset)
      | None => None
      end
  | None => None
end.

Fixpoint find_label_in_code_helper
         (cde : code) (comps: list (Component.id * (seq (instr * mem_tag))))
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


Fixpoint find_plabel (cd : seq (instr * mem_tag)) (c : Component.id) (p : Procedure.id) : option Z :=
  let fix aux cd o :=
      match cd with
      | [] => None
      | (TrLabel (inr (c',p')),_) :: cd' =>
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
      | Some offset => Some (c, 0, offset)
      | None => None
      end
  | None => None
end.


Inductive check_pc : code -> Pointer.t -> mem_tag -> Prop :=
| PcFall : forall cde pc tg i tni c, 
    executing cde (Pointer.inc pc) i tni c ->
    (* color tg = c -> *) check_pc cde pc tg.


Inductive check_pc_jump : code -> mem_tag -> Pointer.t -> Component.id -> Prop :=
 |PcJump : forall cde tg pc' i tni c c0,
    executing cde (pc') i tni c ->
    Pointer.component pc' = c0 -> check_pc_jump cde tg pc' c0.

Inductive check_pc_call : Component.id -> mem_tag -> Procedure.id -> Prop := 
 | PcCall : forall c tni pid l, (* color ti = c ->  *)
  entry tni = Some (pid,l) -> 
  check_comp_belongs c l -> check_pc_call c tni pid.


(* missing stuff *)
Inductive check_pc_ret : Component.id -> mem_tag -> Prop := 
 | PcRet : forall c tni pid l, (* color ti = c ->  *)
  entry tni = Some (pid,l) -> 
  check_comp_belongs c l -> check_pc_ret c tni.


(*** !IMPORTANT: PROTECT Return Adress registers with tags in a 'linear' way,
                 so that they can't be copied ***)
(* make the code separated  by compartments in the compilation *)
(* well-formedness & interfaces *)
(*step for return *)
(* where is return adress stored?*)
(* TODO Add Jal for (c,pid) type (TrJalProc), but intra compartment ?? 
todo? (in order to reduce UB), allow TrJalNat to different components *)

Inductive step (cde : code) : state -> trace -> state -> Prop :=
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
    Register.set r (imm_to_val v) Other regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| Mov: forall st mem regs regs_tmp regs' pc tg c pct r1 r2,
    executing cde pc (TrMov r1 r2) tg c ->
    check_pc cde pc tg ->
    Register.set r2 (val (Register.get r1 regs)) ((tvtag (Register.get r1 regs))) regs = regs_tmp ->
    (*remove capability, if any*)
    let ts' := if (is_address (tvtag (Register.get r1 regs))) then Invalidated else Other in
    Register.set r1 (val (Register.get r1 regs)) ts' regs_tmp = regs' -> 
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| BinOp: forall st mem regs regs' pc tg c pct r1 r2 r3 op,
    executing cde pc (TrBinOp op r1 r2 r3) tg c ->
    check_pc cde pc tg ->
    (tvtag (Register.get r1 regs) = Other) ->
    (tvtag (Register.get r2 regs) = Other) ->
    let result := eval_binop op (val (Register.get r1 regs)) (val (Register.get r2 regs)) in
    Register.set r3 result Other regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', Pointer.inc pc, pct)

| Load: forall st mem mem' regs regs' pc tg c pct r1 r2 ptr v,
    executing cde pc (TrLoad r1 r2) tg c ->
    check_pc cde pc tg ->
    (tvtag (Register.get r1 regs) = Other) ->
    val (Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Memory.load mem ptr = Some v ->
    Register.set r2 (val (fst v)) (tvtag (fst v)) regs = regs' ->
    (*remove capability, if any*)
    let ts' := if (is_address (tvtag (fst v))) then Invalidated else Other in
    Memory.store mem ptr ({|val := val (fst v); tvtag := Other |}, {|vtag := ts' ; color := c ; entry := None|}) = Some mem' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem', regs', Pointer.inc pc, pct)

| Store: forall st mem mem' regs regs' pc tg c pct ptr r1 r2 vt,
    executing cde pc (TrStore r1 r2) tg c ->
    check_pc cde pc tg ->
    (tvtag (Register.get r1 regs) = Other) ->
    val (Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr =  c ->
    ((Register.get_tag r2 regs) = Some vt) ->
    Memory.store mem ptr ((Register.get r2 regs), {|vtag := vt ; color := c ; entry := None|}) = Some mem' ->
    (*remove capability, if any*)
    let ts' := if (is_address (tvtag (Register.get r2 regs))) then Invalidated else Other in
    Register.set r2 (val (Register.get r2 regs)) ts' regs = regs' -> 
    step cde (st, mem, regs, pc, pct) E0
           (st, mem', regs', Pointer.inc pc, pct)

| Jal: forall st mem regs regs' pc tg c pct pc' l,
    executing cde pc (TrJalNat l) tg c ->
(*   check_pc cde pc tg ->*)
(*    find_label_in_component G pc l = Some pc' -> *)
    find_label_in_comp cde c l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) InternalJump regs = regs' ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs', pc', pct)

| Jump: forall st mem regs pc tg c pct pc' r,
    executing cde pc (TrJump r) tg c ->
(*    check_pc cde pc tg ->*)
    ((Register.get r regs) = MVal InternalJump (Ptr pc')) ->
    Pointer.component pc' = Pointer.component pc ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
      (st, mem, regs, pc', pct)

| JumpRet: forall st mem regs pc tg c pct pc' r rcomval,
    executing cde pc (TrJump r) tg c ->
(*    check_pc cde pc tg ->*)
    val (Register.get r regs) = Ptr pc' ->
    Pointer.component pc' <> Pointer.component pc ->
    (Some pct = value_to_pc_tag (tvtag (Register.get r regs))) ->
    (val (Register.get R_COM regs) = Int rcomval) ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) [ERet (Pointer.component pc) rcomval (Pointer.component pc')]
    (st, mem, regs, pc', dec_pc_tag pct)

| BnzNZ: forall st mem regs pc tg c pct pc' r l v,
    executing cde pc (TrBnz r l) tg c ->
(*    check_pc cde pc tg ->*)
    (tvtag (Register.get r regs) = Other) ->
    val (Register.get r regs) = Int v ->
    (v <> 0) % Z ->
    find_label_in_code cde l = Some pc' ->
    check_pc_jump cde tg pc' c ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, pc', pct)

| BnzZ: forall st mem regs pc tg c pct r l,
    executing cde pc (TrBnz r l) tg c ->
    (tvtag (Register.get r regs) = Other) ->
    val (Register.get r regs) = Int 0 ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem, regs, Pointer.inc pc, pct)

| Alloc: forall st mem mem' regs regs' pc tg c pct rsize rptr size ptr,
    executing cde pc (TrAlloc rptr rsize) tg c ->
    check_pc cde pc tg ->
    (tvtag (Register.get rsize regs) = Other) ->
    val (Register.get rsize regs) = Int size ->
    (size > 0) % Z ->
    Memory.alloc mem c (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) Other regs = regs' ->
    step cde (st, mem, regs, pc, pct) E0
           (st, mem', regs', Pointer.inc pc, pct)

| Call: forall st mem regs regs' pc tg c pct pc' i tni c' pid call_arg n,
    executing cde pc (TrJalProc (c',pid)) tg c ->
(*   check_pc cde pc tg ->*)
(*    find_label_in_component G pc l = Some pc' -> *)
    find_plabel_in_code cde c' pid = Some pc' ->
    executing cde pc' i tni c' ->
    c <> c' ->
    check_pc_call c tni pid ->
    (pct = Level n) ->
    Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n) regs = regs' ->
    val (Register.get R_COM regs) = Int call_arg ->
    step cde (st, mem, regs, pc, pct) [ECall c pid call_arg c']
           (Pointer.inc pc :: st, mem, Register.invalidate regs', pc', inc_pc_tag pct).



Import MonadNotations.
Open Scope monad_scope.



Definition eval_step (cde: code) (s: stackless) : option (trace * stackless) :=
  let '(mem, regs, pc, pct) := s in
  (* fetch the next instruction to execute *)
  if (Pointer.offset pc <? 0) % Z then
    None
  else
      do C_code <- cde (Pointer.component pc);
      do (instr,tag) <- nth_error C_code (Z.to_nat (Pointer.offset pc));
    match instr with
    | TrLabel _ =>
      ret (E0, (mem, regs, Pointer.inc pc, pct))
    | TrNop =>
      ret (E0, (mem, regs, Pointer.inc pc, pct))
    | TrConst v r =>
      let regs' := Register.set r (imm_to_val v) Other regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrMov r1 r2 =>
      let regs' := Register.set r2 (val (Register.get r1 regs)) (tvtag (Register.get r1 regs)) regs in
      (*remove capability, if any*)
      let ts' := if (is_address (tvtag (Register.get r1 regs))) then Invalidated else Other in
      let regs'' := Register.set r1 (val (Register.get r1 regs)) ts' regs' in
      ret (E0, (mem, regs'', Pointer.inc pc, pct))
    | TrBinOp op r1 r2 r3 =>
        match (tvtag (Register.get r1 regs), tvtag (Register.get r2 regs)) with
        | (Other, Other) =>
            let result := eval_binop op (val (Register.get r1 regs)) (val (Register.get r2 regs)) in
            let regs' := Register.set r3 result Other regs in
            ret (E0, (mem, regs', Pointer.inc pc, pct))
        | _ => None end
    | TrLoad r1 r2 =>
      match (Register.get r1 regs) with
      | MVal Other (Ptr ptr) =>
        let c := (Pointer.component ptr) in
        if Component.eqb c (Pointer.component pc) then
          do v <- Memory.load mem ptr;
          let regs' := Register.set r2 (val (fst v)) (tvtag (fst v))  regs in
          (*remove capability, if any*)
          let ts' := if (is_address (tvtag (fst v))) then Invalidated else Other in
          do mem' <- Memory.store mem ptr ({|val := val (fst v); tvtag := ts' |}, {|vtag := ts' ; color := c ; entry := None|});
          ret (E0, (mem', regs', Pointer.inc pc, pct))
        else
          None
      | _ => None
      end
    | TrStore r1 r2 =>
      match (Register.get r1 regs) with
      | MVal Other (Ptr ptr) =>
          let c := (Pointer.component ptr) in
          if Component.eqb c (Pointer.component pc) then
            do vt <- Register.get_tag r2 regs ;
            do mem' <- Memory.store mem ptr ((Register.get r2 regs), {|vtag := vt ; color := c ; entry := None|});
            (*remove capability, if any*)
            let ts' := if (is_address (vt)) then Invalidated else Other in
            let regs' := Register.set r2 (val (Register.get r2 regs)) ts' regs in
            ret (E0, (mem', regs', Pointer.inc pc, pct))
          else
            None
      | _ => None
      end
    | TrAlloc rptr rsize =>
      match (Register.get rsize regs) with
      | MVal Other (Int size) =>
        if (size <=? 0) % Z then
          None
        else
          do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
          let regs' := Register.set rptr (Ptr ptr) Other regs in
          ret (E0, (mem', regs', Pointer.inc pc, pct))
      | _ => None
      end
    | TrJump r =>
      match (Register.get r regs) with
      | MVal tag (Ptr pc') =>
          if Component.eqb (Pointer.component pc') (Pointer.component pc) then
            match tag with
            | InternalJump => ret (E0, (mem, regs, pc', pct))
            | _ => None
            end
        else (
          match (tag, pct) with
          | (Other, _) | (InternalJump, _) | (Invalidated, _) => None
          | (Ret n, Level m) =>(
         if orb ((Pointer.offset pc' <? 0) % Z)  (negb (ssrnat.eqn (S n) m)) then
            None
         else
            do C_code' <- cde (Pointer.component pc');
            do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
            match val (Register.get R_COM regs) with
            | Int rcomval =>
              let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
              ret (t, (mem, Register.invalidate regs, pc', dec_pc_tag pct))
            | _ => None
            end)
          end)
      | _ => None
      end
    | TrBnz r l =>
      match (Register.get r regs) with
      | MVal Other (Int 0) =>
        ret (E0, (mem, regs, Pointer.inc pc, pct))
      | MVal Other (Int val) =>
        do pc' <- find_label_in_code cde l;
        ret (E0, (mem, regs, pc', pct))
      | _ => None
      end
    | TrJalNat l =>
      do pc' <- find_label_in_comp cde (Pointer.component pc) l;
      let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) InternalJump regs in
      ret (E0, (mem, regs', pc', pct))
    | TrJalProc (c',pid) =>
      match find_plabel_in_code cde c' pid with 
      | Some pc' => 
          (if Component.eqb (Pointer.component pc') (Pointer.component pc) then
              let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) Other regs in
              ret (E0, (mem, regs', pc', pct))
           else 
             if (Pointer.offset pc' <? 0) % Z then
               None
             else
               do C_code' <- cde (Pointer.component pc');
               do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
               match entry tni with
               | Some (pid',lc) => 
                   if andb (Procedure.eqb pid pid') (check_comp_belongs_b (Pointer.component pc) lc) then
                     match (val (Register.get R_COM regs), pct) with
                     | (Int rcomval, Level n) =>
                         let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n) (Register.invalidate regs) in
                         let t := [ECall (Pointer.component pc) pid rcomval (Pointer.component pc')] in
                         ret (t, (mem, regs', pc', inc_pc_tag pct))
                     | _ => None
                     end
                   else None
               | _ => None
               end)
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
      match val (Register.get R_COM regs) with
      | Int i => inl (Some i)
      | _ => inr 4
      end
    | Some (_, st') => execN n' cde st'
    end
  end.



Definition head_tag (pr : Intermediate.program) (c : Component.id) (p : Procedure.id) : mem_tag :=
  let I := Intermediate.prog_interface pr in
  let allowed_call_by (c' : Component.id) :=
      Option.default false (do i <- getm I c ;
                            do i' <- getm I c' ;
                            Some ((p \in Component.export i) && ((c, p) \in Component.import i')))
  in MTag LRC.Other c (Some (p, filter allowed_call_by (domm I))).


Definition linearize_proc (pr : Intermediate.program )
           (c : Component.id) (p : Procedure.id) : seq (instr * mem_tag) :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (pr)) c;
                                    getm map p)
  in ((TrLabel (inr (c,p))), head_tag pr c p) :: (map (instr_to_transitional c) code).

Definition linearize_component (pr : Intermediate.program ) (c : Component.id) : seq (instr * mem_tag) :=
  let procs : seq Procedure.id :=
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (pr)) c;
                            Some (domm map)) in
  flatten (map (linearize_proc pr c) procs).


Fixpoint compile_component_list {T} cenv (l : list (Component.id * T)) :=
 match l with 
  | [] => []
  | (c,_) :: cs => (c,linearize_component cenv c) :: compile_component_list cenv cs
end.

Definition intermediate_to_transitional (pr : Intermediate.program) : code := 
mkfmap (compile_component_list pr (elementsm (Intermediate.prog_procedures (pr)))).



(*
Definition pre_linearize (p : Intermediate.program) : code :=
 intermediate_to_transitional p. *)

(* Record program : Type := mkProg
    prog_code : code;
    prog_buffers : NMap {fmap Block.id -> nat + seq value};
    prog_main : bool } *)

Definition run_transitional cd fuel p :=
    let mem  := Memory.prepare_procedures_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code cd Component.main Procedure.main) with
    | Some pc =>
      execN fuel cd (mem, regs, pc, Level 0)
    | None => inr 5
end.

Definition compile_run fuel (p : Intermediate.program) :=
 run_transitional (intermediate_to_transitional p) fuel p.

Close Scope monad_scope.


Require Import S2I.Compiler.

Definition compile_and_run_from_source := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p => compile_run fuel compiled_p
| None => inl None
end.

Require Export Extraction.Definitions.

Definition compile_and_run_from_intermediate compiled_p fuel :=
    match compile_run fuel compiled_p with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
    end.

Definition compile_and_run_from_source_ex := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p => compile_and_run_from_intermediate compiled_p fuel
| None => print_error ocaml_int_0
end.

(*
Module I.
  Import Intermediate.Machine.
  Import Intermediate.CS.
  Module CS := CS.
End I.

Definition is_initial_state (c: code) (s:state) : Prop :=
  exists p, (c = pre_linearize p) ->
  let (ics,tag) := s in
  initial_state (I.CS.sem p) ics.

Definition is_final_state (c: code) (s:state) : Prop :=
  exists p, (c = pre_linearize p) ->
  let (ics,tag) := s in
  final_state (I.CS.sem p) ics.

Section Semantics.
  Variable p: Intermediate.program.
  Let c := pre_linearize p.

  
 (* Let G := prepare_global_env p.*)

  Definition sem :=
    @Semantics_gen state code step (is_initial_state c) (is_final_state c) c.

  (*
  Definition sem :=
    @Semantics_gen state code step (initial_state p). *)

End Semantics.

Lemma forward_simulation_intermediate_transitional:
  forall p, forward_simulation (I.CS.sem p) (sem p).
Proof.
  intro p.
  eapply (Forward_simulation (lt) ).
Admitted.
 *)


(*
Require Import Source.Examples.Identity.

Eval compute in compile_and_run_from_source_ex identity 10.*)





(*version for extraction : 
Definition compile_and_run_from_source := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match compile_run fuel compiled_p with
    | Some n => print_ocaml_int (z2int n)
    | None => print_error ocaml_int_1
    end
| None => print_error ocaml_int_0
end.  *)



(*
Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st = Some (t, st').


Theorem eval_step_sound:
  forall G st t st',
    eval_step G st = Some (t, st') -> step G st t st'. *)





(*** BELOW : OLD COMPILATION PROCEDURE (WORKED WITH SINGLE CODE BLOCK, NOT 
NECESSARY TO ADAPT DIRECTLY FROM THERE ***)

(* Definition head_tag (cenv : compiler_env) (c : Component.id) (p : Procedure.id) : mem_tag :=
  let I := Intermediate.prog_interface (program cenv) in
  let allowed_call_by (c' : Component.id) :=
      Option.default false (do i <- getm I c ;
                            do i' <- getm I c' ;
                            Some ((p \in Component.export i) && ((c, p) \in Component.import i')))
  in {| vtag := Other ;
        color := c ;
        entry := Some (p, filter allowed_call_by (domm I)) |}.


Definition linearize_proc (cenv : compiler_env)
           (c : Component.id) (p : Procedure.id) : code :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                                    getm map p)
  in (inr (ILabel (make_label cenv c p)), head_tag cenv c p) :: flatten (map (linearize_instr cenv c) code).

Definition linearize_component (cenv : compiler_env) (c : Component.id) : code :=
  let procs : seq Procedure.id :=
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                            Some (domm map)) in
  flatten (map (linearize_proc cenv c) procs).

Definition linearize_code (cenv : compiler_env) : code :=
  let main_code :=
      [:: (inr (IJal (make_label cenv Component.main Procedure.main)), def_mem_tag Component.main) ; (inr IHalt, def_mem_tag Component.main)] in

  let components : seq Component.id := domm (Intermediate.prog_procedures (program cenv)) in
  main_code ++ flatten (map (linearize_component cenv) components).


Notation bufs := {fmap (nat * nat * nat) -> (value * mem_tag)}.

Definition linearize_buf (cenv : compiler_env) (c : Component.id) (b : Block.id) : seq (value * mem_tag) :=
  Option.default [::] (do map <- getm (Intermediate.prog_buffers (program cenv)) c ;
                       do block <- getm map b ;
                       Some match block with
                            | inl n => repeat (Undef, def_mem_tag c) n
                            | inr l => [seq (x, def_mem_tag c) | x <- l]
                            end).

Definition linearize_bufs (cenv : compiler_env) : bufs :=
  let bufs' : NMap (NMap (NMap (value * mem_tag))) :=
      mapim (fun c map => mapim (fun b _ => fmap_of_seq (linearize_buf cenv c b)) map)
            (Intermediate.prog_buffers (program cenv))
  in Tmp.mapk (fun c => match c with (x, (y, z)) => (x, y, z) end)
              (uncurrym (mapm (fun m : NMap (NMap (value * mem_tag)) => uncurrym m) bufs')).

Record prog :=
  { procedures : code ;
    buffers : bufs ;
  }.
 


Definition max_label (p : Intermediate.program) : nat :=
  let soup := (flatten (flatten (map codomm' (codomm' (Intermediate.prog_procedures p))))) in
  let get_label i := match i with
                    | ILabel l => Some l
                    | _ => None
                    end in
  let labels := pmap get_label soup in foldl max 0 labels + 1.

Definition max_proc_id (p : Intermediate.program) : nat :=
  let componnent_max_proc_id (map : NMap Machine.code) : nat :=
      foldl max 0 (domm map) in
  let max_proc_ids := map componnent_max_proc_id (codomm' (Intermediate.prog_procedures p)) in
  foldl max 0 max_proc_ids + 1.

Definition linearize (p : Intermediate.program) : prog :=
  let lmax := max_label p in
  let pmax := max_proc_id p in
  let cenv := {| program := p ;
                 make_label := (fun c p => lmax + c * pmax + p) |} in
  {| procedures := linearize_code_bis cenv ;
     buffers    := linearize_bufs cenv |}.
*)


(* 


Module Compartmentless_Pointer.
  Definition t : Type := Block.id * Block.offset.

  Definition block (p : t) : Block.id :=
    let '(b, _) := p in b.

  Definition offset (p : t) : Block.offset :=
    let '( _, o) := p in o.

  Definition eq (p1 p2 : t) : bool :=
    let '( b1, o1) := p1 in
    let '(b2, o2) := p2 in
 (Nat.eqb b1 b2) && (Z.eqb o1 o2).

  Definition leq (p1 p2 : t) : option bool :=
    let '(b1, o1) := p1 in
    let '( b2, o2) := p2 in
    if  (Nat.eqb b1 b2) then
      Some ((o1 <=? o2) % Z)
    else
      None.

  Definition add (ptr : t) (offset : Z) : t :=
    let '( b, o) := ptr in (b, (o+offset)%Z).

  Definition sub (ptr : t) (offset : Z) : t :=
    let '(C, b, o) := ptr in (C, b, (o-offset)%Z).

  Definition inc (ptr : t) : t := add ptr 1.

  Lemma add_preserves_component:
    forall p n, component (add p n) = component p.
  Proof.
    intros p n.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma add_preserves_block:
    forall p n, block (add p n) = block p.
  Proof.
    intros p n.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma inc_preserves_component:
    forall p, component (inc p) = component p.
  Proof.
    intros p.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma inc_preserves_block:
    forall p, block (inc p) = block p.
  Proof.
    intros p.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma compose :
    forall ptr,
      (component ptr, block ptr, offset ptr) = ptr.
  Proof.
    now intros [[C b] o].
  Qed.
End Pointer.


*)

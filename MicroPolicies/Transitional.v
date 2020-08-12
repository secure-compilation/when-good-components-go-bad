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

Definition proc_label : Set := Component.id * Procedure.id.

Definition plabel : Set := label * option proc_label.

Definition label_of (pl : plabel) : label := let (n,_) := pl in n.

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



Record mem_tag : Type := MTag
  { vtag : value_tag;
    entry : option (Procedure.id * seq Component.id) }.




Definition code := NMap (seq (instr * mem_tag)).
Definition def_mem_tag (c : Component.id) := MTag Other None.


Record compiler_env :=
  { program : Intermediate.program ;
    make_label : Component.id -> Procedure.id -> label ;
  }.


Definition instr_to_transitional (cenv : compiler_env)
           (c : Component.id) (i : Machine.instr) : (instr * mem_tag) :=
  match i with
  | ICall c' P => if beq_nat c c' then  ((TrJalNat (make_label cenv c' P)), def_mem_tag c)
    else ((TrJalProc (c',P)), def_mem_tag c)
  | IReturn => ((TrJump R_RA), def_mem_tag c)
  | INop => (TrNop, def_mem_tag c)
  | ILabel l =>  (TrLabel (l,None), def_mem_tag c)
  | IConst v r =>  (TrConst v r, def_mem_tag c)
  | IMov r r' => (TrMov r r', def_mem_tag c)
  | IBinOp op r r' r'' => (TrBinOp op r r' r'', def_mem_tag c)
  | ILoad r r' => (TrLoad r r', def_mem_tag c)
  | IStore r r' => (TrStore r r', def_mem_tag c)
  | IAlloc r r' => (TrAlloc r r', def_mem_tag c)
  | IBnz r l => (TrBnz r l, def_mem_tag c)
  | IJump r => (TrJump r, def_mem_tag c)
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


Definition state : Type := list Pointer.t * Memory.t * Intermediate.Register.t * Pointer.t * pc_tag.

Definition stackless : Type := Memory.t * Intermediate.Register.t * Pointer.t * pc_tag.


Fixpoint find_label (cd : seq (instr * mem_tag)) (l : label) : option Z :=
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
   | (comp_id,comp_code) :: comps' => find_label_in_comp cde comp_id l
  end.

Definition find_label_in_code (cde : code) (l : label) : option Pointer.t :=
  find_label_in_code_helper cde (elementsm cde) l.


Fixpoint find_plabel (cd : seq (instr * mem_tag)) (c : Component.id) (p : Procedure.id) : option Z :=
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
      | Some offset => Some (c, 0, offset)
      | None => None
      end
  | None => None
end.




(*      match find_label cde l with
      | Some offset => Some (Pointer.component pc, Pointer.block pc, offset)
      | None => None
      end.


Fixpoint find_label_in_component_helper
         G (procs: list (Block.id * code))
         (pc: Pointer.t) (l: label) : option Pointer.t :=
  match procs with
  | [] => None
  | (p_block,p_code) :: procs' =>
    match find_label_in_procedure G (Pointer.component pc, p_block, 0%Z) l with
    | None => find_label_in_component_helper G procs' pc l
    | Some ptr => Some ptr
    end
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    find_label_in_component_helper G (elementsm C_procs) pc l
  | None => None *)




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
      let regs' := Register.set r (imm_to_val v) regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrMov r1 r2 =>
      let regs' := Register.set r2 (Register.get r1 regs) regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrBinOp op r1 r2 r3 =>
      let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
      let regs' := Register.set r3 result regs in
      ret (E0, (mem, regs', Pointer.inc pc, pct))
    | TrLoad r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do v <- Memory.load mem ptr;
          let regs' := Register.set r2 v regs in
          ret (E0, (mem, regs', Pointer.inc pc, pct))
        else
          None
      | _ => None
      end
    | TrStore r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do mem' <- Memory.store mem ptr (Register.get r2 regs);
          ret (E0, (mem', regs, Pointer.inc pc, pct))
        else
          None
      | _ => None
      end
    | TrAlloc rptr rsize =>
      match Register.get rsize regs with
      | Int size =>
        if (size <=? 0) % Z then
          None
        else
          do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
          let regs' := Register.set rptr (Ptr ptr) regs in
          ret (E0, (mem', regs', Pointer.inc pc, pct))
      | _ => None
      end
    | TrJump r =>
      match Register.get r regs with
      | Ptr pc' =>
        if Component.eqb (Pointer.component pc') (Pointer.component pc) then
          ret (E0, (mem, regs, pc', pct))
        else
         if (Pointer.offset pc' <? 0) % Z then
            None
         else
            do C_code' <- cde (Pointer.component pc');
            do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
            match Register.get R_COM regs with
            | Int rcomval =>
              let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
              ret (t, (mem, Register.invalidate regs, pc', dec_pc_tag pct))
            | _ => None
            end
            (* MISSING HERE : ENFORCEMENT ABOUT LEVEL OF RETURN AND RA (should be same level) *)
      | _ => None
      end
    | TrBnz r l =>
      match Register.get r regs with
      | Int 0 =>
        ret (E0, (mem, regs, Pointer.inc pc, pct))
      | Int val =>
        do pc' <- find_label_in_code cde l;
        ret (E0, (mem, regs, pc', pct))
      | _ => None
      end
    | TrJalNat l =>
      do pc' <- find_label_in_code cde l;
      let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) regs in
      ret (E0, (mem, regs', pc', pct))
    | TrJalProc (c',pid) =>
      match find_plabel_in_code cde c' pid with 
      | Some pc' => 
        if Component.eqb (Pointer.component pc') (Pointer.component pc) then
          ret (E0, (mem, regs, pc', pct))
        else 
         if (Pointer.offset pc' <? 0) % Z then
            None
         else
            do C_code' <- cde (Pointer.component pc');
            do (ni,tni) <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
            match entry tni with
             | Some (pid',lc) => 
               if Procedure.eqb pid pid' then 
                if check_comp_belongs_b (Pointer.component pc) lc then
                  match Register.get R_COM regs with
                  | Int rcomval =>
                      let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) regs in
                      let t := [ECall (Pointer.component pc) pid rcomval (Pointer.component pc')] in
                      ret (t, (mem, Register.invalidate regs', pc', inc_pc_tag pct))
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


Fixpoint execN (n: nat) (cde: code) (st: stackless) : option Z :=
  match n with
  | O => None
  | S n' =>
    match eval_step cde st with
    | None =>
      let '(_, regs, _, _) := st in
      match Register.get R_COM regs with
      | Int i => Some i
      | _ => None
      end
    | Some (_, st') => execN n' cde st'
    end
  end.



Definition head_tag (cenv : compiler_env) (c : Component.id) (p : Procedure.id) : mem_tag :=
  let I := Intermediate.prog_interface (program cenv) in
  let allowed_call_by (c' : Component.id) :=
      Option.default false (do i <- getm I c ;
                            do i' <- getm I c' ;
                            Some ((p \in Component.export i) && ((c, p) \in Component.import i')))
  in {| vtag := Other ;
        entry := Some (p, filter allowed_call_by (domm I)) |}.

Print getm.

Definition linearize_proc (cenv : compiler_env)
           (c : Component.id) (p : Procedure.id) : seq (instr * mem_tag) :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                                    getm map p)
  in ((TrLabel (make_label cenv c p, Some (c,p))), head_tag cenv c p) :: (map (instr_to_transitional cenv c) code).

Definition linearize_component (cenv : compiler_env) (c : Component.id) : seq (instr * mem_tag) :=
  let procs : seq Procedure.id :=
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                            Some (domm map)) in
  flatten (map (linearize_proc cenv c) procs).

Check mapm.
Print NMap.

Fixpoint compile_component_list {T} cenv (l : list (Component.id * T)) :=
 match l with 
  | [] => []
  | (c,_) :: cs => (c,linearize_component cenv c) :: compile_component_list cenv cs
end.

Definition intermediate_to_transitional (cenv : compiler_env) : code := 
mkfmap (compile_component_list cenv (elementsm (Intermediate.prog_procedures (program cenv)))).




Definition pre_linearize (p : Intermediate.program) : code :=
  let lmax := max_label p in
  let pmax := max_proc_id p in
  let cenv := {| program := p ;
                 make_label := (fun c p => lmax + c * pmax + p) |} in
 intermediate_to_transitional cenv.

(* Record program : Type := mkProg
    prog_code : code;
    prog_buffers : NMap {fmap Block.id -> nat + seq value};
    prog_main : bool } *)


Definition run_transitional cd fuel p :=
    let '(mem, _, entrypoints) := prepare_procedures_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code cd Component.main Procedure.main) with
    | Some pc =>
      execN fuel cd (mem,regs, pc, Level 0)
    | None => None
end.

Definition compile_run fuel (p : Intermediate.program) :=
  run_transitional (pre_linearize p) fuel p.

Close Scope monad_scope.


Require Import Compiler.

Definition compile_and_run_from_source := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match compile_run fuel compiled_p with
    | Some n => Some n
    | None => None
    end
| None => None
end.

Require Export Extraction.Definitions.

Definition compile_and_run_from_source_ex := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match compile_run fuel compiled_p with
    | Some n => print_ocaml_int (z2int n)
    | None => print_error ocaml_int_1
    end
| None => print_error ocaml_int_0
end.


(* Require Import Source.Examples.Identity.

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

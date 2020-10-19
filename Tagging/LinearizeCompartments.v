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
Require Import Tags.
Require Import Tagging.Memory.
Require Import Tagging.Language.

Require Import Lib.Extra.
Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


Record compiler_env :=
  { program : Intermediate.program ;
    make_label : Component.id -> Procedure.id -> label ;
    block_renum : Component.id -> Block.id -> Block.id ;
  }.

Definition ptr_to_ptr (ptr : BigPointer) (cenv : compiler_env) : Pointer.t := let '(c,b,o) := ptr in (block_renum cenv c b,o).

Definition instr_to_transitional (cenv : compiler_env)
           (c : Component.id) (i : Machine.instr) : instr :=
  match i with
  | ICall c' P => (TrJalProc (c',P)) 
(* if beq_nat c c' then (TrJalProc (c',P)) (* ((TrJalNat (make_label cenv c' P)), def_mem_tag c) *)
    else (TrJalProc (c',P)) *)
  | IReturn => (TrJump R_RA)
  | INop => TrNop
  | ILabel l =>  TrLabel (l,None)
  | IConst v r =>  
    match v with 
      | IInt z => TrConst (Int z) r
      | IPtr ptr => TrConst (Ptr (ptr_to_ptr ptr cenv)) r
    end
  | IMov r r' => TrMov r r'
  | IBinOp op r r' r'' => TrBinOp op r r' r''
  | ILoad r r' => TrLoad r r'
  | IStore r r' => TrStore r r'
  | IAlloc r r' => TrAlloc r r'
  | IBnz r l => TrBnz r l
  | IJump r => TrJump r
  | IJal l => TrJalNat l
  | IHalt => TrHalt
  end.


Definition head_tag (cenv : compiler_env) (c : Component.id) (p : Procedure.id) : code_tag :=
  let I := Intermediate.prog_interface (program cenv) in
  let allowed_call_by (c' : Component.id) :=
      Option.default false (do i <- getm I c ;
                            do i' <- getm I c' ;
                            Some ((p \in Component.export i) && ((c, p) \in Component.import i')))
  in Some (p, filter allowed_call_by (domm I)).


Definition linearize_proc (cenv : compiler_env)
           (c : Component.id) (p : Procedure.id) : seq (instr * code_tag) :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                                    getm map p)
  in ((TrLabel (make_label cenv c p, Some (c,p))), head_tag cenv c p) :: (map (fun x => (instr_to_transitional cenv c x,None)) code).

Definition linearize_component (cenv : compiler_env) (c : Component.id) : seq (instr * code_tag) :=
  let procs : seq Procedure.id :=
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                            Some (domm map)) in
  flatten (map (linearize_proc cenv c) procs).


Fixpoint compile_component_list {T} cenv (l : list (Component.id * T)) :=
 match l with 
  | [] => []
  | (c,_) :: cs => (c,linearize_component cenv c) :: compile_component_list cenv cs
end.

Definition intermediate_to_transitional (cenv : compiler_env) : code := 
mkfmap (compile_component_list cenv (elementsm (Intermediate.prog_procedures (program cenv)))).


Definition max_component p := foldl Nat.max 0 (extructures.fmap.domm (Intermediate.prog_interface p)).

Definition pre_linearize_code (p : Intermediate.program) : code :=
  let lmax := max_label p in
  let pmax := max_proc_id p in
  let cmax := max_component p in
  let cenv := {| program := p ;
                 make_label := (fun c p => lmax + c * pmax + p + pmax * cmax +1) |} in 
 intermediate_to_transitional cenv.

(*  *)

Print Intermediate.prepare_procedures_initial_memory_aux.

Definition run_transitional cd fuel p :=
    let '(mem, _, entrypoints) := Intermediate.prepare_procedures_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code cd Component.main Procedure.main) with
    | Some pc =>
      execN fuel cd (mem,regs, pc, Level 0)
    | None => inr 5
end.

Definition compile_run fuel (p : Intermediate.program) :=
 run_transitional (pre_linearize p) fuel p.

Close Scope monad_scope.


Require Import Compiler.

Definition compile_and_run_from_source := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p => compile_run fuel compiled_p
| None => inl None
end.

Require Export Extraction.Definitions.


Definition compile_and_run_from_source_ex := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match compile_run fuel compiled_p with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
    end
| None => print_error ocaml_int_0
end.



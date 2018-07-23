Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From extructures Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import Tmp.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.

Record compiler_env :=
  { program : Intermediate.program ;
    make_label : Component.id -> Procedure.id -> label ;
  }.

(* non intermediate instr *)
Inductive sp_instr :=
| SJalAlloc       : sp_instr
| SSyscallSetArg1 : register -> sp_instr
| SSyscallGetRet  : register -> sp_instr
(* Using syscall_arg3 to save ra, quick and dirty, but effective *)
| SSyscallSetArg3 : register -> sp_instr
| SSyscallGetArg3 : register -> sp_instr.

Notation code := (seq (sum sp_instr instr * mem_tag)).

(** Precompilation: translate call/ret, tag code and data, linearize code **)

Definition linearize_instr (cenv : compiler_env)
           (c : Component.id) (i : instr) : code :=
  match i with
  | ICall C P => [:: (inr (IJal (make_label cenv C P)), def_mem_tag c)]
  | IReturn => [:: (inr (IJump R_RA), def_mem_tag c)]
  | IAlloc rptr rsize => [:: (inl (SSyscallSetArg1 rsize), def_mem_tag c) ;
                             (inl (SSyscallSetArg3 R_RA), def_mem_tag c) ;
                             (inl (SJalAlloc), def_mem_tag c) ;
                             (inl (SSyscallGetArg3 R_RA), def_mem_tag c) ;
                             (inl (SSyscallGetRet rptr), def_mem_tag c) ]
  | _ => [:: (inr i, def_mem_tag c) ]
  end.



Definition head_tag (cenv : compiler_env) (c : Component.id) (p : Procedure.id) : mem_tag :=
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
  {| procedures := linearize_code cenv ;
     buffers    := linearize_bufs cenv |}.
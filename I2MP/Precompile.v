Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From CoqUtils Require Import fmap fset.

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

Notation code := (seq (instr * mem_tag)).

(** Precompilation: translate call/ret, tag, linearize **)

Definition def_tag (c : Component.id) : mem_tag :=
  {| vtag := Other ;
     color := c ;
     entry := [:: ]
  |}.

Definition precompile_callret (cenv : compiler_env)
           (c : Component.id) (i : instr) : code :=
  match i with
  | ICall C P => [:: (IJal (make_label cenv C P), def_tag c)]
  | IReturn => [:: (IJump R_RA, def_tag c)]
  | _ => [:: (i, def_tag c) ]
  end.



Definition head_tag (cenv : compiler_env) (c : Component.id) (p : Procedure.id) : mem_tag :=
  let I := Intermediate.prog_interface (program cenv) in
  let allowed_call_by (c' : Component.id) :=
      Option.default false (do i <- getm I c ;
                            do i' <- getm I c' ;
                            Some ((p \in Component.export i) && ((c, p) \in Component.import i')))
  in {| vtag := Other ;
        color := c ;
        entry := filter allowed_call_by (domm I) |}.


Definition precompile_proc (cenv : compiler_env)
           (c : Component.id) (p : Procedure.id) : code :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                                    getm map p)
  in (ILabel (make_label cenv c p), head_tag cenv c p) :: flatten (map (precompile_callret cenv c) code).

Definition precompile_component (cenv : compiler_env) (c : Component.id) : code :=
  let procs : {fset Procedure.id} := (* TODO: use explicit coercion? *)
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                            Some (domm map)) in
  flatten (map (precompile_proc cenv c) procs).


Definition precompile_code (cenv : compiler_env) : code :=
  (* TL TODO: jump to main!!! *)
  let components : {fset Component.id} := domm (Intermediate.prog_procedures (program cenv)) in
  flatten (map (precompile_component cenv) components).

Notation bufs := (NMap (NMap (seq (value * mem_tag)))).

Definition precompile_buf (cenv : compiler_env) (c : Component.id) (b : Block.id) : seq (value * mem_tag) :=
  Option.default [::] (do map <- getm (Intermediate.prog_buffers (program cenv)) c ;
                       do block <- getm map b ;
                       Some match block with
                            | inl n => repeat (Undef, def_tag c) n
                            | inr l => [seq (x, def_tag c) | x <- l]
                            end
                      ).

Definition precompile_component_bufs (cenv : compiler_env) (c : Component.id) : bufs : :=


Record prog :=
  { interface : Program.interface ;
    procedures : code ;
    buffers : bufs ;
  }.

Definition max_label (p : Intermediate.program) : nat :=
  let soup := (flatten (flatten (map codomm' (codomm' (Intermediate.prog_procedures p))))) in
  let get_label i := match i with
                    | ILabel l => Some l
                    | _ => None
                    end in
  let labels := pmap get_label soup in foldl max 0 labels + 1.

Definition max_proc_id (p : Intermediate.program) (* : *) (* nat *) :=
  let componnent_max_proc_id (map : NMap Machine.code) : nat :=
      foldl max 0 (domm map) in
  let max_proc_ids := map componnent_max_proc_id (codomm' (Intermediate.prog_procedures p)) in
  foldl max 0 max_proc_ids.

Definition precompile (p : Intermediate.program) : prog :=
  let lmax := max_label p in
  let pmax := max_proc_id p in
  let cenv := {| program := p ;
                 make_label := (fun c p => lmax + c * pmax + p) |} in
  {| interface  := Intermediate.prog_interface p ;
     procedures := precompile_code cenv ;
     buffers    := precompile_bufs cenv |}.
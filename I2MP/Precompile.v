Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From CoqUtils Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.

Record compiler_env :=
  { program : Intermediate.program ;
    make_label : Component.id -> Procedure.id -> label ;
  }.

(** Precompilation: translate call/ret, tag, linearize **)

Definition precompile_callret (cenv : compiler_env)
           (c : Component.id) (i : instr) : seq (instr * mem_tag) :=
  let def_tag := {| vtag := Other ;
                    color := c ;
                    entry := [:: ]
                 |} in
  match i with
  | ICall C P => [:: (IJal (make_label cenv C P), def_tag)]
  | IReturn => [:: (IJump R_RA, def_tag)]
  | _ => [:: (i, def_tag) ]
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
           (c : Component.id) (p : Procedure.id) : seq (instr * mem_tag) :=
  let code := Option.default [:: ] (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                                    getm map p)
  in (ILabel (make_label cenv c p), head_tag cenv c p) :: flatten (map (precompile_callret cenv c) code).

Definition precompile_component (cenv : compiler_env) (c : Component.id) :=
  let procs : {fset Procedure.id} := (* TODO: use explicit coercion? *)
      Option.default fset0 (do map <- getm (Intermediate.prog_procedures (program cenv)) c;
                            Some (domm map)) in
  flatten (map (precompile_proc cenv c) procs).


Definition precompile_code (cenv : compiler_env) :=
  let components : {fset Component.id} := domm (Intermediate.prog_procedures (program cenv)) in
  flatten (map (precompile_component cenv) components).

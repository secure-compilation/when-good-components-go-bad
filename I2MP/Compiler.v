Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq.
From CoqUtils Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


(* Definition flatten_procs (p : Intermediate.program) -> code *)

(* TODO: compiler env? *)

Record compiler_env :=
  { program : Intermediate.program ;
    make_label : Component.id -> Procedure.id -> label ;
  }.

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

From mathcomp Require Import ssreflect eqtype seq.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.

(* Definition flatten_procs (p : Intermediate.program) -> code *)

(* TODO: compiler env? *)

Record compiler_env :=
  { program : Intermediate.program ;
    current_c : LRC.ccolor (* TL TODO: conform to common *)
  }.

Definition make_tag (cenv : compiler_env) (l : option label) : mem_tag :=
  {| vtag := Other ;
     color := current_c cenv ;
     entry := match l with
                | None => [:: ]
                | Some _ => (* TL TODO *) [:: ]
              end
  |}.

Definition compile_callret cenv i :=
  match i with
  | ICall _ _ => (* TL TODO *) [:: ]
  | IReturn => [:: (IJump R_RA, make_tag cenv None)]
  | ILabel l => (* TL TODO *) [:: ]
  | _ => [:: (i, make_tag cenv None) ]
  end.

(* Definition pre_compile_proc (program : Intermediate.program) (c : unit) (p : unit) : tagged_code. *)
  (* flatten [seq compile_instr i | i <- flatten_procs p]. *)
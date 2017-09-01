Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

Record global_env := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : NMap.t (NMap.t code);
  genv_entrypoints : EntryPoint.t;
}.

Record well_formed_global_env (G: global_env) := {
  (* the interface is sound (but maybe not closed) *)
  wfgenv_interface_soundness:
    sound_interface (genv_interface G);
  (* the entrypoints and the interface are in sync *)
  wfgenv_entrypoints_soundness:
    forall C, NMap.In C (genv_entrypoints G) <-> NMap.In C (genv_interface G);
  (* the procedures and the interface are in sync *)
  wfgenv_procedures_soundness:
    forall C, NMap.In C (genv_procedures G) <-> NMap.In C (genv_interface G)
}.

Definition executing G (pc : Pointer.t) (i : instr) : Prop :=
  exists C_procs P_code,
    NMap.find (Pointer.component pc) (genv_procedures G) = Some C_procs /\
    NMap.find (Pointer.block pc) C_procs = Some P_code /\
    nth_error P_code (Pointer.offset pc) = Some i.

Fixpoint find_label (c : code) (l : label) : option nat :=
  let fix aux c o :=
      match c with
      | [] => None
      | ILabel l' :: c' =>
        if l =? l' then
          Some o
        else
          aux c' (1+o)
      | _ :: c' =>
        aux c' (1+o)
      end
  in aux c 0.

Definition find_label_in_procedure G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match NMap.find (Pointer.component pc) (genv_procedures G) with
  | Some C_procs =>
    match NMap.find (Pointer.block pc) C_procs with
    | Some P_code =>
      match find_label P_code l with
      | Some offset => Some (Pointer.component pc, Pointer.block pc, offset)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match NMap.find (Pointer.component pc) (genv_procedures G) with
  | Some C_procs =>
    let fix search ps :=
        match ps with
        | [] => None
        | (p_block,p_code) :: ps' =>
          match find_label_in_procedure G (Pointer.component pc, p_block, 0) l with
          | None => search ps'
          | Some ptr => Some ptr
          end
        end
    in search (NMap.elements C_procs)
  | None => None
  end.

Definition init_genv (p: program) : global_env :=
  let '(m, E, ps) := init_all p in
  {| genv_interface := prog_interface p;
     genv_procedures := ps;
     genv_entrypoints := E |}.

(* TODO prove the lemma, it is reasonably true *)
Lemma init_genv_preserves_well_formedness:
  forall p, well_formed_program p ->
       well_formed_global_env (init_genv p).
Proof.
Admitted.
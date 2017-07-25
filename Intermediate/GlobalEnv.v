Require Import Common.Definitions.
Require Import Intermediate.Machine.

Import Intermediate.

Record global_env := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : NMap.t (NMap.t code);
  genv_entrypoints : EntryPoint.t;
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
      | Label l' :: c' =>
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
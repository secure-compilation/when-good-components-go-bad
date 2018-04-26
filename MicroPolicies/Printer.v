From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.


Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Instance.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Export Extraction.Definitions.

Open Scope string_scope.

Axiom coqstring_of_word : forall {k}, word k -> string.
(* TL TODO: move this to Extraction.v *)
Extract Constant coqstring_of_word => "(fun _ w -> let Word x = Lazy.force w in coqstring_of_camlstring (Big.to_string x))".

Definition coqstring_of_nat (n : nat) : string := coqstring_of_word (@as_word 32 (Posz n)).

Fixpoint coqstring_of_nat_list_aux (l : list nat) : string :=
  match l with
  | nil => "]"
  | cons n nil => " " ++ coqstring_of_nat n ++ " ]"
  | cons n l' => " " ++ coqstring_of_nat n ++ ";"
  end.

Definition coqstring_of_nat_list (l : list nat) : string :=
  "[" ++ coqstring_of_nat_list_aux l.


Definition coqstring_of_value_tag (t : value_tag) : string :=
  match t with
    | Ret n => "Ret " ++ coqstring_of_nat n
    | Other => "Other"
  end.

Definition coqstring_of_ratom (a : ratom) : string :=
  "{ value: " ++ coqstring_of_word (vala a) ++ "; " ++ "tag: " ++ coqstring_of_value_tag (taga a) ++ " }".

Definition coqstring_of_regs (regs : { fmap reg mt -> ratom }) : string :=
  "regs:{
  " ++ foldl (fun s r =>
  "reg " ++ coqstring_of_word (fst r) ++ " : " ++ coqstring_of_ratom (snd r) ++ "
  " ++ s) "" regs ++ "}
  ".

Definition coqstring_of_instr (i : instr mt) : string :=
  match i with
  | Nop => "Nop"
  | Const i r => "Const r_" ++ coqstring_of_word r ++ " <- " ++ coqstring_of_word i
  | Mov r1 r2 => "Mov [TODO]"
  | Binop o r1 r2 r3 => "Binop [TODO]"
  | Load r1 r2 => "Load [TODO]"
  | Store r1 r2 => "Store [TODO]"
  | Jump r => "Jump r_" ++ coqstring_of_word r
  | Bnz r i => "Bnz [TODO]"
  | Jal i => "Jal " ++ coqstring_of_word i
  | JumpEpc => "JumpEpc"
  | AddRule => "AddRule"
  | GetTag r1 r2 => "GetTag [TODO]"
  | PutTag r1 r2 r3 => "PutTag [TODO]"
  | Halt => "Halt"
  end.


Definition coqstring_of_mem_tag (t : mem_tag) :=
  "{ vtag: " ++ coqstring_of_value_tag (vtag t) ++
  "; color: " ++ coqstring_of_nat (color t) ++
  "; entry: " ++ coqstring_of_nat_list (entry t) ++ "; }".

Definition coqstring_of_matom (a : matom) : string :=
  let value := match decode_instr (vala a) with
               | Some i => coqstring_of_instr i
               | None => coqstring_of_word (vala a)
               end in
"{ value: " ++ value ++ "; " ++ "
      tag: " ++ coqstring_of_mem_tag (taga a) ++ " }".

Definition coqstring_of_mem (mem : { fmap mword mt -> matom }) : string :=
  "mem:{
" ++ foldl (fun s m =>
              coqstring_of_word (fst m) ++ " : " ++ coqstring_of_matom (snd m) ++ "
" ++ s) "" mem ++ "}
".

Definition coqstring_of_pc_tag (t : pc_tag) : string :=
  match t with
  | Level n => "Level " ++ coqstring_of_nat n
  end.

Definition coqstring_of_pc (pc : atom (mword mt) pc_tag) : string :=
  "pc: " ++ coqstring_of_word (vala pc) ++ "; " ++ coqstring_of_pc_tag (taga pc) ++ "
".

Definition coqstring_of_internal (_ : unit) : string := "".


Definition coqstring_of_state (st : state) : string :=
"============================
" ++ coqstring_of_pc (Symbolic.pc st)
  ++ coqstring_of_internal (Symbolic.internal st)
  ++ coqstring_of_regs (Symbolic.regs st)
  ++ coqstring_of_mem (Symbolic.mem st) ++
"============================
".

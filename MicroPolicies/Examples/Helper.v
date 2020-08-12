From QuickChick Require Import Show.
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import I2MP.Encode.
Require Import I2MP.Linearize.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Exec.
Require Export Extraction.Definitions.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.Utils.
Import DoNotation.

Require Import String.
Open Scope string.

Instance showInt : Show int :=
  {
  show i := match i with
            | Posz n => show n
            | Negz n => "−" ++ show n
            end
  }.

Instance showWord {k : nat} : Show (word k) :=
  {
  show m := show (fintype.nat_of_ord (val m))
  }.

(* Instance showRegInt : Show (Types.reg mt) := *)
(*   { *)
(*   show r := show (int_of_word r) *)
(*   }. *)

Instance showRegNameOrInt : Show (reg mt) :=
  {
  show r :=
    match int_of_word r with
    | 1 => "R_ONE"
    | 2 => "R_COM"
    | 3 => "R_AUX1"
    | 4 => "R_AUX2"
    | 5 => "R_RA"
    | 6 => "R_SP"
    | 7 => "R_ARG"
    | _ => "R_" ++ show r
    end
  }.

Definition showOpcodeString (op: instr mt) :=
  match op with
  | Nop => "Nop"
  | Const i r => "Const " ++ show i ++ " " ++ show r
  | Mov r1 r2 => "Mov " ++ show r1 ++ " " ++ show r2
  | Binop _ r1 r2 r3 => "Binop " ++ "_ " ++ show r1 ++ " " ++ show r2 ++ " " ++ show r3
  | Load r1 r2 => "Load " ++ show r1 ++ " " ++ show r2
  | Store r1 r2 => "Store " ++ show r1 ++ " " ++ show r2
  | Jump r => "Jump " ++ show r
  | Bnz r i => "Bnz " ++ show r ++ " " ++ show i
  | Jal i => "Jal " ++ show i
  | JumpEpc => "JUMPEPC"
  | AddRule => "ADDRULE"
  | GetTag _ _ => "GETTAG"
  | PutTag _ _ _ => "PUTTAG"
  | Halt => "Halt"
  end.

Definition showMword (m : mword mt) :=
  match decode_instr m with
  | None => "Not an op"
  | Some op => showOpcodeString op
  end.

Definition showMwordNat (m : mword mt) :=
  show (fintype.nat_of_ord (val m)).

Definition showAtom {A : Type} `{Show A} (x: atom (mword mt) A) :=
  showMword (vala x) ++ " @ " ++ show (taga x).

Definition showAtom' {A : Type} `{Show A} (x: atom (mword mt) A) :=
  showMwordNat (vala x) ++ " @ " ++ show (taga x).
(* Instance showAtom {A B : Type} `{Show A} `{Show B} : Show (atom A B) := *)
(*   { *)
(*   show x := show (vala x) ++ "@" ++ show (taga x) *)
(*   }. *)

Definition showMem {A : Type} `{Show A} (f : {fmap (mword mt) -> atom (mword mt) A}) :=
  foldl (fun acc '(key,elt) =>
           acc ++ (showMwordNat key) ++ " : "
               ++ (showAtom elt) (* ++ " " ++ (showAtom' elt) *) ++ newline)
        "" f.

(* Inductive pc_tag : Type := Level : nat -> pc_tag. *)

(* Module Import PCTagEq. *)
(* Definition nat_of_pc_tag t := *)
(*   match t with *)
(*   | Level n => n *)
(*   end. *)

(* Definition pc_tag_of_nat n := Level n. *)

(* Lemma nat_of_pc_tagK : cancel nat_of_pc_tag pc_tag_of_nat. *)
(* Proof. by case. Qed. *)

(* Definition pc_tag_eqMixin := CanEqMixin nat_of_pc_tagK. *)
(* Canonical pc_tag_eqType := EqType pc_tag pc_tag_eqMixin. *)
(* End PCTagEq. *)

(* Record mem_tag : Type := MTag { *)
(*   vtag   : [eqType of value_tag]; *)
(*   color  : Component.id; *)
(*   entry  : option (Procedure.id * list Component.id); *)
(* }. *)


(* Definition def_mem_tag (c : Component.id) : mem_tag := *)
(*   {| vtag := Other ; *)
(*      color := c ; *)
(*      entry := None *)
(*   |}. *)

Instance showTag {tk : Symbolic.tag_kind} : Show (Symbolic.tag_type Symbolic.ttypes tk) :=
  {
  show t := match tk, t as to return string with
            | Symbolic.R, t => "Register tag: " ++ match t with
                                                  | Ret n => "Ret " ++ show n
                                                  | Other => "Other"
                                                  end
            | Symbolic.M, t => "Memory tag: (" ++
                                             match vtag t with
                                             | Ret n => "Ret " ++ show n
                                             | Other => "Other"
                                             end ++
                                             ", " ++
                                             match color t with
                                             | n => "Component " ++ show n
                                             end ++
                                             ", " ++
                                             match entry t with
                                             | None => "Not an entry point"
                                             | Some (pid, cids) => "Entry point for procedure " ++ show pid
                                             end ++
                                             ")"
            | Symbolic.P, t => "PC tag: " ++
                                      match t with
                                      | Level n => "Level " ++ show n
                                      end
            end
  }.


Definition showRegs {A : Type} `{Show A} (f : {fmap (Types.reg mt) -> atom (mword mt) A}) :=
  foldl (fun acc '(key,elt) =>
           acc ++ (show key) ++ " : "
               ++ (showAtom' elt) ++ newline)
        "" f.
Instance showState : Show state :=
  {
  show st := let 'Symbolic.State mem reg pc@tpc extra := st in
             ""
               ++ "Mem:" ++ nl ++ showMem mem ++ nl
               ++ "Reg:" ++ nl ++ showRegs reg ++ nl
               ++ "PC:" ++ showMwordNat pc ++ " @ " ++ show tpc
  }.


Fixpoint execN (n: nat) (st: state) : (option state) * string :=
  let 'Symbolic.State mem reg pc@tpc extra := st in
  match n with
  | O => (Some st, "No more fuel in state:" ++ nl ++ show st)
  | S n' =>
    match mem pc with
    | Some iti => let: i@_ := iti in
                 match decode_instr i with
                 | Some Halt => (Some st, "Halted with registers:" ++ nl ++ showRegs (Symbolic.regs st))
                 | _ => match stepf st with
                       | None => (None, "Invalid step")
                       | Some (st', _) => execN n' st'
                       end
                 end
    | _ => match table pc with
          | Some _ => match stepf st with
                     | None => (None, "Invalid step")
                     | Some (st', _) => execN n' st'
                     end
          | None => (None, "Invalid PC")
          end
    end
  end.

Definition print_reg (st : state) (n : nat) : unit :=
  match (Symbolic.regs st) (as_word n) with
  | None => print_error ocaml_int_2
  | Some n => print_ocaml_int (int2int (int_of_word (vala n)))
  end.

Fixpoint print_regs (st : state) (n : nat) (f : fstate) : fstate :=
  match n with
  | O => unit_to_fstate (print_reg st n)
  | S n => let f' := unit_to_fstate (print_reg st (S n)) in print_regs st n f'
  end.


Definition compile_and_run (p: Source.program) (fuel: nat) :=
  let str :=
      match compile_program p with
      | None => "Compilation failed"%string
      | Some inter_p =>
        let st := load (encode (linearize inter_p)) in
        match execN fuel st with
        | (None, str) => str
        | (Some st, str) => str
        end
      end in
  print_string_ocaml str.

(* Definition compile_and_run' (p: Intermediate.program) (fuel:nat) := *)
(*   let st := load (encode (linearize p)) in *)
(*     match execN fuel st with *)
(*     | None => print_error ocaml_int_1 *)
(*     | Some st' => fstate_to_unit (print_regs st' 6 fstate0) *)
(*     end *)
(* . *)

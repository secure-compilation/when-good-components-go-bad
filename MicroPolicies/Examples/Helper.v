From QuickChick Require Import Show.
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.

Require Import Transitional.
(* Require Import I2MP.Encode.
Require Import I2MP.Linearize.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Exec.

Require Import MicroPolicies.Instance.
 *)
Require Import MicroPolicies.Utils.
Require Export Extraction.Definitions.
Require Import Intermediate.Machine.

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

Print value.

Instance showValue : Show value :=
 {
  show v := match v with
    | Int z => show z
    | Ptr p => "Pointer: (" ++ show p ++ ")"
    | Undef => "Undef"
  end
}.


Instance showRegInter : Show (Intermediate.Register.t) :=
 {
 show r :=   foldl (fun acc '(n,v) =>
           acc ++ (show n) ++ " : "
               ++ (show v) ++ newline)
        "" r
 }.

Print Transitional.stackless.

Instance showStackless : Show (Transitional.stackless) :=
  {
  show s := let '(mem,regs,pc,Level n) := s in
   "Memory: NO" ++ newline ++ "Registers: " ++ (show regs) ++ newline ++ "pc: " ++ show pc ++ "; level: " ++ show n
  }.


Instance show_immv : Show imvalue :=
  {|
    show :=
      fun iv =>
        match iv with
        | IInt n => "IInt " ++ (show n)
        | IPtr p => "IPtr " ++ (show p)
        end
  |}.

Instance show_register : Show register :=
  {|
    show :=
      fun r =>
        match r with
        | R_ONE => "R_ONE"
        | R_COM => "R_COM"
        | R_AUX1 => "R_AUX1"
        | R_AUX2 => "R_AUX2"
        | R_RA => "R_RA"
        | R_SP => "R_SP"
        | R_ARG => "R_ARG"
        end
  |}.

Instance show_binop : Show Common.Values.binop :=
  {|
    show :=
      fun op =>
        match op with
        | Common.Values.Add => "+"
        | Common.Values.Minus => "-"
        | Common.Values.Mul => "*"
        | Common.Values.Eq => "="
        | Common.Values.Leq => "<="
        end
  |}.


Instance show_trans : Show Transitional.instr :=
  {| show :=
       fun i =>
         match (i:Transitional.instr) with
           | Transitional.TrNop => "INop"
           | Transitional.TrLabel lbl => "ILabel " ++ (show lbl)
           | Transitional.TrConst v r => "IConst " ++ (show v) ++ " " ++ (show r)
           | Transitional.TrMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrBinOp op r1 r2 r3 => "IBinop " ++ (show op)
                                            ++ " " ++ (show r1)
                                            ++ " " ++ (show r2)
                                            ++ " " ++ (show r3)
           | Transitional.TrLoad r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrStore r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrAlloc r1 r2 => "IAlloc " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
           | Transitional.TrJump r => "IJump " ++ (show r)
           | Transitional.TrJalNat l => "IJalNat " ++ (show l)
           | Transitional.TrJalProc l => "IJalProc " ++ (show l)
           | Transitional.TrHalt => "IHalt"
         end
  |}.


Definition show_nmap { A :Type} `{_ : Show A} (m : (NMap A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (elementsm m)
    Coq.Strings.String.EmptyString.




Instance show_dummymemtag : Show Transitional.mem_tag :=
 {
  show mt := ""
}.

Instance show_seq : Show (list (Transitional.instr * Transitional.mem_tag)) :=
{
  show l := let fix show_aux l := match l with 
    | [] => ""
    | i :: iss => show i ++ newline ++ show_aux iss
   end
  in show_aux l
}.

Instance show_code : Show Transitional.code :=
 {
  show c := show_nmap c
}.


Definition compile_and_show (p: Source.program) :=
  let str :=
      match compile_program p with
      | None => "Compilation failed"%string
      | Some inter_p =>
        let cde := (pre_linearize inter_p) in
        (* match execN fuel st with
        | (None, str) => str
        | (Some st, str) => str
        end*)
        show cde
      end in
  print_string_ocaml str.

(* Definition compile_and_run' (p: Intermediate.program) (fuel:nat) := *)
(*   let st := load (encode (linearize p)) in *)
(*     match execN fuel st with *)
(*     | None => print_error ocaml_int_1 *)
(*     | Some st' => fstate_to_unit (print_regs st' 6 fstate0) *)
(*     end *)
(* . *)

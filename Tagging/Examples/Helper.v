From QuickChick Require Import Show.
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.

Require Import Tagging.Tags.
Require Import Tagging.Memory.
Require Import Tagging.Language.
Require Import Tagging.LinearizeCompartments.
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
Require Import Compiler.

Import DoNotation.

Require Import String.




Definition compile_run fuel (p : Intermediate.program) :=
 run_transitional fuel (pre_linearize p).



Definition compile_and_run_from_source := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p => compile_run fuel compiled_p
| None => inl None
end.

Definition compile_and_run_from_source_ex := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match compile_run fuel compiled_p with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
    end
| None => print_error ocaml_int_0
end.



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
  show m := show (fintype.nat_of_ord (mathcomp.ssreflect.eqtype.val m))
  }.

(* Instance showRegInt : Show (Types.reg mt) := *)
(*   { *)
(*   show r := show (int_of_word r) *)
(*   }. *)

Print value.

Instance showValue : Show Tags.value :=
 {
  show v := match v with
    | Tags.Int z => show z
    | Tags.Ptr p => "Pointer: (" ++ show p ++ ")"
    | Tags.Undef => "Undef"
  end
}.

Instance showTValue : Show tvalue :=
 {
  show v := show (val v)
}.


(* Instance showRegInter : Show (Intermediate.Register.t) :=
 {
 show r :=   foldl (fun acc '(n,v) =>
           acc ++ (show n) ++ " : "
               ++ (show v) ++ newline)
        "" r
 }. *)


Instance showReg : Show Register.t :=
 { show r := foldl (fun acc '(n,v) =>
           acc ++ (show n) ++ " : "
               ++ (show v) ++ newline)
        "" r
 }.

Instance showStackless : Show (Tagging.Language.stackless) :=
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


Instance show_trans : Show Tagging.Language.instr :=
  {| show :=
       fun i =>
         match i with
           | Tagging.Language.TrNop => "INop"
           | Tagging.Language.TrLabel lbl => "ILabel " ++ (show lbl)
           | Tagging.Language.TrConst v r => "IConst " ++ (show v) ++ " " ++ (show r)
           | Tagging.Language.TrMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
           | Tagging.Language.TrBinOp op r1 r2 r3 => "IBinop " ++ (show op)
                                            ++ " " ++ (show r1)
                                            ++ " " ++ (show r2)
                                            ++ " " ++ (show r3)
           | Tagging.Language.TrLoad r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
           | Tagging.Language.TrStore r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
           | Tagging.Language.TrAlloc r1 r2 => "IAlloc " ++ (show r1) ++ " " ++ (show r2)
           | Tagging.Language.TrBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
           | Tagging.Language.TrJump r => "IJump " ++ (show r)
           | Tagging.Language.TrJalNat l => "IJalNat " ++ (show l)
           | Tagging.Language.TrJalProc l => "IJalProc " ++ (show l)
           | Tagging.Language.TrHalt => "IHalt"
         end
  |}.


Definition show_nmap { A :Type} `{_ : Show A} (m : (NMap A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (elementsm m)
    Coq.Strings.String.EmptyString.




Instance show_dummymemtag : Show Tags.mem_tag :=
 {
  show mt := ""
}.

Instance show_prod : Show (Tagging.Language.instr * mem_tag) :=
 {
 show p := let '(i,t) := p in show i
}.

Instance show_seq : Show (list (Tagging.Language.instr * mem_tag)) :=
{
  show l := let fix show_aux l := match l with 
    | [] => ""
    | i :: iss => show i ++ newline ++ show_aux iss
   end
  in show_aux l
}.

Instance show_code : Show Tagging.Language.code :=
 {
  show c := show_nmap c
}.


Instance show_prog : Show Language.program :=
{
  show p := show (prog_code p)
}.

Instance show_pc : Show Tags.Pointer.t :=
{
   show pc := let '(b,o) := pc in "(" ++ show b ++ "," ++ show o ++ ")"
}.

Definition compile_and_show (p: Source.program) :=
  let str :=
      match S2I.Compiler.compile_program p with
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



Fixpoint execN_more (n: nat) (cde: Language.code) (st: stackless) str : string * (option Z + nat) :=
  match n with
  | O => (str, inr 3)
  | S n' =>
    match eval_step cde st with
    | None =>
      let '(_, regs, _, _) := st in
      match val (Tags.Register.get R_COM regs) with
      | Tags.Int i => (str,inl (Some i))
      | _ => (str,inr 4)
      end
    | Some (_, st') => let '(_, regs, pc, _) := st' in
        let stri := match cde (Tags.Pointer.block pc) with
                    | Some c_cde => match nth_error c_cde (Z.to_nat (Tags.Pointer.offset pc)) with
                              | Some (instr,tag) => show instr
                              | None => "nth_error"
                              end
                    | None => "No C_Cde"
                    end in 
      if Nat.leb 0 n then  execN_more n' cde st' (show pc ++ " [" ++ stri ++ "]" ++
                                                        " | RCOM=" ++ show (Tags.Register.get R_COM regs) ++ 
                                                        " | RRA=" ++ show (Tags.Register.get R_RA regs) ++ 
                                                        " | RSP=" ++ show (Tags.Register.get R_SP regs) ++ 
                                                        " | RAUX1=" ++ show (Tags.Register.get R_AUX1 regs) ++ newline ++ str) 
      else execN_more n' cde st' str
    end
  end.


Definition run_transitional_bis fuel (p : Language.program) :=
    let mem := prepare_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code (prog_code p) Component.main Procedure.main) with
    | Some pc =>
      execN_more fuel (prog_code p) (mem,regs, pc, Level 0) ""
    | None => ("",inr 5)
end.


Definition debug := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match  run_transitional_bis fuel (pre_linearize compiled_p) with
    | (str,inl (Some n)) => print_string_ocaml str (* print_ocaml_int (z2int n)*)
    | (str,inl None) => print_string_ocaml str
    | (str,inr n) => print_string_ocaml str
    end
| None => print_error ocaml_int_0
end.


(* Definition compile_and_run' (p: Intermediate.program) (fuel:nat) := *)
(*   let st := load (encode (linearize p)) in *)
(*     match execN fuel st with *)
(*     | None => print_error ocaml_int_1 *)
(*     | Some st' => fstate_to_unit (print_regs st' 6 fstate0) *)
(*     end *)
(* . *)

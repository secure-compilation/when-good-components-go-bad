Require Import Common.Definitions.
Require Import Common.Values.



Require Import String.
Open Scope string.
Require Import Intermediate.Machine.
From QuickChick Require Import Show.
Require Import Source.Language.

Require Import Transitional.
Require Import I2MP.Examples.Helper.
Require Import Source.Examples.Factorial.


Fixpoint execN (n: nat) (cde: code) (st: stackless) str : string * (option Z + nat) :=
  match n with
  | O => (str, inr 3)
  | S n' =>
    match eval_step cde st with
    | None =>
      let '(_, regs, _, _) := st in
      match Intermediate.Register.get R_COM regs with
      | Int i => (str,inl (Some i))
      | _ => (str,inr 4)
      end
    | Some (_, st') => let '(_, regs, pc, _) := st' in
        let stri := match cde (Pointer.component pc) with
                    | Some c_cde => match nth_error c_cde (Z.to_nat (Pointer.offset pc)) with
                              | Some (instr,tag) => show instr
                              | None => "nth_error"
                              end
                    | None => "No C_Cde"
                    end in 
      if Nat.leb 0 n then  execN n' cde st' (show pc ++ " [" ++ stri ++ "]" ++
                                                        " | RCOM=" ++ show (Intermediate.Register.get R_COM regs) ++ 
                                                        " | RRA=" ++ show (Intermediate.Register.get R_RA regs) ++ newline ++ str) 
      else execN n' cde st' str
    end
  end.


Definition run_transitional cd fuel p :=
    let '(mem, _, entrypoints) := Intermediate.prepare_procedures_initial_memory p in
    let regs := Intermediate.Register.init in
    match (find_plabel_in_code cd Component.main Procedure.main) with
    | Some pc =>
      execN fuel cd (mem,regs, pc, Level 0) ""
    | None => ("",inr 5)
end.


Definition debug := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match  run_transitional (pre_linearize compiled_p) fuel compiled_p with
    | (str,inl (Some n)) => print_string_ocaml str (* print_ocaml_int (z2int n)*)
    | (str,inl None) => print_string_ocaml str
    | (str,inr n) => print_string_ocaml str
    end
| None => print_error ocaml_int_0
end.




Definition fuel := 2000%nat.
Definition to_run := compile_and_run_from_source_ex factorial fuel.
Definition to_show := compile_and_show factorial.
Definition to_debug := debug factorial fuel.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_mp_compiled_factorial.ml" to_run.

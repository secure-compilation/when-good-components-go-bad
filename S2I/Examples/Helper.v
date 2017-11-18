Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.CS.
Require Import S2I.Compiler.
Require Export Extraction.Definitions.

Definition compile_and_run (p: Source.program) (input: value) (fuel: nat) :=
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some compiled_p =>
    match CS.init_genv_and_state compiled_p input with
    | None => print_error ocaml_int_1
    | Some (G, st) =>
      match CS.execN fuel G st with
      | None => print_error ocaml_int_2
      | Some n => print_ocaml_int (z2int n)
      end
    end
  end.
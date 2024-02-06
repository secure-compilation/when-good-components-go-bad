Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.CS.
Require Import Source.GlobalEnv.

Require Export Source.Language.
Require Export Extraction.Definitions.

Import Source.

Definition run (p: program) (fuel: nat) :=
  let G := prepare_global_env p in
  let st := CS.initial_machine_state p in
  match CS.execN fuel G st with
  | Some [CState _, _, _, _, E_exit, _] => print_explicit_exit tt
  | Some [CState _, _, _, _, E_val (Int n), _] => print_ocaml_int (z2int n)
  | Some [CState _, _, _, Kif _ _ _, E_val (Undef), _] => print_error ocaml_int_1
  | Some [CState _, _, _, Kalloc _, E_val (Undef), _] => print_error ocaml_int_2
  | _ => print_error ocaml_int_0
  end.

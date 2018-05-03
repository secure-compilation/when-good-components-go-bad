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
  | Some [CState _, _, _, _, E_exit] => print_explicit_exit tt
  | Some [CState _, _, _, _, E_val (Int n)] => print_ocaml_int (z2int n)
  | _ => print_error ocaml_int_0
  end.

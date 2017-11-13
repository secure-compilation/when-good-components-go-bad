(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Source.Language.
Require Import Source.Examples.
Require Import S2I.Compiler.
Require Import I2SFI.Compiler.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Import MonadNotations.
Open Scope monad_scope.

Open Scope positive_scope.
Definition increment : Source.program := {|
  Source.prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [(2, 1)];
                              Component.export := [1] |});
                       (2, {| Component.import := [];
                              Component.export := [1] |})];
  Source.prog_buffers := PMapExtra.of_list [(1, 1%nat); (2, 1%nat)];
  Source.prog_procedures := PMapExtra.of_list [
    (* NOTE the version with E_exit is the right one, but unfortunately it is difficult
            to debug with extraction. Hence, the second version without E_exit *)
    (*(1, NMapExtra.of_list [(0, E_seq (E_call 2 0 (E_val (Int 6))) E_exit)]);*)
    (1, PMapExtra.of_list [(1, E_call 2 1 (E_val (Int 6)))]);
    (2, PMapExtra.of_list [(1,     
        (E_binop Add
                 (E_deref E_local)
                 (E_val (Int 1))))])];
  Source.prog_main := (1, 1)
|}.
Close Scope positive_scope.

Definition test (sp : Source.program) : @Either sfi_program :=
  match S2I.Compiler.compile_program sp with
  | None => Left "S2I compiler failed"
  | Some ip => compile_program ip
  end.


Example test_increment :
  exists (tp : sfi_program),
    test increment = Right tp.
Proof.
  compute. eauto. Qed.

(* (* this doesn't end Need to figure out TODO *) *)
(* Example test_factorial : *)
(*   exists (ip : Intermediate.program) (tp : sfi_program), *)
(*     S2I.Compiler.compile_program Examples.factorial = Some ip /\ *)
(*     I2SFI.Compiler.compile_program ip = Right tp. *)
(* Proof. *)
(*   compute. eauto. Qed. *)


(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Source.Language.
(* Require Import Source.Examples.Factorial. *)
(* Require Import Source.Examples.Identity. *)
(* Require Import Source.Examples.Increment. *)
Require Import S2I.Compiler.
Require Import I2SFI.Compiler.
Require Import I2SFI.CompilerFlags.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Require Import I2SFI.CompTestUtil.
Require Import I2SFI.AbstractMachine.
Require Import I2SFI.CompEitherMonad.
Require Import I2SFI.CompStateMonad.


Import MonadNotations.
Open Scope monad_scope.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)

Definition newline := String "010" ""%string.

Open Scope nat_scope.
Definition increment : Source.program := {|
  Source.prog_interface :=
   mkfmap [(1, {| Component.import := fset1 (2, 1);
                              Component.export := (fset1 1) |});
                       (2, {| Component.import := fset0;
                              Component.export := fset1 1 |})];
  Source.prog_buffers := mkfmap [(1, (inl 1%nat)); (2, (inl 1%nat))];
  Source.prog_procedures := mkfmap [
    (* NOTE the version with E_exit is the right one, but unfortunately it is difficult
            to debug with extraction. Hence, the second version without E_exit *)
    (*(1, NMapExtra.of_list [(0, E_seq (E_call 2 0 (E_val (Int 6))) E_exit)]);*)
    (1, mkfmap [(1, E_call 2 1 (E_val (Int 6)))]);
    (2, mkfmap [(1,     
        (E_binop Add
                 (E_deref E_local)
                 (E_val (Int 1))))])];
  Source.prog_main := Some (1, 1)
|}.
Close Scope nat_scope.

Definition test (sp : Source.program) : @CompEither sfi_program :=
  match S2I.Compiler.compile_program sp with
  | None => CompEitherMonad.Left "S2I compiler failed" NoInfo
  | Some ip => compile_program all_flags_off ip
  end.

Instance show_sp : Show Source.program :=
  {|
    show := fun _ => Coq.Strings.String.EmptyString
  |}.

Definition integration_pbt (sp : Source.program) : Checker :=
  forAll (returnGen sp)
         ( fun sp =>
             match S2I.Compiler.compile_program sp with
             | None => whenFail "Source program does not compile" false
             | Some ip =>
               match I2SFI.Compiler.compile_program all_flags_off ip with
               | CompEitherMonad.Left msg err =>
                 whenFail ("Compilation error: "
                             ++ msg
                             ++ newline
                             ++ (show err)
                             ++ newline
                             ++ (show ip)
                          ) false
               | CompEitherMonad.Right p =>
                 match CS.eval_program (5000%nat) p (RiscMachine.RegisterFile.reset_all) with
                 | TargetSFI.EitherMonad.Left msg err => whenFail
                                                          (msg ++ (show err)
                                                               ++ newline
                                                               ++ (show ip) )
                                                          false
                 | TargetSFI.EitherMonad.Right (t,(mem,_,regs)) => checker true
                 end
               end
             end
         ).

(* Definition procs_labels_increment : Checker := *)
(*   forAll *)
(*     (  *)
(*        match S2I.Compiler.compile_program increment with *)
(*        | None => *)
(*          returnGen 0%N *)
(*        | Some ip => *)
(*          returnGen ( *)
(*              let procs_labels := exported_procs_labels (Intermediate.prog_procedures ip) *)
(*                                               (Intermediate.prog_interface ip) in *)
(*              List.fold_left *)
(*                 N.max *)
(*                 (List.flat_map *)
(*                    (fun m => List.map (fun '(_,(_,l)) => l) (elementsm m)) *)
(*                    (List.map snd (elementsm procs_labels))) *)
(*                 1%N  *)
(*            ) *)
(*        end *)
(*     ) *)
(*     ( fun x => *)
(*         checker *)
(*           ( *)
(*               N.eqb 3 x *)
(*           ) *)
(*     ). *)

Extract Constant Test.defNumTests => "1".
(* QuickChick (procs_labels_increment). *)
(* QuickChick (integration_pbt identity). *)
(* QuickChick (integration_pbt increment). *)
(* QuickChick (integration_pbt factorial). *)
(* QuickChick (integration_pbt Source.Examples.Increment.increment). *)
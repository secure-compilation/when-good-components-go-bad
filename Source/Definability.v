Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.

Import Source.

Section Definability.
  Variable p: program.
  Variable ictx: Program.interface.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  Theorem context_definability:
    forall beh,
      program_behaves (PS.sem p ictx) beh ->
    exists ctx,
      PMap.Equal (prog_interface ctx) ictx /\
      program_behaves (CS.sem (program_link p ctx mainC mainP)) beh.
  Proof.
  Admitted.
End Definability.
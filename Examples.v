Require Import CompCert.Behaviors.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.TracesInform.
Require Import Common.RenamingOption.
Require Import Common.Memory.
Require Import Common.Values.

Require Import Source.DefinabilityEnd.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import Intermediate.RecombinationRel.
Require Import S2I.Compiler.
Require Import S2I.Definitions.


From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.

Set Bullet Behavior "Strict Subproofs".


Definition c1 : Component.id := 1.
Definition c1p1 : Procedure.id := 1.
Definition c1exports : {fset Procedure.id} := fset1 c1p1.
Definition c1imports : {fset Component.id * Procedure.id} := fset0.

Definition c1intf : Component.interface.
  constructor; [exact c1exports | exact c1imports].
Defined.

Definition Pintf : Program.interface :=
  setm emptym c1 c1intf.

Definition prog_of_trace_Pintf := Definability.program_of_trace Pintf.

Definition Pbuffers : NMap (nat + list value) :=
  setm emptym c1 (inr [Int 50; Int 60; Int 70]).

Definition c1mem :=
  ComponentMemory.prealloc Pbuffers.

Definition Pmem := setm emptym c1 c1mem.

Definition prog_of_trace_Pintf_Pbuffers := prog_of_trace_Pintf Pbuffers.

Definition tP : Events.trace event_inform.
  apply cons.
  - apply EConst.
    + exact c1.
    + exact (Int 700).
    + exact E_R_ONE.
    + exact (setm emptym c1 c1mem).
    + exact (setm Intermediate.Register.init (Intermediate.Register.to_nat R_ONE) (Int 700)).
  - exact nil.
Defined.

Compute match (Definability.program_of_trace Pintf Pbuffers tP) with
        | Some p =>
          match getm (Source.prog_procedures p) 1 with
          | Some c1procs => getm c1procs 1
          | _ => None
          end
        | _ => None
        end.

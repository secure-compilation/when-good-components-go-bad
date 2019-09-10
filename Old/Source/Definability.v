Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.Definability.
Import Source.Definability.
Module D := Source.Definability.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Definability.

  Section WithTrace.

    Lemma counter_value_app C prefix1 prefix2 :
      D.counter_value C (prefix1 ++ prefix2)
      = (D.counter_value C prefix1 + D.counter_value C prefix2) % Z.
    Proof.
      unfold D.counter_value.
      now rewrite comp_subtrace_app app_length Nat2Z.inj_add.
    Qed.

End WithTrace.
End Definability.

Require Import CompCert.Events.
Require Import CompCert.Coqlib.

Require Import Coq.Relations.Relations.
Require Import Coq.Wellfounded.Wellfounded.

Require Import CompCert.Smallstep.

Set Implicit Arguments.


Section STEP.

Variable genv: Type.
Variable state: Type.

Variable stepS: genv -> state -> trace -> state -> Prop.
Variable stepT: genv -> state -> trace -> state -> Prop.

Variable allowed_UB: state -> Prop.

Variant step_restricted_UB (ge: genv): state -> trace -> state -> Prop :=
  | step_UB_allowed: forall s t s',
      stepT ge s t s' ->
      allowed_UB s ->
      step_restricted_UB ge s t s'
  | step_UB_disallowed: forall s t s',
      stepS ge s t s' ->
      stepT ge s t s' ->
      step_restricted_UB ge s t s'
.

End STEP.

Section SEMANTICS.

  Context {state genvtype: Type}.
  Variable step1: genvtype -> state -> trace -> state -> Prop.
  Variable step2: genvtype -> state -> trace -> state -> Prop.
  Variable initial_state: state -> Prop.
  Variable final_state: state -> Prop.
  Variable globalenv: genvtype.


  Variable allowed_UB: state -> Prop.

  Let L1: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step1;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Let L2: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step2;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Definition L_restricted_UB: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step_restricted_UB step1 step2 allowed_UB;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Hypothesis extends_step: forall ge s t s',
      step L1 ge s t s' ->
      step L2 ge s t s'.

End SEMANTICS.

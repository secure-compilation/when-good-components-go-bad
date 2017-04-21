(* from CompCert Smallstep.v *)

Require Import Common.
Require Import Events.

Set Implicit Arguments.
Section CLOSURES.

Variable genv: Type.
Variable state: Type.
Variable step: genv -> state -> trace -> state -> Prop.

Definition nostep (ge: genv) (s: state) : Prop :=
  forall t s', ~(step ge s t s').

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

End CLOSURES.

Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> Prop;   (* we don't have a return value *)
  globalenv: genvtype;
}.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : smallstep_scope.
Open Scope smallstep_scope.


(* removed return value and order (measure) *)
Record fsim_properties (L1 L2: semantics)
       (match_states: state L1 -> state L2 -> Prop) : Prop := {
    fsim_match_initial_states:
      forall s1, initial_state L1 s1 ->
      exists s2, initial_state L2 s2 /\ match_states s1 s2;
    fsim_match_final_states:
      forall s1 s2,
      match_states s1 s2 -> final_state L1 s1 -> final_state L2 s2;
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall s2, match_states s1 s2 ->
      exists s2',
         (Step L2 s2 t s2') /\ match_states s1' s2';
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics) : Prop :=
  Forward_simulation (match_states: state L1 -> state L2 -> Prop)
                     (props: fsim_properties L1 L2 match_states).

Arguments Forward_simulation {L1 L2} match_states props.



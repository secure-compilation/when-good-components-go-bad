Require Import Common.Definitions.
Require Import Common.Util.

(* an imported procedure is either open (the interface is missing)
   or exported by the right component *)
Definition sound_interface (interface : Program.interface) : Prop :=
  forall C CI,
    Program.has_component interface C CI ->
  forall C' P,
    Component.is_importing CI C' P ->
  forall CI',
    Program.has_component interface C' CI' ->
    Component.is_exporting CI' P.

(* an imported procedure is always exported by the right component *)
Definition closed_interface (interface : Program.interface) : Prop :=
  forall C CI,
    Program.has_component interface C CI ->
  forall C' P,
    Component.is_importing CI C' P ->
  exists CI',
    Program.has_component interface C' CI' /\
    Component.is_exporting CI' P.

Lemma closed_interface_is_sound:
  forall iface,
    closed_interface iface -> sound_interface iface.
Proof.
  unfold closed_interface, sound_interface.
  intros iface Hiface_closed.
  intros.
  specialize (Hiface_closed C CI H C' P H0).
  destruct Hiface_closed as [CI'' [H1' H2]].
  unfold Program.has_component in H1, H1'.
  enough (HsameCI: CI' = CI'').
  - subst. auto.
  - apply ZMapFacts.MapsTo_fun with iface C'; auto.
Qed.

Definition mergeable_interfaces (i1 i2 : Program.interface) : Prop :=
  ZMapExtra.Disjoint i1 i2.

Definition interface_merge (i1 i2 : Program.interface) (prf: mergeable_interfaces i1 i2) :=
  ZMapExtra.update i1 i2.

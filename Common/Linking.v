Require Import Common.Definitions.
Require Import Common.Util.

(* an imported procedure is either open (the interface is missing)
   or exported by the right component *)
Definition sound_interface (interface : Program.interface) : Prop :=
  forall C C' P, imported_procedure interface C C' P ->
  forall CI',
    Program.has_component interface C' CI' ->
    Component.is_exporting CI' P.

(* an imported procedure is always exported by the right component *)
Definition closed_interface (interface : Program.interface) : Prop :=
  forall C C' P, imported_procedure interface C C' P ->
                 exported_procedure interface C' P.

Lemma closed_interface_is_sound:
  forall iface,
    closed_interface iface -> sound_interface iface.
Proof.
  unfold closed_interface, sound_interface.
  intros iface Hiface_closed C C' P Himported CI' HCI'.
  specialize (Hiface_closed C C' P Himported).
  destruct Hiface_closed as [CI'' [HCI'' Hexporting]].
  unfold Program.has_component in HCI', HCI''.
  enough (HsameCI: CI' = CI'').
  - subst. auto.
  - apply PMapFacts.MapsTo_fun with iface C'; auto.
Qed.

Definition mergeable_interfaces (i1 i2 : Program.interface) : Prop :=
  PMapExtra.Disjoint i1 i2.

Definition interface_merge (i1 i2 : Program.interface) (prf: mergeable_interfaces i1 i2) :=
  PMapExtra.update i1 i2.

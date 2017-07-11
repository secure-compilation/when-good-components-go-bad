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

Definition mergeable_interfaces (i1 i2 : Program.interface) : Prop :=
  NMapExtra.Disjoint i1 i2.

Definition interface_merge (i1 i2 : Program.interface) (prf: mergeable_interfaces i1 i2) :=
  NMapExtra.update i1 i2.

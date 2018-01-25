Require Import Common.Definitions.
Require Import Common.Util.

From mathcomp Require Import ssreflect ssrfun ssrbool.

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
  - rewrite HCI'' in HCI'. inversion HCI'. reflexivity.
Qed.

Definition linkable_mains (main1 main2: option (Component.id * Procedure.id)) : Prop :=
  ~~ (main1 && main2).

Lemma linkable_mains_sym:
  forall m1 m2,
    linkable_mains m1 m2 -> linkable_mains m2 m1.
Proof.
  intros m1 m2 Hlinkable.
  destruct m1; destruct m2; simpl in *; auto.
Qed.

(* we assume that the provided mains are linkable *)
Definition main_link (main1 main2: option (Component.id * Procedure.id))
  : option (Component.id * Procedure.id) :=
  if main1 then main1 else main2.

Lemma main_link_with_empty_main:
  forall main,
    main_link main None = main.
Proof.
  intros main.
  destruct main; reflexivity.
Qed.

Require Export Common.Maps.

Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.

Export ListNotations.
Open Scope list_scope.

Module Procedure.
  Definition id := nat.
End Procedure.

Module Component.
  Definition id := nat.

  Record interface := mkCompInterface {
    export : list Procedure.id;
    import : list (Component.id * Procedure.id)
  }.

  Definition is_importing CI C P : Prop := In (C,P) (import CI).
  Definition is_exporting CI P : Prop := In P (export CI).
End Component.

Module Program.
  Definition interface := NMap.t Component.interface.
  Definition has_component Is C (CI : Component.interface) := NMap.MapsTo C CI Is.
End Program.

Definition exported_procedure
           (Is : Program.interface)
           (C : Component.id) (P : Procedure.id) :=
  exists CI,
    Program.has_component Is C CI /\ Component.is_exporting CI P.

Definition imported_procedure
           (Is : Program.interface)
           (C C': Component.id) (P : Procedure.id) : Prop :=
  exists CI,
    Program.has_component Is C CI /\ Component.is_importing CI C' P.

Lemma procs_eqdec (CP : Component.id * Procedure.id) (CP' : Component.id * Procedure.id) :
  {CP=CP'} + {CP<>CP'}.
Proof.
  repeat decide equality.
Qed.

Definition imported_procedure_b
           (Is : Program.interface)
           (C C': Component.id) (P : Procedure.id) : bool :=
  match NMap.find C Is with
  | Some CI => negb ((count_occ procs_eqdec (Component.import CI) (C',P)) =? 0)
  | None => false
  end.
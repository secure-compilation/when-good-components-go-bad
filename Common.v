Require Export List.
Require Export Bool.
Require Export Arith.

Export ListNotations.
Open Scope list_scope.

Definition admit {T: Type} : T. Admitted.

Module Procedure.
  Definition id := nat.
End Procedure.

Module Component.
  Definition id := nat.

  Record interface :=
    mkCompInterface {
        name : id;
        export : nat;
        import : list (id * Procedure.id)
    }.
End Component.

Module Program.
  Definition interface := list (option Component.interface).
End Program.

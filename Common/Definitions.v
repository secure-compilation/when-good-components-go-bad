Module Procedure.
  Definition id := nat.
End Procedure.

Module Component.
  Definition id := nat.

  Record interface := mkCompInterface {
    name : id;
    export : nat;
    import : list (id * Procedure.id)
  }.
End Component.

Module Program.
  Definition interface := list Component.interface.
End Program.
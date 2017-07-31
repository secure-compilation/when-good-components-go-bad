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

Lemma imported_procedure_iff :
  forall Is C C' P,
    imported_procedure Is C C' P <-> imported_procedure_b Is C C' P = true.
Proof.
  intros Is C C' P.
  split.
  - intros Himport.
    destruct Himport as [CI [HCI Himport]].
    unfold Program.has_component in HCI.
    unfold Component.is_importing in Himport.
    unfold imported_procedure_b.
    apply NMap.find_1 in HCI. rewrite HCI.
    rewrite count_occ_In in Himport.
    inversion Himport.
    + rewrite <- H0. simpl. auto.
    + rewrite <- H. simpl. auto.
  - intros Himport.
    unfold imported_procedure.
    unfold imported_procedure_b in Himport.
    destruct (NMap.find (elt:=Component.interface) C Is) eqn:Hfind;
      try discriminate.
    exists i.
    unfold Program.has_component, Component.is_importing.
    split.
    + apply (NMap.find_2 Hfind).
    + rewrite count_occ_In.
      destruct (count_occ procs_eqdec (Component.import i) (C', P) =? 0) eqn:Hcount;
        try discriminate.
      rewrite beq_nat_false_iff in Hcount.
      apply Nat.neq_0_lt_0 in Hcount.
      unfold gt. eauto.
Qed.
Require Import Common.Definitions.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.PartialForward.

Section SourceProperties.
  Variable p: Source.program.

  Let mainC := fst (Source.prog_main p).
  Let mainP := snd (Source.prog_main p).

  Definition fully_defined: Prop :=
    forall c b,
      program_behaves (S.CS.sem (Source.program_link c p mainC mainP)) b ->
      not_wrong b.
End SourceProperties.

Section MainIngredients.
  (* is this ok?
     it depends whether we have exact behavior preservation or not.
     if we have the refinement of undefined behavior, then one of the two
     conclusions is false. *)
  Lemma decomposition:
    forall c p mainC mainP b,
      program_behaves (I.CS.sem (Intermediate.program_link c p mainC mainP)) b ->
      program_behaves (I.PS.sem c (Intermediate.prog_interface p)) b /\
      program_behaves (I.PS.sem p (Intermediate.prog_interface c)) b.
  Proof. Admitted.

  (* same as for decomposition
     when undefined behavior happens, one of the premises is false *)
  Lemma composition:
    forall c p mainC mainP b,
      program_behaves (I.PS.sem c (Intermediate.prog_interface p)) b ->
      program_behaves (I.PS.sem p (Intermediate.prog_interface c)) b ->
      program_behaves (I.CS.sem (Intermediate.program_link c p mainC mainP)) b.
  Proof. Admitted.

  (* note that the produced context must be something that we can compile.
     this might be annoying to prove and we would like to avoid it.
     a possible fix consists in writing a total compiler that outputs garbage code
     whenever a condition is not met. *)
  Lemma definability:
    forall p ctx b,
      program_behaves (I.PS.sem p ctx) b ->
    exists C c,
      fully_defined C /\ Source.prog_interface C = ctx /\ compile_program C = Some c /\
      program_behaves (S.PS.sem C (Intermediate.prog_interface p)) b.
  Proof. Admitted.

  (* this is probably too strong, the refinement of p undefined behavios is missing *)
  Lemma partial_forward:
    forall p tp ctx b,
      compile_program p = Some tp ->
      program_behaves (S.PS.sem p ctx) b ->
      program_behaves (I.PS.sem tp ctx) b.
  Proof. Admitted.

  (* this should be easily provable *)
  Lemma compilation_preserves_interface:
    forall p tp,
      compile_program p = Some tp ->
      Source.prog_interface p = Intermediate.prog_interface tp.
  Proof. Admitted.
End MainIngredients.

(*
  New RC_DC:
    c[P↓] ⇓ b  ⇒  ∃C. C fully defined ∧ C↓[P↓] ⇓ b

  Notes:
  - is c a single component?
*)

Section New_RC_DC.
  Variable p : Source.program.
  Variable tp : Intermediate.program.

  Hypothesis successful_compilation:
    compile_program p = Some tp.

  Let mainC := fst (Intermediate.prog_main tp).
  Let mainP := snd (Intermediate.prog_main tp).

  Theorem RC_DC:
    forall c b,
      Intermediate.single_component c ->
      program_behaves (I.CS.sem (Intermediate.program_link c tp mainC mainP)) b ->
    exists C c',
      Source.prog_interface C = Intermediate.prog_interface c /\
      fully_defined C /\ compile_program C = Some c' /\
      program_behaves (I.CS.sem (Intermediate.program_link c' tp mainC mainP)) b.
  Proof.
    intros c b Hsingle_comp Hbeh.
    destruct (decomposition c tp mainC mainP b Hbeh) as [Hpp Hpc].
    destruct (definability tp (Intermediate.prog_interface c) b Hpc)
      as [C [c' [HCdef [Hiface [Hcomp Hbeh']]]]].
    exists C. exists c'.
    repeat split.
    + auto.
    + auto.
    + auto.
    + pose proof (partial_forward C c' (Intermediate.prog_interface tp) b Hcomp Hbeh').
      pose proof (compilation_preserves_interface C c' Hcomp) as Hiface'.
      apply composition; auto.
      rewrite <- Hiface', Hiface. auto.
  Qed.
End New_RC_DC.
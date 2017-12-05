Require Import Common.Definitions.
Require Import Common.Blame.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.
Require Import S2I.Compiler.
Require Import S2I.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  Let pCt := Intermediate.program_link p_compiled Ct.

  (* FCC *)
  Hypothesis I_simulates_S:
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      forward_simulation (S.CS.sem p) (I.CS.sem tp).

  (* BCC *)
  Corollary S_simulates_I:
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      backward_simulation (S.CS.sem p) (I.CS.sem tp).
  Proof.
    intros.
    apply forward_to_backward_simulation.
    - apply I_simulates_S; auto.
    - apply S.CS.receptiveness.
    - apply I.CS.determinacy.
  Qed.

  Hypothesis successfull_compilation:
    compile_program p = Some p_compiled.

  Hypothesis linkability:
    Intermediate.linkable_programs p_compiled Ct.

  Hypothesis closedness:
    Intermediate.closed_program pCt.

  Definition main_comp (p: Source.program): Component.id :=
    match Source.prog_main p with
    | Some (mainC, _) => mainC
    | None => 0
    end.

  Theorem RSC_DC_MD:
    forall t,
      program_behaves (I.CS.sem pCt) (Terminates t) ->
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      exists t',
        (beh = Terminates t' /\ behavior_prefix t (Terminates t')) \/
        (beh = Goes_wrong t' /\ behavior_prefix t' (Terminates t) /\
         undef_in (main_comp p) t' (Source.prog_interface p)).
  Proof.
    intros t Hbeh. subst pCt.
    destruct (decomposition_with_refinement linkability Hbeh)
      as [beh' [Hbeh' Hbeh_improves]].
    inversion Hbeh_improves; subst.
    - (* apply definability
         go down with forward simulation (compiler correctness)
         compose with CC result
         go up with backward simulation (compiler correctness)
         reason on who blame when ub *)
      admit.
    - destruct H as [? []]. discriminate.
  Admitted.
End RSC_DC_MD.
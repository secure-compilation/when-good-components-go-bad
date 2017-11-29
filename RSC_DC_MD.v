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
Require Import S2I.Compiler.
Require Import S2I.Definitions.

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  Hypothesis successfull_compilation:
    compile_program p = Some p_compiled.

  Hypothesis linkability_1:
    Intermediate.prog_main p_compiled = Intermediate.prog_main Ct.

  Hypothesis linkability_2:
    PMapExtra.Disjoint (Source.prog_interface p) (Intermediate.prog_interface Ct).

  Definition same_interface (p1 p2: Source.program) : Prop :=
    PMap.Equal (Source.prog_interface p1) (Source.prog_interface p2).

  Let mainC := fst (Source.prog_main p).
  Let mainP := snd (Source.prog_main p).
  Let pCt := Intermediate.program_link p_compiled Ct mainC mainP.

  Theorem RSC_DC_MD:
    forall t,
      program_behaves (I.CS.sem pCt) (Terminates t) ->
    exists C beh,
      PMap.Equal (Source.prog_interface C) (Intermediate.prog_interface Ct) /\
      program_behaves (S.CS.sem (Source.program_link p C mainC mainP)) beh /\
      exists t',
        (beh = Terminates t' /\ behavior_prefix t (Terminates t')) \/
        (beh = Goes_wrong t' /\ behavior_prefix t' (Terminates t) /\
         undef_in mainC t' (Source.prog_interface p)).
  Proof.
  Admitted.
End RSC_DC_MD.

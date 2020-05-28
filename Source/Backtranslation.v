Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Source.Definability.

Require Import Intermediate.CS.
Require Import Intermediate.Machine.

Require Import S2I.Definitions.
Require Import Coq.Logic.IndefiniteDescription.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section DefinabilityWithLinking.
  Variable k: nat. (* number of programs *)
  Variable ps: list Intermediate.program.
  Hypothesis length_ps: length ps = k.
  Variable c: Intermediate.program.
  Variable ms: list finpref_behavior.
  Hypothesis length_ms: length ms = k.

  (* Some assumptions about interfaces*)
  Variable ifacep: Program.interface.
  Hypothesis p_has_interface: forall p,
      In p ps ->
      Intermediate.prog_interface p = ifacep.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : forall p,
      In p ps ->
      Intermediate.well_formed_program p.
  Hypothesis well_formed_Ct : Intermediate.well_formed_program c.
  Hypothesis linkability : forall p,
      In p ps ->
      linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c).
  Hypothesis closedness : forall p,
      In p ps ->
      Intermediate.closed_program (Intermediate.program_link p c).

  Parameter obtained_from_traces: Source.program -> Source.program -> list finpref_behavior -> Prop.

  Lemma backtranslation :
    (forall n p m,
        nth_error ms n = Some m ->
        nth_error ps n = Some p ->
        does_prefix (CS.sem (Intermediate.program_link p c)) m) ->
    exists ps' c',
      Source.prog_interface c' = Intermediate.prog_interface c /\
      matching_mains c' c /\
      Source.well_formed_program c' /\
      (forall n p p' m,
          nth_error ms n = Some m ->
          nth_error ps n = Some p ->
          nth_error ps' n = Some p' ->
          (* In p ps -> In p' ps' -> *)
          Source.prog_interface p' = Intermediate.prog_interface p /\
          matching_mains p' p /\
          Source.well_formed_program p' /\
          Source.closed_program (Source.program_link p' c') /\
          does_prefix (S.CS.sem (Source.program_link p' c')) m )
  .
  Proof.
    intros H.
    assert (Hfun: exists f: Intermediate.program -> (Source.program * Source.program),
               forall p p' c' m,
                 does_prefix (CS.sem (Intermediate.program_link p c)) m ->
                 f p = (p', c') ->
                 Source.prog_interface p' = ifacep /\
                 Source.well_formed_program p' /\
                 Source.closed_program (Source.program_link p' c') /\
                 does_prefix (S.CS.sem (Source.program_link p' c')) m
           ).
    {
      (* Proof using functional_choice and definability_with_linking *)
      pose proof definability_with_linking as Hdef.
      admit.
    }
    destruct Hfun as [f Hf].
    exists (map fst (map f ps)).
    assert (Htree: exists p'' c': Source.program,
               Source.prog_interface p'' = ifacep /\
               Source.prog_interface c' = Intermediate.prog_interface c /\
               matching_mains c' c /\
               Source.well_formed_program p'' /\
               Source.well_formed_program c' /\
               Source.closed_program (Source.program_link p'' c') /\
               obtained_from_traces p'' c' ms).
    {
      admit.
    }
    destruct Htree as [p'' [c' [_ [? [? [_ [? [? Hobt]]]]]]]].
    exists c'.
    split; auto.
    split; auto.
    split; auto.

    intros n p p' m Hm Hp Hp'.
    assert (exists c'', f p = (p', c'')) as [? Heqfp].
    { admit. } 
    specialize (H n p m Hm Hp).
    specialize (Hf p p' _ m H Heqfp) as [? [? [Hclosed Hdoes_pref]]].
    split; auto. admit. (* simple *)
    split; auto. admit. (* need to add one more thing to Hfun *)
    split; auto.

    (* Now, if we clean up a bit, this looks like recombination! except with some kind of
     invariant instead of another does_prefix *)
    (* clear -Hobt Hclosed Hdoes_pref. *)

    (* But then, why even bother building a new [p] in the first place? *)
    (* We already know that the orignal [p] does [m]: hypothesis H *)
    clear -Hobt closedness H.

  Admitted.

End DefinabilityWithLinking.

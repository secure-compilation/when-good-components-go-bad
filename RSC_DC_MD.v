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
Require Import Intermediate.Composition.
Require Import Source.Decomposition.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import Definability.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* CH: TODO: turn all admits in the code into assumed lemmas -- one left!*)

(* CH: TODO: move these to CompCert files??? *)

Lemma help : forall m1 m2 T,
    trace_prefix m1 T -> trace_prefix m2 T ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1. induction m1 as [| e m1]; intros m2 T [x1 H1] [x2 H2].
  - left. now exists m2.
  - assert (foo : (exists s, m2 = e :: s) \/ m2 = []).
   { destruct m2. right. reflexivity. subst T. inversion H2.
     left. now exists m2. }
    destruct foo as [[s k0] | k1].
     + subst m2. subst T. inversion H2. specialize (IHm1 s (m1 ** x1)).
       assert (use1 : trace_prefix m1 (m1 ** x1)) by now exists x1.
       assert (use2 : trace_prefix s (m1 ** x1)) by (rewrite H0; now exists x2).
       destruct (IHm1 use1 use2) as [K | K]. clear IHm1.
       left. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. rewrite k1. now exists (e :: m1).                                             
Qed.
    
Lemma help_inf : forall m1 m2 T,
    traceinf_prefix m1 T -> traceinf_prefix m2 T ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
   intros m1. induction m1 as [| e m1]; intros m2 T [x1 H1] [x2 H2].
  - left. now exists m2.
  - assert (foo : (exists s, m2 = e :: s) \/ m2 = []).
   { destruct m2. right. reflexivity. subst T. inversion H2.
     left. now exists m2. }
    destruct foo as [[s k0] | k1].
     + subst m2. subst T. inversion H2. specialize (IHm1 s (m1 *** x1)).
       assert (use1 : traceinf_prefix m1 (m1 *** x1)) by now exists x1.
       assert (use2 : traceinf_prefix s (m1 *** x1)) by (rewrite H0; now exists x2).
       destruct (IHm1 use1 use2) as [K | K]. clear IHm1.
       left. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. rewrite k1. now exists (e :: m1).
Qed.


(* How to simplify this proof ? *)
Lemma behavior_prefix_comp : forall m1 m2 b,
    behavior_prefix m1 b ->
    behavior_prefix m2 b ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1 m2 b [beh1 H1] [beh2 H2].
  destruct b.
  
  destruct beh1; inversion H1;
  destruct beh2; inversion H2;
  inversion H1; inversion H2.
  assert (K1 : trace_prefix m1 t) by now exists t0.
  assert (K2 : trace_prefix m2 t) by now exists t1. 
  apply (help K1 K2). 
   
  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : trace_prefix m1 t ) by now exists t0.
  assert (K2 : trace_prefix m2 t) by now exists t1.
  apply (help K1 K2).
                                                
  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : traceinf_prefix m1 t) by now exists t0.
  assert (K2 : traceinf_prefix m2 t) by now exists t1.
  apply (help_inf K1 K2).
                                                   
  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : trace_prefix m1 t) by now exists t0.
  assert (K2 : trace_prefix m2 t). by now exists t1.
  apply (help K1 K2).
Qed.      


Lemma trace_behavior_prefix_trans : forall m1 m2 b,
    trace_prefix m1 m2 ->
    behavior_prefix m2 b ->
    behavior_prefix m1 b.
Proof.
  unfold trace_prefix, behavior_prefix.
  intros m1 m2 b [m3 Hm3] [b' Hb].
  subst m2 b.
  exists (behavior_app m3 b').
  now rewrite <- behavior_app_assoc.
Qed.

Lemma behavior_prefix_goes_wrong_trans : forall t b m,
  behavior_prefix t b ->
  behavior_prefix m (Goes_wrong t) ->
  behavior_prefix m b.
Proof.
  unfold behavior_prefix.
  destruct t as [| e t']; intros b m [b1 H1] [b2 H2]; subst b.
  - destruct m; destruct b2; simpl in H2; try discriminate.
    injection H2; intro H. subst. now eauto.
  - destruct m; destruct b2 as [| | | t'']; simpl in *; try discriminate.
    + exists (behavior_app (e :: t') b1). now rewrite behavior_app_E0.
    + injection H2; intros E1 E2; subst e t'.
      exists (behavior_app t'' b1). rewrite <- behavior_app_assoc.
      reflexivity.
Qed.

Lemma behavior_prefix_improves_trans : forall t b m,
    behavior_prefix m t ->
    behavior_improves t b ->
    behavior_prefix m b.
Proof.
  intros t b m H0 H1.
  destruct H1 as  [H1 | [t' [H11 H12]]].
  + subst. assumption.
  + subst. eapply  behavior_prefix_goes_wrong_trans; eassumption.
Qed.

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : Source.well_formed_program p.
  Hypothesis successfull_compilation : compile_program p = Some p_compiled.
  Hypothesis well_formed_Ct : Intermediate.well_formed_program Ct.
  Hypothesis linkability : linkable (Source.prog_interface p) (Intermediate.prog_interface Ct).
  Hypothesis closedness:
    Intermediate.closed_program (Intermediate.program_link p_compiled Ct).

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall b m,
      program_behaves (I.CS.sem (Intermediate.program_link p_compiled Ct)) b ->
      behavior_prefix m b ->
      not_wrong b -> (* CH: could try to remove this later *)
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link p Cs) /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      (behavior_prefix m beh \/
      (exists t',
        beh = Goes_wrong t' /\ trace_prefix t' m /\
         undef_in (Source.main_comp (Source.program_link p Cs)) t' (Source.prog_interface p))).
  Proof.
    intros t m Hbeh Hprefix0 Hsafe_beh.

    assert(sound_interface_p_Ct : sound_interface (unionm (Source.prog_interface p)
                                                          (Intermediate.prog_interface Ct)))
      by apply linkability.
    assert(fdisjoint_p_Ct : fdisjoint (domm (Source.prog_interface p))
                                      (domm (Intermediate.prog_interface Ct)))
      by apply linkability.

    assert(linkable (Intermediate.prog_interface p_compiled)
                    (Intermediate.prog_interface Ct)) as linkability'''. {
         constructor.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
    }

    (* intermediate decomposition (for p_compiled) *)
    pose proof
      Compiler.compilation_preserves_well_formedness well_formed_p successfull_compilation
      as well_formed_p_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
      well_formed_p_compiled well_formed_Ct linkability''' Hbeh Hsafe_beh as HP_decomp.

    (* CH: if we had undefined behavior we would use this *)
    (* destruct (decomposition_with_refinement linkability Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)

    (* definability *)
    destruct (definability_with_linking well_formed_p_compiled well_formed_Ct linkability''' closedness Hbeh Hprefix0)
      as [P' [Cs [beh [Hsame_iface1 [Hsame_iface2 [well_formed_P' [well_formed_Cs [HP'Cs_closed [HP'_Cs_beh Hprefix1]]]]]]]]].

    (* FCC *)

    assert (exists P'_compiled Cs_compiled,
               compile_program P' = Some P'_compiled /\
               compile_program Cs = Some Cs_compiled /\
               compile_program (Source.program_link P' Cs) = Some (Intermediate.program_link P'_compiled Cs_compiled))
      as HP'_Cs_compiles. {
      (* the definability output can be splitted in two programs *)
      (* probably need partialize to obtain them *)
      assert (exists P'_compiled, compile_program P' = Some P'_compiled)
        as [P'_compiled HP'_compiles]
        by (now apply well_formed_compilable).
      assert (exists Cs_compiled, compile_program Cs = Some Cs_compiled)
        as [Cs_compiled HCs_compiles]
        by (now apply well_formed_compilable).
      exists P'_compiled, Cs_compiled.
      split; [assumption |].
      split; [assumption |].
      apply Compiler.separate_compilation; try assumption.
      - congruence.
    }
    destruct HP'_Cs_compiles
      as [P'_compiled [Cs_compiled [HP'_compiles [HCs_compiles HP'_Cs_compiles]]]].
    assert (exists b', program_behaves (I.CS.sem (Intermediate.program_link P'_compiled Cs_compiled)) b'
                       /\ behavior_prefix m b')
      as HP'_Cs_compiled_beh. {
      apply forward_simulation_behavior_improves
        with (L2:=I.CS.sem (Intermediate.program_link P'_compiled Cs_compiled)) in HP'_Cs_beh;
        simpl; eauto.
      - destruct HP'_Cs_beh as [b2 [H1 H2]]. exists b2. split.
        + assumption.
        + destruct H2 as [|[t' [H21 H22]]].
          * subst. assumption.
          * subst. eapply behavior_prefix_goes_wrong_trans; eassumption.
      - apply Compiler.I_simulates_S; auto.
        apply Source.linking_well_formedness.
        * assumption.
        * assumption.
        * rewrite <- Hsame_iface1 in linkability'''.
          rewrite <- Hsame_iface2 in linkability'''.
          now apply linkability'''.
    }
    destruct HP'_Cs_compiled_beh as [t2 [HP'_Cs_compiled_beh HP'_Cs_compiled_prefix]].

    (* intermediate decomposition (for Cs_compiled) *)
    assert
      (linkable
         (Intermediate.prog_interface Cs_compiled)
         (Intermediate.prog_interface P'_compiled))
      as linkability'. {
      eapply @Compiler.compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply linkable_sym.
      (* RB: If [linkability] is not used for anything else, refactor these
         rewrites with the instance above, or craft a separate assumption. *)
      rewrite <- Hsame_iface1 in linkability'''.
      rewrite <- Hsame_iface2 in linkability'''.
      apply linkability'''.
    }
    rewrite <- Intermediate.link_sym in HP'_Cs_compiled_beh; [| assumption].
    pose proof Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles
      as well_formed_P'_compiled.
    pose proof Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles
      as well_formed_Cs_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_refinement
         well_formed_Cs_compiled well_formed_P'_compiled
         linkability' HP'_Cs_compiled_beh as [beh2 [HCs_decomp HCs_beh_improves]].

    (* intermediate composition *)
    assert (Intermediate.prog_interface Ct = Intermediate.prog_interface Cs_compiled)
      as Hctx_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
      - rewrite <- Hsame_iface2. reflexivity.
      - assumption.
    }
    rewrite Hctx_same_iface in HP_decomp.
    assert (Intermediate.prog_interface p_compiled = Intermediate.prog_interface P'_compiled) as Hprog_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
      - apply Hsame_iface1.
      - assumption.
    }
    rewrite <- Hprog_same_iface in HCs_decomp.

    assert (linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface Cs_compiled))
      as linkability''.
    {
      unfold linkable. split; try
        rewrite Hprog_same_iface;
        apply linkable_sym in linkability';
        now inversion linkability'.
    }
    assert (Intermediate.closed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_closed
      by (apply (Intermediate.interface_preserves_closedness_r closedness Hctx_same_iface)).
    assert (Intermediate.well_formed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
        by (apply Intermediate.linking_well_formedness; assumption).

    assert (behavior_prefix m beh2) as Hpref_m_beh2 by (eapply behavior_prefix_improves_trans; eassumption).
    pose proof composition_prefix
         well_formed_p_compiled well_formed_Cs_compiled
         linkability'' HpCs_compiled_closed
         HP_decomp HCs_decomp
         Hprefix0 Hpref_m_beh2
      as HpCs_compiled_beh.
    destruct HpCs_compiled_beh as [b3 [HpCs_compiled_beh HpCs_compiled_prefix]].

    assert (Source.closed_program (Source.program_link p Cs)) as Hclosed_p_Cs. {
      apply (Source.interface_preserves_closedness_l HP'Cs_closed).
      apply compilation_preserves_interface in HP'_compiles.
      apply compilation_preserves_interface in successfull_compilation.
      congruence.
    }
    assert (linkable (Source.prog_interface p) (Source.prog_interface Cs))
      as Hlinkable_p_Cs. {
      inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs].
      constructor;
        (apply compilation_preserves_interface in HCs_compiles;
        apply compilation_preserves_interface in successfull_compilation;
        rewrite <- HCs_compiles; rewrite <- successfull_compilation;
        assumption).
    }
    assert (Source.well_formed_program (Source.program_link p Cs)) as Hwf_p_Cs
      by (apply Source.linking_well_formedness; assumption).

    (* BCC *)
    assert (exists beh1,
               program_behaves (S.CS.sem (Source.program_link p Cs)) beh1 /\
               behavior_improves beh1 b3) as HpCs_beh. {
      apply backward_simulation_behavior_improves
        with (L1:=S.CS.sem (Source.program_link p Cs)) in HpCs_compiled_beh; auto.
      apply S_simulates_I.
      - assumption.
      - assumption.
      - apply Compiler.separate_compilation; try assumption.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].
    exists Cs. exists pCs_beh.
    split; [assumption |].
    split; [assumption |].
    split; [assumption |].
    split; [assumption |].
    inversion HpCs_beh_imp as [pCs_beh_ok|].
    - split.
      + subst pCs_beh. assumption.
      + left. subst. assumption.
    - destruct H as [t' [Hgoes_wrong Hprefix]].
      assert(trace_prefix m t' \/ trace_prefix t' m) as H by (eapply behavior_prefix_comp; eauto).
      destruct H as [H | H].
      + split.
        * subst pCs_beh. assumption.
        * left. subst. eapply trace_behavior_prefix_trans.
          - apply H.
          - unfold behavior_prefix. exists (Goes_wrong []). simpl.
            setoid_rewrite <- app_nil_end. reflexivity.
      + split.
        * subst pCs_beh. assumption.
        * right. exists t'. repeat split; auto.
          (* blame UB -- Guglielmo working on proof *)
          rewrite Source.link_sym in HpCs_beh; [| assumption].
          apply Source.Decomposition.decomposition_with_refinement_and_blame in HpCs_beh;
              try assumption.
          - setoid_rewrite Source.link_sym in HP'_Cs_beh; [|congruence].
            eapply Source.Decomposition.decomposition_with_refinement in HP'_Cs_beh;
              [| assumption | assumption | congruence].
            destruct HP'_Cs_beh as [beh' [G1 G2]].
            destruct HpCs_beh as [b [H1 [H2 | H2]]].
            + subst pCs_beh. subst b.
              eapply (@blame_program p Cs).
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * pose proof (compilation_preserves_interface p p_compiled
                                               successfull_compilation) as HH.
                assert(Source.prog_interface P' = Source.prog_interface p) as HHH
                    by congruence.
                rewrite <- HHH.
                now apply G1.
              * assumption.
              * assert(behavior_prefix t' beh) as H0. {
                  eapply trace_behavior_prefix_trans.
                  - now apply H.
                  - assumption.
                }
                eapply behavior_prefix_improves_trans.
                - now eapply H0.
                - assumption.
            + destruct H2 as [t'' [H21 [H22 H23]]].
              subst pCs_beh. injection H21; intro H21'. subst t''.
              setoid_rewrite Source.link_sym; assumption.
          - now apply linkable_sym.
          - setoid_rewrite <- Source.link_sym; assumption.
 Qed.
  
End RSC_DC_MD.

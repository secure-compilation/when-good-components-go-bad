Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.

Require Import RSC_DC_MD_Sigs.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module RSC_DC_MD_Gen
       (Target: Target_Sig).

Definition behavior_improves_blame b m p :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m /\
             undef_in t (Target.prog_interface p).

Section RSC_DC_MD_Section.
  Import Target.
  Variable p: program.
  Variable Ct: program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : well_formed_program p.
  Hypothesis well_formed_Ct : well_formed_program Ct.
  Hypothesis linkability : linkable (prog_interface p) (prog_interface Ct).
  Hypothesis closedness :
    closed_program (program_link p Ct).
  Hypothesis mains : linkable_mains p Ct.

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall m,
      does_prefix (CS.sem2 (program_link p Ct)) m ->
      not_wrong_finpref m ->
    exists Cs beh,
      prog_interface Cs = prog_interface Ct /\
      well_formed_program Cs /\
      linkable (prog_interface p) (prog_interface Cs) /\
      closed_program (program_link p Cs) /\
      program_behaves (CS.sem1 (program_link p Cs)) beh /\
      (prefix m beh \/ behavior_improves_blame beh m p).
  Proof.
    intros m [t [Hbeh Hprefix0]] Hsafe_pref.

    (* Some auxiliary results. *)

    (* definability *)
    destruct (Target.definability_with_linking
                well_formed_p well_formed_Ct
                linkability closedness Hbeh Hprefix0 Hsafe_pref)
      as [P' [Cs
         [Hsame_iface1 [Hsame_iface2
         [well_formed_P' [well_formed_Cs [HP'Cs_closed HP'_Cs_m]]]]]]].

    (* assert (linkable_mains P' Cs) as HP'Cs_mains. *)
    (* { apply linkable_disjoint_mains; trivial; congruence. } *)

    (* FCC *)
    (* the definability output can be split in two programs *)
    (* probably need partialize to obtain them *)

    (* At this point, we compile P' and Cs and establish their basic properties. *)
    (* destruct (Compiler.well_formed_compilable well_formed_P') as [P'_compiled HP'_compiles]. *)
    (* pose proof Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles *)
    (*   as well_formed_P'_compiled. *)
    (* destruct (Compiler.well_formed_compilable well_formed_Cs) as [Cs_compiled HCs_compiles]. *)
    (* pose proof Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles *)
    (*   as well_formed_Cs_compiled. *)
    (* assert *)
    (*   (linkable *)
    (*      (prog_interface Cs_compiled) *)
    (*      (prog_interface P'_compiled)) *)
    (*   as linkability'. { *)
    (*   eapply @Compiler.compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto. *)
    (*   apply linkable_sym. *)
    (*   rewrite <- Hsame_iface1 in linkability_pcomp_Ct. *)
    (*   rewrite <- Hsame_iface2 in linkability_pcomp_Ct. *)
    (*   apply linkability_pcomp_Ct. *)
    (* } *)
    (* assert (exists P'_Cs_compiled, *)
    (*           Compiler.compile_program (program_link P' Cs) = Some P'_Cs_compiled) *)
    (*   as [P'_Cs_compiled HP'_Cs_compiles]. { *)
    (*   rewrite <- Hsame_iface1 in linkability_pcomp_Ct. *)
    (*   rewrite <- Hsame_iface2 in linkability_pcomp_Ct. *)
    (*   pose proof linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct *)
    (*     as Hlinking_wf. *)
    (*   apply Compiler.well_formed_compilable; assumption. *)
    (* } *)

    (* have well_formed_P'Cs : well_formed_program (program_link P' Cs). *)
    (*   rewrite -Hsame_iface1 -Hsame_iface2 in linkability_pcomp_Ct. *)
    (*   exact: linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct. *)
    (*   have HP'_Cs_compiled_doesm : does_prefix (CS.sem (program_link P'_compiled Cs_compiled)) m. *)
    (*   { *)
    (*     eapply Compiler.forward_simulation_same_safe_prefix; try eassumption. congruence. *)
    (*   } *)

    (* (* intermediate decomposition (for Cs_compiled) *) *)
    (* rewrite program_linkC in HP'_Cs_compiled_doesm; *)
    (*    [| assumption |assumption | apply linkable_sym in linkability'; assumption]. *)
    (* (* pose proof (decomposition_prefix *) *)
    (* (*        well_formed_Cs_compiled well_formed_P'_compiled *) *)
    (* (*        linkability' mains' Hsafe_pref HP'_Cs_compiled_doesm) as HCs_decomp. *) *)

    (* (* intermediate composition *) *)
    (* assert (prog_interface Ct = prog_interface Cs_compiled) *)
    (*   as Hctx_same_iface. { *)
    (*   symmetry. erewrite Compiler.compilation_preserves_interface. *)
    (*   - rewrite <- Hsame_iface2. reflexivity. *)
    (*   - assumption. *)
    (* } *)
    (* (* rewrite Hctx_same_iface in HP_decomp. *) *)
    (* assert (prog_interface p_compiled = prog_interface P'_compiled) as Hprog_same_iface. { *)
    (*   symmetry. erewrite Compiler.compilation_preserves_interface. *)
    (*   - apply Hsame_iface1. *)
    (*   - assumption. *)
    (* } *)
    (* (* rewrite <- Hprog_same_iface in HCs_decomp. *) *)

    (* assert (linkable (prog_interface p_compiled) (prog_interface Cs_compiled)) *)
    (*   as linkability''. *)
    (* { *)
    (*   unfold linkable. split; try *)
    (*     rewrite Hprog_same_iface; *)
    (*     apply linkable_sym in linkability'; *)
    (*     now inversion linkability'. *)
    (* } *)
    (* assert (closed_program (program_link p_compiled Cs_compiled)) *)
    (*   as HpCs_compiled_closed. *)
    (* pose proof S2I.matching_mains_equiv *)
    (*      Hmatching_mains_Cs_Ct *)
    (*      (Compiler.compilation_has_matching_mains well_formed_Cs HCs_compiles) *)
    (*      as Hctx_match_mains. *)
    (* now apply (interface_preserves_closedness_r *)
    (*              well_formed_p_compiled well_formed_Cs_compiled *)
    (*              Hctx_same_iface linkability_pcomp_Ct closedness mains Hctx_match_mains); auto. *)
    (* assert (well_formed_program (program_link p_compiled Cs_compiled)) *)
    (*   as HpCs_compiled_well_formed *)
    (*     by (apply linking_well_formedness; assumption). *)

    (* assert (linkable_mains p_compiled Cs_compiled) as linkable_mains. *)
    (* { *)
    (*   eapply (@Compiler.compilation_preserves_linkable_mains p _ Cs); *)
    (*     try assumption. *)
    (*   - rewrite <- Hsame_iface2 in linkability. *)
    (*     eapply linkable_disjoint_mains; assumption. *)
    (* } *)

    (* assert (mergeable_interfaces (prog_interface p_compiled) *)
    (*                              (prog_interface Cs_compiled)) *)
    (*   as Hmergeable_ifaces. *)
    (*   by apply compose_mergeable_interfaces. *)

    (* (* pose proof composition_prefix *) *)
    (* (*      well_formed_p_compiled well_formed_Cs_compiled *) *)
    (* (*      linkable_mains HpCs_compiled_closed *) *)
    (* (*      Hmergeable_ifaces *) *)
    (* (*      HP_decomp HCs_decomp *) *)
    (* (*   as HpCs_compiled_beh. *) *)
    (* assert (closed_program (program_link p Cs)) as Hclosed_p_Cs. { *)
    (*   apply (interface_preserves_closedness_l HP'Cs_closed); trivial. *)
    (*   apply Compiler.compilation_preserves_interface in HP'_compiles. *)
    (*   apply Compiler.compilation_preserves_interface in successful_compilation. *)
    (*   congruence. *)
    (* } *)
    (* assert (linkable (prog_interface p) (prog_interface Cs)) *)
    (*   as Hlinkable_p_Cs. { *)
    (*   inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs]. *)
    (*   constructor; *)
    (*     (apply Compiler.compilation_preserves_interface in HCs_compiles; *)
    (*     apply Compiler.compilation_preserves_interface in successful_compilation; *)
    (*     rewrite <- HCs_compiles; rewrite <- successful_compilation; *)
    (*     assumption). *)
    (* } *)
    (* assert (well_formed_program (program_link p Cs)) as Hwf_p_Cs *)
    (*   by (apply linking_well_formedness; assumption). *)

    (* assert (HP'Cs_compiled_closed : *)
    (*           closed_program (program_link P'_compiled Cs_compiled)). *)
    (* { *)
    (*   rewrite program_linkC; try easy; try now apply linkable_sym. *)
    (*   apply interface_preserves_closedness_r with (p2 := p_compiled); eauto. *)
    (*   apply linkable_sym; eauto. *)
    (*   rewrite program_linkC; eauto. *)
    (*   apply linkable_sym; eauto. *)
    (*   apply linkable_mains_sym; eauto. *)
    (*   eapply S2I.matching_mains_equiv; eauto. *)
    (*   apply Compiler.compilation_has_matching_mains; eauto. *)
    (* } *)

    (* rewrite program_linkC in HP'_Cs_compiled_doesm; try assumption. *)
    (* rewrite <- Hctx_same_iface in Hmergeable_ifaces. *)

    assert (mergeable_interfaces (prog_interface p)
                                 (prog_interface Ct))
      as Hmergeable_ifaces by (split ; try eauto ; admit).
    
    assert (
        exists m', does_prefix
                (CS.sem_restricted_UB (program_link p Ct)
                   (allowed_UB (prog_interface Ct))) m' /\
                (m = m' \/
                   (m <> m' /\
                  (finpref_trace_prefix m' (finpref_trace m) /\
                     forall m'', finpref_trace_prefix m' (finpref_trace m'') ->
                            m <> m'' ->
                            not (does_prefix
                              (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct)))
                              m'')))))
             as [m' [p_Ct_does_m' H]] by admit.
    destruct H as [? | [m_not_m' [m'_m m'_maximal]]]; try subst m'.
    - pose proof Target.recombination_blame_prefix
                 well_formed_p well_formed_Ct well_formed_P' well_formed_Cs Hmergeable_ifaces
                 (eq_sym Hsame_iface1) (eq_sym Hsame_iface2) closedness HP'Cs_closed
                 p_Ct_does_m' HP'_Cs_m.

      destruct H  as [t' [p_Cs_t' m_t']].
      exists Cs, t'.
      repeat (split; [now auto |]).
      rewrite Hsame_iface2; split; [now auto |].
      split; [ admit | ].
      split; eauto.

    -
      assert (p_Ct_wrong_m': does_prefix
                (CS.sem_restricted_UB (program_link p Ct) (fun s : CS.state => allowed_UB (prog_interface Ct) s))
                (FGoes_wrong (finpref_trace m'))).
      { exists (Goes_wrong (finpref_trace m')).
        split; [| constructor].

        destruct p_Ct_does_m' as [b' [p_Ct_b' m'_b']].
        inversion p_Ct_b'; subst; clear p_Ct_b'.
        - destruct b' as [tra | tra | trainf | tra].
          + eapply program_runs ; eauto.  admit.
          + admit.
          + admit.
          + admit.
        - destruct m'; try now inversion m'_b'.
          simpl in m'_b'.
          destruct m'_b' as [? G].
          destruct t0; destruct x; inversion G; subst. simpl.
          constructor. eauto. }

      assert (P'_Cs_tbc_m':
               does_prefix (CS.sem1 (program_link P' Cs)) (FTbc (finpref_trace m'))).
      { clear -HP'_Cs_m m'_m.
        admit. }

      assert (undef_in_m'_p: undef_in (finpref_trace m') (prog_interface p)) by admit.

      pose proof Target.recombination_blame_prefix_final_UB
                 well_formed_p well_formed_Ct well_formed_P' well_formed_Cs Hmergeable_ifaces
                 (eq_sym Hsame_iface1) (eq_sym Hsame_iface2) closedness HP'Cs_closed
                 p_Ct_wrong_m' P'_Cs_tbc_m' undef_in_m'_p.

      assert (exists t', program_behaves (CS.sem1 (program_link p Cs)) t' /\
                      prefix m t') as [t' [p_Cs_t' m_t']] by admit.
      exists Cs, t'.
      repeat (split; [now auto |]).
      rewrite Hsame_iface2; split; [now auto |].
      split; [ admit | ].
      split; eauto.
  Admitted.

  Lemma max_prefix_no_UB {t} (m : finpref_behavior) {m_eq: m = FTbc t}
    (Hexec : does_prefix
                (CS.sem_restricted_UB (program_link p Ct)
                   (allowed_UB (prog_interface Ct))) m) :
    exists m', does_prefix
            (CS.sem_restricted_UB (program_link p Ct)
               (allowed_UB (prog_interface Ct))) m' /\
            (m = m' \/
               (m <> m' /\
                  (finpref_trace_prefix m' (finpref_trace m) /\
                     forall m'', finpref_trace_prefix m' (finpref_trace m'') ->
                            m <> m'' ->
                            not (does_prefix
                                   (CS.sem_restricted_UB (program_link p Ct) (allowed_UB (prog_interface Ct)))
                                   m'')))).
Proof.
  subst.
  induction t.
  - exists (FTbc []) ; split ; try eauto.
  - destruct IHt as [m' Hm'] ;  destruct Hexec as [beh [beh_behaves m_beh_prefix]].
    -- simpl in m_beh_prefix.
        destruct beh as [bt|bt|bt|bt] ; destruct bt ; destruct m_beh_prefix as [beh' beh_beh'_eq] ;
          try (destruct beh' ; simpl in beh_beh'_eq ; inversion beh_beh'_eq).
        --- admit.
        --- exists (Diverges bt). split ; try eauto. admit.
            subst. simpl. exists (Diverges t0). eauto.
        --- exists (Reacts bt). split ; try eauto. admit.
            subst. simpl. exists (Reacts t0). eauto.
        --- exists (Goes_wrong bt). split ; try eauto. admit.
            subst. simpl. exists (Goes_wrong t0). eauto.
    -- destruct Hm' as [m'prefix disj]. destruct disj.
       --- destruct beh_behaves as [s beh s_init s_beh|].
           
         exists m'. split ; try eauto.
Admitted.
(*
Lemma
  Target.sem_restricted_UB_computable
*)
    
End RSC_DC_MD_Section.
End RSC_DC_MD_Gen.

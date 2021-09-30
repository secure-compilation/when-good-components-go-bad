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
Require Import Common.TracesInform.
Require Import Common.RenamingOption.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Lia.
Require Intermediate.CS.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Source.Definability.

(* NOTE: [DynShare] Do we need the metadata size to range over components?
   (Likely, for composition of partial programs.) We may not need the more
   general setup in this particular setting of back-translation, however. *)
(* NOTE: [DynShare] It is unlikely that we would ever need more than one block
   of metadata per component. That is, metadata would be an optional block for
   each component containing certain fixed data, such as the shift to apply to
   block identifiers. *)
(* Definition metadata_size : Component.id -> nat (* := uniform_shift metadata_size_per_cid*). *)
(* Admitted. *)

Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import S2I.Definitions.

(*Section MainDefinability.*)

(* FG : Put back some sanity checks ? some are present but commented in the premise and the move => *)
Lemma matching_mains_backtranslated_program p c intf bufs back m:
  Intermediate.well_formed_program p ->
  Intermediate.well_formed_program c ->
  (* intf = unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c) -> *)
  back = program_of_trace intf m bufs ->
  intf Component.main ->
  (* well_formed_trace intf m -> *)
  matching_mains (Source.program_unlink (domm (Intermediate.prog_interface p)) back) p.
Proof.
  move => wf_p wf_c (* intf' *) Hback intf_main (* wf_back *).
  unfold matching_mains.
  split.
  - (* <-, no main in intermediate implies no main in source bactkanslated *)
    unfold Source.prog_main, Source.program_unlink. simpl.
    rewrite Source.find_procedure_filter_comp.
    move => Hinterm.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hcase.
    + inversion wf_p as [_ _ _ _ _ _ Hmain_component].
      pose proof (proj1 (Intermediate.wfprog_main_component wf_p) Hcase) as Hmainp.
      done.
    + rewrite Hcase in Hinterm. done.
  - (* -> *) (* maybe can be done with more finesse *)
    unfold Source.prog_main. unfold Source.program_unlink. rewrite Hback. simpl. rewrite Source.find_procedure_filter_comp.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hmain_comp ; rewrite Hmain_comp.
    + intros Hprog_main.
      rewrite find_procedures_of_trace_main. done.
      assumption.
    + intros Hcontra.
      apply (Intermediate.wfprog_main_component wf_p) in Hcontra.
      rewrite Hmain_comp in Hcontra. done.
Qed.

(* Definability *)

(* RB: TODO: Refactor and relocate. *)
Lemma prefix_project m :
  not_wrong_finpref m ->
  prefix (project_finpref_behavior m)
         (Terminates (project_non_inform (finpref_trace m))).
Proof.
  unfold project_finpref_behavior, finpref_trace.
  destruct m as [t | t | t]; simpl.
  - reflexivity.
  - done.
  - intros _. exists (Terminates E0). simpl. rewrite E0_right. reflexivity.
Qed.

Lemma not_wrong_finpref_project m :
 not_wrong_finpref m ->
 not_wrong_finpref (project_finpref_behavior m).
Proof.
  now destruct m.
Qed.

(* RB: Relocate? As the S2I require above seems to indicate, this is not where
   this result belongs. *)
Lemma star_well_formed_intermediate_prefix:
  forall p t s,
    Intermediate.well_formed_program p ->
    Star (I.CS.sem_inform p) (I.CS.initial_machine_state p) t s ->
    well_formed_intermediate_prefix (Intermediate.prog_interface p)
                                    (Intermediate.prog_buffers p) t.
Proof.
  admit.
Admitted.


Lemma definability_with_linking:
  forall p c t s,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.closed_program (Intermediate.program_link p c) ->
    Star (I.CS.sem_inform (Intermediate.program_link p c))
         (I.CS.initial_machine_state (Intermediate.program_link p c))
         t
         s
    ->
    exists p' c' t' s' metadata_size,
      Source.prog_interface p' = Intermediate.prog_interface p /\
      Source.prog_interface c' = Intermediate.prog_interface c /\
      matching_mains p' p /\
      matching_mains c' c /\
      Source.well_formed_program p' /\
      Source.well_formed_program c' /\
      Source.closed_program (Source.program_link p' c') /\
      Star (Source.CS.CS.sem (Source.program_link p' c'))
           (Source.CS.CS.initial_machine_state (Source.program_link p' c'))
           t'
           s'
      /\
      traces_shift_each_other_option
        metadata_size all_zeros_shift t' (project_non_inform t).
Proof.
  move=> p c t s wf_p wf_c Hlinkable Hclosed Hstar.
  pose intf := unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c).
  have Hclosed_intf : closed_interface intf by case: Hclosed.
  have intf_main : intf Component.main.
  case: Hclosed => [? [main_procs [? [/= e ?]]]].
  rewrite /intf -mem_domm domm_union.
  do 2![rewrite Intermediate.wfprog_defined_procedures //].
  {  by rewrite -domm_union mem_domm e. }
  set procs := Intermediate.prog_procedures (Intermediate.program_link p c).
  have wf_events : all (well_formed_event intf procs) t.
    (* by apply: CS.intermediate_well_formed_events Hstar. *)
  {
    apply: CS.intermediate_well_formed_events Hstar.
    - by apply: Intermediate.linking_well_formedness.
    - assumption.
  }
  have wf_p_c := Intermediate.linking_well_formedness wf_p wf_c Hlinkable.
  have wf_t : well_formed_trace intf procs t.
  {
    have [mainP [HmainP _]] := Intermediate.cprog_main_existence Hclosed.
      (* TODO: Duplicate assumption, new non-implicit parameters. *)
      by apply: (CS.intermediate_well_formed_trace
                   _ wf_p_c Hclosed _ _ _ Hstar Logic.eq_refl HmainP wf_p_c).
  }
  pose bufs := Intermediate.prog_buffers (Intermediate.program_link p c).
  have intf_dom_buf:
    domm intf = domm bufs.
  {
    unfold intf, bufs.
    assert (Intermediate.prog_interface (Intermediate.program_link p c) =
            unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c)
           ) as Hrewr.
      by easy.
      rewrite -Hrewr.
      by apply Intermediate.wfprog_defined_buffers.
  }
  have wf_buf : (forall (C : nat_ordType) (buf : nat + seq value),
                      bufs C =
                      Some buf ->
                      Buffer.well_formed_buffer buf).
  {
    intros ? ? Hsome.
    by eapply Intermediate.wfprog_well_formed_buffers in wf_p_c; eassumption.
  }
  assert (H_is_prefix: exists s : CS.state,
             CSInvariants.CSInvariants.is_prefix
               s
               (Intermediate.program_link p c)
               (project_non_inform t)).
  {
    unfold CSInvariants.CSInvariants.is_prefix.
    exists s. by eapply I.CS.star_sem_inform_star_sem_non_inform.
  }
  have wf_i_t := star_well_formed_intermediate_prefix wf_p_c Hstar.
  have := definability Hclosed_intf intf_main intf_dom_buf wf_buf _ _
                       H_is_prefix wf_p_c Hclosed wf_t wf_i_t.
    (* RB: TODO: [DynShare] Check added assumptions in previous line. Section
       admits? *)
  set back := (program_of_trace intf bufs t) => Hback.
  assert (domm_procs: domm procs = domm intf).
  { unfold procs, intf.
    by rewrite -Intermediate.wfprog_defined_procedures. }
  specialize (Hback procs domm_procs wf_events (*all_zeros_shift*)) as
    [s' [t' [const_map [Hstar' Hshift]]]].
  exists (Source.program_unlink (domm (Intermediate.prog_interface p)) back).
  exists (Source.program_unlink (domm (Intermediate.prog_interface c)) back).
  (* Check project_finpref_behavior (FTerminates m'). *)
  exists t'. exists s'. exists const_map.

  (*   [t' [const_map [Hback Hshift]]]. *)
  (* assert (Hback_ : program_behaves (CS.sem (program_of_trace intf bufs t)) *)
  (*                                  (Terminates t')). *)
  (* { *)
  (*   (* This should follow directly from the definability lemma. *) *)
  (*   apply Hback. *)
  (* } *)
  (*   (* RB: TODO: [DynShare] Passing the section variables above should not be *)
  (*      needed, nor should the additional assumption. *) *)
  (* exists (Source.program_unlink (domm (Intermediate.prog_interface p)) back). *)
  (* exists (Source.program_unlink (domm (Intermediate.prog_interface c)) back). *)
  (* (* Check project_finpref_behavior (FTerminates m'). *) *)
  (* exists t'. *)
  (* inversion Hback as [? ? Hinit Hbeh|]; subst. clear Hback. *)
  (* inversion Hbeh as [? s' Hstar' Hfinal| | |]; subst. *)
  (* simpl in Hinit. unfold Source.CS.CS.initial_state in *. subst. *)
  (* exists s', const_map. *)

  split=> /=; last split.
  - rewrite -[RHS](unionmK (Intermediate.prog_interface p) (Intermediate.prog_interface c)).
      by apply/eq_filterm=> ??; rewrite mem_domm.
  - rewrite /intf unionmC; last by case: Hlinkable.
    rewrite -[RHS](unionmK (Intermediate.prog_interface c) (Intermediate.prog_interface p)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  (* have wf_back : Source.well_formed_program back by exact: well_formed_events_well_formed_program. *)
  - have wf_back : Source.well_formed_program back.
    {
      eapply well_formed_events_well_formed_program; auto.
      (* by exact: well_formed_events_well_formed_program. *)
      eassumption.
    }
    (* RB: TODO: [DynShare] Passing the section variables above should not be needed. *)
    split; first exact: matching_mains_backtranslated_program
                          wf_p wf_c Logic.eq_refl intf_main.
    split; first exact: matching_mains_backtranslated_program
                          wf_c wf_p Logic.eq_refl intf_main.

  split; first exact: Source.well_formed_program_unlink.
  split; first exact: Source.well_formed_program_unlink.
  rewrite Source.program_unlinkK //; split; first exact: closed_program_of_trace.
  (* RB: TODO: [DynShare] New split, the existential is now given above and in modified form. *)
  split; auto.
  by apply traces_shift_each_other_option_symmetric.
Qed.

Print Assumptions definability_with_linking.

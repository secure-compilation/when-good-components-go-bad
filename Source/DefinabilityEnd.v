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
Lemma matching_mains_backtranslated_program p c intf m back bufs:
  Intermediate.well_formed_program p ->
  Intermediate.well_formed_program c ->
  (* intf = unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c) -> *)
  Some back = program_of_trace intf bufs m ->
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
    unfold Source.prog_main. unfold Source.program_unlink.
    simpl. rewrite Source.find_procedure_filter_comp.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hmain_comp ; rewrite Hmain_comp.
    + intros Hprog_main.
      symmetry in Hback. unfold program_of_trace in Hback.
      destruct (procedures_of_trace intf bufs m) eqn:eprocs; [|discriminate]. inversion Hback.
      subst. simpl in *.
      eapply find_procedures_of_trace_main in eprocs; eauto. by rewrite eprocs.
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
    Intermediate.closed_program p ->
    Star (I.CS.sem_inform p) (I.CS.initial_machine_state p) t s ->
    well_formed_intermediate_prefix (Intermediate.prog_interface p)
                                    (Intermediate.prog_buffers p) t.
Proof.
  intros p t s wfp closed Hstar.
  assert (Hmain: Intermediate.prog_main p).
  { destruct closed. by destruct cprog_main_existence as [? [G _]]. }
  remember (CS.initial_machine_state p) as s0 eqn:Hs0.
  revert Hs0.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros; subst.
  - by constructor; constructor.
  - assert (length t2 <= 1). by eapply I.CS.singleton_traces_inform; eauto.
    destruct t2; first by rewrite E0_right; apply IHstar.
    destruct t2; simpl in *; last lia.
    setoid_rewrite cats1.
    destruct t1 as [|t1 et1] using last_ind; simpl.
    + constructor; constructor.
      CS.unfold_states.
      assert (mem0 =
              (mkfmapf
                 (fun C : nat_ordType =>
                    ComponentMemory.prealloc
                      match Intermediate.prog_buffers p C with
                      | Some buf => [fmap (Block.local, buf)]
                      | None => emptym
                      end) (domm (Intermediate.prog_interface p)))).
      {
        apply star_iff_starR in Hstar01.
        apply I.CS.epsilon_star_preserves_memory in Hstar01.
        simpl in *. subst. unfold CS.initial_machine_state. rewrite Hmain. simpl.
        unfold Intermediate.prepare_procedures_initial_memory,
        Intermediate.prepare_procedures_initial_memory_aux.
        rewrite mapm_mkfmapf.
        apply eq_fmap.
        assert (Hassert:
                  mkfmapf ((fun x : ComponentMemory.t * NMap code * seq Procedure.id =>
                              x.1.1) \o
                                     (fun C : nat_ordType =>
                                        (ComponentMemory.prealloc
                                           match Intermediate.prog_buffers p C with
                                           | Some buf => [fmap (Block.local, buf)]
                                           | None => emptym
                                           end,
                                         odflt emptym (Intermediate.prog_procedures p C),
                                         [seq pid <- domm (odflt emptym (Intermediate.prog_procedures p C))
                                         | Intermediate.is_entrypoint_of_comp p C pid]))
                          ) =1
                 mkfmapf (fun C : nat =>
                            ComponentMemory.prealloc
                              match Intermediate.prog_buffers p C with
                              | Some buf => setm emptym Block.local buf
                              | None => emptym
                              end)
               ).
        {
          apply eq_mkfmapf.
          match goal with |- ?x =1 ?y => assert (Hrewr: x = y) end.
          {
            apply FunctionalExtensionality.functional_extensionality_dep.
            intros C. by simpl.
          }
          by rewrite Hrewr.
        }
        by rewrite -Hassert.
      }
      assert (regs0 = Intermediate.Register.init).
      {
        apply star_iff_starR in Hstar01.
        apply I.CS.epsilon_star_preserves_registers in Hstar01.
        simpl in *. subst. unfold CS.initial_machine_state. by rewrite Hmain.
      }
      subst.
      assert (Hreginit:
                Intermediate.Register.set R_COM (Int 0) Intermediate.Register.init =
                Intermediate.Register.init
             ).
      {
        unfold Intermediate.Register.set, Intermediate.Register.init. by rewrite setmI. 
      }
      destruct e; inversion Hstep12; subst; simpl in *;
        remember (mkfmapf
                    (fun C : nat_ordType =>
                       ComponentMemory.prealloc
                         match Intermediate.prog_buffers p C with
                         | Some buf => [fmap (Block.local, buf)]
                         | None => emptym
                         end) (domm (Intermediate.prog_interface p))) as init_mem;
        rewrite -Heqinit_mem.
      * apply step_ECallInform; auto.
      * apply step_ERetInform; auto.
      * apply step_EConst; auto.
        by rewrite Ereg_to_reg_to_Ereg Hreginit.
      * apply step_EConst; auto.
        by rewrite Ereg_to_reg_to_Ereg Hreginit.
      * apply step_EConst; auto. simpl.
        by rewrite Hreginit.
      * apply step_EMov; auto.
        by rewrite !Ereg_to_reg_to_Ereg Hreginit.
      * eapply step_EBinop; auto. unfold result.
        by rewrite !Ereg_to_reg_to_Ereg !Ebinop_to_binop_to_Ebinop Hreginit.
      * subst. eapply step_ELoad; eauto; by rewrite !Ereg_to_reg_to_Ereg Hreginit.
      * subst. rewrite Hreginit.
        eapply step_EStore; eauto;
          erewrite !Ereg_to_reg_to_Ereg; eassumption.
      * subst. eapply step_EAlloc; eauto; by rewrite !Ereg_to_reg_to_Ereg Hreginit.

    + clear IHt1. specialize (IHstar Logic.eq_refl). inversion IHstar as [? ?].
      constructor; first (constructor; auto).
      CS.unfold_states.
      assert (Hrewr1: mem_of_event_inform et1 = mem0).
      {
        by specialize (I.CS.starR_memory_of_event_inform _ _ _ _ _ Hstar01).
      }
      assert (Hrewr2: register_file_of_event_inform et1 = regs0).
      {
        by specialize (I.CS.starR_register_file_of_event_inform _ _ _ _ _ Hstar01).
      }
      rewrite Hrewr1 Hrewr2.
      * destruct e; inversion Hstep12; subst; simpl in *.
        -- apply step_ECallInform; auto.
        -- apply step_ERetInform; auto.
        -- apply step_EConst; auto. by rewrite Ereg_to_reg_to_Ereg.
        -- apply step_EConst; auto. by rewrite Ereg_to_reg_to_Ereg.
        -- apply step_EConst; auto.
        -- apply step_EMov; auto. by rewrite !Ereg_to_reg_to_Ereg.
        -- eapply step_EBinop; auto. unfold result.
             by rewrite !Ereg_to_reg_to_Ereg !Ebinop_to_binop_to_Ebinop.
        -- subst. eapply step_ELoad; eauto; by rewrite !Ereg_to_reg_to_Ereg.
        -- subst. eapply step_EStore; eauto; erewrite !Ereg_to_reg_to_Ereg; eassumption.
        -- subst. eapply step_EAlloc; eauto; by rewrite !Ereg_to_reg_to_Ereg.
      * constructor; auto.
        by eapply I.CS.next_comp_of_event_cur_comp_of_event; eauto.
Qed.


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
        metadata_size all_zeros_shift t' (project_non_inform t) /\
        metadata_size = uniform_shift 1 /\
      Source.CS.CS.private_pointers_never_leak_S
        (Source.program_link p' c')
        (uniform_shift 1)
      /\
      (
        forall C P expr,
          Source.find_procedure (Source.prog_procedures (Source.program_link p' c')) C P =
          Some expr
          ->
          NoLeak.safe_cont_expr Kstop expr
      )
      /\
        NoLeak.good_Elocal_usage_program (Source.program_link p' c').
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
  }
  have wf_p_c := Intermediate.linking_well_formedness wf_p wf_c Hlinkable.
  have wf_t : well_formed_trace intf procs t.
  {
    have [mainP [HmainP _]] := Intermediate.cprog_main_existence Hclosed.
      (* TODO: Duplicate assumption, new non-implicit parameters. *)
      by apply: (CS.intermediate_well_formed_trace
                   _ wf_p_c _ _ _ Hstar Logic.eq_refl HmainP wf_p_c).
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
  assert (H_is_prefix: exists s : state (CS.sem_inform (Intermediate.program_link p c)),
             Star (CS.sem_inform (Intermediate.program_link p c)) (CS.initial_machine_state (Intermediate.program_link p c)) t s).
  { by exists s. }
  have wf_i_t := star_well_formed_intermediate_prefix wf_p_c Hclosed Hstar.
  assert (Hdomm_exported_procs: domm (exported_procedures_of_trace intf bufs t) = domm intf).
  {
    by rewrite domm_exported_procedures_of_trace_interface.
  }
  
  assert (Hrewr_: domm procs = domm intf).
  {
    unfold procs. by erewrite <- Intermediate.wfprog_defined_procedures.
  }
  rewrite -Hrewr_ in Hdomm_exported_procs.
  symmetry in Hdomm_exported_procs.
  specialize (well_formed_events_well_formed_program
                Hclosed_intf intf_main wf_buf Hdomm_exported_procs wf_events)
    as [back [Hback wf_back]].

  
  have Hback_trans := definability Hclosed_intf intf_main intf_dom_buf wf_buf _ _
                       H_is_prefix Hback wf_p_c Hclosed Logic.eq_refl wf_t wf_i_t.
    (* RB: TODO: [DynShare] Check added assumptions in previous line. Section
       admits? *)
  assert (domm_procs: domm procs = domm intf) by assumption.

  specialize (Hback_trans procs domm_procs wf_events (*all_zeros_shift*)) as
      [s' [t' [const_map [Hstar' [Hshift Hconst_map]]]]].
  subst const_map.
  exists (Source.program_unlink (domm (Intermediate.prog_interface p)) back).
  exists (Source.program_unlink (domm (Intermediate.prog_interface c)) back).
  (* Check project_finpref_behavior (FTerminates m'). *)
  exists t'. exists s'. exists (uniform_shift 1).

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

  assert (Hback_intf: Source.prog_interface back = intf).
  {
    unfold program_of_trace in *.
    destruct (procedures_of_trace intf bufs t); [|discriminate].
      by inversion Hback.
  }
  
  split=> /=; last split.
  - rewrite -[RHS](unionmK (Intermediate.prog_interface p) (Intermediate.prog_interface c)).
    rewrite Hback_intf.
    apply/eq_filterm => ??; by rewrite mem_domm.
  - rewrite Hback_intf /intf unionmC; last by case: Hlinkable.
    rewrite -[RHS](unionmK (Intermediate.prog_interface c) (Intermediate.prog_interface p)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  (* have wf_back : Source.well_formed_program back by exact: well_formed_events_well_formed_program. *)
  -
    (* RB: TODO: [DynShare] Passing the section variables above should not be needed. *)
    split; first (symmetry in Hback;
                  exact: matching_mains_backtranslated_program
                           wf_p wf_c Hback intf_main).
    split; first (symmetry in Hback;
                  exact: matching_mains_backtranslated_program
                           wf_c wf_p Hback intf_main).

    split; first exact: Source.well_formed_program_unlink.
    split; first exact: Source.well_formed_program_unlink.
    rewrite Source.program_unlinkK //; split; first (by eapply closed_program_of_trace; eauto).
    (* RB: TODO: [DynShare] New split, the existential is now given above and in modified form. *)
    split; auto.
    split; [by apply traces_shift_each_other_option_symmetric | split; [reflexivity| ]].
    split; last split.
    + by eapply Definability.definability_does_not_leak; subst; eauto.
    + intros ? ? ? Hfind.
      assert (Hback2: program_of_trace intf bufs t = Some back) by auto.
      unfold program_of_trace in Hback.
      change ((filterm (fun C : nat => fun=> C \in domm (Intermediate.prog_interface p))
                       (Source.prog_procedures back)))
        with (Source.prog_procedures
                (Source.program_unlink (domm (Intermediate.prog_interface p)) back)) in Hfind.

      
      change ((filterm (fun C : nat => fun=> C \in domm (Intermediate.prog_interface c))
                       (Source.prog_procedures back)))
        with (Source.prog_procedures
                (Source.program_unlink (domm (Intermediate.prog_interface c)) back)) in Hfind.

      change ((unionm
               (Source.prog_procedures
                  (Source.program_unlink (domm (Intermediate.prog_interface p)) back))
               (Source.prog_procedures
                  (Source.program_unlink (domm (Intermediate.prog_interface c)) back))))
        with
          (Source.prog_procedures
             (Source.program_link
                (Source.program_unlink (domm (Intermediate.prog_interface p)) back)
                (Source.program_unlink (domm (Intermediate.prog_interface c)) back)
             )
          ) in Hfind.
      rewrite Source.program_unlinkK in Hfind; auto.
      
      eapply Definability.definability_disciplined_program; eauto.
    + eapply definability_good_Elocal_usage; eauto.
Qed.

Print Assumptions definability_with_linking.

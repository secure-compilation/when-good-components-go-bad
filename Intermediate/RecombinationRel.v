Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.RenamingOption.
Require Import Common.Reachability.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.CSInvariants.
Require Import Intermediate.RecombinationRelCommon.
Require Import Intermediate.RecombinationRelOptionSim.
Require Import Intermediate.RecombinationRelLockstepSim.
Require Import Intermediate.RecombinationRelStrengthening.

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Lia.

From mathcomp Require Import ssreflect ssrnat ssrint ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(* Helpers, epsilon and lockstep versions of three-way simulation. *)
Section ThreewayMultisem1.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.
  Let n' := fun cid =>
              if cid \in domm (prog_interface p)
              then n   cid
              else n'' cid.
  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  

  (* Compose two stars into a merged star. The "program" side drives both stars
     and performs all steps without interruption, the "context" side remains
     unaltered in both stars. *)
  (* NOTE: By itself, the reformulation of this lemma does not say anything
     interesting, because the existential can be discharged trivially by
     reflexivity, but that is not what we want. In fact, even the proof is
     tellingly boring. *)
  Theorem threeway_multisem_star_E0_program s1 s1' s1'' t1 t1' t1'' s2 s2'':
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstar12 Hstar12''.
    inversion Hmerge1.
    - pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'.

      (* inversion H (* as ...*). *)
      find_and_invert_mergeable_states_well_formed.

      rewrite (* Hifacec *) Hifc_cc' in Hcomp1'.
      remember E0 as t eqn:Ht.
      revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''.
      apply star_iff_starR in Hstar12.
      induction Hstar12 as [s | s1 t1E0 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Ht Hmerge1 Hcomp1 Hcomp1'' Hstar12''.
      + exists s1'. split.
        * now apply star_refl.
        * eapply merge_states_silent_star; eassumption.
      + apply Eapp_E0_inv in Ht. destruct Ht; subst.
        specialize (IHstar H H0 H2 H3
                           Hpref_t (*Hgood_mem*) Hstack_s_s' Hpccomp_s'_s
                           Logic.eq_refl Hmerge1 Hcomp1 Hcomp1'' Hstar12'')
          as [s2' [Hstar12' Hmerge2]].
        pose proof CS.epsilon_star_non_inform_preserves_program_component _ _ _ _
             Hcomp1 ((proj2 (star_iff_starR _ _ _ _ _)) Hstar12) as Hcomp2.
        pose proof threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23
          as [s3' [Hstep23' Hmerge3]].
        exists s3'. split.
        * apply star_trans with (t1 := E0) (s2 := s2') (t2 := E0);
            [assumption | | reflexivity].
          now apply star_one.
        * assumption.
    - (* derive a contradiction to Hcomp1 *)
      destruct s1' as [[[? ?] ?] s1'pc].
      destruct s1 as [[[? ?] ?] s1pc].
      destruct s1'' as [[[? ?] ?] s1''pc].
      
      unfold CS.is_program_component,
      CS.is_context_component, turn_of, CS.state_turn in *.
      find_and_invert_mergeable_states_well_formed.
      simpl in *. subst.
      match goal with
      | H1: context[Pointer.component s1''pc \in _] |- _ =>
        rewrite Hpccomp_s'_s in H1;
          by rewrite H1 in Hcomp1
      end.
  Qed.


  Theorem threeway_multisem_star_program s1 s1' s1'' t1 t1' t1'' s2 s2'' t2 t2'':
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t2   s2   ->
    Star sem'' s1'' t2'' s2'' ->
    traces_shift_each_other_option n n'' (t1 ** t2) (t1'' ** t2'') ->
  exists s2' t2',
    Star sem'  s1'  t2'  s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2''
                              (t1 ** t2) (t1' ** t2') (t1'' ** t2'').
  Proof.
    intros Hcomp Hmerge Hstar12 Hstar12'' Hshift.

    (** First, assert that t2 and t2'' must have the same size. *)
    assert (szt2t2'': size t2 = size t2'').
    {
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      - inversion Hshift as [? ? Hren]; subst.
        specialize (traces_rename_each_other_option_same_size _ _ _ _ Hren) as Hsz.
        
        specialize (traces_shift_each_other_option_symmetric _ _ _ _ Hshift_t''t')
          as t1't1''.
        specialize (traces_shift_each_other_option_transitive
                      _ _ _ _ _ _
                      Hshift_tt' t1't1'') as  t1t1''.
        inversion t1t1'' as [? ? t1t1''ren]; subst.
        specialize (traces_rename_each_other_option_same_size _ _ _ _ t1t1''ren).
        (** TODO: Refactor lemma: *)
        (** size (t1 ** t2) = size (t1' ** t2') -> *)
        (** size t2 = size t2'                  -> *)
        (** size t1 = size t1'.                     *)
        unfold Eapp in Hsz.
        assert (forall (A: Type) l, size l = @length A l) as size_length.
        {
          induction l; auto.
        }
        rewrite !size_length !app_length in Hsz.
        rewrite !size_length.
        intros rewr; rewrite rewr in Hsz; by apply Nat.add_cancel_l in Hsz.
      - CS.simplify_turn.
        destruct s1  as [[[? ?] ?] pc ]; 
          destruct s1' as [[[? ?] ?] pc']; simpl in *.
        rewrite Hpccomp_s'_s in H_c'. by rewrite H_c' in Hcomp.
    }
    
    (** Now, do induction on t2:       *)
    (** - Base case:                   *)
    (**   Use option simulation, and   *)
    (**   lock-step simulation.        *)
    (** - Inductive case:              *)
    (**   Use strengthening?           *)
    generalize dependent t2''. generalize dependent s2''. generalize dependent s2.
    induction t2 as [|t2 e2] using last_ind; intros ? ? ? ? Hstar12'' Hshift szt2t2''. 
    - assert (t2'' = nil); subst.
      { by apply size0nil; auto. }
      simpl in *.
      pose proof (merge_states_silent_star) as Hoption_sim; unfold E0 in *.
      specialize (Hoption_sim _ _ _ _ _ _ _ _ _ _ _ _ _
                              Hmerge Hcomp Hstar12'').
      pose proof (threeway_multisem_star_E0) as Hlockstep.
      apply star_iff_starR in Hstar12.
      specialize (Hlockstep _ _ _ _ _ _ _ _ _ _ _ _ _
                            Hcomp Hoption_sim Hstar12) as [s2' [Hstep12' Hmerge']].
      exists s2'; exists E0.
      unfold Eapp, prog' in *.
      rewrite star_iff_starR !app_nil_r; by intuition.
    - assert (exists t2''pref e2'', t2'' = rcons t2''pref e2'') as [t2''pref [e2'' ?]];
        subst.
      {
        induction t2'' as [|tG eG] using last_ind;
          rewrite !size_rcons in szt2t2''; first by auto.
        do 2 eexists; eauto.
      }

      apply star_iff_starR in Hstar12.
      apply star_iff_starR in Hstar12''.

      apply CSInvariants.starR_rcons in Hstar12   as [st2 [se2 [Ht2 [He2 Hse2]]]]; auto;
        last by apply CS.singleton_traces_non_inform.
      apply CSInvariants.starR_rcons in Hstar12'' as [st2'' [se2'' [Ht2'' [He2'' Hse2'']]]];
        auto; last by apply CS.singleton_traces_non_inform.

      assert (exists (s2' : state sem') (t2' : trace event),
                 Star sem' s1' t2' s2' /\
                 mergeable_internal_states p c p' c' n n'' st2 s2' st2'' (t1 ** t2) 
                                           (t1' ** t2') (t1'' ** t2''pref))
        as [st2' [t2' [Ht2' Ht2t2't2'']]].
      {
        apply IHt2.
        - by apply star_iff_starR.
        - by apply star_iff_starR.
        - unfold Eapp in *. rewrite <- !rcons_cat in Hshift.
          constructor.
          inversion Hshift as [? ? Hren]; subst; inversion Hren as [|];
            first by find_nil_rcons.
          repeat find_rcons_rcons. assumption.
        - rewrite !size_rcons in szt2t2''. lia.
      }

      assert (exists e2' se2', Step sem' st2' [:: e2'] se2' /\
                               mergeable_border_states p c p' c' n n'' se2 se2' se2''
                                                       (rcons (t1   ** t2)       e2)
                                                       (rcons (t1'  ** t2')      e2')
                                                       (rcons (t1'' ** t2''pref) e2'')
             ) as [e2' [se2' [He2' Hborder]]].
      {
        find_and_invert_mergeable_internal_states.
        - (** Use the strengthening lemma: *)
          eapply threeway_multisem_event_lockstep_program_step.
          2: { exact Ht2t2't2''. }
          + destruct st2  as [[[? ?] ?] pc].
            destruct st2' as [[[? ?] ?] pc'].
            CS.simplify_turn. by subst.
          
          + auto.
          + auto.
          + unfold Eapp. rewrite !rcons_cat. exact Hshift.
          + unfold Eapp in *. rewrite <- !rcons_cat in Hshift.
            inversion Hshift as [? ? Hren]; subst; inversion Hren; subst;
              first by find_nil_rcons.
            repeat find_rcons_rcons. assumption.
          + unfold Eapp in *. rewrite <- !rcons_cat in Hshift.
            inversion Hshift as [? ? Hren]; subst; inversion Hren; subst;
              first by find_nil_rcons.
            repeat find_rcons_rcons. assumption.
        - (** Use symmetry lemmas, then use the strengthening lemma: *)
          apply mergeable_internal_states_sym in Ht2t2't2''.
          apply mergeable_states_well_formed_sym in Hmergewf.

          assert (eprog'': prog'' = program_link c' p').
          {
            rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
            by unfold mergeable_interfaces in *; intuition.
          }

          assert (eprog: prog = program_link c p).
          {
            rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
            rewrite <- Hifc_cc', <- Hifc_pp'.
            by unfold mergeable_interfaces in *; intuition.
          }

          assert (eprog': prog' = program_link c' p).
          {
            rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
            rewrite <- Hifc_cc'. by unfold mergeable_interfaces in *; intuition.
          }

          
          suffices Hsymborder:
            exists (e2' : event)
                   (se2' : state ((CS.sem_non_inform (program_link c' p)))),
               Step (CS.sem_non_inform (program_link c' p)) st2' [:: e2'] se2' /\
               mergeable_border_states c' p' c p n'' n se2'' se2' se2
                                       (rcons (t1'' ** t2''pref) e2'')
                                       (rcons (t1' ** t2') e2')
                                       (rcons (t1 ** t2) e2).
          {
            destruct Hsymborder as [e2' [se2' [Hse2' Gsym]]].
            apply mergeable_border_states_sym in Gsym.
            rewrite <- eprog' in Hse2'.
            do 2 eexists; eauto; by intuition; eauto.
          }

         
          eapply threeway_multisem_event_lockstep_program_step; eauto.
          + CS.unfold_state st2''. CS.unfold_state st2'. CS.simplify_turn. subst.
            eapply mergeable_states_in_to_notin2; eauto.
            find_and_invert_mergeable_states_well_formed. by erewrite Hifc_pp'.
          + by erewrite <- eprog''.
          + by erewrite <- eprog.
          + apply traces_shift_each_other_option_symmetric.
            unfold Eapp. rewrite !rcons_cat. exact Hshift.
          + unfold Eapp in *. rewrite <- !rcons_cat in Hshift.
            inversion Hshift as [? ? Hren]; subst; inversion Hren; subst;
              first by find_nil_rcons.
            repeat find_rcons_rcons. assumption.
          + unfold Eapp in *. rewrite <- !rcons_cat in Hshift.
            inversion Hshift as [? ? Hren]; subst; inversion Hren; subst;
              first by find_nil_rcons.
            repeat find_rcons_rcons. assumption.
      }


      (** Use weakening *)
      apply mergeable_border_mergeable_internal in Hborder.
      invert_non_eagerly_mergeable_internal_states Hborder.
      + 
        (** Use option simulation (starting from the state right after 
            the border crossing). *)
        pose proof (merge_states_silent_star) as Hoption_sim; unfold E0 in *.
        assert (Hcomp_se2: CS.is_program_component se2 (prog_interface c)).
        {
          CS.unfold_state se2. CS.unfold_state se2'. simpl in *.
          subst. by CS.simplify_turn.
        }
        apply star_iff_starR in Hse2''. 
        specialize (Hoption_sim _ _ _ _ _ _ _ _ _ _ _ _ _
                                Hborder Hcomp_se2 Hse2'').
        
        (** Use lock-step simulation (starting from the state right after 
            the border crossing). *)      
        pose proof (threeway_multisem_star_E0) as Hlockstep.
        specialize (Hlockstep _ _ _ _ _ _ _ _ _ _ _ _ _
                              Hcomp_se2 Hoption_sim Hse2) as [s2' [Hstep12' Hmerge']].
        
        exists s2', (rcons t2' e2').
        rewrite <- !rcons_cat.
        
        unfold Eapp in *.
        split; last exact Hmerge'.
        
        apply star_iff_starR. 
        eapply starR_trans.
        * eapply starR_step.
          -- apply star_iff_starR; eauto.
          -- eauto.
          -- eauto.
        * exact Hstep12'.
        * rewrite <- cats1. unfold Eapp. by rewrite app_nil_r.

      +
        apply mergeable_internal_states_sym in Hborder.
        apply mergeable_states_well_formed_sym in Hmergewf.

        assert (eprog'': prog'' = program_link c' p').
        {
          rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
            by unfold mergeable_interfaces in *; intuition.
        }

        assert (eprog: prog = program_link c p).
        {
          rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
          rewrite <- Hifc_cc', <- Hifc_pp'.
            by unfold mergeable_interfaces in *; intuition.
        }

        assert (eprog': prog' = program_link c' p).
        {
          rewrite program_linkC; find_and_invert_mergeable_states_well_formed; auto.
          rewrite <- Hifc_cc'. by unfold mergeable_interfaces in *; intuition.
        }
        
        suffices HsymG:
          exists (s2' : state ((CS.sem_non_inform (program_link c' p))))
                 (t2'G: trace event),
            Star (CS.sem_non_inform (program_link c' p)) s1' t2'G s2' /\
            mergeable_internal_states c' p' c p n'' n s2'' s2' s2
                                      (rcons (t1'' ** t2''pref) e2'')
                                      (t1' ** t2'G)
                                      (rcons (t1 ** t2) e2).
        {
          destruct HsymG as [s2' [t2'G [Ht2'G HmergeG]]].
          exists s2', t2'G.
          unfold sem'. rewrite eprog'. split; first assumption.
          apply mergeable_internal_states_sym.
          by rewrite <- !rcons_cat.
        }

        (** Use option simulation (starting from the state right after 
            the border crossing). *)
        pose proof (merge_states_silent_star) as Hoption_sim; unfold E0 in *.
        assert (Hcomp_se2: CS.is_program_component se2'' (prog_interface p')).
        {
          find_and_invert_mergeable_states_well_formed.
          CS.unfold_state se2''. CS.unfold_state se2. CS.unfold_state se2'. simpl in *.
          subst. CS.simplify_turn.
          eapply mergeable_states_in_to_notin2; eauto. by rewrite Hifc_pp'.          
        }
        apply star_iff_starR in Hse2.
        unfold sem in *. rewrite eprog in Hse2.
        specialize (Hoption_sim _ _ _ _ _ _ _ _ _ _ _ _ _
                                Hborder Hcomp_se2 Hse2).
        
        (** Use lock-step simulation (starting from the state right after 
            the border crossing). *)      
        pose proof (threeway_multisem_star_E0) as Hlockstep.
        unfold sem'' in *. rewrite eprog'' in Hse2''.
        specialize (Hlockstep _ _ _ _ _ _ _ _ _ _ _ _ _
                              Hcomp_se2 Hoption_sim Hse2'') as [s2' [Hstep12' Hmerge']].
        
        exists s2', (rcons t2' e2').
        rewrite <- !rcons_cat.
        
        unfold Eapp in *.
        split; last exact Hmerge'.
        
        apply star_iff_starR. 
        eapply starR_trans.
        * eapply starR_step.
          -- apply star_iff_starR; rewrite <- !eprog'; eauto.
          -- rewrite <- !eprog'; eauto.
          -- eauto.
        * exact Hstep12'.
        * rewrite <- cats1. unfold Eapp. by rewrite app_nil_r.
  Qed.


  Print Assumptions threeway_multisem_star_program.
  
End ThreewayMultisem1.


(* Theorems on initial states for main simulation. *)
Section ThreewayMultisem4.
  Variables p c p' c' : program.

  (* In this section, we should instantiate n and n'', not parameterize over them. *)
  Variables n n'' : Component.id -> nat.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog''_is_closed : closed_program (program_link p' c').
    

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.


  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_trace_extensional (left_addr_good_for_shifting n) tt
      /\
      forall mem ptr addr v,
        CS.state_mem ss = mem ->
        Memory.load mem ptr = Some v ->
        addr = (Pointer.component ptr, Pointer.block ptr) ->
        left_addr_good_for_shifting n addr ->
        left_value_good_for_shifting n v.
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_trace_extensional (left_addr_good_for_shifting n'') tt''
      /\
      forall mem ptr addr v,
        CS.state_mem ss'' = mem ->
        Memory.load mem ptr = Some v ->
        addr = (Pointer.component ptr, Pointer.block ptr) ->
        left_addr_good_for_shifting n'' addr ->
        left_value_good_for_shifting n'' v.

  Lemma merged_program_is_closed: closed_program prog'.
  Proof.
    unfold mergeable_interfaces in *.
    destruct Hmergeable_ifaces.
    eapply interface_preserves_closedness_r; eauto.
    - by eapply linkable_implies_linkable_mains.
    - by eapply interface_implies_matching_mains.
  Qed.

  Lemma match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
  exists s',
    initial_state sem'  s'  /\
    mergeable_border_states p c p' c' n n'' s s' s'' E0 E0 E0.
  Proof.
    intros Hini Hini''. simpl in *.
    exists (CS.initial_machine_state prog'). split.
    - unfold initial_state, CS.initial_machine_state; reflexivity.
    - pose proof merged_program_is_closed as Hprog'_is_closed.
      assert (CS.initial_machine_state (program_link p c') =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitpc'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacec.
      }
      assert (CS.initial_machine_state (program_link p c) =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c,
                  Z.of_nat 0
                )
              )
             ) as Hinitpc.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          by destruct Hmergeable_ifaces as [? _].
      }
      
      assert (CS.initial_machine_state (program_link p' c') =
              (
                [],
                unionm (prepare_procedures_memory p') (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p' + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitp'c'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacep; rewrite <- Hifacec.
      }

      unfold CS.initial_state in *; subst.
      
      rewrite Hinitpc'.
      (* 
         Need to know whether to apply mergeable_border_states_p_executing
         or mergeable_border_states_c'_executing.

         But in any case, we will need mergeable_states_well_formed.
       *)
      assert (mergeable_states_well_formed
                p c p' c' n n''
                (CS.initial_machine_state prog)
                ([],
                 unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                 Register.init,
                 (Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0)
                )
                (CS.initial_machine_state prog'')
                E0 E0 E0
             ) as Hmergewf.
      {
        eapply mergeable_states_well_formed_intro;
          simpl; eauto; unfold CS.initial_state, CSInvariants.is_prefix in *; subst.
        + by apply star_refl.
        + rewrite Hinitpc'; by apply star_refl.
        + by apply star_refl.
        + unfold E0; constructor; intros ? Hcontra.
          inversion Hcontra; subst; by find_nil_rcons.
        + unfold E0; constructor; intros ? Hcontra.
          inversion Hcontra; subst; by find_nil_rcons.
        + unfold E0; constructor; intros ? Hcontra.
          inversion Hcontra; subst; by find_nil_rcons.
        + unfold CS.initial_machine_state. destruct (prog_main prog); by constructor.
        + unfold CS.initial_machine_state. destruct (prog_main prog''); by constructor.
        + unfold CS.initial_machine_state. by destruct (prog_main prog).
        + unfold CS.initial_machine_state. by destruct (prog_main prog'').
        + constructor. constructor.
        + constructor. constructor.
      }

      destruct (Component.main \in domm (prog_interface p)) eqn:whereismain.
      + (* Component.main is in p. *)
        assert (Hmainc: Component.main \notin domm (prog_interface c)).
        {
          unfold mergeable_interfaces, linkable in *.
          destruct Hmergeable_ifaces as [[_ Hdisj] _].
          move : Hdisj => /fdisjointP => Hdisj.
          by apply Hdisj.
        }
        eapply mergeable_border_states_p_executing; simpl; eauto.
        * (* Goal: program counters equal *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          assert (CS.prog_main_block c = CS.prog_main_block c') as Hprogmainblk.
          {    
            rewrite !CS.prog_main_block_no_main; auto.
            by rewrite <- Hifacec.
          }
          by rewrite Hprogmainblk.
        * (* Goal: registers related *)
          unfold CS.initial_state in *; subst; rewrite Hinitpc; simpl.
          eapply regs_rel_of_executing_part_intro.
          intros reg. left.
          unfold Register.get.
          destruct (Register.to_nat reg \in domm Register.init) eqn:regdomm.
          -- rewrite (Register.reg_in_domm_init_Undef regdomm).
             by destruct reg.
          -- assert (Register.init (Register.to_nat reg) = None) as Hreginit_none.
             {
               rewrite mem_domm in regdomm.
               by destruct (Register.init (Register.to_nat reg)) eqn:e.
             }
             rewrite Hreginit_none. by simpl.
        * (* Goal: mem_of_part_executing_rel_original_and_recombined *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          constructor.
          -- intros [cidorig bidorig] Horig.
            (* Observe that because of Horig, we
               only care about addresses from the left part of the "unionm"'s.
               And observe that the left part is the same in both "uninonm"'s.
             *)
             constructor.
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                assert (e: isSome (prepare_procedures_memory p cidorig)).
                {
                  rewrite <- mem_domm; by rewrite domm_prepare_procedures_memory.
                }
                rewrite !e in Hload. rewrite !e !Hload.

                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                             Component.main
                             E0
                             (Permission.data, cidorig, bidorig, offset)
                             (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp.
                        -- exact Hwfc.
                        -- by unfold mergeable_interfaces in *; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e; simpl; assumption.
                    + by unfold mergeable_interfaces in *; intuition.
                }
                destruct (sigma_shifting_lefttoright_option
                            (n cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                ** 
                  inversion G as [ | ? ? Hshr | ];
                    simpl in *; subst; auto.
                  --- rewrite Horig in ebidv'.
                      apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                        by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** split; auto.
                   inversion G as [ | ? ? Hshr | ];
                    simpl in *; subst; auto.
                   --- rewrite Horig in ebidv'. by rewrite Horig ebidv'.
                   --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                   --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                assert (e: isSome (prepare_procedures_memory p cidorig)).
                {
                  rewrite <- mem_domm; by rewrite domm_prepare_procedures_memory.
                }
                rewrite !e in Hload. rewrite !e !Hload.
                exists v'.
                
                destruct v' as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                             Component.main
                             E0
                             (Permission.data, cidorig, bidorig, offset)
                             (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp.
                        -- exact Hwfc.
                        -- by unfold mergeable_interfaces in *; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e; simpl; assumption.
                    + by unfold mergeable_interfaces in *; intuition.
                }
                destruct (sigma_shifting_lefttoright_option
                            (n cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                ** split; auto. right.
                  inversion G as [ | ? ? Hshr | ];
                    simpl in *; subst; auto.
                  --- rewrite Horig in ebidv'.
                      apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                        by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** split; auto. left.
                   inversion G as [ | ? ? Hshr | ];
                    simpl in *; subst; auto.
                   --- rewrite Horig in ebidv'. by rewrite Horig ebidv'.
                   --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                   --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

          -- constructor.
             ++ intros ? Hcontra; unfold E0 in *;
                  inversion Hcontra; subst; by find_nil_rcons.
             ++ intros ? Hcid.
                unfold omap, obind, oapp.
                rewrite !unionmE.
                by rewrite <- !mem_domm, !domm_prepare_procedures_memory, Hcid.
                
         
        * (* Goal: mem_of_part_not_executing_rel_original_and_recombined_at_border*)
          unfold CS.initial_state in *. subst. rewrite Hinitp'c'. simpl.
          constructor.
          -- intros [cidorig bidorig] Horig.
            (* Observe that because of Horig, we
               only care about addresses from the right part of the "unionm"'s.
               And observe that the right part is the same in both "uninonm"'s.
             *)
             assert (e: isSome (prepare_procedures_memory c' cidorig)).
             {
               rewrite <- mem_domm; by rewrite domm_prepare_procedures_memory.
             }
             assert (e2: isSome (prepare_procedures_memory p' cidorig) = false).
             {
               rewrite <- mem_domm, domm_prepare_procedures_memory.
               assert (Hdisj: fdisjoint (domm (prog_interface p'))
                                        (domm (prog_interface c'))).
               {
                    unfold mergeable_interfaces, linkable in *.
                    rewrite <- Hifacep, <- Hifacec. by intuition.
               }
               move : Hdisj => /fdisjointP => Hdisj.
               destruct (cidorig \in domm (prog_interface p')) eqn:econtra; auto.
                 by apply Hdisj in econtra; rewrite Horig in econtra.
             }
             
             constructor.
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                rewrite !e2 in Hload.
                rewrite <- mem_domm, domm_prepare_procedures_memory, <- Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e2.
                rewrite !e2 !Hload.

                rewrite <- mem_domm, domm_prepare_procedures_memory, Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e2.

                
                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                               Component.main
                               E0
                               (Permission.data, cidorig, bidorig, offset)
                               (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog''_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp'.
                        -- exact Hwfc'.
                        -- by unfold mergeable_interfaces in *;
                             rewrite <- Hifacep, <- Hifacec; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *;
                          rewrite <- Hifacep, <- Hifacec; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e2; simpl; assumption.
                    + by unfold mergeable_interfaces in *;
                        rewrite <- Hifacep, <- Hifacec; intuition.
                }
                assert (Hdisj: fdisjoint (domm (prog_interface p'))
                                         (domm (prog_interface c'))).
                {
                  unfold mergeable_interfaces, linkable in *.
                  rewrite <- Hifacep, <- Hifacec. by intuition.
                }
                move : Hdisj => /fdisjointP => Hdisj.
                rewrite <- Hifacep in Hdisj.
                
                destruct (sigma_shifting_lefttoright_option
                            (n'' cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                **
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'.
                          apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** split; auto.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'. by rewrite ecidorig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                   
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                exists v'.
                rewrite !e2.

                rewrite <- mem_domm, domm_prepare_procedures_memory, <- Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e2.
                rewrite e2 in Hload.

                rewrite <- mem_domm, domm_prepare_procedures_memory, Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e2.

                rewrite Hload.
                
                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v' as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto. split; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                               Component.main
                               E0
                               (Permission.data, cidorig, bidorig, offset)
                               (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog''_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp'.
                        -- exact Hwfc'.
                        -- by unfold mergeable_interfaces in *;
                             rewrite <- Hifacep, <- Hifacec; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *;
                          rewrite <- Hifacep, <- Hifacec; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e2; simpl; assumption.
                    + by unfold mergeable_interfaces in *;
                        rewrite <- Hifacep, <- Hifacec; intuition.
                }
                assert (Hdisj: fdisjoint (domm (prog_interface p'))
                                         (domm (prog_interface c'))).
                {
                  unfold mergeable_interfaces, linkable in *.
                  rewrite <- Hifacep, <- Hifacec. by intuition.
                }
                move : Hdisj => /fdisjointP => Hdisj.
                rewrite <- Hifacep in Hdisj.
                
                destruct (sigma_shifting_lefttoright_option
                            (n'' cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                **
                  right.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'.
                          apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

                ** left.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'. by rewrite ecidorig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

          -- constructor.
             ++ intros ? Hcontra; unfold E0 in *;
                  inversion Hcontra; subst; by find_nil_rcons.
             ++ intros ? Hcid.
                unfold omap, obind, oapp.
                rewrite !unionmE.
                rewrite <- !mem_domm, !domm_prepare_procedures_memory.
                assert (Hcid': cid \in domm (prog_interface p) = false).
                {
                  unfold mergeable_interfaces, linkable in *.
                  destruct Hmergeable_ifaces as [[_ Hdisj2] _].
                  rewrite fdisjointC in Hdisj2.
                  move : Hdisj2 => /fdisjointP => Hdisj2.
                  rewrite Hifacec in Hdisj2.
                  apply Hdisj2 in Hcid.
                  by destruct (cid \in domm (prog_interface p)) eqn:econtra; auto.
                }
                by rewrite <- Hifacep, Hcid'.

            

      + (* Component.main is in c'. Should be analogous to the parallel goal. *)
        assert (Hmainc: Component.main \in domm (prog_interface c)).
        {
          destruct (Component.main \in domm (prog_interface c)) eqn:econtra; auto.
          exfalso.
          eapply domm_partition_program_link_in_neither;
            last (by erewrite econtra); last (by erewrite whereismain); assumption. 
        }
        eapply mergeable_border_states_c'_executing; simpl; eauto.
        * (* Goal: program counters equal *)
          unfold CS.initial_state in *. subst. rewrite Hinitp'c'. simpl.
          assert (CS.prog_main_block p = CS.prog_main_block p') as Hprogmainblk.
          {
            rewrite !CS.prog_main_block_no_main; auto.
            - by rewrite <- Hifacep, whereismain.
            - by rewrite whereismain.
          }
          by rewrite Hprogmainblk.
        * (* Goal: registers related *)
          unfold CS.initial_state in *; subst; rewrite Hinitp'c'; simpl.
          eapply regs_rel_of_executing_part_intro.
          intros reg. left.
          unfold Register.get.
          destruct (Register.to_nat reg \in domm Register.init) eqn:regdomm.
          -- rewrite (Register.reg_in_domm_init_Undef regdomm).
             by destruct reg.
          -- assert (Register.init (Register.to_nat reg) = None) as Hreginit_none.
             {
               rewrite mem_domm in regdomm.
               by destruct (Register.init (Register.to_nat reg)) eqn:e.
             }
             rewrite Hreginit_none. by simpl.
        * (* Goal: mem_of_part_executing_rel_original_and_recombined *)
          assert (Hdisj: fdisjoint (domm (prog_interface p'))
                                   (domm (prog_interface c'))).
          {
            unfold mergeable_interfaces, linkable in *.
            rewrite <- Hifacep, <- Hifacec. by intuition.
          }
          move : Hdisj => /fdisjointP => Hdisj.
          
          unfold CS.initial_state in *. subst. rewrite Hinitp'c'. simpl.
          constructor.
          -- intros [cidorig bidorig] Horig.
            (* Observe that because of Horig, we
               only care about addresses from the left part of the "unionm"'s.
               And observe that the left part is the same in both "uninonm"'s.
             *)
             constructor.
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                assert (e: isSome (prepare_procedures_memory p' cidorig) = false).
                {
                  rewrite <- mem_domm.
                  destruct (cidorig \in domm (prepare_procedures_memory p'))
                           eqn:econtra; auto.
                  rewrite domm_prepare_procedures_memory in econtra.
                  apply Hdisj in econtra. by rewrite Horig in econtra.
                }
                rewrite !e in Hload.
                rewrite <- mem_domm, domm_prepare_procedures_memory, <- Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e.
                rewrite !e !Hload.

                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                             Component.main
                             E0
                             (Permission.data, cidorig, bidorig, offset)
                             (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog''_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp'.
                        -- exact Hwfc'.
                        -- by unfold mergeable_interfaces in *;
                             rewrite <- Hifacec, <- Hifacep; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *;
                          rewrite <- Hifacec, <- Hifacep; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE; simpl.
                      rewrite <- mem_domm, domm_prepare_procedures_memory, Hifacep,
                      <- domm_prepare_procedures_memory, mem_domm in e.
                      rewrite e.
                      assumption.                      
                    + by unfold mergeable_interfaces in *;
                        rewrite <- Hifacec, <- Hifacep; intuition.
                }
                destruct (sigma_shifting_lefttoright_option
                            (n'' cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                ** 
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ rewrite Hifacep in ecidorig.
                          apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'.
                          apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** split; auto.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ rewrite Hifacep in ecidorig.
                          apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'. by rewrite ecidorig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                assert (e: isSome (prepare_procedures_memory p cidorig) = false).
                {
                  rewrite <- mem_domm.
                  destruct (cidorig \in domm (prepare_procedures_memory p))
                           eqn:econtra; auto.
                  
                  rewrite domm_prepare_procedures_memory Hifacep in econtra.
                  apply Hdisj in econtra. by rewrite Horig in econtra.
                }
                rewrite !e in Hload.
                rewrite <- mem_domm, domm_prepare_procedures_memory, Hifacep,
                  <- domm_prepare_procedures_memory, mem_domm in e.
                rewrite !e !Hload.

                exists v'.
                
                destruct v' as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                             Component.main
                             E0
                             (Permission.data, cidorig, bidorig, offset)
                             (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog''_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp'.
                        -- exact Hwfc'.
                        -- by rewrite <- Hifacep, <- Hifacec;
                             unfold mergeable_interfaces in *; intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by rewrite <- Hifacep, <- Hifacec;
                          unfold mergeable_interfaces in *; intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e; simpl; assumption.
                    + by rewrite <- Hifacep, <- Hifacec;
                        unfold mergeable_interfaces in *; intuition.
                }

                destruct (sigma_shifting_lefttoright_option
                            (n'' cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                **
                  split; auto; right.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ rewrite Hifacep in ecidorig.
                          apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'.
                          apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** split; auto; left.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- destruct (cidorig \in domm (prog_interface p)) eqn:ecidorig.
                      +++ rewrite Hifacep in ecidorig.
                          apply Hdisj in ecidorig. by rewrite Horig in ecidorig.
                      +++ rewrite ecidorig in ebidv'. by rewrite ecidorig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

          -- constructor.
             ++ intros ? Hcontra; unfold E0 in *;
                  inversion Hcontra; subst; by find_nil_rcons.
             ++ intros ? Hcid.
                unfold omap, obind, oapp.
                rewrite !unionmE.
                rewrite <- !mem_domm, !domm_prepare_procedures_memory.
                assert (Hcid': cid \in domm (prog_interface p) = false).
                {
                  unfold mergeable_interfaces, linkable in *.
                  destruct Hmergeable_ifaces as [[_ Hdisj2] _].
                  rewrite fdisjointC in Hdisj2.
                  move : Hdisj2 => /fdisjointP => Hdisj2.
                  rewrite Hifacec in Hdisj2.
                  apply Hdisj2 in Hcid.
                  by destruct (cid \in domm (prog_interface p)) eqn:econtra; auto.
                }
                by rewrite <- Hifacep, Hcid'.
                


        * (* Goal: mem_of_part_not_executing_rel_original_and_recombined_at_border*)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          constructor.
          -- intros [cidorig bidorig] Horig.
            (* Observe that because of Horig, we
               only care about addresses from the right part of the "unionm"'s.
               And observe that the right part is the same in both "uninonm"'s.
             *)
             assert (e: isSome (prepare_procedures_memory p cidorig)).
             {
               rewrite <- mem_domm; by rewrite domm_prepare_procedures_memory.
             }
             assert (e2: isSome (prepare_procedures_memory c cidorig) = false).
             {
               rewrite <- mem_domm, domm_prepare_procedures_memory.
               assert (Hdisj: fdisjoint (domm (prog_interface p))
                                        (domm (prog_interface c))).
               {
                    unfold mergeable_interfaces, linkable in *; by intuition.
               }
               rewrite fdisjointC in Hdisj.
               move : Hdisj => /fdisjointP => Hdisj.
               destruct (cidorig \in domm (prog_interface c)) eqn:econtra; auto.
                 by apply Hdisj in econtra; rewrite Horig in econtra.
             }
             
             constructor.
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                rewrite !e in Hload.
                rewrite !e !Hload.

                
                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                               Component.main
                               E0
                               (Permission.data, cidorig, bidorig, offset)
                               (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp.
                        -- exact Hwfc.
                        -- by unfold mergeable_interfaces in *;
                             intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *;
                          intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE; simpl.
                      rewrite e;  assumption.
                    + by unfold mergeable_interfaces in *; intuition.
                }
                assert (Hdisj: fdisjoint (domm (prog_interface p))
                                         (domm (prog_interface c))).
                {
                  unfold mergeable_interfaces, linkable in *; by intuition.
                }
                move : Hdisj => /fdisjointP => Hdisj.
                
                destruct (sigma_shifting_lefttoright_option
                            (n cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                ** 
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  ---
                    rewrite Horig in ebidv'.
                    apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                ** 
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- rewrite Horig in ebidv'. by rewrite Horig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.

                   
             ++ intros ? ? Hload. unfold Memory.load in *; simpl in *.
                rewrite unionmE in Hload. rewrite !unionmE.
                exists v'.
                rewrite !e.

                rewrite e in Hload.

                rewrite Hload.
                
                (** Here, need some invariant about the values that exist *)
                (** in the initial memory. Probably need to instantiate   *)
                (** CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc         *)
                

                destruct v' as [| [[[permv cidv] bidv] offv] |]; auto; simpl in *;
                  try reflexivity.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto. split; auto.
                assert (permv = Permission.data). by apply/Permission.eqP. subst.
                unfold rename_addr_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *.
                assert (G: CSInvariants.wf_load
                             Component.main
                             E0
                             (Permission.data, cidorig, bidorig, offset)
                             (Permission.data, cidv, bidv, offv)
                       ).
                {
                  eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                  - eapply CSInvariants.wf_state_wf_mem; eauto.
                    + eapply CSInvariants.is_prefix_wf_state_t.
                      * exact Hprog_is_closed.
                      * eapply linking_well_formedness.
                        -- exact Hwfp.
                        -- exact Hwfc.
                        -- by unfold mergeable_interfaces in *;
                             intuition.
                      * eapply star_refl.
                    + rewrite CS.initial_machine_state_after_linking; eauto.
                        by unfold mergeable_interfaces in *;
                          intuition.
                  - rewrite CS.initial_machine_state_after_linking; eauto.
                    + unfold Memory.load; rewrite !unionmE e; simpl; assumption.
                    + by unfold mergeable_interfaces in *;
                        intuition.
                }
                assert (Hdisj: fdisjoint (domm (prog_interface p))
                                         (domm (prog_interface c))).
                {
                  unfold mergeable_interfaces, linkable in *; by intuition.
                }
                move : Hdisj => /fdisjointP => Hdisj.
                
                destruct (sigma_shifting_lefttoright_option
                            (n cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv';
                  rewrite ebidv'.
                **
                  right.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  ---
                    rewrite Horig in ebidv'.
                    apply sigma_shifting_lefttoright_option_n_n_id in ebidv';
                            by subst.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
                **
                  left; split; auto; split; auto.
                  inversion G as [| ? ? Hshr |]; simpl in *; subst; auto.
                  --- rewrite Horig in ebidv'. by rewrite Horig ebidv'.
                  --- unfold E0 in *; inversion Hshr; by find_nil_rcons.
                  --- unfold E0 in *;
                        match goal with | Hshr: addr_shared_so_far _ _ |- _ =>
                                          inversion Hshr; by find_nil_rcons
                        end.
          -- constructor.
             ++ intros ? Hcontra; unfold E0 in *;
                  inversion Hcontra; subst; by find_nil_rcons.
             ++ intros ? Hcid.
                unfold omap, obind, oapp.
                rewrite !unionmE.
                by rewrite <- !mem_domm, !domm_prepare_procedures_memory, Hcid.

  Qed.         

End ThreewayMultisem4.

(* Remaining theorems for main simulation.  *)
Section ThreewayMultisem5.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  (* RB: NOTE: Consider execution invariance and similar lemmas on the right as
     well, as symmetry arguments reoccur all the time.
     TODO: Observe the proof of match_nostep is almost identical, and refactor
     accordingly. *)

  Theorem match_final_states s s' s'' t t' t'':
    mergeable_internal_states p c p' c' n n'' s s' s'' t t' t'' ->
    final_state sem   s   ->
    final_state sem'' s'' ->
    final_state sem'  s'.
  Proof.
    intros Hmerge Hfin Hfin''.
    find_and_invert_mergeable_internal_states.
    - eapply mergeable_internal_states_final_state_prog; eauto.
    - eapply mergeable_internal_states_final_state_prog''; eauto.
  Qed.

  
  Theorem match_nofinal s s' s'' t t' t'':
    mergeable_internal_states p c p' c' n n'' s s' s'' t t' t'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    ~ final_state sem'  s'.
  Proof.
    intros Hmerge Hfin Hfin''.
    find_and_invert_mergeable_internal_states.
    - eapply mergeable_internal_states_nofinal_prog; eauto.
    - eapply mergeable_internal_states_nofinal_prog''; eauto.
  Qed.

    
End ThreewayMultisem5.

(* Main simulation theorem. *)
Section Recombination.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.

  Let n' := fun cid =>
              if cid \in domm (prog_interface p)
              then n   cid
              else n'' cid.
  
  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_trace_extensional (left_addr_good_for_shifting n) tt
      /\
      forall mem ptr addr v,
        CS.state_mem ss = mem ->
        Memory.load mem ptr = Some v ->
        addr = (Pointer.component ptr, Pointer.block ptr) ->
        left_addr_good_for_shifting n addr ->
        left_value_good_for_shifting n v.
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_trace_extensional (left_addr_good_for_shifting n'') tt''
      /\
      forall mem ptr addr v,
        CS.state_mem ss'' = mem ->
        Memory.load mem ptr = Some v ->
        addr = (Pointer.component ptr, Pointer.block ptr) ->
        left_addr_good_for_shifting n'' addr ->
        left_value_good_for_shifting n'' v.


  Theorem recombination_trace_rel s s'' t t'':
    Star sem   (CS.initial_machine_state prog)   t   s   ->
    Star sem'' (CS.initial_machine_state prog'') t'' s'' ->
    traces_shift_each_other_option n n'' t t''           ->
  exists s' t',
    Star sem'  (CS.initial_machine_state prog')  t'  s'  /\
    mergeable_internal_states p c p' c' n n'' s s' s'' t t' t'' /\
    traces_shift_each_other_option n n' t t'.
  Proof.
    assert (exists s',
               initial_state (CS.sem_non_inform (program_link p c')) s' /\
               mergeable_border_states p c p' c' n n''
                                       (CS.initial_machine_state prog)
                                       s'
                                       (CS.initial_machine_state prog'') E0 E0 E0)
      as [s'ini [Hs'ini Hmerge]].
    {
      by eapply match_initial_states; eauto.
    }
    inversion Hs'ini; subst.

    (** Use weakening for Hmerge. *)
    apply mergeable_border_mergeable_internal in Hmerge.
    intros Hstar Hstar'' Hshift.
    rewrite <- E0_left in Hshift. rewrite <- E0_left in Hshift at 1.

    (** Distinguish which side is executing at the initial state. *)
    find_and_invert_mergeable_internal_states.
    - assert (H_p_prog: CS.is_program_component
                (CS.initial_machine_state prog)
                (prog_interface c)
             ).
      {
        CS.unfold_state (CS.initial_machine_state prog).
        CS.unfold_state (CS.initial_machine_state (program_link p c')).
        CS.simplify_turn. by subst.
      }

      (** Instantiate lemma "mergeable_internal_states_matching_stars" *)
      specialize (threeway_multisem_star_program H_p_prog Hmerge Hstar Hstar'' Hshift)
        as [s' [t' [Hstar' Hmerge']]].
      do 2 eexists; split; last (split); eauto.
      rewrite !E0_left in Hmerge'.
        by find_and_invert_mergeable_internal_states;
          find_and_invert_mergeable_states_well_formed.
    - apply mergeable_internal_states_sym in Hmerge.
      apply mergeable_states_well_formed_sym in Hmergewf.
      assert (eprog: prog = program_link c p).
      { unfold prog; rewrite program_linkC; auto.
          by unfold mergeable_interfaces in *; intuition. }
      assert (eprog'': prog'' = program_link c' p').
      { unfold prog''; rewrite program_linkC; auto.
          unfold mergeable_interfaces in *;
            find_and_invert_mergeable_states_well_formed;
          rewrite Hifc_cc' Hifc_pp'; by intuition. }
      assert (eprog': prog' = program_link c' p).
      { unfold prog'; rewrite program_linkC; auto.
          unfold mergeable_interfaces in *;
            find_and_invert_mergeable_states_well_formed;
          rewrite Hifc_pp'; by intuition. }
      
      unfold prog' in *.
      rewrite eprog eprog' eprog'' in Hmerge.
      unfold sem, sem'' in Hstar, Hstar''.
      rewrite !eprog in Hstar.
      rewrite !eprog'' in Hstar''.
      apply traces_shift_each_other_option_symmetric in Hshift.

      rewrite eprog' eprog'' in Hpc.
      rewrite eprog' in H_c'.
      
      assert (H_p_prog: CS.is_program_component
                (CS.initial_machine_state (program_link c' p'))
                (prog_interface p')
             ).
      {
        CS.unfold_state (CS.initial_machine_state (program_link c' p')).
        CS.unfold_state (CS.initial_machine_state (program_link c' p)).
        CS.simplify_turn. subst.
        eapply mergeable_states_in_to_notin2; eauto.
        find_and_invert_mergeable_states_well_formed; by rewrite Hifc_pp'.
      }

      unfold sem'. rewrite !eprog'.
      
      (** Instantiate lemma "mergeable_internal_states_matching_stars" *)
      specialize (threeway_multisem_star_program H_p_prog Hmerge Hstar'' Hstar Hshift)
        as [s' [t' [Hstar' Hmerge']]].
      do 2 eexists; split; last (split); eauto.
      + by apply mergeable_internal_states_sym.
      + {
      
          rewrite !E0_left in Hmerge'.
          inversion Hmerge' as [Hwf | Hwf];
            inversion Hwf.
          
          + constructor. eapply traces_rename_each_other_option_n'_if.
            * inversion H26; subst. exact H27.
            * intros [cid bid] Hshr''. simpl.
              destruct (cid \in domm (prog_interface c')) eqn:ecid; rewrite ecid.
              -- destruct Hmergeable_ifaces as [[_ G] _].
                 rewrite fdisjointC in G.
                 move : G => /fdisjointP => G. rewrite Hifacec in G.
                 symmetry. by apply G.
              -- assert (cid \in domm (prog_interface p) \/
                                 cid \in domm (prog_interface c)) as [G | contra].
                 {
                   eapply CSInvariants.addr_shared_so_far_domm_partition; eauto.
                   - unfold prog in eprog. rewrite eprog. eassumption.
                   - apply linking_well_formedness; auto.
                     by destruct Hmergeable_ifaces; intuition.
                 }
                 ++ by rewrite G.
                 ++ by rewrite -Hifacec contra in ecid.
            * intros [cid bid] Hshr''. simpl.
              destruct (cid \in domm (prog_interface c')) eqn:ecid; rewrite ecid.
              -- destruct Hmergeable_ifaces as [[_ G] _].
                 rewrite fdisjointC in G.
                 move : G => /fdisjointP => G. rewrite Hifacec in G.
                 symmetry. by apply G.
              -- assert (cid \in domm (prog_interface p) \/
                                 cid \in domm (prog_interface c')) as [G | contra].
                 {
                   eapply CSInvariants.addr_shared_so_far_domm_partition; eauto.
                   - by rewrite -Hifacec; destruct Hmergeable_ifaces; intuition.
                   - unfold prog' in eprog'. rewrite eprog'. eassumption.
                   - eapply merged_program_is_closed with (p := p) (c := c); eauto.
                   - apply linking_well_formedness; auto.
                       by rewrite -Hifacec; destruct Hmergeable_ifaces; intuition.
                 }
                 ++ by rewrite G.
                 ++ by rewrite contra in ecid.
          + constructor. eapply traces_rename_each_other_option_n'_if.
            * inversion H26; subst. exact H27.
            * intros [cid bid] Hshr''. simpl.
              destruct (cid \in domm (prog_interface c')) eqn:ecid; rewrite ecid.
              -- destruct Hmergeable_ifaces as [[_ G] _].
                 rewrite fdisjointC in G.
                 move : G => /fdisjointP => G. rewrite Hifacec in G.
                 symmetry. by apply G.
              -- assert (cid \in domm (prog_interface p) \/
                                 cid \in domm (prog_interface c)) as [G | contra].
                 {
                   eapply CSInvariants.addr_shared_so_far_domm_partition;
                     eauto.
                   - unfold prog in eprog. rewrite eprog. eassumption.
                   - apply linking_well_formedness; auto.
                       by destruct Hmergeable_ifaces; intuition.
                 }
                 ++ by rewrite G.
                 ++ by rewrite -Hifacec contra in ecid.
            * intros [cid bid] Hshr''. simpl.
              destruct (cid \in domm (prog_interface c')) eqn:ecid; rewrite ecid.
              -- destruct Hmergeable_ifaces as [[_ G] _].
                 rewrite fdisjointC in G.
                 move : G => /fdisjointP => G. rewrite Hifacec in G.
                 symmetry. by apply G.
              -- assert (cid \in domm (prog_interface p) \/
                                 cid \in domm (prog_interface c')) as [G | contra].
                 {
                   eapply CSInvariants.addr_shared_so_far_domm_partition; eauto.
                   - by rewrite -Hifacec; destruct Hmergeable_ifaces; intuition.
                   - unfold prog' in eprog'. rewrite eprog'. eassumption.
                   - eapply merged_program_is_closed with (p := p) (c := c); eauto.
                   - apply linking_well_formedness; auto.
                       by rewrite -Hifacec; destruct Hmergeable_ifaces; intuition.
                 }
                 ++ by rewrite G.
                 ++ by rewrite contra in ecid.
        }
  Qed.

  Theorem recombination_prefix_rel m m'' :
    does_prefix sem   m ->
    does_prefix sem'' m'' ->
    behavior_rel_behavior n  n'' m  m'' ->
  exists m' n',
    does_prefix sem'  m' /\
    behavior_rel_behavior n' n   m' m.
  Proof.
    unfold does_prefix.
    intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']] Hrel.
    (* Invert prefix executions to expose their initial states (and full program
       behaviors. *)
    assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh'').
    apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]].
    apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']].
    (* Suppose we can establish the relation between the initial states of the
       two runs and the initial state of the recombined program. *)
    
    assert (exists s1',
               CS.initial_state prog' s1' /\
               mergeable_border_states
                 p c p' c' n n''
                 s1 s1' s1'' E0 E0 E0) as [s1' [Hini1' Hmerge1]].
    {
      eapply match_initial_states; eauto.
    }

    destruct m as [tm | tm | tm]; destruct m'' as [tm'' | tm'' | tm''];
      try by inversion Hrel.
    - destruct b   as [t   | ? | ? | ?]; try contradiction.
      destruct b'' as [t'' | ? | ? | ?]; try contradiction.
      simpl in Hprefix, Hprefix''. subst t t''.
      inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst.
      inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst.

      unfold CS.initial_state in *; subst.
      inversion Hrel as [? ? Htraces|? ? Htraces]; try discriminate; subst.
      
      specialize (recombination_trace_rel Hstar12 Hstar12'' Htraces)
        as [s2' [tm' [Hstar12' [Hmerge Htraces']]]].
      
      exists (FTerminates tm'), n'.
      split.
      + exists (Terminates tm').
        split.
        * eapply program_runs with (s := (CS.initial_machine_state prog')); eauto.
          -- reflexivity.
          -- econstructor; eauto.
             eapply match_final_states; eauto.
        * by simpl.
      + constructor. by apply traces_shift_each_other_option_symmetric.

    - destruct b   as [t   | ? | ? | ?]; try contradiction;
        destruct b'' as [t'' | ? | ? | ?]; try contradiction;
          simpl in *;
        destruct Hprefix as [tm2 Hrewr]; subst;
        destruct Hprefix'' as [tm''2 Hrewr'']; subst;
        rewrite Hrewr in Hst_beh;
        rewrite Hrewr'' in Hst_beh'';
        (apply state_behaves_app_inv in Hst_beh as [s2 [Hstar12 Hst_beh]];
         last (by apply CS.singleton_traces_non_inform));
        (apply state_behaves_app_inv in Hst_beh'' as [s2'' [Hstar12'' Hst_beh'']];
         last by apply CS.singleton_traces_non_inform);
        unfold CS.initial_state in *; subst;
          inversion Hrel as [? ? Htraces|? ? Htraces]; try discriminate; subst;
            specialize (recombination_trace_rel Hstar12 Hstar12'' Htraces)
            as [s2' [tm' [Hstar12' [_ Htraces']]]];
            exists (FTbc tm'), n';
            (split;
             [eapply program_behaves_finpref_exists; eauto; by simpl
             | econstructor; by apply traces_shift_each_other_option_symmetric
             ]
            ).

  Qed.
  

End Recombination.


Print Assumptions recombination_prefix_rel.

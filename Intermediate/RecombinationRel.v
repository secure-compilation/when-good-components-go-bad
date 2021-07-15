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

      (** TODO: Refactor into a CompCert/Common-level lemma? *)
      assert (forall (sem: semantics event) s1 s2 t1 e1,
                 single_events sem ->
                 starR (step sem) (globalenv sem) s1 (rcons t1 e1) s2 ->
                 exists st1 se1,
                   starR (step sem) (globalenv sem) s1 t1 st1 /\
                   Step sem st1 [:: e1] se1 /\
                   starR (step sem) (globalenv sem) se1 E0 s2
             ) as starR_rcons_lemma.
      {
        clear.
        intros ? ? ? ? ? Hsingle Hstar.
        remember (rcons t1 e1) as t1_.
        revert e1 t1 Heqt1_.
        induction Hstar; intros; subst; unfold E0 in *; first by find_nil_rcons.
        induction t1 using last_ind.
        - unfold Eapp in *. rewrite app_nil_l in Heqt1_; subst.
          pose proof (Hsingle _ _ _ H) as Hlength.
          destruct t0; auto; simpl in *; auto.
          + exists s2, s3; intuition. constructor.
          + (** TODO: Use a "length_size" lemma. Get a contra in Hlength. *)
            assert (forall (A: Type) l, size l = @length A l) as size_length.
            {
              induction l; auto.
            }
            rewrite <- size_length, size_rcons in Hlength. omega. 
        - specialize (IHHstar x t1 Logic.eq_refl) as [st1 [se1 [Ht2 [He1 Hnil]]]].
          pose proof (Hsingle _ _ _ H) as Hlength.
          destruct t2; auto; simpl in *.
          + unfold Eapp in *. rewrite app_nil_r in Heqt1_. find_rcons_rcons.
            do 2 eexists; intuition; eauto.
            eapply starR_step; eauto.
          + destruct t2; simpl in *; auto.
            * unfold Eapp in *.
              assert (e1 = e /\ t0 = rcons t1 x) as [rewr1 rewr2]; subst.
              {
                rewrite <- cats1, <- catA, cats1, <- rcons_cat in Heqt1_.
                find_rcons_rcons.
                by rewrite cats1.
              }
              exists s2, s3; intuition. constructor.
            * omega.
      }
      
      apply star_iff_starR in Hstar12.
      apply star_iff_starR in Hstar12''.

      apply starR_rcons_lemma in Hstar12   as [st2 [se2 [Ht2 [He2 Hse2]]]]; auto;
        last by apply CS.singleton_traces_non_inform.
      apply starR_rcons_lemma in Hstar12'' as [st2'' [se2'' [Ht2'' [He2'' Hse2'']]]];
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
        - rewrite !size_rcons in szt2t2''. omega.
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

  
End ThreewayMultisem1.

(* Helpers and symmetric version of three-way simulation. *)
Section ThreewayMultisem2.
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

  (* RB: TODO: Rename, relocate. *)
  (* RB: NOTE: [DynShare] In this series of results, identical traces will need
     to be replaced by related traces. We can expect similar complications as in
     previous sections, especially in the need to produce explicit successor
     states that continue to satisfy the mergeability relation. *)
(*FIXME
  Lemma threeway_multisem_mergeable
        s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s1, t) (CS.state_mem s1'', t'') p ->
  exists s2' t',
    mergeable_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  (* Qed. *)
  Admitted. (* RB: TODO: Add stepping of [s1']. Redundant? *)

  (* RB: TODO: Implicit parameters, compact if possible. *)
  (* RB: NOTE: Again, without mergeability, this lemma is trivial and
     uninteresting. *)
  Lemma threeway_multisem_star_E0 s1 s1' s1'' t1 t1' t1'' s2 s2'':
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    (* Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2''). *)
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros H H0 H1.
  (*   inversion H as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hprg_component.
    - eapply threeway_multisem_star_E0_program; eassumption.
    - admit.
  (*   - rewrite (merge_states_sym H); try assumption. *)
  (*     rewrite (merge_states_sym (threeway_multisem_mergeable H H0 H1)); try assumption. *)
  (*     assert (Hlinkable : linkable ip ic) by now destruct Hmergeable_ifaces. *)
  (*     unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. *)
  (*     pose proof (program_linkC Hwfp Hwfc' Hlinkable) as Hprg_linkC'. *)
  (*     unfold sem', prog'. *)
  (*     rewrite Hprg_linkC'. *)
  (*     pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''. *)
  (*     unfold sem'', prog'' in H1. *)
  (*     rewrite (Hprg_linkC'' Hlinkable) in H1. *)
  (*     pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC. *)
  (*     unfold sem, prog in H0. *)
  (*     rewrite (Hprg_linkC Hlinkable) in H0. *)
  (*     pose proof (threeway_multisem_star_E0_program) as Hmultisem. *)
  (*     specialize (Hmultisem c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in Hmultisem. *)
  (*     specialize (Hmultisem s1'' s1 s2'' s2). *)
  (*     assert (His_prg_component'' : CS.is_program_component s1'' (prog_interface p)). *)
  (*     { eapply mergeable_states_context_to_program. *)
  (*       apply H. *)
  (*       unfold CS.is_program_component in Hprg_component. apply negbFE in Hprg_component. *)
  (*       assumption. *)
  (*     } *)
  (*     assert (Hmerg_sym : mergeable_states c' p' c p s1'' s1). *)
  (*     { inversion H. *)
  (*       econstructor; *)
  (*         try rewrite <- (Hprg_linkC Hlinkable); try rewrite <- (Hprg_linkC'' Hlinkable); eauto. *)
  (*       apply mergeable_interfaces_sym; congruence. *)
  (*     } *)
  (*     specialize (Hmultisem His_prg_component'' Hmerg_sym H1 H0). *)
  (*     assumption. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Add mergeability. *)

  (* A restricted version of the lockstep simulation on event-producing steps.
     RB: NOTE: Here is where we depart from the multi-semantics and need to
     furnish our own version. We may save effort if, as is the case here, we only
     need to concern ourselves with visible steps. *)
  (* RB: NOTE: Events need to be properly for full generality. Otherwise, this
     is just a symmetry lemma. *)
  Lemma threeway_multisem_event_lockstep s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    mergeable_internal_states p c p' c' n n''  s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    traces_shift_each_other n n'' (rcons t1 e) (rcons t1'' e'') ->
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mergeable_border_states p c p' c' n n'' s2 s2' s2'' (rcons t1 e) 
                            (rcons t1' e') (rcons t1'' e'').
  Proof.
    intros Hmerge1 Hstep12 Hstep12'' Hrel2.
  (*   inversion Hmerge1 as [? ? ? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed _ Hini H1 Hstar H2]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - inversion Hmerge1.
      eapply threeway_multisem_event_lockstep_program; try eassumption.
  (*   - inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof @threeway_multisem_event_lockstep_program c' p' c p as H. *)
  (*     rewrite <- Hifacec, <- Hifacep in H. *)
  (*     specialize (H s1'' s1 e s2'' s2). *)
  (*     assert (Hmerge11 := Hmerge1). *)
  (*     erewrite mergeable_states_sym in Hmerge11; try eassumption. *)
  (*     erewrite mergeable_states_sym; try eassumption. *)
  (*     unfold ip, ic; erewrite merge_states_sym; try eassumption. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s2 s2''). *)
  (*     { inversion Hmerge1. *)
  (*       econstructor; try eassumption. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. } *)
  (*     rewrite (merge_states_sym Hmerge2); try assumption. *)
  (*     unfold sem', prog'; rewrite program_linkC; try congruence. *)
  (*     apply H; try assumption. *)
  (*     + unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn. *)
  (*       pose proof mergeable_states_pc_same_component Hmerge1 as Hpc. *)
  (*       destruct s1 as [[[[? ?] ?] pc1] ?]; destruct s1'' as [[[[? ?] ?] pc1''] ?]. *)
  (*       simpl in Hpc. *)
  (*       rewrite -Hpc. *)
  (*       unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcase. *)
  (*       destruct (CS.star_pc_domm_non_inform _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hdomm | Hdomm]. *)
  (*       apply domm_partition_notin_r with (ctx2 := ic) in Hdomm. *)
  (*       move: Hcase => /idP Hcase. rewrite Hdomm in Hcase. congruence. assumption. *)
  (*       now apply domm_partition_notin with (ctx1 := ip) in Hdomm. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       apply linkable_sym; congruence. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       now apply linkable_sym. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Symmetry lemma. Fix according to program side. *)
  (* JT: TODO: clean this proof. *)

  Theorem threeway_multisem_star_program
          s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    (* mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2',  t' ). *)
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' t'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 ta s2 tb s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' t'' s2'' Hcomp1 Hmerge1 Hstar12'' Hrel3.
    - assert (t'' = E0) by admit; subst t''. (* By the relation. *)
      exists E0, s1'. split.
      + now apply star_refl.
      + eapply merge_states_silent_star; try eassumption.
        (* AEK: 
           The lemma applied above looks suspicious because it seems
           we are now getting the same goal (as before the apply) again.
         *)
        admit.
        (* eapply context_epsilon_star_merge_states. eassumption. *)
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      assert (exists ta'' tb'', t'' = ta'' ** tb'')
        as [ta'' [tb'' ?]] by admit; subst t''. (* By pairwise events.
                                                   More info? *)
      assert (Hstar13''_ := Hstar13''). (* Which variants are needed? *)
      apply (star_app_inv (@CS.singleton_traces_non_inform _)) in Hstar13''_
        as [s2'' [Hstar12'' Hstar23'']].
      assert (Hrel1 : mem_rel2 n n'' (CS.state_mem s2, ta) (CS.state_mem s2'', ta'') p)
        by admit. (* Need to recompose memory relation based on executions. *)

      (*******************************************************************************)
      (*
      specialize (IHstar12' _ _ _ Hcomp1 Hmerge1 Hstar12'' Hrel1)
        as [ta' [s2' [Hstar12' Hmerge2]]].
      destruct tb as [| e2 [| e2' tb]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star.
           eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl]. *)
        assert (tb'' = E0) by admit; subst tb''.
        destruct (threeway_multisem_star_E0
                    Hmerge2 (star_one _ _ _ _ _ Hstep23) Hstar23'')
          as [s3' [Hstar23' Hmerge3]].
        exists ta', s3'. split.
        * eapply star_trans; try eassumption. by rewrite E0_right.
        * by rewrite !E0_right.
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        assert (exists e2'', tb'' = [e2'']) as [e2'' ?]
            by admit; subst tb''. (* By one-to-one event correspondence. More? *)
        change [e2''] with (E0 ** e2'' :: E0) in Hstar23''.
        apply (star_middle1_inv (@CS.singleton_traces_non_inform _)) in Hstar23''
          as [s2''1 [s2''2 [Hstar2'' [Hstep23'' Hstar3'']]]].
        (* Prefix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s2
          as Hstar2.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar2 as Hstar2_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge2 Hstar2_non_inform Hstar2''
          as [s2'1 [Hstar2' Hmerge21]].
        (* Propagate mergeability, step.
           NOTE: This is done early now, just above. *)
        (* assert (Hrel2 : mem_rel2 p α γ (CS.state_mem s2, E0) (CS.state_mem s2'', E0)) *)
          (* by admit. (* Should be easy. *) *)
        (* pose proof threeway_multisem_mergeable Hmerge2 Hstar2_non_inform Hstar2'' Hrel2 *)
          (* as [s2'2 Hmerge21']. *)
        assert (Hrel2 :
                  mem_rel2 n n'' (CS.state_mem s3, [e2]) (CS.state_mem s2''2, [e2'']) p)
          by admit. (* This one should also be obtainable from premises. *)
        pose proof threeway_multisem_event_lockstep Hmerge21 Hstep23 Hstep23'' Hrel2
          as [e' [s2'2 [Hstep23' Hmerge22]]].
        (* Propagate mergeability, suffix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s3
          as Hstar3.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar3 as Hstar3_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge22 Hstar3_non_inform Hstar3''
          as [s3' [Hstar3' Hmerge3]].
        (* Compose. *)
        exists (ta' ++ [e']), s3'. split. (*[| assumption].*)
        * eapply star_trans; first eassumption.
        exact (star_trans
                 (star_right _ _ Hstar2' Hstep23' (eq_refl _))
                 Hstar3' (eq_refl _)).
        rewrite -> E0_right, <- Eapp_assoc, -> E0_right.
        reflexivity.
        * by rewrite <- !Eapp_assoc.
      + (* Contradiction: a step generates at most one event. *)
        pose proof @CS.singleton_traces_non_inform _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  (* Qed. *)
       *)
      (******************************************************************************)
  Admitted. (* RB: TODO: Check admits. *)
*)
End ThreewayMultisem2.

(* Three-way simulation and its inversion. *)
Section ThreewayMultisem3.
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

(*FIXME
  Theorem threeway_multisem_star s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star (CS.sem_non_inform (program_link p  c')) (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
    (* /\ mergeable_states ip ic s2 s2'' *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    intros Hmerge1 Hstar12 Hstar12'' Hrel2.
  (*   inversion Hmerge1 as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcomp1.
    - eapply threeway_multisem_star_program; eassumption.
  Admitted. (* TODO: Proof of symmetry. Harmonize statements as needed. *)
  (*   - apply negb_false_iff in Hcomp1. *)
  (*     apply (mergeable_states_context_to_program Hmerge1) *)
  (*       in Hcomp1. *)
  (*     assert (Hmerge2: mergeable_states p c p' c' s2 s2'') *)
  (*       by (eapply threeway_multisem_mergeable; eassumption). *)
  (*     rewrite program_linkC in Hstar12; try assumption; *)
  (*       last now destruct Hmergeable_ifaces. *)
  (*     rewrite program_linkC in Hstar12''; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec -Hifacep. *)
  (*     rewrite program_linkC; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec. *)
  (*     unfold ip, ic. *)
  (*     setoid_rewrite merge_states_sym at 1 2; try eassumption. *)
  (*     pose proof threeway_multisem_star_program as H. *)
  (*     specialize (H c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in H. *)
  (*     specialize (H s1'' s1 t s2'' s2). *)
  (*     apply H; try assumption. *)
  (*     apply mergeable_states_sym in Hmerge1; try assumption; *)
  (*       try rewrite -Hifacec; try rewrite -Hifacep; try apply mergeable_interfaces_sym; *)
  (*         now auto. *)
  (* Qed. *)
  (* JT: TODO: improve this proof *)

  (* RB: NOTE: With the added premises, this becomes simply the three-way
     simulation lemma, and one of them ([threeway_multisem_mergeable]) becomes
     redundant.
     TODO: Possibly remove that lemma, and/or merge this with the main three-way
     result. *)
  Corollary star_simulation s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n''  (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
  exists t' s2',
    Star sem'  s1' t' s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    now apply threeway_multisem_star.
  Qed.

  (* [DynShare]
     The following tactic applies program_store_from_partialized_memory
     and program_alloc_from_partialized_memory, which will both fail.
   *)
  (* Ltac t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec:= *)
  (*   match goal with *)
  (*   (* Memory operations. *) *)
  (*   | Hstore : Memory.store _ _ _ = _ |- _ => *)
  (*     apply program_store_from_partialized_memory in Hstore as [mem1_ Hstore]; *)
  (*       try eassumption *)
  (*   | Halloc : Memory.alloc _ _ _ = _ |- _ => *)
  (*     apply program_alloc_from_partialized_memory in Halloc as [mem1_ [ptr_ Halloc]]; *)
  (*       try assumption *)
  (*   (* Calls. *) *)
  (*   | Hget : EntryPoint.get _ _ _ = _ |- _ => *)
  (*     apply (genv_entrypoints_interface_some) with (p' := prog) in Hget as [b' Hget]; *)
  (*     last (simpl; congruence); *)
  (*     try assumption *)
  (*   (* Returns. *) *)
  (*   | Hcons : ?PC' :: ?GPS' = ?GPS (* merge_states_stack *) |- _ => *)
  (*     destruct GPS as [| frame1' gps1'] eqn:Hgps; [discriminate |]; *)
  (*     destruct gps1 as [| frame1 gps1]; [now destruct gps1'' |]; *)
  (*     destruct gps1'' as [| frame1'' gps1'']; [easy |]; *)
  (*     inversion Hcons; subst PC' GPS'; *)
  (*     assert (Heq : Pointer.component frame1 = Pointer.component frame1') *)
  (*       by (unfold merge_states_stack in Hgps; *)
  (*           inversion Hgps as [[Hframe Hdummy]]; *)
  (*           unfold merge_frames; *)
  (*           destruct (Pointer.component frame1 \in domm ip) eqn:Hcase; rewrite Hcase; *)
  (*           [ reflexivity *)
  (*           | eapply mergeable_states_cons_domm; last exact Hmerge; eassumption]); *)
  (*     rewrite <- Heq *)
  (*   | _ => idtac *)
  (*   end; *)
  (*   [eexists; *)
  (*   CS.step_of_executing]; *)
  (*     try eassumption; try congruence; try reflexivity; *)
  (*     try (simpl; rewrite Hifacec; eassumption); *)
  (*     match goal with *)
  (*     (* Memory operations. *) *)
  (*     | Hload : Memory.load _ _ = _ |- Memory.load _ _ = _ => *)
  (*       unfold merge_states_mem in Hload; *)
  (*       erewrite <- program_load_to_partialized_memory_strong in Hload; *)
  (*       try exact Hmerge; eassumption *)
  (*     (* Jumps. *) *)
  (*     | Hlabel : find_label_in_component _ _ _ = _ |- find_label_in_component _ _ _ = _ => *)
  (*       rewrite find_label_in_component_program_link_left; *)
  (*       rewrite find_label_in_component_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     | Hlabel : find_label_in_procedure _ _ _ = _ |- find_label_in_procedure _ _ _ = _ => *)
  (*       rewrite find_label_in_procedure_program_link_left; *)
  (*       rewrite find_label_in_procedure_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     (* Calls. *) *)
  (*     | Himp : imported_procedure _ _ _ _ |- imported_procedure _ _ _ _ => *)
  (*       rewrite imported_procedure_unionm_left; [| assumption]; *)
  (*       rewrite Hifacec in Hnotin; now rewrite imported_procedure_unionm_left in Himp *)
  (*     | _ => idtac *)
  (*     end; *)
  (*   [apply execution_invariant_to_linking with (c1 := c')]; *)
  (*   try congruence; *)
  (*   try eassumption. *)
  (*     (* try eassumption; [congruence]. *) *)


  (* AEK: Looks too strong. *)
  Theorem threeway_multisem_step_inv_program s1 s1' s1'' t1 t1' t1'' t' s2' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    (* Step sem' (merge_states ip ic s1 s1'') t s2' -> *)
    Step sem' s1' t' s2' ->
  exists t s2,
    Step sem  s1  t  s2 /\
    mem_rel2 n n'' (CS.state_mem s1', t') (CS.state_mem s1, t) p.
  Admitted. (* RB: TODO: Tweak relations, prove later IF NEEDED. *)
  (* Proof. *)
  (*   intros Hpc Hmerge Hstep. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct s1 as [[[[gps1 mem1] regs1] pc1] addrs1]. *)
  (*   destruct s1'' as [[[[gps1'' mem1''] regs1''] pc1''] addrs1'']. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm'. *)
  (*   pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin; unfold ic in Hnotin; *)
  (*   assert (Hmains : linkable_mains p c') *)
  (*     by (apply linkable_implies_linkable_mains; congruence). *)
  (*   rewrite (mergeable_states_merge_program _ Hmerge) in Hstep; *)
  (*     try assumption. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc Hlinkable as Hwfprog. *)
  (*   pose proof linking_well_formedness Hwfp' Hwfc' Hlinkable' as Hwfprog'. *)
  (*   assert (Hlinkable'' := Hlinkable); rewrite Hifacec in Hlinkable''. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc' Hlinkable'' as Hwfprog''. *)

  (*   (* [DynShare] *)
  (*      Fails because of the program_store_from_partialized_memory and *)
  (*      program_alloc_from_partialized_memory *)
  (*    *) *)
  (*   (* *)
  (*   inversion Hstep; subst; *)
  (*     t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec. *)
  (* Qed. *)
  (*    *) *)
*)
End ThreewayMultisem3.

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
          -- assert (Register.init (Register.to_nat reg) = Some Undef)
              as Hreginit_undef.
             {
               by apply Register.reg_in_domm_init_Undef.
             }
             rewrite Hreginit_undef. by simpl.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto. split; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
          -- assert (Register.init (Register.to_nat reg) = Some Undef)
              as Hreginit_undef.
             {
               by apply Register.reg_in_domm_init_Undef.
             }
             rewrite Hreginit_undef. by simpl.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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
                destruct (permv =? Permission.data) eqn:epermv; auto. split; auto.
                assert (permv = Permission.data). by apply beq_nat_true. subst.
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

  (** AEK: To prove theorems 'nofinal' and 'nostep', we can *)
  (** use lemmas mergeable_internal_states_executing_prog'' *)
  (** and mergeable_internal_states_executing_prog.         *)
  
(*FIXME

  Theorem match_nofinal s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    (* ~ final_state sem'  (merge_states ip ic s s''). *)
    ~ final_state sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   destruct s as [[[[gps mem] regs] pc] addrs]. *)
  (*   destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal'' Hfinal'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _ ]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c2 := c) in Hfinal'; try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal'; try congruence. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     apply execution_invariant_to_linking with (c2 := p') in Hfinal'; try easy. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now eapply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)

  Lemma match_nostep s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    Nostep sem   s   ->
    Nostep sem'' s'' ->
    (* Nostep sem'  (merge_states ip ic s s''). *)
    Nostep sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   rename s into s1. rename s'' into s1''. *)
  (*   intros Hmerge Hstep Hstep'' t s2' Hstep'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable' _]; rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
  (*   - pose proof threeway_multisem_step_inv_program Hcase Hmerge Hstep' *)
  (*       as [s2 Hcontra]. *)
  (*     specialize (Hstep t s2). contradiction. *)
  (*   - (* Symmetric case. *) *)
  (*     apply negb_false_iff in Hcase. *)
  (*     pose proof mergeable_states_context_to_program Hmerge Hcase as Hcase'. *)
  (*     pose proof proj1 (mergeable_states_sym _ _ _ _ _ _) Hmerge as Hmerge'. *)
  (*     pose proof @threeway_multisem_step_inv_program c' p' c p as H. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H s1'' s1 t s2' Hcase' Hmerge'). *)
  (*     rewrite program_linkC in H; try assumption; [| apply linkable_sym; congruence]. *)
  (*     rewrite Hifacec Hifacep in H. *)
  (*     erewrite merge_states_sym with (p := c') (c := p') (p' := c) (c' := p) in H; *)
  (*       try eassumption; try now symmetry. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H Hstep'). *)
  (*     destruct H as [s2'' Hcontra]. *)
  (*     specialize (Hstep'' t s2''). *)
  (*     unfold sem'', prog'' in Hstep''; rewrite program_linkC in Hstep''; try assumption. *)
  (*     contradiction. *)
  (* Qed. *)
*)
End ThreewayMultisem5.

(* Main simulation theorem. *)
Section Recombination.
  Variables p c p' c' : program.
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


  (* RB: NOTE: Possible improvements:
      - Try to refactor case analysis in proof.
      - Try to derive well-formedness, etc., from semantics.
     This result is currently doing the legwork of going from a simulation on
     stars to one on program behaviors without direct mediation from the CompCert
     framework. *)
  (* Theorem recombination_prefix m : *)
  (*   does_prefix sem   m -> *)
  (*   does_prefix sem'' m -> *)
  (*   does_prefix sem'  m. *)
  (* Proof. *)
  (*   unfold does_prefix. *)
  (*   intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']]. *)
  (*   assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh''). *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]]. *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']]. *)
  (*   destruct m as [tm | tm | tm]. *)
  (*   - destruct b   as [t   | ? | ? | ?]; try contradiction. *)
  (*     destruct b'' as [t'' | ? | ? | ?]; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst. *)
  (*     inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst. *)
  (*     exists (Terminates tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_terminates with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     now apply match_final_states with (p' := p'). *)
  (*   - destruct b   as [? | ? | ? | t  ]; try contradiction. *)
  (*     destruct b'' as [? | ? | ? | t'']; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst. *)
  (*     inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst. *)
  (*     exists (Goes_wrong tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_goes_wrong with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     + eapply match_nostep; eassumption. *)
  (*     + eapply match_nofinal; eassumption. *)
  (*   - (* Here we talk about the stars associated to the behaviors, without *)
  (*        worrying now about connecting them to the existing initial states. *) *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix) *)
  (*       as [s1_ [s2 [Hini1_ Hstar12]]]. *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'') *)
  (*       as [s1''_ [s2'' [Hini1''_ Hstar12'']]]. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1_ Hini1''_ as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     eapply program_behaves_finpref_exists; *)
  (*       last now apply Hstar12'. *)
  (*     assumption. *)
  (* Qed. *)

  (* RB: NOTE: [DynShare] This definition may be used to expose a simpler
     relation, which would still fit the theorem statement, though one of the
     explicit connections would be lost. *)
  (* Definition prefix_rel m m' := *)
  (*   exists n n', behavior_rel_behavior_all_cids n n' m m'. *)
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
      exists (Terminates tm). split; last reflexivity.
      
    (* In the standard proof, because the two executions produce the same
       prefix, we know that the two runs either terminate, go wrong or are
       unfinished. The third case is probably the most interesting here. *)
    (***********************************************************
    destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix)
      as [s1_ [s2 [Hini1_ Hstar12]]].
    destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'')
      as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
     **********************************************************)

    (** TODO: Maybe get rid of the Hstar12 and Hstar12'' the way they are 
        produced above. *)
    (** And instead get them by inverting state_behaves (Will generate a side 
        condition that asserts, e.g., final_state) *)
    
    inversion Hst_beh as [ t ? Hstar12 Hfin
                         | t ? Hstar12
                         |
                         | t ? Hstar12];
      inversion Hst_beh'' as [ t'' ? Hstar12'' Hfin''
                             | t'' ? Hstar12''
                             |
                             | t'' ? Hstar12''];
      (*subst; destruct m; simpl in *; subst; destruct m''; simpl in *; subst;*)
      subst; simpl in *;
        clear Hst_beh Hst_beh'';
        
        try (
            apply star_iff_starR in Hstar12;
            apply star_iff_starR in Hstar12'';
            
            unfold CS.initial_state in *;
            
            induction t'' as [|? e''] using last_ind;
            subst;
            induction t as [|? e] using last_ind;
            subst;
            simpl in *
          ).
    - Search _ finpref_behavior.

      
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - 
    
    clear Hbeh Hbeh''.

    apply star_iff_starR in Hstar12.
    apply star_iff_starR in Hstar12''.
    
    unfold CS.initial_state in *.
    
    remember (finpref_trace m) as t.
    remember (finpref_trace m'') as t''.
    generalize dependent t. generalize dependent t''.

    intros ?.
    induction t'' as [|? e''] using last_ind; intros ? Hstar12''; subst.
    - intros ?; induction t as [|? e] using last_ind; intros ? Hstar12; subst.
      + destruct m; simpl in *; subst; destruct m''; simpl in *; try by inversion Hrel.
        * exists (FTerminates E0).
          exists (fun cid => if cid \in domm (prog_interface p)
                             then n cid else n'' cid).
          split; last (by repeat constructor).
          unfold does_prefix. exists (Terminates E0). split; last by simpl.
          apply program_runs with (s := (CS.initial_machine_state prog'));
            first by simpl.
          eapply state_terminates.
    - 
      assert (Hrewr: rcons t'' e'' = rcons t'' e'' ++ nil).
        by rewrite <- app_nil_r at 1.
      Search _ rcons cons.
      rewrite cat_rcons in Hrewr.
      rewrite Hrewr in Hstar12''.
      rewrite <- star_iff_starR in Hstar12''.
      apply star_middle1_inv in Hstar12''.
      Search _ star starR.
      
        
    intros ? ? Hstar12''.
    induction Hstar12''.
    - destruct m''; simpl in *.
      + intros ? ? Hstar12; induction Hstar12; subst.
        * destruct m; simpl in *; subst; try by inversion Hrel.
          exists (FTerminates E0).
          exists (fun cid => if cid \in domm (prog_interface p)
                             then n cid else n'' cid).
          constructor; last (by constructor; constructor; constructor).
          unfold does_prefix.
          (** Invert Hst_beh, and get a contradiction to Hprefix *)
          inversion Hst_beh as [? ? Hstar Hfin | | |]; subst; try by exfalso.
          exists (Terminates E0).
          apply mergeable_border_mergeable_internal in Hmerge1.
          split; last by simpl.
          eapply program_runs; first constructor.
          (** Need a lemma that assumes Hstar, Hfin, Hmergewf1, Hbeh, and Hbeh'' *)
          (** The lemma will use mergeable_internal_states_final_state_prog      *)
          (** and mergeable_internal_states_final_state_prog'', and will apply   *)
          (** the constructor state_terminates.                                  *)
          (** The proof of this lemma will proceed by induction on Hstar.        *)

          (*****************************************
          find_and_invert_mergeable_internal_states.
               ** 
                eapply state_terminates; first eapply star_refl.
                ** eapply mergeable_internal_states_final_state_prog; eauto.
                   
                ** eapply mergeable_internal_states_final_state_prog''; eauto.
                *******************************************)
          admit.
        * 


               
(*FIXME
    pose proof match_initial_states (*n n''*) Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
         Hprog_is_closed Hprog_is_closed' Hprog_is_good Hprog''_is_good Hini1_ Hini1''_
      as [s1'_ [Hini1' Hmerge1_]].
    (* By determinacy of initial program states: *)
    assert (Heq1 : s1 = s1_) by admit.
    assert (Heq1' : s1' = s1'_) by admit.
    assert (Heq1'' : s1'' = s1''_) by admit.
    subst s1_ s1'_ s1''_.
    clear Hini1_ Hini1''_ Hmerge1_.
*)


    (* Now we should be able to apply a modified star simulation. *)

    (* AEK: TODO: Uncomment after having defined Hmerge1. See the TODO above. *)
    (************
    pose proof star_simulation Hmerge1 Hstar12 Hstar12''
      as [t' [s2' [Hstar12' Hmerge2]]].
    {
      (* For this, however, we need to be able to establish the memory
         relation between the two, in principle starting from [Hmerge1] and
         [Hrel]. *)
      (* NOTE: The memory relation is designed to hold at the boundaries!
         vs. higher-level memory relation *)
      admit.
    }
`   *************)



    (* AEK: TODO: Uncomment after having defined t'. See the TODO above. *)
    (*************
    (* Actually, we need to ensure that the executed trace corresponds to a
       finite prefix behavior (and that the obtained relation extends to
       it.) *)
    assert (exists m', t' = finpref_trace m') as [m' Heq] by admit; subst.


    (* Now we can instantiate the quantifiers (assume the mapping [n'] can be
       obtained easily). *)
    exists m'. eexists. split.
    - (* In principle, the same lemma that was used for the third case of the
         original proof should work here. *)
      pose proof program_behaves_finpref_exists Hini1' Hstar12'
             as [beh' [Hbeh' Hprefix']].
      exists beh'. admit.
    - (* We would then be left to establish the trace relation. *)
      admit.
     *********)



  Admitted.

End Recombination.

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


   (*[DynShare]

     This lemma should intuitively continue to hold (under some weaker
     definition of mergeable_states).

     The current proof that is commented below relies on "to_partial_memory_epsilon_star",
     the lemma that does not hold any more in the [DynShare] world.

     We should be able to find a weaker version of "to_partial_memory_epsilon_star"
     that will help us complete the proof of this lemma.

    *)

    (*;
        try (pose proof to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' Hstep23'' as Hmem23'';
             simpl in Hmem23''; rewrite Hmem23'');
        reflexivity.
  Qed.
     *)

  (* RB: NOTE: By itself, this lemma no longer says anything interesting, in
     fact it is trivial because [s1'] and [s1''] are not really related. To add
     significance to it, one may consider adding the mergeability relation, but
     then we need to know what [s1] is doing. *)
  Lemma context_epsilon_star_merge_states s1 s1' s1'' s2'' t t' t'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s1 s2' s2'' t t' t''.
  Admitted. (* RB: TODO: Currently not useful, maybe with tweaks later? *)
  (* Proof. *)
  (*   intros Hmerge1 Hcomp1 Hstar12''. *)
  (*   remember E0 as t12'' eqn:Ht12''. *)
  (*   revert s1 s1' Hmerge1 Hcomp1 Ht12''. *)
  (*   induction Hstar12''; intros; subst. *)
  (*   - exists s1'. now apply star_refl. *)
  (*   - (* Fix some names quickly for now... *) *)
  (*     rename s1 into s1''. rename s2 into s2''. rename s3 into s3''. rename s0 into s1. *)
  (*     (* Back to the proof. *) *)
  (*     apply Eapp_E0_inv in Ht12'' as [? ?]; subst. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s1 s1' s2''). *)
  (*     { *)
  (*       eapply merge_states_silent_star; try eassumption. *)
  (*       eapply star_step; [eassumption | eapply star_refl | reflexivity]. *)
  (*     } *)
  (*     exact (IHHstar12'' _ _ Hmerge2 Hcomp1 eq_refl). *)
  (* Qed. *)

  (* RB: NOTE: This lemma no longer holds as currently stated: even if [p]
     steps silently (no calls and returns), it can perform memory-altering
     operations that will not be reflected in [s1']. It can be repaired by
     adding a matching [Step] on [sem']. *)
  Lemma threeway_multisem_mergeable_step_E0 s1 s2 s1' s1'' t t' t'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    Step sem s1 E0 s2 ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s1'' t t' t''.
  Abort. (* RB: TODO: Check repair, uses. Should be provable, but see
            [threeway_multisem_step_E0]. *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12. *)
  (*   inversion Hmerge1 *)
  (*     as [s0 s0' s0'' t t' t'' n n' n'' Hwfp Hwfc Hwfp' Hwfc' *)
  (*         Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed' *)
  (*         Hini Hini' Hini'' Hstar01 Hstar01' Hstar01'' Hrel' Hrel'']. *)
  (*   apply mergeable_states_intro with s0 s0' s0'' t t' t'' n n' n''; *)
  (*     try assumption. *)
  (*   eapply (star_right _ _ Hstar01 Hstep12); try eassumption. now rewrite E0_right. *)
  (* Qed. *)

  (* RB: NOTE: The structure follows closely that of
     threeway_multisem_star_program. *)
  (* RB: NOTE: Expect the proof to hold, but the statement is in all likelihood
     not sufficiently informative, as the sequence of steps taken by [s1'] will
     be hidden by the existential. *)

  (* AEK: This lemma is probably redundant.  *)
  (*Lemma threeway_multisem_mergeable_program
        s1 s1' s1'' t1 t1' t1'' t2 t2'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t2   s2   ->
    Star sem'' s1'' t2'' s2'' ->
    behavior_rel_behavior_all_cids n n'' (FTbc t2) (FTbc t2'') ->
    (*mem_rel2 n n'' (CS.state_mem s1, t2) (CS.state_mem s1'', t2'') p -> *)
  exists s2' t2',
    mergeable_internal_states p c p' c' n n'' s2 s2' s2''
                     (t1 ++ t2) (t1' ++ t2') (t1'' ++ t2'').
  Admitted.*) (* RB: TODO: Wait to see how this will be useful. *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstar12 Hstar12'' Hrel''. *)
  (*   inversion Hmerge1 *)
  (*     as [s0 s0' s0'' t1 t1' t1'' ? n' ? Hwfp Hwfc Hwfp' Hwfc' *)
  (*         Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed' *)
  (*         Hini Hini' Hini'' Hstar01 Hstar01' Hstar01'' Hrel Hrel']. *)
  (*   (* Assume that we can not only execute the star in the recombined context, *)
  (*      but also establish the trace relation, here on partial traces. *) *)
  (*   assert (exists t2' s2', *)
  (*              Star sem' s1' t2' s2' /\ *)
  (*              behavior_rel_behavior_all_cids n n' (FTbc t2) (FTbc t2')) *)
  (*     as [t2' [s2' [Hstar12' Hrel2']]] *)
  (*     by admit. *)
  (*   (* If we do so, we can begin to reconstruct the mergeability relation... *) *)
  (*   exists s2'. *)
  (*   eapply mergeable_states_intro; try assumption. *)
  (*   eassumption. eassumption. eassumption. *)
  (*   (* The various stars compose easily (and in the way the old proof was *)
  (*      written). *) *)
  (*   instantiate (1 := t1 ++ t2). eapply star_trans; try eassumption; reflexivity. *)
  (*   instantiate (1 := t1' ++ t2'). eapply star_trans; try eassumption; reflexivity. *)
  (*   instantiate (1 := t1'' ++ t2''). eapply star_trans; try eassumption; reflexivity. *)
  (*   (* And it should be possible to compose the relations, possibly using some *)
  (*      of the stars. *) *)
  (*   instantiate (1 := n'). instantiate (1 := n). admit. *)
  (*   instantiate (1 := n''). admit. *)
  (* (* Qed. *) *)

  (* Ltac t_threeway_multisem_step_E0 := *)
  (*   CS.step_of_executing; *)
  (*   try eassumption; try reflexivity; *)
  (*   (* Solve side goals for CS step. *) *)
  (*   match goal with *)
  (*   | |- Memory.load _ _ = _ => *)
  (*     eapply program_load_to_partialized_memory; *)
  (*     try eassumption; [now rewrite Pointer.inc_preserves_component] *)
  (*   | |- Memory.store _ _ _ = _ => *)
  (*     eapply program_store_to_partialized_memory; eassumption *)
  (*   | |- find_label_in_component _ _ _ = _ => *)
  (*     eapply find_label_in_component_recombination; eassumption *)
  (*   | |- find_label_in_procedure _ _ _ = _ => *)
  (*     eapply find_label_in_procedure_recombination; eassumption *)
  (*   | |- Memory.alloc _ _ _ = _ => *)
  (*     eapply program_alloc_to_partialized_memory; eassumption *)
  (*   | _ => idtac *)
  (*   end; *)
  (*   (* Apply linking invariance and solve side goals. *) *)
  (*   eapply execution_invariant_to_linking; try eassumption; *)
  (*   [ congruence *)
  (*   | apply linkable_implies_linkable_mains; congruence *)
  (*   | apply linkable_implies_linkable_mains; congruence *)
  (*   | eapply is_program_component_in_domm; eassumption *)
  (*   ]. *)

  (* Ltac solve_executing_threeway_multisem_step_E0 Hlinkable pc1 := *)
  (*   eapply execution_invariant_to_linking with (c1 := c); eauto; *)
  (*   match goal with *)
  (*   | Hcc' : prog_interface c = _ |- _ => *)
  (*     match goal with *)
  (*       Hcomp1 : is_true (CS.is_program_component (?gps2, ?mem2, ?regs2, pc1, ?addrs2) _) *)
  (*       |- _ => *)
  (*       match goal with *)
  (*       | |- linkable _ _ => rewrite Hcc' in Hlinkable; exact Hlinkable *)
  (*       | |- linkable_mains p c => eapply linkable_implies_linkable_mains; eauto *)
  (*       | |- linkable_mains p c' => eapply linkable_implies_linkable_mains; eauto; *)
  (*                                   rewrite Hcc' in Hlinkable; exact Hlinkable *)
  (*       | |- _ => *)
  (*         eapply is_program_component_pc_in_domm *)
  (*           with (s := (gps2, mem2, regs2, pc1, addrs2)) *)
  (*                (c := c); eauto *)
  (*       end *)
  (*     end *)
  (*   end. *)

  (* RB: NOTE: Another trivial lemma that needs to add the mergeability relation
     to make up for the information lost by removing the computable state
     merging functions and hiding the third execution in the relation. *)
  Theorem threeway_multisem_step_E0 s1 s1' s1'' t1 t1' t1'' s2 :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Step sem  s1  E0 s2  ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s1'' t1 t1' t1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstep12.
    (* NOTE: Keep the context light for now, rewrite lemmas are no longer
       directly applicable, as [s2'] is not computed explicitly. *)
    (* inversion Hmerge1 as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hmergeable_ifaces _ _ _ _ _ _ _ _ _ _ _ _]. *)
    (* Derive some useful facts and begin to expose state structure. *)
    (* inversion Hmergeable_ifaces as [Hlinkable _]. *)
    (* rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)
    pose proof CS.silent_step_non_inform_preserves_program_component
         _ _ _ _ Hcomp1 Hstep12 as Hcomp2.
    (* pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12 *)
      (* as Hmerge2. *)
    (* rewrite (mergeable_states_merge_program Hcomp2 Hmerge2). *)
    (* NOTE: As usual, we should proceed by cases on the step. *)
    simpl in Hstep12.
    inversion Hstep12 as [? t ? ? Hstep12' DUMMY Ht DUMMY'];
      subst; rename Hstep12 into Hstep12_.
    inversion Hstep12'; subst; rename Hstep12' into Hstep12'_.

    - (* INop *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; eauto. exact (CS.Nop _ _ _ _ _ Hex'). (* Make more implicit later. *)
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; eauto. by eapply CS.Nop.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.
  
    - (* ILabel *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; eauto. exact (CS.Label _ _ _ _ _ _ Hex'). (* Make more implicit later. *)
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; eauto. eapply CS.Label; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IConst *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Const.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Const; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- inversion Hregsp as [Hregs]. simpl in *. constructor. intros reg.
             unfold Register.set, Register.get in *.
             destruct (Register.to_nat reg == Register.to_nat r) eqn:Hreg;
               rewrite setmE Hreg; specialize (Hregs reg).
             ++ rewrite setmE Hreg.
                assert (well_formed_program prog) as Hwf.
                  by eapply linking_well_formedness; eauto;
                    unfold mergeable_interfaces in *; intuition.
                  match goal with
                  | Hexec: executing (prepare_global_env prog) _ _ |- _ =>
                    specialize (CS.IConst_possible_values
                                  _
                                  Hwf Hclosed_prog pc v r Hexec)
                      as Hv
                  end.
                  destruct Hv as [[i Hvi] |
                                  [perm [cid [bid [off [procs
                                                          [Hvptr [Hcid [_ _]
                                             ]]]]]]]].
                ** left. by subst.
                ** subst. simpl.
                   destruct (perm =? Permission.data) eqn:eperm; auto.
                   unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr.
                   simpl.
                   assert (Pointer.component pc \in domm (prog_interface p))
                     as Hpc_p.
                   {
                       by specialize
                            (is_program_component_pc_in_domm Hcomp1 Hmerge1).
                   }
                   rewrite Hpc_p.
                   destruct (sigma_shifting_lefttoright_option
                               (n (Pointer.component pc))
                               (n (Pointer.component pc)) bid) eqn:ebid.
                   --- by
                         left;
                         apply
                           sigma_shifting_lefttoright_option_n_n_id in ebid;
                         subst.
                   --- right. split; auto; split; auto.
                       (**************************************************
                       split; intros ? Ha; rewrite in_fset1 in Ha;
                         specialize (eqP Ha) as rewr; subst; clear Ha;
                           intros contra.
                       +++
                         inversion Hgood_t as [? Hcontra]; subst.
                         specialize (Hcontra _ contra).
                         unfold left_addr_good_for_shifting in *.
                         erewrite sigma_lefttoright_Some_spec in Hcontra.
                         destruct Hcontra as [? G].
                         by erewrite ebid in G.
                       +++
                         inversion Hgood_t' as [? Hcontra]; subst.
                         specialize (Hcontra _ contra).
                         unfold left_addr_good_for_shifting in *.

                         rewrite Hpc_p in Hcontra.
                         erewrite sigma_lefttoright_Some_spec in Hcontra.
                         destruct Hcontra as [? G].
                         by erewrite ebid in G.
                        ******************************************************)

             ++ rewrite setmE Hreg. assumption.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IMov *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Mov.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Mov; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (* regs_rel_of_executing_part *)
            constructor.
            match goal with
            | H: regs_rel_of_executing_part _ _ _ _  |- _ => inversion H as [Hreg] end.
            intros reg.
            pose proof (Hreg r1)
              as [Hget_shift | [Hshift_r1_None Heq1]];
              pose proof (Hreg reg)
              as [Hreg_shift | [Hshift_reg_None Heq2]];
              destruct ((Register.to_nat reg == Register.to_nat r2)) eqn:Hreg_r; simpl;
                unfold Register.set, Register.get; rewrite !setmE Hreg_r.
            ++ left. by simpl in *.
            ++ left. eauto.
            ++ left. by simpl in *.
            ++ right. split; eauto.
            ++ right. split.
               ** by simpl in *.
               ** by simpl in *.
            ++ left. eauto.
            ++ right. split; eauto.
            ++ right. split; eauto.

      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBinOp *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_p.
        {
            by specialize (is_program_component_pc_in_domm Hcomp1 Hmerge1).
        }

        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.BinOp.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.BinOp; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (* regs_rel_of_executing_part *)
            constructor.
            match goal with
            | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
              inversion H as [Hreg] end.
            intros reg. simpl in *.
            destruct ((Register.to_nat reg == Register.to_nat r3)) eqn:Hreg_r; simpl.
            ++ unfold Register.set, Register.get in *. rewrite !setmE Hreg_r.
               unfold result, shift_value_option, rename_value_option,
               rename_value_template_option, sigma_shifting_wrap_bid_in_addr,
               rename_addr_option in *.

               pose proof (Hreg r1) as rel_r1.
               pose proof (Hreg r2) as rel_r2.
               pose proof (Hreg r3) as rel_r3.

               destruct op; simpl.
               **
                 (* Add *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq2 rel_r1_eq'
                                               (*[rel_r1_shr_t1 rel_r1_shr_t1']*)
                                       ]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq2 rel_r2_eq'
                                              (*[rel_r2_shr_t1 rel_r2_shr_t1']*)
                                       ]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.add;
                    (* 15 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          );
                    (* 9 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          ).

                 (* 8 subgoals *)
                  --- destruct (perm2 =? Permission.data) eqn:eperm2.
                      +++ 
                        destruct (sigma_shifting_lefttoright_option
                                    (n cid2)
                                    (if cid2 \in domm (prog_interface p)
                                     then n cid2 else n'' cid2)
                                    bid2) as [bid2_shift|] eqn:ebid2_shift;
                          rewrite ebid2_shift in Hrel_r2_eq; try discriminate;
                            rewrite ebid2_shift.
                        inversion Hrel_r2_eq; subst. by left.
                      +++ 
                        inversion Hrel_r2_eq; subst. by left.
                  --- destruct (perm2 =? Permission.data) eqn:eperm2;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid2)
                                  (if cid2 \in domm (prog_interface p)
                                   then n cid2 else n'' cid2)
                                  bid2) as [bid2_shift|] eqn:ebid2_shift;
                        rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                      rewrite ebid2_shift.
                      inversion rel_r2_eq'; subst.
                      rewrite eperm2 in rel_r2_eq2. simpl in *.
                      destruct (sigma_shifting_lefttoright_option
                                  (if cid2' \in domm (prog_interface p)
                                   then n cid2'
                                   else n'' cid2') (n cid2') bid2') eqn:esigma2';
                        rewrite esigma2' in rel_r2_eq2; try discriminate.
                      rewrite eperm2 esigma2'. 
                      right. by intuition.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1.
                      +++
                        destruct (sigma_shifting_lefttoright_option
                                    (n cid1)
                                    (if cid1 \in domm (prog_interface p)
                                     then n cid1 else n'' cid1)
                                    bid1) as [bid1_shift|] eqn:ebid1_shift;
                          rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                        rewrite ebid1_shift.
                        inversion Hrel_r1_eq. subst. by left.
                      +++
                        inversion Hrel_r1_eq. subst. by left.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                      rewrite ebid1_shift. inversion rel_r1_eq'. subst.
                      inversion Hrel_r1_eq.
                      rewrite eperm1 in rel_r1_eq2. simpl in *.
                      destruct (sigma_shifting_lefttoright_option
                                  (if cid1' \in domm (prog_interface p)
                                   then n cid1'
                                   else n'' cid1') (n cid1') bid1') eqn:esigma1';
                        rewrite esigma1' in rel_r1_eq2; try discriminate.
                      rewrite eperm1 esigma1'.
                      right; by intuition.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.


               **
                 (* Minus *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq2 rel_r1_eq'
                                               (*[rel_r1_shr_t1 rel_r1_shr_t1']*)
                                       ]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq2 rel_r2_eq'
                                              (*[rel_r2_shr_t1 rel_r2_shr_t1']*)
                                       ]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.sub;
                    (* 31 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 13 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).

                 (* 10 subgoals *)
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.

                 --- destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       rewrite ebid1_shift.
                       inversion Hrel_r1_eq. subst. by left.
                     +++
                       inversion Hrel_r1_eq. subst. by left.
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                           
                 --- destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                     assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2) bid2)
                       as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                     inversion rel_r2_eq'. subst.
                     destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid1)
                                     (if cid1 \in domm (prog_interface p)
                                      then n cid1 else n'' cid1) bid1)
                         as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                         inversion Hrel_r1_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid12.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                         ----
                           assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                         ----
                           simpl in *. rewrite ebid2_shift.
                           destruct (bid1' =? bid2') eqn:ebid1'2'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (by simpl);
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               - eapply interface_preserves_closedness_r; eauto.
                                 + by unfold mergeable_interfaces in *; intuition.
                                 + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                                 + apply interface_implies_matching_mains; auto.
                               - eapply linking_well_formedness; eauto.
                                 unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                             rewrite G in ebid2_shift.
                             rewrite G in ebid1_shift.
                             apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid1_shift.
                             by rewrite sigma_shifting_righttoleft_lefttoright
                               ebid2_shift in ebid1_shift.
                             -----
                               inversion Hgood_t' as [? Hcontra]; subst.
                             specialize (Hcontra _ Hshr) as contra.
                             unfold left_addr_good_for_shifting in *.
                             erewrite sigma_lefttoright_Some_spec in contra.
                             (* TODO: The following destruct fails in some
                                still-supported Coq versions, e.g. 8.9. Fix
                                later or adjust dependencies. *)
                             destruct contra as [? G].
                               by erewrite G in rel_r2_eq2.
                               (********************************
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                               pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               ***************************************)
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r1_eq. subst.
                       rewrite eperm1 !andFb. by left.

                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1)
                                 bid1) as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     rewrite ebid1_shift. inversion rel_r1_eq'. subst.
                     rewrite eperm2 in rel_r1_eq2. simpl in *.
                     destruct (
                         sigma_shifting_lefttoright_option
                           (if cid1' \in domm (prog_interface p)
                            then n cid1'
                            else n'' cid1') (n cid1') bid1'
                       ) eqn:esigma1'; rewrite esigma1' in rel_r1_eq2;
                       try discriminate.
                     rewrite eperm2 esigma1'.
                     by right; intuition.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (by simpl);
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               - eapply interface_preserves_closedness_r; eauto.
                                 + by unfold mergeable_interfaces in *; intuition.
                                 + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                                 + apply interface_implies_matching_mains; auto.
                               - eapply linking_well_formedness; eauto.
                                 unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                             rewrite G in ebid1_shift.
                             rewrite G in ebid2_shift.
                             apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid2_shift.
                             by rewrite sigma_shifting_righttoleft_lefttoright
                               ebid1_shift in ebid2_shift.
                             -----
                               inversion Hgood_t' as [? Hcontra]; subst.
                             specialize (Hcontra _ Hshr) as contra.
                             unfold left_addr_good_for_shifting in *.
                             erewrite sigma_lefttoright_Some_spec in contra.
                             destruct contra as [? G].
                               by erewrite G in rel_r1_eq2.
                               (************************************
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               ***************************************)
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       assert (Permission.data = perm2'). by apply beq_nat_true.
                       by subst.

                 --- inversion rel_r1_eq'. subst.
                     inversion rel_r2_eq'. subst.

                     by destruct ((perm1' =? perm2') &&
                                  (cid1' =? cid2') &&
                                  (bid1' =? bid2')); auto.

               **
                 (* Mul *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq2 rel_r1_eq'
                                               (*[rel_r1_shr_t1 rel_r1_shr_t1']*)
                                       ]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq2 rel_r2_eq'
                                                       (*[rel_r2_shr_t1 rel_r2_shr_t1']*)
                                       ]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left).

                 (* 3 subgoals *)
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.

                 --- destruct (perm1 =? Permission.data) eqn:eperm1;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1)
                                 bid1) as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.

                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.




               **
                 (* Eq *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq2 rel_r1_eq'
                                                        (*[rel_r1_shr_t1 rel_r1_shr_t1']*)
                                       ]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq2 rel_r2_eq'
                                                       (*[rel_r2_shr_t1 rel_r2_shr_t1']*)
                                       ]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.eq;
                    (* 27 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 11 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).

                 (* 8 subgoals *)
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                   assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                   
                   destruct (sigma_shifting_lefttoright_option
                               (n cid2)
                               (if cid2 \in domm (prog_interface p)
                                then n cid2 else n'' cid2) bid2)
                     as [bid2_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                   inversion rel_r2_eq'. subst.
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                   +++
                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion Hrel_r1_eq. subst.
                     rewrite andTb.
                     destruct (cid1' =? cid2') eqn:ecid12.
                     ***
                       assert (cid1' = cid2'). by apply beq_nat_true. subst.
                       rewrite andTb.
                       destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                       ----
                         assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                       ----
                         simpl in *. rewrite ebid2_shift.
                         destruct (bid1' =? bid2') eqn:ebid1'2'.
                         ****
                           assert (bid1' = bid2'). by apply beq_nat_true. subst.
                           assert (CSInvariants.wf_ptr_wrt_cid_t
                                     (Pointer.component pc)
                                     t1'
                                     (Permission.data, cid2', bid2', off2'))
                             as Hwf.
                           {
                             eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                               last (by simpl);
                               last (unfold Register.get;
                                       by erewrite eregs1'r2).
                             eapply CSInvariants.wf_state_wf_reg
                               with (s := (gps1', mem1', regs1', pc)); eauto.
                             eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                             - eapply interface_preserves_closedness_r; eauto.
                               + by unfold mergeable_interfaces in *; intuition.
                               + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                               + apply interface_implies_matching_mains; auto.
                             - eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                           }
                           inversion Hwf as [| ? ? ? ? Hshr]; subst.
                           -----
                             assert (Pointer.component pc \in domm
                                                                (prog_interface p))
                             as G. by eapply mergeable_states_program_component_domm;
                                     eauto.
                           rewrite G in ebid2_shift.
                           rewrite G in ebid1_shift.
                           apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid1_shift.
                             by rewrite sigma_shifting_righttoleft_lefttoright
                               ebid2_shift in ebid1_shift.
                             
                             -----
                               inversion Hgood_t' as [? Hcontra]; subst.
                             specialize (Hcontra _ Hshr) as contra.
                             unfold left_addr_good_for_shifting in *.
                             erewrite sigma_lefttoright_Some_spec in contra.
                             destruct contra as [? G].
                               by erewrite G in rel_r2_eq2.
                               (**********************************
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                               pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               ************************************)
                         ****
                             by left.
                     *** rewrite !andFb. by left.
                   +++
                     inversion Hrel_r1_eq. subst.
                     rewrite eperm1 !andFb. by left.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (by simpl);
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               - eapply interface_preserves_closedness_r; eauto.
                                 + by unfold mergeable_interfaces in *; intuition.
                                 + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                                 + apply interface_implies_matching_mains; auto.
                               - eapply linking_well_formedness; eauto.
                                 unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                             rewrite G in ebid2_shift.
                             rewrite G in ebid1_shift.
                             apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid2_shift.
                               by rewrite sigma_shifting_righttoleft_lefttoright
                                          ebid1_shift in ebid2_shift.
                           
                             -----
                               inversion Hgood_t' as [? Hcontra]; subst.
                             specialize (Hcontra _ Hshr) as contra.
                             unfold left_addr_good_for_shifting in *.
                             erewrite sigma_lefttoright_Some_spec in contra.
                             destruct contra as [? G].
                               by erewrite G in rel_r1_eq2.
                               (**********************************
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               ***********************************)
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       
                 ---
                   inversion rel_r1_eq'. inversion rel_r2_eq'. subst. by left. 

                 
               ** 
                 (* Leq *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq2 rel_r1_eq'
                                                        (*[rel_r1_shr_t1 rel_r1_shr_t1']*)
                                       ]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq2 rel_r2_eq'
                                                       (*[rel_r2_shr_t1 rel_r2_shr_t1']*)
                                       ]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.leq;
                    (* 27 subgoals *)
                    
                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 11 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).


                 (* 8 subgoals *)
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                   assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                   
                   destruct (sigma_shifting_lefttoright_option
                               (n cid2)
                               (if cid2 \in domm (prog_interface p)
                                then n cid2 else n'' cid2) bid2)
                     as [bid2_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                   inversion rel_r2_eq'. subst.
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                   +++
                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion Hrel_r1_eq. subst.
                     rewrite andTb.
                     destruct (cid1' =? cid2') eqn:ecid12.
                     ***
                       assert (cid1' = cid2'). by apply beq_nat_true. subst.
                       rewrite andTb.
                       destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                       ----
                         assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                       ----
                         simpl in *. rewrite ebid2_shift.
                         destruct (bid1' =? bid2') eqn:ebid1'2'.
                         ****
                           assert (bid1' = bid2'). by apply beq_nat_true. subst.
                           assert (CSInvariants.wf_ptr_wrt_cid_t
                                     (Pointer.component pc)
                                     t1'
                                     (Permission.data, cid2', bid2', off2'))
                             as Hwf.
                           {
                             eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                               last (by simpl);
                               last (unfold Register.get;
                                       by erewrite eregs1'r2).
                             eapply CSInvariants.wf_state_wf_reg
                               with (s := (gps1', mem1', regs1', pc)); eauto.
                             eapply CSInvariants.is_prefix_wf_state_t;
                               last exact Hpref_t'.
                             - eapply interface_preserves_closedness_r; eauto.
                               + by unfold mergeable_interfaces in *; intuition.
                               + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                               + apply interface_implies_matching_mains; auto.
                             - eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                           }
                           inversion Hwf as [| ? ? ? ? Hshr]; subst.
                           -----
                             assert (Pointer.component pc \in domm
                                                                (prog_interface p))
                             as G. by eapply mergeable_states_program_component_domm;
                                     eauto.
                             rewrite G in ebid2_shift.
                             rewrite G in ebid1_shift.
                             apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid1_shift.
                               by rewrite sigma_shifting_righttoleft_lefttoright
                                          ebid2_shift in ebid1_shift.
                           
                               -----
                                 inversion Hgood_t' as [? Hcontra]; subst.
                               specialize (Hcontra _ Hshr) as contra.
                               unfold left_addr_good_for_shifting in *.
                               erewrite sigma_lefttoright_Some_spec in contra.
                               destruct contra as [? G].
                                 by erewrite G in rel_r2_eq2.
                               (**********************************
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                             pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                             rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               **************************************)
                         ****
                             by left.
                     *** rewrite !andFb. by left.
                   +++
                     inversion Hrel_r1_eq. subst.
                     rewrite eperm1 !andFb. by left.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (by simpl);
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               - eapply interface_preserves_closedness_r; eauto.
                                 + by unfold mergeable_interfaces in *; intuition.
                                 + eapply linkable_implies_linkable_mains; eauto.
                                   by unfold mergeable_interfaces in *; intuition.
                                 + apply interface_implies_matching_mains; auto.
                               - eapply linking_well_formedness; eauto.
                                 unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                               rewrite G in ebid2_shift.
                               rewrite G in ebid1_shift.
                               apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in ebid2_shift.
                             by rewrite sigma_shifting_righttoleft_lefttoright
                                        ebid1_shift in ebid2_shift.
                           
                             -----
                               inversion Hgood_t' as [? Hcontra]; subst.
                             specialize (Hcontra _ Hshr) as contra.
                             unfold left_addr_good_for_shifting in *.
                             erewrite sigma_lefttoright_Some_spec in contra.
                             destruct contra as [? G].
                               by erewrite G in rel_r1_eq2.
                               (**********************************
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                               ***********************************)
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       assert (Permission.data = perm2'). by apply beq_nat_true.
                       by subst.

                 ---
                   inversion rel_r1_eq'. inversion rel_r2_eq'. subst. left. 
                     by destruct ((perm1' =? perm2') &&
                                  (cid1' =? cid2') &&
                                  (bid1' =? bid2')).


                     
            ++ unfold Register.set, Register.get in *.
               rewrite !setmE Hreg_r.
               pose proof (Hreg reg)
                 as [Hget_shift_reg | [HNone Heq]].
              ** left. assumption. 
              ** right. split; eauto.

      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
            by rewrite H_c' in Hcomp1.
    - (* IPtrOfLabel *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1',
                      Register.set r (Ptr ptr) regs1',
                      (Pointer.inc pc)
                     )
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.PtrOfLabel.
          -- exact Hex'.
          -- unfold sem', prog'.
             eapply find_label_in_component_mergeable_internal_states; auto.
             ++ exact H_p.
             ++ exact Hmerge1.
             ++ reflexivity.
             ++ eassumption.
          -- reflexivity.
          -- reflexivity.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem, Register.set r (Ptr ptr) regs, Pointer.inc pc)
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', Register.set r (Ptr ptr) regs1', Pointer.inc pc)
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl. symmetry.
             by rewrite Pointer.inc_preserves_component.
        * by simpl.
        * simpl. constructor. intros ?.
          inversion Hregsp as [Hregs]. specialize (Hregs reg).
          unfold Register.get, Register.set in *. simpl in Hregs. rewrite !setmE.
          destruct (Register.to_nat reg == Register.to_nat r) eqn:ereg;
            rewrite ereg; try assumption.
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.
          destruct ptr as [[[perm cid] bid] ?]. simpl in *.
          assert (perm = Permission.code).
          {
            unfold find_label_in_component in *.
            destruct (genv_procedures (prepare_global_env prog)
                                      (Pointer.component pc)); try discriminate.
            
            match goal with
            | H: find_label_in_component_helper _ _ _ _ = _ |- _ =>
              apply find_label_in_component_helper_guarantees in H as [? ?]
            end.
            simpl in *. subst.
            match goal with
            | H: executing _ pc _ |- _ =>
              destruct H as [? [? ?]]; by intuition
            end.
          }
          subst. by left.

      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.


    - (* ILoad *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)

        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_in.
        {
          by eapply mergeable_states_program_component_domm; eauto.
        }
            
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }


        (* ILoad-specific *)

        match goal with
        | H: Memory.load _ _ = Some _ |- _ =>
          specialize (Memory.load_some_permission mem ptr _ H) as Hperml
        end.
        destruct ptr as [[[perml cidl] bidl] offl].
        simpl in Hperml. subst.
        
        assert (CSInvariants.wf_ptr_wrt_cid_t
                  (Pointer.component pc) t1
                  (Permission.data, cidl, bidl, offl)
               ) as cidl_bidl_invariant.
        {
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - reflexivity.
        }

        unfold mem_of_part_executing_rel_original_and_recombined,
        memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
        memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr
         in Hmemp.
        simpl in Hmemp.
        destruct Hmemp as [Hmem_own [Hmem_shared Hmem_next_block]].
        
        assert (
            (cidl, bidl).1 \in domm (prog_interface p) ->
                               (
                                 Memory.load mem1' (Permission.data,
                                                    cidl, bidl, offl) =
                                 match
                                   rename_value_option
                                     (rename_addr_option
                                        (sigma_shifting_wrap_bid_in_addr
                                           (sigma_shifting_lefttoright_addr_bid
                                              n
                                              (fun cid : nat =>
                                                 if cid \in domm (prog_interface p)
                                                 then n cid else n'' cid)))) v
                                 with
                                 | Some v' => Some v'
                                 | None => Some v
                                 end)
          ) as Hmem_own1.
        {
          intros Hcidl.
          specialize (Hmem_own _ Hcidl) as [Hspec _].
          
          match goal with | H: Memory.load _ _ = _ |- _ => 
                            specialize (Hspec _ _ H)
          end.
          destruct (
              rename_value_option
                (sigma_shifting_wrap_bid_in_addr
                   (sigma_shifting_lefttoright_addr_bid
                      n
                      (fun cid : nat =>
                         if cid \in domm (prog_interface p)
                         then n cid else n'' cid)))
                v
            ) eqn:eshiftv; rewrite eshiftv; rewrite eshiftv in Hspec; auto.
          intuition.
        }
        
                
        assert (CSInvariants.is_prefix
                  (gps,
                   mem,
                   Register.set
                     r2
                     v
                     regs,
                   Pointer.inc pc
                  )
                  prog
                    t1
               ) as Hprefix_t1_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }



        inversion Hregsp as [Hregs]. simpl in Hregs.
        specialize (Hregs r1) as Hregsr1.

        assert (exists ptr, Register.get r1 regs1' = Ptr ptr) as Hget_r1_ptr.
        {
          unfold shift_value_option, rename_value_option, rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.

          inversion Hregsr1 as [Hregs1'_r1 | [Hregs1'_r1 [Hregs1'_r1_2 Heq
                                                                       (*[Hnotshr1 Hnotshr2]*)
                               ]]].
          - match goal with
            | H: Register.get r1 regs = Ptr _ |- _ =>
              rewrite H in Hregs1'_r1
            end.
            simpl in *.
            destruct (sigma_shifting_lefttoright_option
                        (n cidl)
                        (if cidl \in domm (prog_interface p)
                         then n cidl else n'' cidl) bidl) eqn:eshift;
              rewrite eshift in Hregs1'_r1;
              try discriminate.
            inversion Hregs1'_r1.
              by eauto.
          - setoid_rewrite <- Heq.
            by eexists;
              match goal with
              | H: Register.get r1 regs = Ptr _ |- _ =>
                erewrite H
              end.
        }

        destruct Hget_r1_ptr as [ptr Hptr].

        match goal with
        | H: Register.get r1 regs = Ptr _ |- _ =>
          rewrite H in Hregsr1
        end.
        rewrite Hptr in Hregsr1.


        unfold shift_value_option, rename_value_option, rename_value_template_option,
        rename_addr_option, sigma_shifting_wrap_bid_in_addr,
        sigma_shifting_lefttoright_addr_bid in *. simpl in *.
        
        assert (
          exists v',
            Memory.load mem1' ptr = Some v'
          ) as [v' Hloadmem1'].
        {
          destruct (
              sigma_shifting_lefttoright_option
                (n cidl)
                (if cidl \in domm (prog_interface p) then n cidl else n'' cidl) bidl
            ) as [bidl_shift|] eqn:ebidl_shift; rewrite ebidl_shift in Hregsr1. 
          - inversion Hregsr1 as [G | [? _]]; try discriminate.
            inversion G. subst. clear G Hregsr1 Hregs.
            inversion cidl_bidl_invariant as [| ? ? ? ?  Hshr]; subst.
            + rewrite Hpc_in in ebidl_shift.
              apply sigma_shifting_lefttoright_option_n_n_id in ebidl_shift.
              rewrite Hpc_in in Hmem_own1.
              inversion ebidl_shift. subst.
              setoid_rewrite Hmem_own1; auto.
              destruct v as [|[[[perm cid] bid] ?]|].
              * eexists; eauto.
              * destruct (perm =? Permission.data).
                -- destruct (sigma_shifting_lefttoright_option
                               (n cid)
                               (if cid \in domm (prog_interface p)
                                then n cid else n'' cid) bid) eqn:rewr;
                     rewrite rewr; eexists; eauto.
                -- eexists; eauto.
              * eexists; eauto.
            + specialize (Hmem_shared _ Hshr) as Hmem_shared_cid_bid.
              setoid_rewrite ebidl_shift in Hmem_shared_cid_bid.
              destruct Hmem_shared_cid_bid as [addr' [addr'eq [addr'load _]]].
              inversion addr'eq. subst.
              match goal with
              | Hload: Memory.load mem _ = _ |- _ =>
                specialize (addr'load _ _ Hload) as [v' [G _]]
              end.
              eexists. eassumption.
          - inversion Hregsr1 as [| [contra1 [contra2 ptr_eq
                                              (*[Hnotshrt1 Hnotshrt1']*)]]];
              try discriminate.
            inversion ptr_eq. subst. simpl in *.
            clear Hregsr1 ptr_eq.
            inversion cidl_bidl_invariant as [| ? ? ? ?  Hshr]; subst.
            + destruct v as [| [[[perm cid] bid] off] |].
              * eexists. erewrite Hmem_own1; auto.
              * destruct (perm =? Permission.data) eqn:eperm; eauto.
                destruct (sigma_shifting_lefttoright_option
                            (n cid)
                            (if cid \in domm (prog_interface p)
                             then n cid else n'' cid) bid) eqn:esigma;
                  eexists; erewrite Hmem_own1; auto;
                    rewrite esigma; eauto.
              * eexists. erewrite Hmem_own1; auto.
            + inversion Hgood_t as [? Hcontra]; subst.
              specialize (Hcontra _ Hshr).
              unfold left_addr_good_for_shifting in *.
              erewrite sigma_lefttoright_Some_spec in Hcontra.
              destruct Hcontra as [? G].
              by erewrite G in ebidl_shift.
              (*************************
              specialize (Hnotshrt1 (cidl, bidl)). 
              rewrite in_fset1 eqxx in Hnotshrt1.
              exfalso. by apply Hnotshrt1.
              ****************************)
        }

        
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Load.
          -- exact Hex'.
          -- exact Hptr.
          -- exact Hloadmem1'. 
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Load; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (** regs_rel_of_executing_part *)
            simpl. constructor. intros reg.
            unfold Register.get, Register.set. rewrite setmE.
            destruct (Register.to_nat reg == Register.to_nat r2) eqn:ereg;
              rewrite ereg; rewrite setmE ereg.
            ++ unfold shift_value_option, rename_value_option,
               rename_value_template_option,
               rename_addr_option, sigma_shifting_wrap_bid_in_addr,
               sigma_shifting_lefttoright_addr_bid in *. simpl in *.
               destruct (
                   sigma_shifting_lefttoright_option
                     (n cidl)
                     (if cidl \in domm (prog_interface p)
                      then n cidl else n'' cidl) bidl
                 ) as [bidl_shift|] eqn:ebidl_shift;
               rewrite !ebidl_shift in Hregsr1.
               ** inversion Hregsr1 as [G | [? _]]; try discriminate.
                  inversion G. subst. clear G Hregsr1 Hregs.

                  (* Is this the right next step? *)
                  inversion cidl_bidl_invariant as [|? ? ? ? Hshr]; subst.
                  ---
                    rewrite Hpc_in in ebidl_shift.
                    apply sigma_shifting_lefttoright_option_n_n_id
                      in ebidl_shift.
                    subst.
                    rewrite <- Hloadmem1'.
                    rewrite Hmem_own1; auto.
                    (* left. *)
                    destruct v as [|[[[perm cid] b] o]|]; simpl; auto.
                    destruct (perm =? Permission.data) eqn:eperm; auto.
                    destruct (sigma_shifting_lefttoright_option
                                (n cid)
                                (if cid \in domm (prog_interface p)
                                 then n cid else n'' cid) b) eqn:esigma;
                      rewrite esigma; auto.
                    assert (perm = Permission.data). by apply beq_nat_true. subst.
                    assert (CSInvariants.wf_load
                              (Pointer.component pc)
                              t1
                              (Permission.data, Pointer.component pc, bidl, offl)
                              (Permission.data, cid, b, o)
                           ) as cid_b_invariant.
                    {
                      eapply CSInvariants.wf_mem_wrt_t_pc_wf_load; eauto.
                      eapply CSInvariants.wf_state_wf_mem
                        with (s := (gps, mem, regs, pc)); eauto.
                      eapply CSInvariants.is_prefix_wf_state_t
                        with (p := (program_link p c)); eauto.
                      eapply linking_well_formedness; eauto.
                      by unfold mergeable_interfaces in *; intuition.
                    }

                    inversion cid_b_invariant as [|? ? Hshr |]; simpl in *; subst; auto.
                    +++ specialize (Hmem_own1 Hpc_in).
                        rewrite Hloadmem1' in Hmem_own1.
                        rewrite esigma in Hmem_own1. inversion Hmem_own1.
                        simpl. rewrite Hpc_in in esigma. rewrite Hpc_in esigma.
                        by right.
                    +++ inversion Hgood_t as [? Hgood]; subst. apply Hgood in Hshr.
                        unfold left_addr_good_for_shifting in *.
                        eapply sigma_lefttoright_Some_spec in Hshr.
                        destruct Hshr as [? rewr].
                        by erewrite rewr in esigma.
                    +++ specialize (Hmem_own1 Hpc_in).
                        rewrite Hloadmem1' in Hmem_own1.
                        rewrite esigma in Hmem_own1. inversion Hmem_own1.
                        simpl. rewrite Hpc_in in esigma. rewrite Hpc_in esigma.
                        by right.

                  ---
                    destruct (Hmem_shared (cidl, bidl) Hshr)
                      as [? [Hcidlbidl [Hmem_shared1 _]]].
                    rewrite ebidl_shift in Hcidlbidl. inversion Hcidlbidl. subst.
                    simpl in *.
                    match goal with
                    | Hload: Memory.load mem _ = _ |- _ =>
                      specialize (Hmem_shared1 _ _ Hload) as [v'exists [v'eq G]]
                    end.
                    rewrite Hloadmem1' in v'eq.
                    inversion v'eq. subst. left. exact G.

               **                     
                 inversion cidl_bidl_invariant as [|? ? ? ? Hshr]; subst.
                 ---
                   destruct Hregsr1 as [| [none1 [none2 eptr
                                                        (*[Hnotshr Hnotshr']*)
                                       ]]];
                     try discriminate.
                   inversion eptr. subst. clear eptr.
                   rewrite Hloadmem1' in Hmem_own1.
                   specialize (Hmem_own1 Hpc_in).
                   rewrite Hmem_own1.
                   destruct v as [| [[[perm cid] bid] off]  |]; auto.
                   destruct (perm =? Permission.data) eqn:eperm; auto.
                   destruct (sigma_shifting_lefttoright_option
                               (n cid)
                               (if cid \in domm (prog_interface p)
                                then n cid else n'' cid) bid) eqn:esigma;
                     rewrite esigma; rewrite esigma in Hmem_own1; auto.
                   inversion Hmem_own1.
                   right; split; auto; split; auto.
                   simpl in *. rewrite eperm.
                   specialize (Hmem_own (_, bidl) Hpc_in) as [_ Hmem_own2].
                   specialize (Hmem_own2 _ _ Hloadmem1') as [? [Hload Hrel]].
                   simpl in *.
                   match goal with
                   | Hl: Memory.load mem _ = Some (Ptr _) |- _ =>
                     rewrite Hload in Hl; inversion Hl; subst
                   end.
                   rewrite eperm esigma in Hrel.
                   destruct (sigma_shifting_lefttoright_option
                               (if cid \in domm (prog_interface p)
                                then n cid else n'' cid)
                               (n cid)
                               bid
                            ) eqn:ebid; rewrite ebid; rewrite ebid in Hrel;
                     destruct Hrel as [[? [? ?]]|]; try discriminate; auto.
                   
                   
                 --- (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Hshr)
                       as cidbgood.*)
                   inversion Hgood_t as [? shared_good]. subst.
                   specialize (shared_good _ Hshr) as cidbgood.
                   
                   unfold left_addr_good_for_shifting in *.
                   erewrite sigma_lefttoright_Some_spec in cidbgood.
                   destruct cidbgood as [? contra].
                   by erewrite contra in ebidl_shift.
                     
            ++ by apply Hregs.

          -- (* mem_of_part_executing_rel_original_and_recombined *)
            by unfold mem_of_part_executing_rel_original_and_recombined; intuition.
            
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
            by rewrite H_c' in Hcomp1.

    - (* IStore *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)

        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_in.
        {
          by eapply mergeable_states_program_component_domm; eauto.
        }
            

        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }


        (* IStore-specific *)

        unfold mem_of_part_executing_rel_original_and_recombined,
        memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
        memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr
         in Hmemp.
        simpl in Hmemp.
        destruct Hmemp as [Hmem_own [Hmem_shared Hmem_next_block]].
        


        assert (CSInvariants.is_prefix
                  (gps,
                   mem',
                   regs,
                   Pointer.inc pc
                  )
                  prog
                    t1
               ) as Hprefix_t1_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }



        match goal with
        | H: Memory.store _ _ _ = Some _ |- _ =>
          specialize (Memory.store_some_permission mem ptr _ _ H) as Hperm_st
        end.
        destruct ptr as [[[perm_st cid_st] bid_st] off_st].
        simpl in Hperm_st. subst.


        inversion Hregsp as [Hregs]. simpl in Hregs.
        specialize (Hregs r1) as Hregs1'r1.
        match goal with
        | H: Register.get r1 regs = Ptr _ |- _ =>
          rewrite H in Hregs1'r1
        end.
        

        assert (exists ptr, Register.get r1 regs1' = Ptr ptr) as Hget_r1_ptr.
        {
          unfold shift_value_option, rename_value_option, rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.

          
          inversion Hregs1'r1 as [Hregs1'_r1 | [Hregs1'_r1 [Hregs1'_r1_2 Heq
                                                                         (*[Hnotshr1 Hnotshr2]*)
                                 ]]].
          - simpl in *.
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) eqn:eshift;
              rewrite eshift in Hregs1'_r1;
              try discriminate.
            inversion Hregs1'_r1.
              by eauto.
          - setoid_rewrite <- Heq.
            by eexists.
        }

        destruct Hget_r1_ptr as [ptr Hptr].


        
        
        assert (CSInvariants.wf_ptr_wrt_cid_t
                  (Pointer.component pc) t1
                  (Permission.data, cid_st, bid_st, off_st)
               ) as cidst_bidst_invariant.
        {
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - by apply Pointer.inc_preserves_component.
        }


        assert (forall cidv bidv offv,
                   Register.get r2 regs = Ptr (Permission.data, cidv, bidv, offv) ->
                   CSInvariants.wf_ptr_wrt_cid_t
                     (Pointer.component pc) t1
                     (Permission.data, cidv, bidv, offv)
               ) as get_r2_invariant.
        {
          intros ? ? ? Hget.
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - by apply Pointer.inc_preserves_component.
        }


        assert (forall cidv bidv offv,
                   Register.get r2 regs1' = Ptr (Permission.data, cidv, bidv, offv) ->
                   CSInvariants.wf_ptr_wrt_cid_t
                     (Pointer.component pc) t1'
                     (Permission.data, cidv, bidv, offv)
               ) as get_r2_invariant'.
        {
          intros ? ? ? Hget.
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog'); eauto.
            + eapply interface_preserves_closedness_r; eauto.
              * by unfold mergeable_interfaces in *; intuition.
              * eapply linkable_implies_linkable_mains; eauto.
                by unfold mergeable_interfaces in *; intuition.
              * eapply interface_implies_matching_mains; eauto.
            + eapply linking_well_formedness; auto.
              rewrite <- Hifc_cc'. unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - reflexivity.
        }

        
        assert (exists v,
                   Memory.load mem (Permission.data, cid_st, bid_st, off_st) =
                   Some v) as [vload Hload].
        {
          eapply Memory.store_some_load_some.
          eexists. eassumption.
        }

        (*assert (good_memory
                  (left_addr_good_for_shifting n)
                  (CS.state_mem (gps, mem', regs, Pointer.inc pc)))
          as Hgood_after_store.
        {
          eapply Hgood_prog; eassumption.
        }*)

        
        
        assert (
          exists mem2',
            Memory.store mem1' ptr (Register.get r2 regs1') = Some mem2'
          ) as [mem2' Hstoremem1'].
        {
          rewrite <- Memory.store_some_load_some.



          (* Consider refactoring the unfold and the assert out of 
             the enclosing assertion proof *)
          unfold mem_of_part_executing_rel_original_and_recombined,
          shift_value_option, rename_value_option,
          rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *. simpl in *.
          
          assert (
              (cid_st, bid_st).1 \in domm (prog_interface p) ->
                                     (
                                       Memory.load mem1' (Permission.data,
                                                          cid_st, bid_st, off_st) =
                                       match
                                         rename_value_option
                                           (rename_addr_option
                                              (sigma_shifting_wrap_bid_in_addr
                                                 (sigma_shifting_lefttoright_addr_bid
                                                    n
                                                    (fun cid : nat =>
                                                       if cid \in domm (prog_interface p)
                                                       then n cid else n'' cid)))) vload
                                       with
                                       | Some v' => Some v'
                                       | None => Some vload
                                       end)
            ) as Hmem_own1.
          {
            intros Hcidl.
            specialize (Hmem_own _ Hcidl) as [Hspec _].
            
            match goal with | H: Memory.load _ _ = _ |- _ => 
                              specialize (Hspec _ _ H)
            end.
            destruct (
                rename_value_option
                  (rename_addr_option
                     (sigma_shifting_wrap_bid_in_addr
                        (sigma_shifting_lefttoright_addr_bid
                           n
                           (fun cid : nat =>
                              if cid \in domm (prog_interface p)
                              then n cid else n'' cid))))
                  vload
              ) eqn:evload;
              unfold
                rename_value_option,
              rename_value_template_option,
              rename_addr_option, sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *; simpl in *;
                rewrite evload in Hspec; auto.
            intuition.
          }


          
          destruct (
              sigma_shifting_lefttoright_option
                (n cid_st)
                (if cid_st \in domm (prog_interface p)
                 then n cid_st else n'' cid_st) bid_st
            ) as [bidst_shift|] eqn:ebidst_shift; rewrite ebidst_shift in Hregs1'r1. 
          - inversion Hregs1'r1 as [G | [? _]]; try discriminate.
            rewrite Hptr in G. inversion G. subst. clear G Hregs1'r1 Hregs.
            inversion cidst_bidst_invariant as [| ? ? ? ?  Hshr]; subst.
            + rewrite Hpc_in in ebidst_shift.
              apply sigma_shifting_lefttoright_option_n_n_id in ebidst_shift.
              subst.
              rewrite Hpc_in in Hmem_own1.
              setoid_rewrite Hmem_own1; auto.
              by destruct (
                     rename_value_option
                       (rename_addr_option
                          (sigma_shifting_wrap_bid_in_addr
                             (sigma_shifting_lefttoright_addr_bid
                                n
                                (fun cid : nat =>
                                   if cid \in domm (prog_interface p)
                                   then n cid else n'' cid))))
                       vload); eexists; auto.
            + specialize (Hmem_shared _ Hshr) as Hmem_shared_cid_bid.
              setoid_rewrite ebidst_shift in Hmem_shared_cid_bid.
              destruct Hmem_shared_cid_bid as [addr' [addr'eq [addr'load _]]].
              inversion addr'eq. subst.
              match goal with
              | Hload: Memory.load mem _ = _ |- _ =>
                specialize (addr'load _ _ Hload) as [v' [G _]]
              end.
              eexists. eassumption.
          - inversion Hregs1'r1 as [| [? [? ptr_eq
                                            (*[Hnotshrt1 Hnotshrt1']*)
                                   ]]];
              try discriminate.
            rewrite Hptr in ptr_eq.
            inversion ptr_eq. subst. simpl in *.
            clear Hregs1'r1 ptr_eq.
            inversion cidst_bidst_invariant as [| ? ? ? ?  Hshr]; subst.
            + rewrite Hmem_own1; auto.
              by destruct (
                     rename_value_option
                       (rename_addr_option
                          (sigma_shifting_wrap_bid_in_addr
                             (sigma_shifting_lefttoright_addr_bid
                                n
                                (fun cid : nat =>
                                   if cid \in domm (prog_interface p)
                                   then n cid else n'' cid))))
                       vload) eqn:e; rewrite e; eexists; auto.
            + inversion Hgood_t as [? Hcontra]; subst.
              specialize (Hcontra _ Hshr).
              unfold left_addr_good_for_shifting in *.
              erewrite sigma_lefttoright_Some_spec in Hcontra.
              destruct Hcontra as [? contra].
                by erewrite contra in ebidst_shift.
        }

        assert (
          Step (CS.sem_non_inform (program_link p c'))
               (gps1', mem1', regs1', pc) 
               E0
               (gps1', mem2', regs1', Pointer.inc pc)
        ) as Hstep.
        {
          eapply CS.Step_non_inform; first eapply CS.Store.
          -- exact Hex'.
          -- exact Hptr.
          -- exact Hstoremem1'. 
          -- reflexivity.
        }
        
        assert (
          CSInvariants.is_prefix
            (gps1',
             mem2',
             regs1',
             Pointer.inc pc
            )
            (program_link p c')
            t1'
        ) as Hprefix_t1'_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }

        (* TODO: Refactor out *)
        Ltac find_if_inside_hyp H :=
          let e := fresh "e" in
          let t := type of H in
          match t with
          |  context [if ?X then _ else _] => destruct X eqn:e
          end.
        Ltac find_if_inside_goal :=
          let e := fresh "e" in
          match goal with
          | [ |- context[if ?X then _ else _] ] => destruct X eqn:e
          end.

        assert (Pointer.permission ptr = Permission.data) as Hptrperm.
        {
          simpl in *.
          unfold rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          rewrite Hptr in Hregs1'r1.
          inversion Hregs1'r1 as [Hregs1'r1a | Hregs1'r1a]; simpl in *;
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) as [?|] eqn:esigma;
            rewrite esigma in Hregs1'r1a; try discriminate.
          - by inversion Hregs1'r1a.
          - exfalso. by destruct Hregs1'r1a.
          - destruct Hregs1'r1a as [_ [_ G]]. by inversion G.
        }

        assert (Pointer.component ptr = cid_st) as Hptrcomp.
        {
          simpl in *.
          unfold rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          rewrite Hptr in Hregs1'r1.
          inversion Hregs1'r1 as [Hregs1'r1a | Hregs1'r1a]; simpl in *;
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) as [?|] eqn:esigma;
            rewrite esigma in Hregs1'r1a; try discriminate.
          - by inversion Hregs1'r1a.
          - exfalso. by destruct Hregs1'r1a.
          - destruct Hregs1'r1a as [_ [_ G]]. by inversion G.
        }

        rewrite Hptr in Hregs1'r1.

        assert (
            mem_of_part_executing_rel_original_and_recombined
              p
              mem'
              mem2'
              n
              (fun cid : nat_ordType =>
                 if cid \in domm (prog_interface p) then n cid else n'' cid) t1
          ) as Hmem'mem2'.
        {
          split; last split.
          - unfold shift_value_option, memory_shifts_memory_at_private_addr,
            memory_renames_memory_at_private_addr,
            rename_value_option, rename_value_template_option,
            rename_addr_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            simpl in *.
            intros ? Horiginal. split.
            + intros ? ? Hloadmem'.
              erewrite Memory.load_after_store in Hloadmem'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem'.
              * inversion Hloadmem'. subst.
                assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq as [[Hcid Hbid]]. subst.
                  rewrite Hcid in Horiginal.
                  rewrite Horiginal
                    in Hregs1'r1.
                  destruct Hregs1'r1 as [G| [G1 [G2 G3]]].
                --
                  destruct (sigma_shifting_lefttoright_option
                              (n (Pointer.component ptr))
                              (n (Pointer.component ptr))
                              original_addr.2
                           ) eqn:eoriginal; try discriminate.
                  apply sigma_shifting_lefttoright_option_n_n_id in eoriginal.
                  inversion G. subst. rewrite Hcid eqxx.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; try by rewrite G'.
                  destruct (Register.get r2 regs) as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [G'' ?]]; try discriminate.
                  destruct (perm =? Permission.data) eqn:eperm; try discriminate.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.
                  match goal with
                  | H: Ptr _ = Register.get r2 regs1' |- _ =>
                    rewrite <- H, eperm in G'';
                      rewrite esigma G'' H
                  end.
                    by auto.
                -- destruct (sigma_shifting_lefttoright_option
                               (n (Pointer.component ptr))
                               (n (Pointer.component ptr))
                               original_addr.2
                            ) eqn:eoriginal; try discriminate.
                   destruct ptr as [[[pptr cptr] bptr] optr].
                   inversion G3. subst. inversion Heq. subst.
                   simpl in G2. clear G1 G3. simpl in *.
                   rewrite eqxx.
                   specialize (Hregs r2) as Hgetr2.
                   destruct Hgetr2 as [G'|G']; try by rewrite G'.
                   destruct G' as [G'' [Hrewr1 Hrewr2]].
                   rewrite Hrewr2 Hrewr1.
                   rewrite Hrewr2 in G''.
                   by rewrite G''.
              * subst.
                find_if_inside_goal.
                --
                  assert (ptr =
                          (Permission.data, original_addr.1, original_addr.2, offset)).
                  by apply/(@eqP (prod_eqType
                                 (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                              nat_eqType)
                                 Extra.Z_eqType)); rewrite eq_sym.
                  subst. simpl in *.
                  rewrite Horiginal
                    in Hregs1'r1.
                  destruct Hregs1'r1 as [G | [G1 [G2 G3]]]; try discriminate.
                  ++
                    destruct (
                      sigma_shifting_lefttoright_option
                        (n original_addr.1)
                        (n original_addr.1) bid_st
                    ) eqn:ebidst; try discriminate.
                    apply sigma_shifting_lefttoright_option_n_n_id in ebidst.
                    inversion G. subst.
                      by rewrite eqxx in e.
                  ++
                    inversion G3. subst.
                    by rewrite eqxx in e.
     
                --
                  specialize (Hmem_own _ Horiginal) as [G _].
                    by eapply G; eauto.
            + intros ? ? Hloadmem2'.
              erewrite Memory.load_after_store in Hloadmem2'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem2'.
              * inversion Hloadmem2'. subst.
                assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                        ptr)
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  subst.
                  simpl in *.
                  rewrite Horiginal
                    in Hregs1'r1.
                  destruct (Hregs1'r1) as [Hrewr | [G1 [G2 G3]]];
                    try discriminate.
                --
                  inversion Hrewr. subst. clear Hregs1'r1 Hrewr.
                  destruct (
                      sigma_shifting_lefttoright_option
                        (n original_addr.1)
                        (n original_addr.1) bid_st
                    ) eqn:ebidst; try discriminate.
                  apply sigma_shifting_lefttoright_option_n_n_id in ebidst.
                  match goal with | H: Some _ = Some _ |- _ =>
                                    inversion H; subst
                  end.
                  rewrite eqxx.
                  eexists; split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; try by right.
                  left. by intuition.
                --
                  inversion G3. subst.
                  rewrite eqxx.
                  eexists; split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; try by right.
                  left. by intuition.
              * subst. find_if_inside_goal.
                --
                  assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                          (Permission.data, Pointer.component ptr, bid_st, off_st))
                    as contra.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  destruct original_addr as [origc origb].
                  inversion contra as [[Hcid Hbid]]. subst.
                  simpl in *.
                  rewrite Horiginal in Hregs1'r1.
                  destruct Hregs1'r1 as [G | [G1 [G2 G3]]]; try discriminate.
                  ++
                    destruct (
                        sigma_shifting_lefttoright_option
                          (n (Pointer.component ptr))
                          (n (Pointer.component ptr)) bid_st
                      ) eqn:ebid_st; try discriminate.
                    apply sigma_shifting_lefttoright_option_n_n_id in ebid_st.
                    inversion G as [G']. subst.
                      by rewrite <- G', eqxx in e.
                  ++
                    inversion G3 as [G'].
                    by rewrite <- G', eqxx in e.
                --
                  specialize (Hmem_own _ Horiginal) as [_ G].
                    by eapply G; eauto.
          - unfold shift_value_option, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            rename_addr_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            simpl in *.
            intros ? Horiginal.
            (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Horiginal)
                as Hgood.*)
            inversion Hgood_t as [? shared_good]. subst.
            specialize (shared_good _ Horiginal) as Hgood.


            unfold left_addr_good_for_shifting in *.
            destruct original_addr as [cid_orig bid_orig].
            erewrite sigma_lefttoright_Some_spec in Hgood.
            destruct Hgood as [rbid Hrbid].
            setoid_rewrite Hrbid.
            eexists. split; auto; split; simpl in *; intros ? ?.
            + intros Hloadmem'.
              specialize (Hgood_prog _ _ Hprefix_t1_E0) as [_ Hgoodv].
              assert (goodv : left_value_good_for_shifting n v).
              {
                eapply Hgoodv; eauto. simpl.
                specialize (shared_good _ Horiginal).
                by simpl in *.
              }
              unfold left_value_good_for_shifting, left_addr_good_for_shifting
                in goodv.
              
              erewrite Memory.load_after_store in Hloadmem'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem'.
              * inversion Hloadmem'. subst. clear Hloadmem'.
                assert ((Permission.data, cid_orig, bid_orig, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e.
                  rewrite Hrbid in Hregs1'r1.
                  destruct Hregs1'r1 as [Heq | [? _]]; try discriminate.
                  inversion Heq. simpl in *. rewrite eqxx. eexists. split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; auto.
                  destruct (Register.get r2 regs)
                    as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [G''' G''
                                                 (*[Hnotshr Hnotshr']*)
                                   ]]; try discriminate.
                  destruct (perm =? Permission.data) eqn:eperm; try discriminate.
                  assert (perm = Permission.data). by apply beq_nat_true. subst.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.
                  erewrite sigma_lefttoright_Some_spec in goodv.
                  destruct goodv as [? G].
                  by erewrite G in esigma.

              * subst.
                find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, rbid, offset) =
                          ptr)
                    as Heq.
                    by apply/(@eqP (prod_eqType
                                      (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                   nat_eqType)
                                      Extra.Z_eqType)).
                    subst.
                    simpl in *.
                    destruct (
                        sigma_shifting_lefttoright_option
                          (n cid_orig)
                          (if cid_orig \in domm (prog_interface p)
                           then n cid_orig else n'' cid_orig)
                          bid_st
                      ) eqn:esigma; rewrite esigma in Hregs1'r1.
                  ++
                    destruct Hregs1'r1 as [contra | [? _]]; try discriminate.
                    inversion contra. subst.
                    assert (bid_orig = bid_st).
                    by eapply sigma_shifting_lefttoright_option_Some_inj; eauto.
                    subst. by rewrite eqxx in e.
                  ++
                    destruct Hregs1'r1 as [contra | [? [contra ? (*[? contra]*)
                                          ]]];
                      try discriminate.
                    apply sigma_shifting_lefttoright_Some_inv_Some in Hrbid.
                    by rewrite Hrbid in contra.
                --
                  specialize (Hmem_shared _ Horiginal) as [? [esigma [G _]]].
                  rewrite Hrbid in esigma. inversion esigma. subst.
                  simpl in *. by eapply G; eauto.
            + intros Hloadmem2'.
              specialize (Hgood_prog _ _ Hprefix_t1_E0) as [_ Hgoodv].
              specialize (Hgoodv
                            mem'
                            (Permission.data, cid_orig, bid_orig, offset)
                            (cid_orig, bid_orig)
                         ).
              simpl in Hgoodv.
              unfold left_value_good_for_shifting, left_addr_good_for_shifting
                in Hgoodv.
              
              erewrite Memory.load_after_store in Hloadmem2'; eauto.
              erewrite Memory.load_after_store in Hgoodv; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem2'.
              * inversion Hloadmem2'. subst. clear Hloadmem2'.
                assert ((Permission.data, cid_orig, rbid, offset) = ptr)
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  subst. simpl in *.
                  find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, bid_orig, offset) =
                          (Permission.data, cid_orig, bid_st, off_st)) as Heq.
                    by apply/(@eqP (prod_eqType
                                      (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                   nat_eqType)
                                      Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e0.
                  eexists; split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; auto.
                  destruct (Register.get r2 regs)
                    as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [? G'' (*[Hnotshr Hnotshr']*)]];
                    try discriminate.
                  destruct (perm =? Permission.data) eqn:eperm; try discriminate.
                  assert (perm = Permission.data). by apply beq_nat_true. subst.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.
                  assert (left_block_id_good_for_shifting (n cid) b) as G.
                  {
                    specialize (Hgoodv (Ptr (Permission.data, cid, b, o))).
                    eapply Hgoodv; eauto.
                    by erewrite sigma_lefttoright_Some_spec; eauto.
                  }
                  erewrite sigma_lefttoright_Some_spec in G.
                  destruct G as [? Gcontra].
                  by erewrite Gcontra in esigma.

                --
                  destruct (
                      sigma_shifting_lefttoright_option
                        (n cid_orig)
                        (if cid_orig \in domm (prog_interface p)
                         then n cid_orig else n'' cid_orig)
                        bid_st
                    ) eqn:esigma; rewrite esigma in Hregs1'r1.
                  ++
                    destruct Hregs1'r1 as [Hrewr|[? _]]; try discriminate.
                    inversion Hrewr. subst. clear Hrewr.
                    assert (bid_orig = bid_st).
                      by eapply sigma_shifting_lefttoright_option_Some_inj; eauto.
                    subst. by rewrite eqxx in e0.
                  ++
                    destruct Hregs1'r1 as [?|[_ [contra Hinv (*[? Hcontra]*)
                                          ]]]; try discriminate.
                    inversion Hinv. subst.
                    apply sigma_shifting_lefttoright_Some_inv_Some in Hrbid.
                    by rewrite Hrbid in contra.

              * find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, bid_orig, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e0.
                  rewrite Hrbid in Hregs1'r1.
                  destruct Hregs1'r1 as [Hrewr|[? _]]; try discriminate.
                  inversion Hrewr as [Hsubst]. by rewrite Hsubst eqxx in e.
                --
                  specialize (Hmem_shared _ Horiginal) as [? [esigma [_ G]]].
                  rewrite Hrbid in esigma. inversion esigma. subst.
                  simpl in *. by eapply G; eauto.

                    
          - unfold Memory.store in *. simpl in *.
            destruct (mem cid_st) as [memC|] eqn:ememC; try discriminate.
            destruct (ComponentMemory.store memC bid_st off_st (Register.get r2 regs))
              as [memC'|] eqn:ememC'; try discriminate.
            match goal with | H: Some _ = Some _ |- _ => inversion H end. subst.
            find_if_inside_hyp Hstoremem1'; try discriminate.
            destruct (mem1' (Pointer.component ptr)) as [mem1'ptr|] eqn:emem1'ptr;
              try discriminate.
            destruct (ComponentMemory.store
                        mem1'ptr
                        (Pointer.block ptr) 
                        (Pointer.offset ptr)
                        (Register.get r2 regs1')) as [mem1'ptrComp|]
            eqn:compMemStore; try discriminate.
            inversion Hstoremem1'. subst.
            intros cid Hcid. rewrite !setmE.
            destruct (cid == Pointer.component ptr) eqn:ecid; rewrite ecid.
            + specialize (Hmem_next_block cid Hcid).
              unfold omap, obind, oapp in *.
              erewrite <- ComponentMemory.next_block_store_stable; last exact ememC'.
              symmetry.
              erewrite <- ComponentMemory.next_block_store_stable;
                last exact compMemStore.
              symmetry.
              assert (cid = Pointer.component ptr). by apply/eqP. subst.
              by rewrite ememC emem1'ptr in Hmem_next_block.
            + by specialize (Hmem_next_block cid Hcid). 
        }


        assert (
          mem_of_part_not_executing_rel_original_and_recombined_at_internal
            c'
            (CS.state_mem s1'')
            mem2'
            n''
            (fun cid : nat_ordType =>
               if cid \in domm (prog_interface p) then n cid else n'' cid)
            t1''
        ).
        {
          unfold
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
          memory_shifts_memory_at_private_addr,
          memory_renames_memory_at_private_addr in *.
          destruct Hmemc' as [Hprivrel Halloc].
          split.
          - intros ? Horiginal Hnotshr.

            assert (original_addr.1 \in domm (prog_interface p) -> False)
              as Horiginal_not_p.
            {
              intros contra.
              rewrite <- Hifc_cc' in Horiginal.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Horiginal contra).
            }
            
            split; intros ? ? Hload_c'.
            + erewrite Memory.load_after_store; last exact Hstoremem1'.
              find_if_inside_goal.
              * assert ((Permission.data, original_addr.1,
                         original_addr.2, offset) = ptr).
                by apply/(@eqP (prod_eqType
                                  (prod_eqType
                                     (prod_eqType nat_eqType nat_eqType)
                                     nat_eqType)
                                  Extra.Z_eqType)).
                subst.
                assert (CSInvariants.wf_ptr_wrt_cid_t
                          (Pointer.component pc)
                          t1'
                          (Permission.data,
                           original_addr.1,
                           original_addr.2, offset)) as Hwf.
                {
                  eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                  eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps1', mem1', regs1', pc)); eauto.
                  eapply CSInvariants.is_prefix_wf_state_t
                    with (p := (program_link p c')); eauto.
                  - eapply interface_preserves_closedness_r; eauto.
                    + by unfold mergeable_interfaces in *; intuition.
                    + eapply linkable_implies_linkable_mains; eauto.
                        by unfold mergeable_interfaces in *; intuition.
                    + apply interface_implies_matching_mains; auto.
                  - eapply linking_well_formedness; try assumption.
                    rewrite <- Hifc_cc'.
                    by unfold mergeable_interfaces in *;
                      intuition.
                }
                

                inversion Hwf as [| ? ? ? ? Hshr]; subst.
                ++
                  match goal with
                  | Hrewr: Pointer.component pc = _ |- _ =>
                    rewrite Hrewr in Hpc_in
                  end.
                  by intuition. (* contradiction *)
                ++
                  inversion Hshift_t''t' as [? ? t''t'ren]. subst.
                  inversion t''t'ren
                    as [|? ? ? ? ? ? _ Hshr'_shr'' _ _ _ _ _]; subst.
                  ** inversion Hshr; by find_nil_rcons.
                  ** specialize (Hshr'_shr'' _ Hshr)
                      as [[cid bid] [Hren [_ Hcontra]]].
                     unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr
                       in *.
                     simpl in *.
                     destruct (cid \in domm (prog_interface p)) eqn:ecid;
                       rewrite ecid in Hren.
                     ---
                       destruct (sigma_shifting_lefttoright_option
                                   (n'' cid) (n cid) bid); try discriminate.
                       inversion Hren. subst.
                         by rewrite ecid in Horiginal_not_p; exfalso; auto.
                     ---
                       destruct
                         (sigma_shifting_lefttoright_option
                            (n'' cid) (n'' cid) bid) eqn:esigma;
                         try discriminate.
                       apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                       inversion Hren. subst.
                         by destruct original_addr; simpl in *; intuition.
                         (* contradiction Hcontra with Hnotshr *)
                    
              * specialize (Hprivrel _ Horiginal Hnotshr) as [Hprivrel' _].
                  by eapply Hprivrel'.
            + erewrite Memory.load_after_store in Hload_c';
                last exact Hstoremem1'.
              find_if_inside_hyp Hload_c'.
              * assert ((Permission.data, original_addr.1,
                         original_addr.2, offset) = ptr).
                by apply/(@eqP (prod_eqType
                                  (prod_eqType
                                     (prod_eqType nat_eqType nat_eqType)
                                     nat_eqType)
                                  Extra.Z_eqType)).
                subst.
                assert (CSInvariants.wf_ptr_wrt_cid_t
                          (Pointer.component pc)
                          t1'
                          (Permission.data,
                           original_addr.1,
                           original_addr.2, offset)) as Hwf.
                {
                  eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                  eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps1', mem1', regs1', pc)); eauto.
                  eapply CSInvariants.is_prefix_wf_state_t
                    with (p := (program_link p c')); eauto.
                  - eapply interface_preserves_closedness_r; eauto.
                    + by unfold mergeable_interfaces in *; intuition.
                    + eapply linkable_implies_linkable_mains; eauto.
                        by unfold mergeable_interfaces in *; intuition.
                    + apply interface_implies_matching_mains; auto.
                  - eapply linking_well_formedness; try assumption.
                    rewrite <- Hifc_cc'.
                    by unfold mergeable_interfaces in *;
                      intuition.
                }
                

                inversion Hwf as [| ? ? ? ? Hshr]; subst.
                ++
                  match goal with
                  | Hrewr: Pointer.component pc = _ |- _ =>
                    rewrite Hrewr in Hpc_in
                  end.
                  by intuition. (* contradiction *)
                ++
                  inversion Hshift_t''t' as [? ? t''t'ren]. subst.
                  inversion t''t'ren
                    as [|? ? ? ? ? ? _ Hshr'_shr'' _ _ _ _ _]; subst.
                  ** inversion Hshr; by find_nil_rcons.
                  ** specialize (Hshr'_shr'' _ Hshr)
                      as [[cid bid] [Hren [_ Hcontra]]].
                     unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr
                       in *.
                     simpl in *.
                     destruct (cid \in domm (prog_interface p)) eqn:ecid;
                       rewrite ecid in Hren.
                     ---
                       destruct (sigma_shifting_lefttoright_option
                                   (n'' cid) (n cid) bid); try discriminate.
                       inversion Hren. subst.
                         by rewrite ecid in Horiginal_not_p; exfalso; auto.
                     ---
                       destruct
                         (sigma_shifting_lefttoright_option
                            (n'' cid) (n'' cid) bid) eqn:esigma;
                         try discriminate.
                       apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                       inversion Hren. subst.
                         by destruct original_addr; simpl in *; intuition.
                         (* contradiction Hcontra with Hnotshr *)
                
              * specialize (Hprivrel _ Horiginal Hnotshr) as [_ Hprivrel'].
                  by eapply Hprivrel'.

          - intros ? Hcid.
            assert (cid \in domm (prog_interface p) -> False)
              as Hcid_not_p.
            {
              intros contra.
              rewrite <- Hifc_cc' in Hcid.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Hcid contra).
            }
            
            unfold Memory.store in *. simpl in *.
            destruct (mem cid_st) as [memC|] eqn:ememC; try discriminate.
            destruct (ComponentMemory.store memC bid_st off_st (Register.get r2 regs))
              as [memC'|] eqn:ememC'; try discriminate.
            match goal with | H: Some _ = Some _ |- _ => inversion H end. subst.
            find_if_inside_hyp Hstoremem1'; try discriminate.
            destruct (mem1' (Pointer.component ptr)) as [mem1'ptr|] eqn:emem1'ptr;
              try discriminate.
            destruct (ComponentMemory.store
                        mem1'ptr
                        (Pointer.block ptr) 
                        (Pointer.offset ptr)
                        (Register.get r2 regs1')) as [mem1'ptrComp|]
            eqn:compMemStore; try discriminate.
            inversion Hstoremem1'. subst.
            rewrite !setmE.
            destruct (cid == Pointer.component ptr) eqn:ecid; rewrite ecid.
            + specialize (Halloc cid Hcid).
              unfold omap, obind, oapp in *.
              erewrite <- ComponentMemory.next_block_store_stable;
                last exact compMemStore.
              rewrite Halloc.
              assert (cid = Pointer.component ptr). by apply/eqP. subst.
              by rewrite emem1'ptr.
              
            + by specialize (Halloc cid Hcid).
        }
        
        
        eexists. split.
        * exact Hstep.

        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ by simpl.
            ++ simpl. rewrite <- Hpccomp_s'_s''.
                 by rewrite Pointer.inc_preserves_component.
          -- by simpl.

      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.
          


    -  (* IJal *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1',
                      Register.set R_RA (Ptr (Pointer.inc pc)) regs1',
                      pc'
                     )
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Jal.
          -- exact Hex'.
          -- unfold sem', prog'.
             eapply find_label_in_component_mergeable_internal_states; auto.
             ++ exact H_p.
             ++ exact Hmerge1.
             ++ reflexivity.
             ++ unfold sem, prog in *. assumption.
          -- reflexivity.
          -- reflexivity.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem,
                   Register.set R_RA (Ptr (Pointer.inc pc)) regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1',
                   Register.set R_RA (Ptr (Pointer.inc pc)) regs1',
                   pc'
                  )
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl. symmetry.
             eapply find_label_in_component_1; eassumption.
        * by simpl.
        * simpl. constructor. intros ?.
          inversion Hregsp as [Hregs]. specialize (Hregs reg).
          unfold Register.get, Register.set in *. simpl in Hregs. rewrite !setmE.
          destruct (Register.to_nat reg == Register.to_nat R_RA) eqn:ereg;
            rewrite ereg; try assumption.
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.
          assert (Pointer.permission pc = Permission.code).
          {
            match goal with
            | H: executing _ pc _ |- _ =>
              destruct H as [? [? ?]]; by intuition
            end.
          }
          assert (Pointer.permission (Pointer.inc pc) = Permission.code) as Hcode.
            by rewrite Pointer.inc_preserves_permission.
            
          destruct (Pointer.inc pc) as [[[perm cid] bid] off]. simpl in *. subst.
          simpl. by left.

      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IJump *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Ptr pc') as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            destruct pc' as [[[perm ?] ?] ?];
            simpl in *;
            subst;
            simpl in *;
            by inversion Hshift.
        }

        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', pc')
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Jump.
          -- exact Hex'.
          -- assumption.
          -- assumption.
          -- assumption.
          -- by simpl.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem, regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', pc')
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl. assumption.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBnz, non-zero case *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Int val) as Hregs1'_r.
        {

          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.

        }

        
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', pc')
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.BnzNZ.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
          -- eapply find_label_in_procedure_mergeable_internal_states; auto.
             ++ exact H_p.
             ++ exact Hmerge1.
             ++ reflexivity.
             ++ unfold sem, prog in *. assumption.
          -- by simpl.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem, regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', pc')
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             symmetry.
             eapply find_label_in_procedure_1; eassumption.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBnz, zero case *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Int 0) as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.
        }

        
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', Pointer.inc pc)
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.BnzZ.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
        }

          assert (CSInvariants.is_prefix
                  (gps, mem, regs, Pointer.inc pc)
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', Pointer.inc pc)
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             by rewrite Pointer.inc_preserves_component.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IAlloc *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get rsize regs1' = Int size) as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs rsize) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get rsize regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.
        }

        assert (
          exists mem2',
            Memory.alloc mem1' (Pointer.component pc) (Z.to_nat size) =
            Some (mem2', ptr)
        ) as [mem2' Halloc'].
        {
          destruct Hmemp as [_ [_ Hnextb_eq]].
          specialize (Hnextb_eq (Pointer.component pc) Hpc_prog_interface_p).
          simpl in Hnextb_eq.
          unfold omap, obind, oapp in *.
          unfold Memory.alloc in *.
          destruct (mem (Pointer.component pc)) as [cMem|] eqn:ecMem; try discriminate.
          destruct (mem1' (Pointer.component pc)) as [cMem1'|] eqn:ecMem1';
            try discriminate.
          destruct (ComponentMemory.alloc cMem1' (Z.to_nat size))
            as [cMem1'_new b] eqn:ecMem1'_new.
          eexists.
          destruct (ComponentMemory.alloc cMem (Z.to_nat size))
            as [cMem_new also_b] eqn:ecMem_new.
          assert (also_b = b).
          {
            specialize (ComponentMemory.next_block_alloc _ _ _ _ ecMem1'_new) as [eb _].
            specialize (ComponentMemory.next_block_alloc _ _ _ _ ecMem_new) as [eb' _].
            subst.
            by inversion Hnextb_eq.
          }
          subst.
          repeat match goal with | H: Some _ = Some _ |- _ => inversion H; clear H end.
          reflexivity.
        }


        assert (Pointer.component ptr \in domm (prog_interface p)) as Hptr.
        {
          specialize (Memory.component_of_alloc_ptr _ _ _ _ _ Halloc').
          intros H_. by rewrite H_.
        }
          
        assert (mem_of_part_executing_rel_original_and_recombined
                  p
                  mem'
                  mem2'
                  n
                  (fun cid : nat_ordType => if cid \in domm (prog_interface p)
                                            then n cid else n'' cid)
                  t1
               ) as [Hpriv [Hshared Hnextblock]].
        {
          destruct Hmemp as [Hpriv_given [Hshared_given Hnextblock_given]].

          specialize (Memory.component_of_alloc_ptr _ _ _ _ _ Halloc')
            as Hcompptr.
          
          split; last split.
          - intros [cid_original bid_original] Horiginal.
            unfold memory_shifts_memory_at_private_addr,
            memory_renames_memory_at_private_addr,
            rename_value_option,
            rename_value_template_option in *.
            
            split.
            + intros ? ? Hload. simpl in *.
              
              specialize (Hpriv_given (cid_original, bid_original) Horiginal).
              destruct Hpriv_given as [Hpriv_given' _].
              simpl in *.
              specialize (Hpriv_given' offset v).

              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Hnoteq.
              simpl in *.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Heq.
              simpl in *.
              
              match goal with
              | H: Memory.alloc mem _ _ = _ |- _ =>
                specialize (Memory.load_after_alloc
                              _ _ _ _ _
                              (Permission.data, cid_original, bid_original, offset)
                              H
                           ) as Hnoteq_p;
                  simpl in Hnoteq_p;
                  
                  specialize (Memory.load_after_alloc_eq
                                _ _ _ _ _
                                (Permission.data, cid_original, bid_original, offset)
                                H
                             ) as Heq_p;
                  simpl in Heq_p
              end.
              
              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by apply/eqP.
                  inversion H_. subst. clear H_.
                  rewrite Heq; auto.
                  unfold Memory.load, Memory.alloc in *. simpl in *.
                  destruct (mem1' (Pointer.component pc)) eqn:emem1'pc;
                    try discriminate.
                  destruct (mem (Pointer.component pc)) eqn:emempc;
                    try discriminate.
                  destruct (mem' (Pointer.component ptr)) eqn:emem'ptr;
                    try discriminate.
                  rewrite Hload in Heq_p.

                  repeat match goal with
                         | H: ?x = ?x -> ?y |- _ =>
                           assert (y) by auto; clear H
                         end.
                  
                  destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
                    destruct (Z.leb Z0 offset); auto; try discriminate.
                    by destruct v; try discriminate.
                    
              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  repeat match goal with
                         | H: ?x <> ?z -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.

                  rewrite assertion0.
                  rewrite Hload in assertion.
                  symmetry in assertion.
                  by apply Hpriv_given'; auto.

            + intros ? ? Hload. simpl in *.
              
              specialize (Hpriv_given (cid_original, bid_original) Horiginal).
              destruct Hpriv_given as [_ Hpriv_given'].
              simpl in *.
              specialize (Hpriv_given' offset v').

              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Hnoteq.
              simpl in *.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Heq.
              simpl in *.
              
              match goal with
              | H: Memory.alloc mem _ _ = _ |- _ =>
                specialize (Memory.load_after_alloc
                              _ _ _ _ _
                              (Permission.data, cid_original, bid_original, offset)
                              H
                           ) as Hnoteq_p;
                  simpl in Hnoteq_p;
                  
                  specialize (Memory.load_after_alloc_eq
                                _ _ _ _ _
                                (Permission.data, cid_original, bid_original, offset)
                                H
                             ) as Heq_p;
                  simpl in Heq_p
              end.
              
              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by apply/eqP.
                  inversion H_. subst. clear H_.
                  rewrite Heq_p; auto.
                  unfold Memory.load, Memory.alloc in *. simpl in *.
                  destruct (mem1' (Pointer.component pc)) eqn:emem1'pc;
                    try discriminate.
                  destruct (mem (Pointer.component pc)) eqn:emempc;
                    try discriminate.
                  destruct (mem2' (Pointer.component ptr)) eqn:emem2'ptr;
                    try discriminate.
                  rewrite Hload in Heq.

                  repeat match goal with
                         | H: ?x = ?x -> ?y |- _ =>
                           assert (y) by auto; clear H
                         end.

                  destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
                    destruct (Z.leb Z0 offset); auto; try discriminate.
                  by destruct v'; try discriminate; eexists; eauto.

              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  repeat match goal with
                         | H: ?x <> ?z -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.

                  rewrite assertion.
                  rewrite Hload in assertion0.
                  symmetry in assertion0.
                    by apply Hpriv_given'; auto.

          - intros [cid_original bid_original] Horiginal.
            unfold memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_shared_addr,
            rename_value_option,
            rename_value_template_option in *.

            specialize (Hshared_given (cid_original, bid_original) Horiginal)
              as [addr' [Haddr' [Hsharedmemmem1' Hsharedmem1'mem]]].
            exists addr'; split; first assumption.
            split.
            + intros ? ? Hload. simpl in *.
              
              simpl in *.
              specialize (Hsharedmemmem1' offset v).

              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, addr'.1, addr'.2, offset)
                            Halloc'
                         ) as Hnoteq.
              simpl in *.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, addr'.1, addr'.2, offset)
                            Halloc'
                         ) as Heq.
              simpl in *.
              
              match goal with
              | H: Memory.alloc mem _ _ = _ |- _ =>
                specialize (Memory.load_after_alloc
                              _ _ _ _ _
                              (Permission.data, cid_original, bid_original, offset)
                              H
                           ) as Hnoteq_p;
                  simpl in Hnoteq_p;
                  
                  specialize (Memory.load_after_alloc_eq
                                _ _ _ _ _
                                (Permission.data, cid_original, bid_original, offset)
                                H
                             ) as Heq_p;
                  simpl in Heq_p
              end.
              
              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by apply/eqP.
                  inversion H_. subst. clear H_.
                  unfold rename_addr_option,
                  sigma_shifting_wrap_bid_in_addr,
                  sigma_shifting_lefttoright_addr_bid in Haddr'.
                  rewrite Hptr in Haddr'.
                  destruct (sigma_shifting_lefttoright_option
                              (n (Pointer.component ptr))
                              (n (Pointer.component ptr))
                              (Pointer.block ptr)) eqn:esigma; try discriminate.
                  apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                  destruct addr' as [cid' bid']. inversion Haddr'. subst.
                  simpl in *.
                  eexists; erewrite Heq; eauto.
                  
                  unfold Memory.load, Memory.alloc in *. simpl in *.
                  destruct (mem1' (Pointer.component pc)) eqn:emem1'pc;
                    try discriminate.
                  destruct (mem (Pointer.component pc)) eqn:emempc;
                    try discriminate.
                  destruct (mem' (Pointer.component ptr)) eqn:emem'ptr;
                    try discriminate.
                  rewrite Hload in Heq_p.

                  repeat match goal with
                         | H: ?x = ?x -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.
                  
                  destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
                    destruct (Z.leb Z0 offset); auto; try discriminate.
                    by destruct v; try discriminate.
                    
              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  
                  assert ((addr'.1, addr'.2) <>
                          (Pointer.component ptr, Pointer.block ptr)).
                  {
                    destruct ptr as [[[? ?] ?] ?].
                    unfold not. intros H'. inversion H'. subst.
                    simpl in *.
                    unfold rename_addr_option,
                    sigma_shifting_wrap_bid_in_addr,
                    sigma_shifting_lefttoright_addr_bid in Haddr'.
                    destruct addr' as [addr'cid addr'bid].
                    simpl in *.
                    destruct (sigma_shifting_lefttoright_option
                                (n cid_original)
                                (if cid_original \in domm (prog_interface p)
                                 then n cid_original
                                 else n'' cid_original) bid_original)
                             eqn:esigma; rewrite esigma in Haddr';
                      try discriminate.
                    inversion Haddr'. subst.
                    rewrite Hpc_prog_interface_p  in esigma.
                    apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                    inversion esigma. subst.
                    by rewrite eqxx in Hwhichaddr.
                  }
                  
                  repeat match goal with
                         | H: ?x <> ?z -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.


                  rewrite assertion0.
                  rewrite Hload in assertion.
                  symmetry in assertion.
                    by apply Hsharedmemmem1'; auto.

            + intros ? ? Hload. simpl in *.
              
              simpl in *.
              specialize (Hsharedmem1'mem offset v').

              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, addr'.1, addr'.2, offset)
                            Halloc'
                         ) as Hnoteq.
              simpl in *.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, addr'.1, addr'.2, offset)
                            Halloc'
                         ) as Heq.
              simpl in *.
              
              match goal with
              | H: Memory.alloc mem _ _ = _ |- _ =>
                specialize (Memory.load_after_alloc
                              _ _ _ _ _
                              (Permission.data, cid_original, bid_original, offset)
                              H
                           ) as Hnoteq_p;
                  simpl in Hnoteq_p;
                  
                  specialize (Memory.load_after_alloc_eq
                                _ _ _ _ _
                                (Permission.data, cid_original, bid_original, offset)
                                H
                             ) as Heq_p;
                  simpl in Heq_p
              end.
              
              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by apply/eqP.
                  inversion H_. subst. clear H_.
                  unfold rename_addr_option,
                  sigma_shifting_wrap_bid_in_addr,
                  sigma_shifting_lefttoright_addr_bid in Haddr'.
                  rewrite Hptr in Haddr'.
                  destruct (sigma_shifting_lefttoright_option
                              (n (Pointer.component ptr))
                              (n (Pointer.component ptr))
                              (Pointer.block ptr)) eqn:esigma; try discriminate.
                  apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                  destruct addr' as [cid' bid']. inversion Haddr'. subst.
                  simpl in *.
                  eexists; erewrite Heq_p; eauto.
                  
                  unfold Memory.load, Memory.alloc in *. simpl in *.
                  destruct (mem1' (Pointer.component pc)) eqn:emem1'pc;
                    try discriminate.
                  destruct (mem (Pointer.component pc)) eqn:emempc;
                    try discriminate.
                  destruct (mem2' (Pointer.component ptr)) eqn:emem'ptr;
                    try discriminate.
                  rewrite Hload in Heq.

                  repeat match goal with
                         | H: ?x = ?x -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.
                  
                  destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
                    destruct (Z.leb Z0 offset); auto; try discriminate.
                    
              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  
                  assert ((addr'.1, addr'.2) <>
                          (Pointer.component ptr, Pointer.block ptr)).
                  {
                    destruct ptr as [[[? ?] ?] ?].
                    unfold not. intros H'. inversion H'. subst.
                    simpl in *.
                    unfold rename_addr_option,
                    sigma_shifting_wrap_bid_in_addr,
                    sigma_shifting_lefttoright_addr_bid in Haddr'.
                    destruct addr' as [addr'cid addr'bid].
                    simpl in *.
                    destruct (sigma_shifting_lefttoright_option
                                (n cid_original)
                                (if cid_original \in domm (prog_interface p)
                                 then n cid_original
                                 else n'' cid_original) bid_original)
                             eqn:esigma; rewrite esigma in Haddr';
                      try discriminate.
                    inversion Haddr'. subst.
                    rewrite Hpc_prog_interface_p  in esigma.
                    apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                    inversion esigma. subst.
                    by rewrite eqxx in Hwhichaddr.
                  }
                  
                  repeat match goal with
                         | H: ?x <> ?z -> ?y |- _ =>
                           let assertion := fresh "assertion" in
                           assert (y) as assertion by auto; clear H
                         end.


                  rewrite assertion.
                  rewrite Hload in assertion0.
                  symmetry in assertion0.
                    by apply Hsharedmem1'mem; auto.

          - intros cid Hcid.
            unfold Memory.alloc in *.
            destruct (mem (Pointer.component pc)) as [memComp|] eqn:ememComp;
              try discriminate.
            destruct (mem1' (Pointer.component pc)) as [mem1'Comp|] eqn:emem1'Comp;
              try discriminate.
            destruct (ComponentMemory.alloc memComp (Z.to_nat size))
              as [memComp' b] eqn:ememComp'.
            destruct (ComponentMemory.alloc mem1'Comp (Z.to_nat size))
              as [mem1'Comp' b'] eqn:emem1'Comp'.
            match goal with
            | H: Some _ = Some _, H2: Some _ = Some _ |- _ =>
              inversion H; subst; clear H; inversion H2; subst; clear H2
            end.
            rewrite !setmE.
            destruct (cid == Pointer.component pc) eqn:ecid.
            + unfold omap, obind, oapp in *.
              
              specialize (ComponentMemory.next_block_alloc _ _ _ _ emem1'Comp')
                as [_ G1].
              rewrite G1.
              specialize (ComponentMemory.next_block_alloc _ _ _ _ ememComp')
                as [_ G2].
              rewrite G2.

              specialize (Hnextblock_given (Pointer.component pc) Hptr).
              simpl in Hnextblock_given.
              rewrite ememComp emem1'Comp in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.

            + specialize (Hnextblock_given cid Hcid).
              simpl in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.
                
        }


        assert (mem_of_part_not_executing_rel_original_and_recombined_at_internal
                  c' 
                  (CS.state_mem s1'')
                  mem2'
                  n''
                  (fun cid : nat => if cid \in domm (prog_interface p)
                                    then n cid else n'' cid)
                  t1''
               ) as [Hpriv_not_exec Hnextblock_not_exec].
        {
          destruct Hmemc' as [Hpriv_given Hnextblock_given].
          split.
          - intros [cid_original bid_original] Horiginal1 Horiginal2.
            unfold memory_shifts_memory_at_private_addr,
            memory_renames_memory_at_private_addr in *.
            split; intros ? ? Hload.
            + 
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Hnoteq.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Heq.
              
              specialize (Hpriv_given
                            (cid_original, bid_original) Horiginal1 Horiginal2)
                as [Hpriv_given' _].
              specialize (Hpriv_given' offset v).
              simpl in *.

              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr))
                  as H_. by apply/eqP.
                inversion H_. subst. clear H_.
                simpl in *.
                rewrite <- Hifc_cc' in Horiginal1.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hcontra] _].
                  by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).
              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  rewrite Hnoteq; auto.
                  eapply Hpriv_given'; eauto.

            +
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Hnoteq.
              
              specialize (Memory.load_after_alloc_eq
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, offset)
                            Halloc'
                         ) as Heq.
              
              specialize (Hpriv_given
                            (cid_original, bid_original) Horiginal1 Horiginal2)
                as [_ Hpriv_given'].
              specialize (Hpriv_given' offset v').
              simpl in *.

              destruct ((cid_original, bid_original) ==
                        (Pointer.component ptr, Pointer.block ptr))
                       eqn:Hwhichaddr.
              * assert ((cid_original, bid_original) =
                        (Pointer.component ptr, Pointer.block ptr))
                  as H_. by apply/eqP.
                inversion H_. subst. clear H_.
                simpl in *.
                rewrite <- Hifc_cc' in Horiginal1.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hcontra] _].
                  by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).
              * assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.

                  rewrite Hnoteq in Hload; auto.

          - intros cid Hcid.
            unfold Memory.alloc in *.
            destruct (mem (Pointer.component pc)) as [memComp|] eqn:ememComp;
              try discriminate.
            destruct (mem1' (Pointer.component pc)) as [mem1'Comp|] eqn:emem1'Comp;
              try discriminate.
            destruct (ComponentMemory.alloc memComp (Z.to_nat size))
              as [memComp' b] eqn:ememComp'.
            destruct (ComponentMemory.alloc mem1'Comp (Z.to_nat size))
              as [mem1'Comp' b'] eqn:emem1'Comp'.
            match goal with
            | H: Some _ = Some _, H2: Some _ = Some _ |- _ =>
              inversion H; subst; clear H; inversion H2; subst; clear H2
            end.
            rewrite !setmE.
            destruct (cid == Pointer.component pc) eqn:ecid.
            + assert (cid = Pointer.component pc). by apply/eqP. subst.
              rewrite <- Hifc_cc' in Hcid.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Hcid Hpc_prog_interface_p).

            + specialize (Hnextblock_given cid Hcid).
              simpl in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.

        }

        
        assert (
          regs_rel_of_executing_part
            (Register.set rptr (Ptr ptr) regs)
            (Register.set rptr (Ptr ptr) regs1')
            n
            (fun cid : nat_ordType =>
               if cid \in domm (prog_interface p) then n cid else n'' cid)
        ) as Hregs.
        {
          constructor. intros reg. unfold Register.get, Register.set.
          rewrite !setmE.
          destruct (Register.to_nat reg == Register.to_nat rptr) eqn:ereg;
            rewrite ereg.
          - destruct ptr as [[[perm cid] bid] off].
            unfold shift_value_option, rename_value_option,
            rename_value_template_option, rename_addr_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *. simpl in *.
            rewrite Hptr.
            assert (perm = Permission.data).
            {
                by specialize (Memory.permission_of_alloc_ptr _ _ _ _ _ Halloc');
                  simpl in *.
            }
            subst. simpl.
            destruct (sigma_shifting_lefttoright_option (n cid) (n cid) bid)
                     eqn:esigma.
            + apply sigma_shifting_lefttoright_option_n_n_id in esigma.
                by subst; left.
            + by right; intuition.
          - inversion Hregsp as [G]. by specialize (G reg).
        }
                
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem2', Register.set rptr (Ptr ptr) regs1', Pointer.inc pc)
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Alloc.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
          -- eassumption.
          -- reflexivity.
          -- reflexivity.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem', Register.set rptr (Ptr ptr) regs, Pointer.inc pc)
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem2', Register.set rptr (Ptr ptr) regs1', Pointer.inc pc)
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }

        (*
        assert (good_memory (left_addr_good_for_shifting n) mem') as Hgood_memp_alloc.
        {
          unfold good_memory.
          intros ? ? ? ? ? ? Hlgood Hloadptr.
          match goal with | Halloc: Memory.alloc mem _ _ = _ |- _ =>
                            specialize (Memory.load_after_alloc_eq
                                          _ _ _ _ _
                                          (Permission.data, cid, bid, offset)
                                          Halloc
                                       ) as Heq;
                            specialize (Memory.load_after_alloc
                                          _ _ _ _ _
                                          (Permission.data, cid, bid, offset)
                                          Halloc
                                       ) as Hnoteq  
          end.
          simpl in Heq. simpl in Hnoteq.
          destruct ((cid, bid) == (Pointer.component ptr, Pointer.block ptr))
                   eqn:eptr.
          - assert ((cid, bid) = (Pointer.component ptr, Pointer.block ptr)) as H_.
              by apply/eqP.
            inversion H_. subst. clear H_ eptr.
            rewrite Heq in Hloadptr; auto.
            destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
              destruct (Z.leb Z0 offset); discriminate.
          - assert ((cid, bid) <> (Pointer.component ptr, Pointer.block ptr)) as H_.
            { intros H_. inversion H_. subst. clear H_. by rewrite eqxx in eptr.  }
            rewrite Hnoteq in Hloadptr; auto.
            by eapply Hgood_mem; eauto.
        }

        assert (good_memory
                  (left_addr_good_for_shifting
                     (fun cid : nat => if cid \in domm (prog_interface p)
                                       then n cid else n'' cid))
                  mem2') as Hgood_mem2'.
        {
          unfold good_memory.
          intros ? ? ? ? ? ? Hlgood Hloadptr.
          specialize (Memory.load_after_alloc_eq
                        _ _ _ _ _
                        (Permission.data, cid, bid, offset)
                        Halloc'
                     ) as Heq.
          specialize (Memory.load_after_alloc
                        _ _ _ _ _
                        (Permission.data, cid, bid, offset)
                        Halloc'
                     ) as Hnoteq.
          simpl in Heq. simpl in Hnoteq.
          destruct ((cid, bid) == (Pointer.component ptr, Pointer.block ptr))
                   eqn:eptr.
          - assert ((cid, bid) = (Pointer.component ptr, Pointer.block ptr)) as H_.
              by apply/eqP.
            inversion H_. subst. clear H_ eptr.
            rewrite Heq in Hloadptr; auto.
            destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
              destruct (Z.leb Z0 offset); discriminate.
          - assert ((cid, bid) <> (Pointer.component ptr, Pointer.block ptr)) as H_.
            { intros H_. inversion H_. subst. clear H_. by rewrite eqxx in eptr.  }
            rewrite Hnoteq in Hloadptr; auto.
            by eapply Hgood_mem'; eauto.
        }
        *)
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             by rewrite Pointer.inc_preserves_component.
        * by simpl.
        * by unfold mem_of_part_executing_rel_original_and_recombined; intuition.
        * by unfold
               mem_of_part_not_executing_rel_original_and_recombined_at_internal;
            intuition.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.


    - discriminate.
    - discriminate.

      
  Qed.
  

  Theorem threeway_multisem_star_E0 s1 s1' s1'' t1 t1' t1'' s2 :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    starR (CS.step_non_inform) (prepare_global_env prog) s1  E0 s2  ->
    exists s2',
      starR (CS.step_non_inform) (prepare_global_env prog') s1' E0 s2' /\
      mergeable_internal_states p c p' c' n n'' s2 s2' s1'' t1 t1' t1''.
  Proof.
    intros Hcomp Hmerge Hstar.
    remember E0 as t.
    induction Hstar as [| ]; subst.
    - eexists; split; last exact Hmerge. constructor.
    - assert (t0 = E0). by now destruct t0. subst.
      assert (t2 = E0). by now destruct t2. subst.
      pose proof (IHHstar Hcomp Hmerge Logic.eq_refl) as [s2' [Hs2' Hmerge2]].
      assert (Hcomp2: CS.is_program_component s2 ic).
      {
        eapply CS.epsilon_star_non_inform_preserves_program_component; eauto.
        erewrite star_iff_starR. simpl.
        exact Hstar.
      }
      match goal with
        | Hstep: CS.step_non_inform _ _ _ _ |- _ =>
          pose proof threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep as G
      end.
      destruct G as [? [? ?]].

      eexists; split; first eapply starR_step; first eassumption; eauto.
  Qed.


End ThreewayMultisem1.

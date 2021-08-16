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

  (* Given a silent star driven by the "program" side p, the "context" side c
     remains unaltered. *)

  (* Ltac t_to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' := *)
  (*   inversion Hmerge1 *)
  (*     as [_ s0'' t01'' _ _ Hwfp' Hwfc' Hmergeable_ifaces *)
  (*         Hifacep Hifacec _ Hprog_is_closed' _ Hini0'' _ Hstar01'']; *)
  (*   pose proof mergeable_states_program_to_program Hmerge1 Hcomp as Hcomp1''; *)
  (*   rewrite Hifacec in Hcomp1''; *)
  (*   assert (Hmergeable_ifaces' := Hmergeable_ifaces); *)
  (*     rewrite Hifacep Hifacec in Hmergeable_ifaces'; *)
  (*   pose proof CS.epsilon_star_preserves_program_component _ _ _ _ Hcomp1'' Hstar12'' as Hcomp2''; *)
  (*   destruct (CS.star_pc_domm _ _ *)
  (*               Hwfp' Hwfc' Hmergeable_ifaces' Hprog_is_closed' Hini0'' *)
  (*               (star_trans Hstar01'' Hstar12'' eq_refl)) as [Hgoal | Hcontra]; *)
  (*   [ now rewrite Hifacep *)
  (*   | CS.simplify_turn; now rewrite Hcontra in Hcomp2'' *)
  (*   ]. *)

  (* [DynShare]

     This lemma is false in the existence of dynamic memory sharing.
     Instead, what remains untouched is *only* the part of the partial memory
     that *remains* private after considering (i.e., set-differencing) the set
     of shared addresses.
   *)
  (* Lemma to_partial_memory_epsilon_star s s1'' s2'' s3'' : *)
  (*   mergeable_states p c p' c' s s1'' -> *)
  (*   CS.is_program_component s ic -> *)
  (*   Star sem'' s1'' E0 s2'' -> *)
  (*   Step sem'' s2'' E0 s3'' -> *)
  (*   to_partial_memory (CS.state_mem s2'') (domm ip) = *)
  (*   to_partial_memory (CS.state_mem s3'') (domm ip). *)
  (* Proof. *)
  (*   intros Hmerge1 Hcomp Hstar12'' Hstep23''. *)
  (*   destruct s2'' as [[[[gps2'' mem2''] regs2''] pc2''] addr2'']. *)
  (*   destruct s3'' as [[[[gps3'' mem3''] regs3''] pc3''] addr3'']. *)
  (*   pose proof CS.step_non_inform_step_inform prog'' *)
  (*        (gps2'', mem2'', regs2'', pc2'', addr2'') _ _ Hstep23'' as *)
  (*       [t_inform [Hstep_inform _]]. *)
  (*   inversion Hstep_inform; subst; *)
  (*     (* Most cases do not touch the memory. *) *)
  (*     try reflexivity. *)
  (*     (* *)
  (*       [DynShare] *)

  (*       The proof below no longer holds. The proof is looking for the assumption *)
  (*       Heq that ensures that the store is not touching any non-pc-owned memory. *)
  (*       However, no such assumption exists anymore for the store instruction. *)
  (*      *) *)
  (* Abort. *)

  (* [DynShare] DEPRECATED ARGUMENT BELOW

      (* Rewrite memory goals, discharge side goals and homogenize shape. *)
      match goal with
      | Hstore : Memory.store _ _ _ = _,
        Heq : Pointer.component _ = Pointer.component _ |- _ =>
        erewrite Memory.program_store_to_partialized_memory; eauto 1; rewrite Heq
      | Halloc : Memory.alloc _ _ _ = _ |- _ =>
        erewrite program_allocation_to_partialized_memory; eauto 1
      end.
      (* Prove the PC is in the program in both cases. *)
      unfold ip;
      t_to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12''.
  Qed.

   *)

  Ltac t_merge_states_silent_star :=
    inversion IHstar''; subst;
    [econstructor]; try eassumption;
    (* In most cases, only one sub-goal is left, always solvable thus: *)
    try (eapply star_right; try eassumption;
         now rewrite E0_right).
    (* In memory-altering cases, a second sub-goal is left to be solved. *)

  (* RB: NOTE: Likely provable: since we are on the program, we would not care
     what changes the "other program" makes to its memory, only what "our
     program" eventually will. *)
  (* AEK: Notice here that the precondition CS.is_program_component looks like *)
  (* it should be accompanied with a "mirrored" version of the same lemma that *)
  (* has the precondition CS.is_context_component instead. However, this mirrored *)
  (* lemma is not really necessary. And the mirroring is instead done at use time. *)
  Lemma merge_states_silent_star s1 s1' s1'' s2'' t t' t'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s2'' t t' t''.
  Proof.
    intros Hmerge1 Hcomp Hstar12''.
    remember E0 as t0.
    apply star_iff_starR in Hstar12''.
    induction Hstar12''
      as [s'' | s1'' t1 s2'' t2 s3'' ? Hstar12'' IHstar'' Hstep23'' Ht12]; subst.
    - assumption.
    - (* Simplify, apply IH and case analyze. *)
      symmetry in Ht12; apply Eapp_E0_inv in Ht12 as [? ?]; subst.
      specialize (IHstar'' Hmerge1 Logic.eq_refl).
      (* rewrite IHstar''. *)
      apply star_iff_starR in Hstar12''.
      destruct s1 as [[[gps1 mem1] regs1] pc1].
      destruct s2'' as [[[gps2'' mem2''] regs2''] pc2''].
      destruct s3'' as [[[gps3'' mem3''] regs3''] pc3''].
      pose proof CS.step_non_inform_step_inform prog''
           (gps2'', mem2'', regs2'', pc2'') _ _ Hstep23'' as
          [t_inform [Hstep_inform _]].
      (* Analyze and recompose mergeability relation in each case. *)
      inversion Hstep_inform; subst.
      + (* INop *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* ILabel *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IConst *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IMov *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBinop *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IPtrOfLabel *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* ILoad *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IStore *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            find_and_invert_mergeable_states_well_formed;
              eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            (* ++ eapply Hgood_prog''.
               (* is_prefix again *)
               unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** by rewrite E0_right.*)
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
          -- (* mem of part not executing *)
            unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal.
            (* Key fact to prove:
               the address that is stored at does NOT satisfy the preconditions
               of this goal.
             *)
            
            match goal with
            | Hstore: Memory.store mem2'' ?PTR _ = _ |- _ =>
              destruct PTR as [[[perm cid_store] bid_store] offset_store]
            end.
            assert (CSInvariants.wf_ptr_wrt_cid_t
                      (Pointer.component (Pointer.inc pc2''))
                      t''
                      (perm, cid_store, bid_store, offset_store)
                   ) as Hwfptr.
            {
              find_and_invert_mergeable_states_well_formed.
          
              eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
              rewrite Pointer.inc_preserves_component.
              eapply CSInvariants.wf_state_wf_reg.
              - eapply CSInvariants.is_prefix_wf_state_t;
                  last (
                      match goal with
                      | H: CSInvariants.is_prefix _ _ t'' |- _ => exact H
                      end
                    ); auto.
                eapply linking_well_formedness; eauto.
                unfold mergeable_interfaces in *.
                  by
                    match goal with
                    | Hp: prog_interface p = _,
                          Hc: prog_interface c = _,
                              Hlink: linkable _ _ /\ _
                      |- _ => rewrite <- Hp, <- Hc; destruct Hlink as [Hgoal _]
                    end.
              - by simpl.
              - by simpl.
              - by auto.
              - eapply Memory.store_some_permission; eauto.
            }
            assert (
              cid_store \in domm (prog_interface c') ->
                            addr_shared_so_far (cid_store, bid_store) t''
            ) as Hstore_addr_fact.
            {
              intros Hcid_store.
              inversion Hwfptr as [ | ]; eauto.
              - (* Now show through mergeable_well_formedness 
                     that Hcid_store is false.
                 *)
                subst.
                find_and_invert_mergeable_states_well_formed.
                simpl in *.
                unfold CS.is_program_component, CS.is_context_component,
                turn_of, CS.state_turn, ic, negb in Hcomp.
                match goal with
                |
                H: prog_interface c = prog_interface c',
                   H1: Pointer.component (CS.state_pc s1') = Pointer.component pc1,
                       H2: Pointer.component (CS.state_pc s1') =
                           Pointer.component pc2''
                |- _ => rewrite <- H1, H2, H in Hcomp
                end.
                rewrite (Pointer.inc_preserves_component) in Hcid_store. 
                  by rewrite Hcid_store in Hcomp. 
            }

            split. (* split into 2 subgoals. *)
            ++ intros original_addr Horiginal_addr1 Horiginal_addr2.
               
               (* destruct whether original_addr == address stored-at, and
                  obtain a contradiction (in the true case) to the key fact above.
                  
                  And in the false case, use Memory.load_after_store to reuse
                  the assumption about mem2'' (H5).
                *)
               
               destruct (@pair_eq
                           nat_eqType nat_eqType
                           original_addr
                           (cid_store, bid_store)
                        ) eqn:eq_original_addr.
               ** unfold pair_eq in *. simpl in *.
                  pose proof (andb_prop _ _ eq_original_addr) as [Hcid Hbid].
                  assert (original_addr.1 = cid_store) as Hcid1. by apply/eqP.
                  assert (original_addr.2 = bid_store) as Hbid1. by apply/eqP.
                  subst.
                  rewrite <- surjective_pairing in Hstore_addr_fact.
                    by pose proof (Hstore_addr_fact Horiginal_addr1).
               **  match goal with
                   | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                          _ _ _ _ _ _ |- _ =>
                     unfold
                       mem_of_part_not_executing_rel_original_and_recombined_at_internal
                       in H;
                       destruct H as [Hshift_mem2'' _]
                   end.
                   specialize
                     (Hshift_mem2'' original_addr  Horiginal_addr1 Horiginal_addr2).
                   unfold memory_shifts_memory_at_private_addr,
                   memory_renames_memory_at_private_addr in *.
                   split.
                   --- simpl. simpl in Hshift_mem2''. intros.
                   pose proof (Memory.load_after_store
                                 mem2''
                                 (perm, cid_store, bid_store, offset_store)
                                 (Register.get r2 regs3'')
                                 mem3''
                                 (Permission.data,
                                  original_addr.1,
                                  original_addr.2,
                                  offset)
                              ) as Hmem2''_mem3''.
                   (* Notation NOT WORKING *)
                   destruct (Pointer.eq
                               (Permission.data,
                                original_addr.1,
                                original_addr.2, offset)
                               (perm, cid_store,
                                bid_store,
                                offset_store)
                            ) eqn:Heq.
                   +++ (* case true; derive a contradiction to eq_original_addr *)
                     destruct original_addr as [cidorig bidorig]. simpl in *.
                     destruct perm; first by auto. simpl in *.
                     apply andb_true_iff in Heq.
                     destruct Heq as [Heq _].
                     apply andb_true_iff in Heq as [contra1 contra2].
                     apply beq_nat_true in contra1.
                     apply beq_nat_true in contra2.
                     subst. by rewrite !eqxx in eq_original_addr.
                   +++ (* case false; now use Hmem2''_mem3'' *)
                     
                     destruct Hshift_mem2'' as [Hrewr _].
                     match goal with
                     | H: Memory.store mem2'' _ _ = _ |- _ =>
                       specialize (Hmem2''_mem3'' H)
                     end.
                     
                     move : Heq => /Pointer.eqP => Heq.
                     match goal with
                     | H: Memory.load mem3'' _ = Some _ |- _ =>
                       rewrite H in Hmem2''_mem3''; symmetry in Hmem2''_mem3'';
                         specialize (Hrewr _ _  Hmem2''_mem3'')   
                     end.
                     destruct (
                         rename_value_option
                           (sigma_shifting_wrap_bid_in_addr
                              (sigma_shifting_lefttoright_addr_bid
                                 n''
                                 (fun cid : nat =>
                                    if cid \in domm (prog_interface p)
                                    then n cid else n'' cid)))
                           v
                       ) eqn:eshiftv;
                       rewrite eshiftv;
                       rewrite eshiftv in Hrewr; auto.
                   --- simpl. simpl in Hshift_mem2''. intros ? ? Hload.
                   pose proof (Memory.load_after_store
                                 mem2''
                                 (perm, cid_store, bid_store, offset_store)
                                 (Register.get r2 regs3'')
                                 mem3''
                                 (Permission.data,
                                  original_addr.1,
                                  original_addr.2,
                                  offset)
                              ) as Hmem2''_mem3''.
                   (* Notation NOT WORKING *)
                   destruct (Pointer.eq
                               (Permission.data,
                                original_addr.1,
                                original_addr.2, offset)
                               (perm, cid_store,
                                bid_store,
                                offset_store)
                            ) eqn:Heq.
                   +++ (* case true; derive a contradiction to eq_original_addr *)
                     destruct original_addr as [cidorig bidorig]. simpl in *.
                     destruct perm; first by auto. simpl in *.
                     apply andb_true_iff in Heq.
                     destruct Heq as [Heq _].
                     apply andb_true_iff in Heq as [contra1 contra2].
                     apply beq_nat_true in contra1.
                     apply beq_nat_true in contra2.
                     subst. by rewrite !eqxx in eq_original_addr.
                   +++ destruct Hshift_mem2'' as [_ Hrewr].
                       specialize (Hrewr offset v' Hload) as [v_exists Hv_exists].
                       eexists.
                       setoid_rewrite Hmem2''_mem3''; eauto.
            ++ intros cid Hcid. simpl.
               unfold Memory.store in *. simpl in *.
               destruct (Permission.eqb perm Permission.data); try discriminate.
               destruct (mem2'' cid_store) as [cMem|] eqn:ecMem; try discriminate.
               destruct (ComponentMemory.store cMem bid_store offset_store
                                               (Register.get r2 regs3''))
                 as [cMem'|] eqn:estore;
                 try discriminate.
               match goal with | H: Some _ = Some _ |- _ => inversion H end.
               rewrite setmE.
               destruct (cid == cid_store) eqn:e; rewrite e.
               ** assert (ComponentMemory.next_block cMem =
                          ComponentMemory.next_block cMem') as Hnextblockeq.
                  by eapply ComponentMemory.next_block_store_stable; eauto.
                  unfold
                  mem_of_part_not_executing_rel_original_and_recombined_at_internal
                    in *.
                  unfold omap, obind, oapp in *. rewrite <- Hnextblockeq.
                  assert (cid = cid_store). by apply/eqP. subst.
                  
                  match goal with
                  | H1: _ /\ _
                    |- _ => destruct H1 as [_ G] end.
                  erewrite <- G; auto.
                   by rewrite ecMem.
               ** unfold
                    mem_of_part_not_executing_rel_original_and_recombined_at_internal
                   in *.
                  by intuition.
               
               
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.

      + (* IJal *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eapply find_label_in_component_1; eauto.
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IJump *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eauto.
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBnz *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eapply find_label_in_procedure_1; eauto. 
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBnz *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IAlloc *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            find_and_invert_mergeable_states_well_formed;
              eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            (* ++ eapply Hgood_prog''.
               (* is_prefix *)
               unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** by rewrite E0_right.*)
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
          -- (* mem of part not executing *)
            unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal
              in *.

            (* key fact to prove is that the address that is allocated *)
            (* does not satisfy the condition \in domm (prog_interface c') *)
            match goal with
            | Halloc: Memory.alloc _ _ _ = _ |- _ =>
              pose proof Memory.component_of_alloc_ptr _ _ _ _ _ Halloc as Hptr_comp
            end.
            
            find_and_invert_mergeable_states_well_formed.
            pose proof CS.is_program_component_pc_notin_domm _ _ Hcomp.
            unfold ic in *. simpl in *.
            
            split.
            ++ intros original_addr.
              (* then, destruct original_addr equals the allocated address *)
              destruct (original_addr == (Pointer.component ptr, Pointer.block ptr))
                       eqn:Heqptr.
              **
                (* in the true case, rely on the key fact above (i.e., Hptr_comp)
                   to prove the goal vacuously. *)
                assert (original_addr = (Pointer.component ptr, Pointer.block ptr))
                  as Heqptr2. by apply/eqP.
                 destruct original_addr. intros Hcontra. inversion Heqptr2. subst.
                 simpl in *.
                 rewrite Hptr_comp in Hcontra.
                 match goal with
                 | H: _ = Pointer.component pc2'',
                      Hiface: prog_interface c = _
                   |- _ => rewrite <- H, <- Hiface in Hcontra
                 end.

                 match goal with
                 | Hnotin: is_true (negb _) (* too hacky *) |- _ =>
                   unfold negb in Hnotin;
                     by rewrite Hcontra in Hnotin
                 end.
              ** 
                (* in the false case, rely on some "load_after_alloc" lemma to
                   use the assumption in H4. *)

                unfold memory_shifts_memory_at_private_addr,
                memory_renames_memory_at_private_addr in *.
                intros Horiginal1 Horiginal2.
                split.
                --- intros offset v.

                match goal with
                | Halloc: Memory.alloc _ _ _ = _ |- _ =>
                  pose proof (Memory.load_after_alloc _ _ _ _ _
                                                      (Permission.data,
                                                       original_addr.1,
                                                       original_addr.2,
                                                       offset)
                                                      Halloc
                             ) as Hload_alloc
                end.
                simpl in *.

                rewrite Hload_alloc.
                +++ match goal with
                    | Hmem_invariant: _ /\ _ (* too hacky *) |- _ =>
                      destruct Hmem_invariant as [Hshift _]; eapply Hshift; eauto
                    end.
                +++ unfold not. intros Heq.
                    rewrite <- surjective_pairing in Heq. subst.
                      by rewrite eqxx in Heqptr.
                --- intros offset v.

                match goal with
                | Halloc: Memory.alloc _ _ _ = _ |- _ =>
                  pose proof (Memory.load_after_alloc _ _ _ _ _
                                                      (Permission.data,
                                                       original_addr.1,
                                                       original_addr.2,
                                                       offset)
                                                      Halloc
                             ) as Hload_alloc
                end.
                simpl in *.

                rewrite Hload_alloc.
                +++ match goal with
                    | Hmem_invariant: _ /\ _ (* too hacky *) |- _ =>
                      destruct Hmem_invariant as [Hshift _]; eapply Hshift; eauto
                    end.
                +++ unfold not. intros Heq.
                    rewrite <- surjective_pairing in Heq. subst.
                      by rewrite eqxx in Heqptr.
            ++ assert (Pointer.component pc2'' \in domm (prog_interface c') = false)
                as Hcontra.
               {
                 rewrite <- Hifc_cc', <- Hpccomp_s'_s'', Hpccomp_s'_s.
                 unfold negb in H5.
                 destruct (Pointer.component pc1 \in domm (prog_interface c)) eqn:e;
                   auto.
                 by rewrite e in H5.
               }

               unfold Memory.alloc in *.
               destruct (mem2'' (Pointer.component pc2'')) as [memC|] eqn:ememc;
                 try discriminate.
               destruct (ComponentMemory.alloc memC (Z.to_nat size))
                 as [memC' b] eqn:ememc'.
               
               match goal with | H: Some _ = Some _ |- _ =>
                                 inversion H as [H'] end.
               intros cid Hcid. rewrite setmE.
               destruct (cid == Pointer.component pc2'') eqn:ecid.
               ** assert (cid = Pointer.component pc2''). by apply/eqP.
                  subst. by rewrite Hcid in Hcontra.
               ** rewrite ecid.
                  by intuition.

        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.

          
      + pose proof CS.silent_step_non_inform_preserves_component _ _ _ Hstep23'' as
            Hpceq.
        simpl in Hpceq. by subst.
      + pose proof CS.silent_step_non_inform_preserves_component _ _ _ Hstep23'' as
            Hpceq.
        simpl in Hpceq. by subst.
  Qed.

End ThreewayMultisem1.

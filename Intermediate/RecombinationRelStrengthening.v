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



  
  (* RB: NOTE: Observe similarity with threeway_multisem_mergeable_program, use
     to replace this if possible. *)
  (* RB: TODO: [DynShare] Events will need to be related instead of identical,
     in addition to the usual existential trick we are using now. *)
  (*Lemma threeway_multisem_event_lockstep_program_mergeable
        s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, [e]) (CS.state_mem s2'', [e'']) p ->
  exists s2' e',
    mergeable_states p c p' c' n n'' s2 s2' s2''
                     (t1 ++ [e]) (t1' ++ [e']) (t1'' ++ [e'']).*)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12 Hstep12''. inversion Hmerge1. *)
  (*   apply mergeable_states_intro with (s0 := s0) (s0'' := s0'') (t := t ** [e]); *)
  (*     try assumption. *)
  (*   - eapply star_right; try eassumption; reflexivity. *)
  (*   - eapply star_right; try eassumption; reflexivity. *)
  (* Qed. *)
  (*Admitted.*) (* RB: TODO: Fix statement as needed, prove later. *)

  (* Ltac t_threeway_multisem_event_lockstep_program_step_call Hcomp1 Hmerge1 := *)
  (*   apply CS.Call; try assumption; *)
  (*   [ *)
  (*   | now apply (imported_procedure_recombination Hcomp1) *)
  (*   | (   (now apply (@genv_entrypoints_recombination_left _ c)) *)
  (*      || (now eapply (@genv_entrypoints_recombination_right _ c p'))) *)
  (*   ]; *)
  (*   (* Apply linking invariance and solve side goals (very similar to the *)
  (*      silent case, but slightly different setup). *) *)
  (*   [eapply execution_invariant_to_linking; try eassumption; *)
  (*     [ congruence *)
  (*     | apply linkable_implies_linkable_mains; congruence *)
  (*     | exact (is_program_component_in_domm Hcomp1 Hmerge1) *)
  (*     ] *)
  (*   ]. *)

  (* Ltac t_threeway_multisem_event_lockstep_program_step_return Hcomp1 Hmerge1 := *)
  (*   apply CS.Return; try congruence; (* [congruence] to cover context case. *) *)
  (*   eapply execution_invariant_to_linking; try eassumption; *)
  (*   [ congruence *)
  (*   | apply linkable_implies_linkable_mains; congruence *)
  (*   | exact (is_program_component_in_domm Hcomp1 Hmerge1) *)
  (*   ]. *)


  
  
  Lemma execution_invariant_to_linking_recombination
        gps mem regs pc gps' mem' regs' s'' t t' t'' instr :
    Pointer.component pc \notin domm (prog_interface c) ->
    mergeable_internal_states p c p' c' n n''
                              (gps, mem, regs, pc)
                              (gps', mem', regs', pc)
                              s'' t t' t'' ->
    executing (prepare_global_env prog) pc instr ->
    executing (prepare_global_env prog') pc instr.
  Proof.
    (*intros Hdomm Hmerge Hexec.
    inversion Hmerge
      as [Hwfp Hwfc Hwfp' Hwfc' [Hlinkable _]
          Hifacep Hifacec Hprog_is_closed Hprog_is_closed'' _ _ _ _ _ _ _ ].
    apply execution_invariant_to_linking with c; try assumption.
    - congruence.
    - inversion Hmerge. simpl in *.
      eapply CS.domm_partition; eauto.
      + by unfold CS.initial_state.
  Qed.*)
  Admitted.

  (* RB: TODO: Does it make sense to compact calls and returns into a unified
     solve tactic? *)
  (* AEK: This lemma is a "strengthening" lemma. It will be a bit involved to 
     establish from both the event-relatedness and the memory-relatedness
     of the non-executing part that mergeable_border_states holds.
   *)
  Theorem threeway_multisem_event_lockstep_program_step
          s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    traces_shift_each_other_option n n'' (rcons t1 e) (rcons t1'' e'') ->
    good_trace_extensional (left_addr_good_for_shifting n) (rcons t1 e) ->
    good_trace_extensional (left_addr_good_for_shifting n'') (rcons t1'' e'') ->
    (*mem_rel2 n n'' (CS.state_mem s2, t1 ++ [e]) 
      (CS.state_mem s2'', t1'' ++ [e'']) p ->*)
    (* TODO: Maybe we want to change this memory relation of the event to be
       directly the event relation.
       The event relation should be exposed from Renaming.v.
       This event relation is also needed in the back-translation proof.
     *)
    exists e' s2',
      Step sem'  s1'  [e' ] s2' /\
      (*mem_rel2 n n' (CS.state_mem s2, t1 ++ [e]) (CS.state_mem s2' , t1' ++ [e' ]) p /\*)
      (* The fact that the produced event e' is also related to e should follow
         from mergeable_border_states, i.e., the following conjunct here:
       *)
      mergeable_border_states p c p' c' n n'' s2 s2' s2''
                              (rcons t1 e) (rcons t1' e') (rcons t1'' e'').
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2''). *)
  Proof.
    intros Hcomp1 Hmerge1 Hstep12 Hstep12'' Hrel2 Hgood2 Hgood2''.
    inversion Hstep12. subst.
    inversion Hmerge1; find_and_invert_mergeable_states_well_formed.
    - match goal with
      | H: CS.step _ s1 t s2 |- _ =>
        eapply CS.non_inform_is_call_or_ret in H; eauto;
          destruct H as [[cid2 [pid2 [v [mem [reg [cid1 Hcall]]]]]]
                         |[cid [v [mem [reg [cid' Hret]]]]]]
      end.
      + subst. simpl in *.
        match goal with
        | H: [:: e] = [:: _] |- _ => inversion H
        end.
        subst.
        inversion Hrel2 as [? ? Hrel2']. subst.
        inversion Hrel2' as [  |
                               tpref1 e1 tpref1'' e1'' arg Hr1 Hr2 Hr3 Hr4 Harg
                                      Harg' Hgood Hgood'' Hr5 Hr6].
        * by find_nil_rcons.
        * apply rcons_inj in Hr5. apply rcons_inj in Hr6. inversion Hr5.
          inversion Hr6. subst. clear Hr5 Hr6.
          unfold match_events in *.
          destruct e'' as [cid pid v_call mem'' cid_callee |]; intuition. subst.
          destruct s1' as [[[s1'stk s1'mem] s1'reg] s1'pc].
          inversion Hstep12 as [? ? ? ? Hstep Hcontra]. subst.
          inversion Hstep; subst; simpl in Hcontra; try discriminate.
          inversion Hcontra. subst.
          assert (prog_interface prog = prog_interface prog') as
                      Hifcprog_prog'.
          {
            unfold prog, prog', program_link, prog_interface.
            destruct p. destruct c. destruct c'.
            simpl in *. by subst.
          }
          assert (exists b',
                     EntryPoint.get C' P
                                    (genv_entrypoints
                                       (prepare_global_env prog')) = Some b'
                 ) as [b' Hb'].
          {
            eapply genv_entrypoints_interface_some with (p := prog); eauto.
            - (* wf prog *)
              apply linking_well_formedness; eauto.
              unfold mergeable_interfaces in *. by intuition.
            - (* wf prog' *)
              apply linking_well_formedness; eauto.
              unfold mergeable_interfaces in *.
              match goal with | H: _ = prog_interface c' |- _ => rewrite <- H
              end.
                by intuition.
          }
          destruct s2'' as [[[s2''stk s2''mem] s2''reg] s2''pc].
          inversion Hstep12'' as [? ? ? ? Hstep'' Hcontra'']. subst.
          inversion Hstep''; subst; simpl in Hcontra''; try discriminate.
          inversion Hcontra''. subst.

          match goal with
          | H: regs_rel_of_executing_part _ _ _ _  |- _ =>
            inversion H as [Hregrel]
          end.
          simpl in Hregrel.
          pose proof Hregrel R_COM as Hrel_R_COM.

          assert (exists (call_arg : value) (s2' : CS.state),
                     Register.get R_COM s1'reg = call_arg /\
                     CS.step_non_inform (prepare_global_env prog')
                                        (s1'stk, s1'mem, s1'reg, s1'pc)
                                        [:: ECall
                                           (Pointer.component pc)
                                           P0
                                           call_arg
                                           s1'mem
                                           C'0
                                        ]
                                        s2')
            as [call_arg' [[[[s2'stk s2'mem] s2'reg] s2'pc]
                             [Hcall_arg' Hstep12']]].
          {
            eexists.
            eexists ((Pointer.inc s1'pc) :: s1'stk,
                   s1'mem,
                   Register.invalidate s1'reg,
                   _).
            split; first by intuition.
            eapply CS.Step_non_inform; eauto.
            ++ eapply (@CS.Call (prepare_global_env prog') _ _ _ _ _ _ _ _);
                 try eassumption.
               ** eapply (execution_invariant_to_linking p c c'); eauto; subst.
                  --- unfold mergeable_interfaces in *. by intuition.
                  --- match goal with
                      | H: _ = prog_interface c' |- _ => rewrite <- H end.
                      unfold mergeable_interfaces in *. by intuition.
                  --- simpl in *. subst.
                        by eapply mergeable_states_program_component_domm;
                          eauto.
                  --- match goal with
                      | H: CS.state_pc _  = _ |- _ => simpl in H; rewrite H
                      end.
                      eassumption.
               ** simpl in *.
                    by match goal with
                       | H: s1'pc = _ |- _ => rewrite H
                       end.
               ** simpl in *.
                  match goal with
                  | H1: s1'pc = _,
                        H2: prog_interface c = _
                    |- _ =>
                    rewrite H1; rewrite <- H2
                  end.
                  assumption.
               ** (** here, use the register relation (Hrel_R_COM) **)
                 by intuition.
            ++ simpl in *. subst. by eauto.
          }

          assert (CSInvariants.is_prefix
                    (Pointer.inc pc :: gps,
                     mem0,
                     Register.invalidate regs,
                     (Permission.code, C'0, b, Z0)
                    )
                    prog
                    (rcons
                       t1
                       (ECall (Pointer.component pc) P0
                              (Register.get R_COM regs)
                              mem0
                              C'0))
                 ) as Hpref_.
          {
            unfold CSInvariants.is_prefix.
            eapply star_right; try eassumption.
              by rewrite <- cats1.
          }

          
          do 2 eexists.
          split; first eassumption.
     
          -- apply mergeable_border_states_c'_executing.
             ++ constructor; auto; simpl.
                ** (* is_prefix *)
                  unfold CSInvariants.is_prefix.
                  eapply star_right; try eassumption.
                    by rewrite <- cats1.
                 
                ** (* is_prefix *)
                  unfold CSInvariants.is_prefix.
                  eapply star_right; try eassumption.
                    by rewrite <- cats1.
                  
                ** constructor; auto.
                   intros a Hshr.
                   inversion Hgood as [? Hgood_]; subst.
                   inversion Hshr as [? ? ? Hreach| ? ? ? ? Haddr'shr Hreach]; subst;
                   match goal with
                   | H11: rcons _ _ = rcons _ _ |- _ =>
                     apply rcons_inj in H11; inversion H11; subst; clear H11
                   end; simpl in *; clear Hshr.
                   ---
                     induction Hreach as [addr Hin |
                                          ? ? [cidloaded bidloaded]
                                            ? ? ? HcompMem Hin ]; subst.
                     +++
                       destruct (Register.get R_COM s1'reg)
                         as [|[[[perm cid] bid] off] |];
                         try by rewrite in_fset0 in Hin.
                       simpl in Hin.
                       destruct (perm =? Permission.data) eqn:eperm;
                         try by rewrite in_fset0 in Hin.
                       rewrite in_fset1 in Hin.
                       assert (perm = Permission.data). by apply beq_nat_true.
                       assert (addr = (cid, bid)). by apply/eqP.
                       subst. clear Hin eperm. simpl in *.
                       destruct Hrel_R_COM
                         as [Hshift | [Hshift [Hshift2 Hrewr
                                                       (*[Hshr1 Hshr2]*)
                            ]]];
                         unfold shift_value_option, rename_value_option,
                         rename_value_template_option,
                         rename_addr_option,
                         sigma_shifting_wrap_bid_in_addr,
                         sigma_shifting_lefttoright_addr_bid in *.
                       ***
                         destruct (Register.get R_COM regs)
                           as [| [[[perm' cid'] bid'] off'] |]; try discriminate.
                         destruct (perm' =? Permission.data) eqn:eperm'.
                         ----
                           destruct (sigma_shifting_lefttoright_option
                                       (n cid')
                                       (if cid' \in domm (prog_interface p)
                                        then n cid' else n'' cid')
                                       bid') as [bid'shift|] eqn:esigma;
                             rewrite esigma in Hshift;
                             try discriminate.
                           inversion Hshift. subst. clear Hshift.
                             by eapply sigma_lefttoright_Some_good; eauto.

                         ----
                           inversion Hshift. subst.
                             by rewrite <- beq_nat_refl in eperm'.
                             
                       ***
                         destruct (Register.get R_COM regs)
                           as [| [[[perm' cid'] bid'] off'] |]; try discriminate.
                         inversion Hrewr. subst. simpl in *.
                         assert (left_addr_good_for_shifting n (cid, bid))
                           as cidbidgood.
                         {
                           apply Hgood_.
                           constructor. constructor. simpl.
                           by rewrite in_fset1.
                         }
                         unfold left_addr_good_for_shifting in cidbidgood.
                         erewrite sigma_lefttoright_Some_spec in cidbidgood.
                         destruct cidbidgood as [? G].
                           by erewrite G in Hshift.
                           
                     +++
                       assert (
                           (exists ptro i : Block.offset,
                               ComponentMemory.load compMem bid i =
                               Some (Ptr (Permission.data,
                                          cidloaded, bidloaded, ptro)))
                         ) as [offloaded [off HcompLoad]].
                       {
                         eapply ComponentMemory.load_block_load.
                         erewrite Extra.In_in in Hin.
                         assumption.
                       }

                       (** Here, we need to use the goodness of program  *)
                       (** p or the goodness of program c (depending on  *)
                       (** whether cid \in domm (prog_interface p), I guess *)

                       (** In case it is, then we use the relation mem0 s1'mem *)
                       (** Otherwise, we use the relation s2''mem s1'mem       *)

                       (** In the first case, goal will follow from Hgood_prog *)
                       (** In the second case, it will follow from Hgood_prog''*)

                       unfold left_addr_good_for_shifting in IHHreach.
                       destruct (cid \in domm (prog_interface p)) eqn:Hcid;
                         rewrite Hcid in IHHreach.
                       ***
                         match goal with
                         | H: mem_of_part_executing_rel_original_and_recombined
                                p _ s1'mem n _ _ |- _ =>
                           inversion H as [s1'mem_rel_p _]
                         end.

                         specialize (s1'mem_rel_p (cid, bid) Hcid)
                           as [_ Hpriv2].

                         unfold Memory.load in Hpriv2. simpl in *.
                         rewrite HcompMem in Hpriv2.
                         specialize (Hpriv2 _ _ HcompLoad)
                           as [v [Hvload Hvshift]].
                         destruct (mem0 cid) as [compMem0|] eqn:HcompMem0;
                           try discriminate.

                         specialize (Hgood_prog _ _ Hpref_t) as [_ Ggood].
                         unfold Memory.load in Ggood.
                         specialize (Ggood
                                       mem0
                                       (Permission.data, cid, bid, off)
                                       (cid, bid)
                                       v
                                    ).
                         setoid_rewrite HcompMem0 in Ggood.
                         assert (left_value_good_for_shifting n v) as Hgoodv.
                         {
                           by apply Ggood; auto.
                         }

                         clear Ggood.

                         destruct v as [| [[[permv cidv] bidv] offv] |];
                           simpl in *;
                           destruct Hvshift as [ [Hvshift1 [Hvshift2 Hvshift3]]
                                               | Hvshift1];
                           try discriminate;

                           unfold 
                           rename_addr_option,
                           sigma_shifting_wrap_bid_in_addr,
                           sigma_shifting_lefttoright_addr_bid in *.

                         ----
                           inversion Hvshift3. subst. clear Hvshift3.
                           simpl in *.
                           erewrite sigma_lefttoright_Some_spec in Hgoodv.
                           destruct Hgoodv as [? contra].
                             by erewrite contra in Hvshift1.
                         ----
                           destruct (permv =? Permission.data) eqn:epermv.
                           ++++
                             destruct (sigma_shifting_lefttoright_option
                                         (n cidv)
                                         (if cidv \in domm (prog_interface p)
                                          then n cidv
                                          else n'' cidv) bidv) eqn:esigma;
                               rewrite esigma in Hvshift1; try discriminate.
                             inversion Hvshift1. subst.
                             rewrite sigma_lefttoright_Some_spec; eexists.
                               by erewrite
                                    sigma_shifting_lefttoright_Some_inv_Some;
                                 eauto.
                           ++++
                             inversion Hvshift1. subst.
                             by rewrite <- beq_nat_refl in epermv.

                       ***

                         (** Here, we need to assert---using Hcid, HcompMem,  *)
                         (** and Hpref_t'---that                              *)
                         (** cid \in domm (prog_interface c')                 *)

                         assert (cid \in domm (prog_interface c')) as Hcidc'.
                         {
                           admit.
                         }

                         (** With this assertion in hand, we need one more    *)
                         (** case distinction...                              *)

                         (** make a case distinction on the address           *)
                         (** (cid, bid), namely, we need to distinguish       *)
                         (** whether addr_shared_so_far (cid, bid) t1''       *)
                         (** -- case true:                                    *)
                         (**    we need to use Hshift_t''t'?                  *)
                         (** -- case false:                                   *)
                         (**    we can instantiate s1'mem_rel_c' and solve    *)
                         (**    the goal similarly to what we did the previous*)
                         (**    goal when we instantiated s1'mem_rel_p?       *)

                         specialize (Coq.Logic.Classical_Prop.classic 
                                       (addr_shared_so_far (cid, bid) t1'')
                                    ) as Hdestruct.

                         destruct Hdestruct as [Hshr | Hnotshr].

                         ----
                           inversion Hshift_t''t' as [? ? Hren]; subst.
                           inversion Hren as [| t'' e'' t' e' ? ? Ht''t' ? ? ?]; subst;
                             try by inversion Hshr; subst; find_nil_rcons.
                           specialize (Ht''t' _ Hshr) as
                               [He''e' [[cid' bid'] [ecid'bid' Hshrcid'bid']]].

                           match goal with
                           | H: mem_of_part_executing_rel_original_and_recombined
                                  p _ s1'mem n _ _ |- _ =>
                             inversion H as [_ [s1'mem_rel_p _]]
                           end.

                           inversion Hshift_tt' as [? ? Hrentt']; subst.
                           inversion Hrentt' as [| t e _t' _e' ? ? ? Htt' ? ? ?];
                             subst;
                             try by inversion Hshr; subst; find_nil_rcons.

                           match goal with
                           | Hrcons: rcons _ _ = rcons _ _ |- _ =>
                             apply rcons_inj in Hrcons; inversion Hrcons; subst;
                               clear Hrcons
                           end.
                           
                           specialize (Htt' _ Hshrcid'bid') as
                               [Hee' [[cid_t bid_t] [ecidbid_t Hshrcidbid_t]]].
                           
                           specialize (s1'mem_rel_p _ Hshrcidbid_t)
                             as [[addr'cid addr'bid] [eaddr' [mem0_s1'mem s1'mem_mem0]]].
                           unfold Memory.load in s1'mem_mem0. simpl in *.

                           unfold memory_shifts_memory_at_shared_addr,
                           memory_renames_memory_at_shared_addr,
                           sigma_shifting_wrap_bid_in_addr,
                           sigma_shifting_lefttoright_addr_bid in *.

                           destruct (sigma_shifting_lefttoright_option
                                       (n cid_t)
                                       (if cid_t \in domm (prog_interface p)
                                        then n cid_t else n'' cid_t) bid_t)
                                    eqn:ebid_t; rewrite ebid_t in ecidbid_t;
                             try discriminate.
                           inversion ecidbid_t; subst; clear ecidbid_t.

                           destruct (sigma_shifting_lefttoright_option
                                       (n'' cid)
                                       (if cid \in domm (prog_interface p)
                                        then n cid else n'' cid) bid)
                                    eqn:ebid; rewrite ebid in ecid'bid';
                             try discriminate.
                           inversion ecid'bid'; subst; clear ecid'bid'.

                           rewrite ebid_t in eaddr'.
                           inversion eaddr'; subst. clear eaddr'.

                           rewrite Hcid in ebid.
                           apply sigma_shifting_lefttoright_option_n_n_id in ebid.
                           subst.

                           rewrite HcompMem in s1'mem_mem0.
                           specialize (s1'mem_mem0 _ _ HcompLoad) as [v [_ ev]].
                           unfold rename_value_option, rename_value_template_option,
                           rename_addr_option in *.

                           destruct v as [| [[[vperm vcid] vbid] voff] |];
                             try discriminate.

                           destruct (vperm =? Permission.data) eqn:eperm.
                           ++++
                             destruct (sigma_shifting_lefttoright_option
                                         (n vcid)
                                         (if vcid \in domm (prog_interface p)
                                          then n vcid else n'' vcid) vbid) eqn:evbid;
                               rewrite evbid in ev; try discriminate.
                             inversion ev; subst.
                             apply sigma_lefttoright_Some_good in evbid.
                               by unfold right_block_id_good_for_shifting,
                                  left_block_id_good_for_shifting in *.
                           ++++
                             inversion ev; subst. by auto.
                           
                         ----
                           match goal with
                           | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                                  c' _ s1'mem n'' _ _ |- _ =>
                             inversion H as [s1'mem_rel_c' _]
                           end.

                         

                           specialize (s1'mem_rel_c' (cid, bid) Hcidc' Hnotshr)
                             as [_ Hpriv2].

                           unfold Memory.load in Hpriv2. simpl in *.
                           rewrite HcompMem in Hpriv2.
                           specialize (Hpriv2 _ _ HcompLoad)
                             as [v [Hvload Hvshift]].
                           destruct (s2''mem cid)
                             as [comps2''mem|] eqn:Hcomps2''mem;
                             try discriminate.

                           specialize (Hgood_prog'' _ _ Hpref_t'') as [_ Ggood].
                           unfold Memory.load in Ggood.
                           specialize (Ggood
                                         s2''mem
                                         (Permission.data, cid, bid, off)
                                         (cid, bid)
                                         v
                                      ).
                           setoid_rewrite Hcomps2''mem in Ggood.
                           assert (left_value_good_for_shifting n'' v) as Hgoodv.
                           {
                               by apply Ggood; auto.
                           }

                           clear Ggood.

                           destruct v as [| [[[permv cidv] bidv] offv] |];
                             simpl in *;
                             destruct Hvshift as [ [Hvshift1 [Hvshift2 Hvshift3]]
                                                 | Hvshift1];
                             try discriminate;

                             unfold 
                               rename_addr_option,
                             sigma_shifting_wrap_bid_in_addr,
                             sigma_shifting_lefttoright_addr_bid in *.

                           ++++
                             inversion Hvshift3. subst. clear Hvshift3.
                             simpl in *.
                             erewrite sigma_lefttoright_Some_spec in Hgoodv.
                             destruct Hgoodv as [? contra].
                               by erewrite contra in Hvshift1.
                           ++++
                             destruct (permv =? Permission.data) eqn:epermv.
                             ****
                               destruct (sigma_shifting_lefttoright_option
                                           (n'' cidv)
                                           (if cidv \in domm (prog_interface p)
                                            then n cidv
                                            else n'' cidv) bidv) eqn:esigma;
                                 rewrite esigma in Hvshift1; try discriminate.
                               inversion Hvshift1. subst.
                               rewrite sigma_lefttoright_Some_spec; eexists.
                                 by erewrite
                                      sigma_shifting_lefttoright_Some_inv_Some;
                                   eauto.
                             ****
                               inversion Hvshift1. subst.
                                 by rewrite <- beq_nat_refl in epermv.

                   ---
                     
                     inversion Hgood_t' as [? Haddr'good]; subst.
                     specialize (Haddr'good _ Haddr'shr).

                     induction Hreach as [addr Hin |
                                          ? ? [cidloaded bidloaded]
                                            ? ? ? HcompMem Hin ]; subst.
                     +++
                       rewrite in_fset1 in Hin.
                       assert (addr = addr'). by apply/eqP. by subst.
                     +++

                       assert (
                           (exists ptro i : Block.offset,
                               ComponentMemory.load compMem bid i =
                               Some (Ptr (Permission.data,
                                          cidloaded, bidloaded, ptro)))
                         ) as [offloaded [off HcompLoad]].
                       {
                         eapply ComponentMemory.load_block_load.
                         erewrite Extra.In_in in Hin.
                         assumption.
                       }

                       (** Chance to refactor case *** and *** into lemmas *)
                       (** because they are exactly the same as the corresp*)
                       (** cases from above.                               *)

                       
                       (** Here, apparently need to again use HcompMem and *)
                       (** Hpref_t' to infer that either                   *)
                       (** *** cid \in domm(prog_interface p) or           *)
                       (** *** cid \in domm(prog_interface c')             *)
                       (** The two cases should be very similar to the     *)
                       (** corresponding cases from above.                 *)

                       assert (cid \in domm (prog_interface p) \/
                                       cid \in domm (prog_interface c')
                              ) as Hdestruct.
                       {
                         admit.
                       }
                       unfold left_addr_good_for_shifting in *.
                       destruct Hdestruct as [Hcid | Hcid].
                       ***
                          rewrite Hcid in IHHreach.

                          match goal with
                          | H: mem_of_part_executing_rel_original_and_recombined
                                 p _ s1'mem n _ _ |- _ =>
                            inversion H as [s1'mem_rel_p _]
                          end.

                         specialize (s1'mem_rel_p (cid, bid) Hcid)
                           as [_ Hpriv2].

                         unfold Memory.load in Hpriv2. simpl in *.
                         rewrite HcompMem in Hpriv2.
                         specialize (Hpriv2 _ _ HcompLoad)
                           as [v [Hvload Hvshift]].
                         destruct (mem0 cid) as [compMem0|] eqn:HcompMem0;
                           try discriminate.

                         specialize (Hgood_prog _ _ Hpref_t) as [_ Ggood].
                         unfold Memory.load in Ggood.
                         specialize (Ggood
                                       mem0
                                       (Permission.data, cid, bid, off)
                                       (cid, bid)
                                       v
                                    ).
                         setoid_rewrite HcompMem0 in Ggood.
                         assert (left_value_good_for_shifting n v) as Hgoodv.
                         {
                           by apply Ggood; auto.
                         }

                         clear Ggood.

                         destruct v as [| [[[permv cidv] bidv] offv] |];
                           simpl in *;
                           destruct Hvshift as [ [Hvshift1 [Hvshift2 Hvshift3]]
                                               | Hvshift1];
                           try discriminate;

                           unfold 
                           rename_addr_option,
                           sigma_shifting_wrap_bid_in_addr,
                           sigma_shifting_lefttoright_addr_bid in *.

                         ----
                           inversion Hvshift3. subst. clear Hvshift3.
                           simpl in *.
                           erewrite sigma_lefttoright_Some_spec in Hgoodv.
                           destruct Hgoodv as [? contra].
                             by erewrite contra in Hvshift1.
                         ----
                           destruct (permv =? Permission.data) eqn:epermv.
                           ++++
                             destruct (sigma_shifting_lefttoright_option
                                         (n cidv)
                                         (if cidv \in domm (prog_interface p)
                                          then n cidv
                                          else n'' cidv) bidv) eqn:esigma;
                               rewrite esigma in Hvshift1; try discriminate.
                             inversion Hvshift1. subst.
                             rewrite sigma_lefttoright_Some_spec; eexists.
                               by erewrite
                                    sigma_shifting_lefttoright_Some_inv_Some;
                                 eauto.
                           ++++
                             inversion Hvshift1. subst.
                             by rewrite <- beq_nat_refl in epermv.

                       ***

                         assert (cid \in domm (prog_interface p) = false) as Hcid_p.
                         {
                           (**
                           Follows from Hcid and HcompMem (after we have proved some
                           partitioning lemma.
                            *)                            
                           admit.
                           
                         }
                         
                         specialize (Coq.Logic.Classical_Prop.classic 
                                       (addr_shared_so_far (cid, bid) t1'')
                                    ) as Hdestruct.

                         destruct Hdestruct as [Hshr | Hnotshr].

                         ----
                           inversion Hshift_t''t' as [? ? Hren]; subst.
                           inversion Hren as [| t'' e'' t' e' ? ? Ht''t' ? ? ?]; subst;
                             try by inversion Hshr; subst; find_nil_rcons.
                           specialize (Ht''t' _ Hshr) as
                               [He''e' [[cid' bid'] [ecid'bid' Hshrcid'bid']]].

                           match goal with
                           | H: mem_of_part_executing_rel_original_and_recombined
                                  p _ s1'mem n _ _ |- _ =>
                             inversion H as [_ [s1'mem_rel_p _]]
                           end.

                           inversion Hshift_tt' as [? ? Hrentt']; subst.
                           inversion Hrentt' as [| t e _t' _e' ? ? ? Htt' ? ? ?];
                             subst;
                             try by inversion Hshr; subst; find_nil_rcons.

                           match goal with
                           | Hrcons: rcons _ _ = rcons _ _ |- _ =>
                             apply rcons_inj in Hrcons; inversion Hrcons; subst;
                               clear Hrcons
                           end.
                           
                           specialize (Htt' _ Hshrcid'bid') as
                               [Hee' [[cid_t bid_t] [ecidbid_t Hshrcidbid_t]]].
                           
                           specialize (s1'mem_rel_p _ Hshrcidbid_t)
                             as [[addr'cid addr'bid] [eaddr' [mem0_s1'mem s1'mem_mem0]]].
                           unfold Memory.load in s1'mem_mem0. simpl in *.

                           unfold memory_shifts_memory_at_shared_addr,
                           memory_renames_memory_at_shared_addr,
                           sigma_shifting_wrap_bid_in_addr,
                           sigma_shifting_lefttoright_addr_bid in *.

                           destruct (sigma_shifting_lefttoright_option
                                       (n cid_t)
                                       (if cid_t \in domm (prog_interface p)
                                        then n cid_t else n'' cid_t) bid_t)
                                    eqn:ebid_t; rewrite ebid_t in ecidbid_t;
                             try discriminate.
                           inversion ecidbid_t; subst; clear ecidbid_t.

                           destruct (sigma_shifting_lefttoright_option
                                       (n'' cid)
                                       (if cid \in domm (prog_interface p)
                                        then n cid else n'' cid) bid)
                                    eqn:ebid; rewrite ebid in ecid'bid';
                             try discriminate.
                           inversion ecid'bid'; subst; clear ecid'bid'.

                           rewrite ebid_t in eaddr'.
                           inversion eaddr'; subst. clear eaddr'.
                           
                           rewrite Hcid_p in ebid.
                           apply sigma_shifting_lefttoright_option_n_n_id in ebid.
                           subst.

                           rewrite HcompMem in s1'mem_mem0.
                           specialize (s1'mem_mem0 _ _ HcompLoad) as [v [_ ev]].
                           unfold rename_value_option, rename_value_template_option,
                           rename_addr_option in *.

                           destruct v as [| [[[vperm vcid] vbid] voff] |];
                             try discriminate.

                           destruct (vperm =? Permission.data) eqn:eperm.
                           ++++
                             destruct (sigma_shifting_lefttoright_option
                                         (n vcid)
                                         (if vcid \in domm (prog_interface p)
                                          then n vcid else n'' vcid) vbid) eqn:evbid;
                               rewrite evbid in ev; try discriminate.
                             inversion ev; subst.
                             apply sigma_lefttoright_Some_good in evbid.
                               by unfold right_block_id_good_for_shifting,
                                  left_block_id_good_for_shifting in *.
                           ++++
                             inversion ev; subst. by auto.
                           
                         ----
                           match goal with
                           | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                                  c' _ s1'mem n'' _ _ |- _ =>
                             inversion H as [s1'mem_rel_c' _]
                           end.

                         

                           specialize (s1'mem_rel_c' (cid, bid) Hcid Hnotshr)
                             as [_ Hpriv2].

                           unfold Memory.load in Hpriv2. simpl in *.
                           rewrite HcompMem in Hpriv2.
                           specialize (Hpriv2 _ _ HcompLoad)
                             as [v [Hvload Hvshift]].
                           destruct (s2''mem cid)
                             as [comps2''mem|] eqn:Hcomps2''mem;
                             try discriminate.

                           specialize (Hgood_prog'' _ _ Hpref_t'') as [_ Ggood].
                           unfold Memory.load in Ggood.
                           specialize (Ggood
                                         s2''mem
                                         (Permission.data, cid, bid, off)
                                         (cid, bid)
                                         v
                                      ).
                           setoid_rewrite Hcomps2''mem in Ggood.
                           assert (left_value_good_for_shifting n'' v) as Hgoodv.
                           {
                             apply Ggood; auto.
                             by rewrite Hcid_p in IHHreach.
                           }

                           clear Ggood.

                           destruct v as [| [[[permv cidv] bidv] offv] |];
                             simpl in *;
                             destruct Hvshift as [ [Hvshift1 [Hvshift2 Hvshift3]]
                                                 | Hvshift1];
                             try discriminate;

                             unfold 
                               rename_addr_option,
                             sigma_shifting_wrap_bid_in_addr,
                             sigma_shifting_lefttoright_addr_bid in *.

                           ++++
                             inversion Hvshift3. subst. clear Hvshift3.
                             simpl in *.
                             erewrite sigma_lefttoright_Some_spec in Hgoodv.
                             destruct Hgoodv as [? contra].
                               by erewrite contra in Hvshift1.
                           ++++
                             destruct (permv =? Permission.data) eqn:epermv.
                             ****
                               destruct (sigma_shifting_lefttoright_option
                                           (n'' cidv)
                                           (if cidv \in domm (prog_interface p)
                                            then n cidv
                                            else n'' cidv) bidv) eqn:esigma;
                                 rewrite esigma in Hvshift1; try discriminate.
                               inversion Hvshift1. subst.
                               rewrite sigma_lefttoright_Some_spec; eexists.
                                 by erewrite
                                      sigma_shifting_lefttoright_Some_inv_Some;
                                   eauto.
                             ****
                               inversion Hvshift1. subst.
                                 by rewrite <- beq_nat_refl in epermv.

                       

                  (*************************************************************
                       specialize (Hgood_ )
                         destruct (perm' =? Permission.data) eqn:eperm'.
                         ----
                           
                           apply sigma_shifting_lefttoright_option_Some_sigma_shifting_righttoleft_option_Some in esigma.
                           Search _ Some "sigma".
                           
                           unfold left_addr_good_for_shifting.
                           unfold left_block_id_good_for_shifting.
                           Search _ "spec" Some.
                     (* argument is good *)
                     simpl in *. intros a Ha.
                     match goal with
                     | Hregs: regs_rel_of_executing_part _ s1'reg _ _ |- _ =>
                       inversion Hregs as [Hreg]
                     end.
                     unfold left_addr_good_for_shifting,
                     left_block_id_good_for_shifting.
                     destruct a as [acid abid].
                     
                     destruct (Hreg R_COM) as [Hshift _].
                     destruct (Register.get R_COM regs) as
                         [ i | [[[perm cid] bid] off] | ];
                       simpl in Hshift; rewrite <- Hshift in Ha; simpl in Ha.
                     +++ by rewrite in_fset0 in Ha.
                     +++ destruct (perm =? Permission.data) eqn:eperm.
                         *** unfold rename_addr in *.
                             destruct (
                                 sigma_shifting_addr n
                                                     (fun cid : nat =>
                                                        if cid \in domm (prog_interface p)
                                                        then n cid else n'' cid)
                                                     (cid, bid)
                               ) as [cidshift bidshift] eqn:eshift.
                             rewrite eshift in Ha.
                             unfold addr_of_value in Ha. rewrite eperm in Ha.
                             rewrite in_fset1 in Ha.
                             rewrite eqE in Ha. simpl in Ha.
                             pose proof
                                  left_addr_good_right_addr_good
                                  n
                                  (fun cid : nat =>
                                     if cid \in domm (prog_interface p)
                                     then n cid else n'' cid)
                                  (cid, bid)
                                  (cidshift, bidshift) as Hleft_right.
                             unfold rename_addr, right_addr_good_for_shifting,
                             right_block_id_good_for_shifting in *.
                             rewrite eshift in Hleft_right.
                             assert (acid == cidshift /\ abid == bidshift) as [h1 h2].
                               by apply/andP.
                               assert (acid = cidshift). by apply/eqP.
                               assert (abid = bidshift). by apply/eqP.
                               subst. clear h1 h2.
                               eapply Hleft_right; auto.
                               (* Remains to prove 
                                  left_addr_good_for_shifting n (cid, bid) *)
                               inversion Hgood2 as [| ? ? ? ? Harg_good Hrcons ].
                             ---- (* nil = rcons *)
                                 by find_nil_rcons.
                             ---- apply rcons_inj in Hrcons.
                                  inversion Hrcons. subst.
                                  eapply Harg_good. simpl.
                                  by rewrite eperm in_fset1.
                         *** unfold addr_of_value in Ha.
                               by rewrite eperm in_fset0 in Ha.
                     +++ by rewrite in_fset0 in Ha.
                   ***********************************************************)
                ** (* stack of p is related to the stack of recombined *)
                  simpl in *. subst.
                  inversion Hstep12'; subst.
                  destruct t; try discriminate.
                  match goal with
                  | Hstep : CS.step _ _ _ _ |- _ =>
                    inversion Hstep; subst; try discriminate
                  end.
                  apply stack_of_program_part_rel_stack_of_recombined_cons; auto.
                    by destruct
                         (Pointer.component (Pointer.inc pc)
                                            \in domm (prog_interface p)).
                ** (* stack of c' is related to the stack of recombined *)
                  simpl in *. subst.
                  inversion Hstep12'; subst.
                  destruct t; try discriminate.
                  match goal with
                  | Hstep : CS.step _ _ _ _ |- _ =>
                    inversion Hstep; subst; try discriminate
                  end.
                  
                  apply stack_of_program_part_rel_stack_of_recombined_cons; auto.
                  rewrite !Pointer.inc_preserves_component.
                  unfold CS.is_program_component, CS.is_context_component,
                  turn_of, CS.state_turn in *.
                  match goal with
                  | Hifc: _ = prog_interface c',
                          Hpc: _ = Pointer.component pc0 |- _ =>
                    rewrite <- Hifc; rewrite <- Hpc
                  end.
                  unfold negb in *.
                  destruct (Pointer.component pc \in domm (prog_interface c));
                    by intuition.
                ** inversion Hstep12'; subst.
                   destruct t; try discriminate.
                   match goal with
                   | Hstep : CS.step _ _ _ _ |- _ =>
                     inversion Hstep; subst; try discriminate
                   end.
                   simpl in *.
                   by
                   match goal with
                   | H: [_] = [_] |- _ => inversion H; subst
                   end.

                ** inversion Hstep12'; subst.
                   destruct t; try discriminate.
                   match goal with
                   | Hstep : CS.step _ _ _ _ |- _ =>
                     inversion Hstep; subst; try discriminate
                   end.
                   simpl in *.
                   by
                   match goal with
                   | H: [_] = [_] |- _ => inversion H; subst
                   end.

                  
                ** (* traces_shift_each_other *)
                  constructor. econstructor; eauto.
                  --- by inversion Hshift_tt'.
                      
                  --- intros addr Haddrshare_t1_call.
                       pose proof Hr2 addr Haddrshare_t1_call as
                          [Hren_n_n'' Hshrt1''].
                       destruct Hshrt1'' as [[cid'' bid''] [Haddr'' Haddr''shr]].
                       (*apply Hr3 in Haddr''shr as [Hinvren_n_n''
                                                     [[cidt bidt] [Haddrt Haddrtshr]]].*)
                       unfold sigma_shifting_wrap_bid_in_addr,
                       sigma_shifting_lefttoright_addr_bid in *.

                       destruct addr as [cid bid].
                       
                       (*destruct (sigma_shifting_lefttoright_option
                                   (n cidt) (n'' cidt) bidt) eqn:ebidt;
                         try discriminate.
                       inversion Haddrt; subst; clear Haddrt.*)

                       destruct (sigma_shifting_lefttoright_option
                                   (n cid) (n'' cid) bid) eqn:ebid; try discriminate.
                       inversion Haddr''; subst; clear Haddr''.

                       (*specialize (sigma_shifting_lefttoright_option_Some_inj
                                  _ _ _ _ _ ebid ebidt) as Hsubst.
                       subst. clear ebid.*)
                       
                       unfold event_renames_event_at_shared_addr in *.
                       
                       simpl in *.
                       
                       inversion Haddrshare_t1_call as
                           [? ? ? Hreach| ? ? ? ? Haddr'shr Hreach]; subst;
                         match goal with
                         | H11: rcons _ _ = rcons _ _ |- _ =>
                           apply rcons_inj in H11; inversion H11; subst; clear H11
                         end; simpl in *.
                      +++

                        (** We will probably need a lemma like this one when *)
                        (** proving the memory relation for the extension of *)
                        (** the traces.                                      *)
                        
                        (*********************************************************
                        assert (
                            desired:
                              forall mem mem' cidarg bidarg bidarg' cid bid bid',
                                Reachable mem (fset1 (cidarg, bidarg)) (cid, bid)  ->
                                (* (
                                   forall cid bid,
                                   addr_shared_so_far (cid, bid) t1 -> *)
                                memory_renames_memory_at_shared_addr
                                  n n'' (cid, bid) mem mem'
                                 (* ) *)
                                ->
                                sigma_shifting_lefttoright_option
                                  (n cid) (n'' cid) bid = Some bid' ->
                                sigma_shifting_lefttoright_option
                                  (n cidarg) (n'' cidarg) bidarg = Some bidarg' ->
                                Reachable mem' (fset1 (cidarg, bidarg')) (cid, bid')
                          ).
                        {
                          clear. intros ? ? ? ? ? ? ? ? Hreach Hren Hsigma1 Hsigma2.
                          remember (fset1 (cidarg, bidarg)) as arg.
                          remember (cid, bid) as cidbid.
                          revert cid bid Hsigma1 Hsigma2 Heqarg Heqcidbid.
                          induction Hreach as [[cid_ bid_] Hin |
                                               ? ? [cidloaded bidloaded]
                                                 ? ? ? HcompMem Hin ]; intros; subst.
                          - rewrite in_fset1 in Hin.
                            inversion Heqcidbid. subst.
                            assert (H:(cid, bid) = (cidarg, bidarg)). by apply/eqP.
                            inversion H. subst. clear H Hin.
                            apply Reachable_refl.
                            rewrite Hsigma1 in Hsigma2; inversion Hsigma2.
                              by rewrite in_fset1.
                          - inversion Heqcidbid. subst. clear Heqcidbid.
                            eapply Reachable_step; eauto.
                            +
                              eapply IHHreach; auto.
                              2: {
                                
                                }
                            
                            
                        }
                        SearchAbout bid.
                        **************************************************************)
                        inversion Hreach as [addr Hin |
                                             ? ? [cidloaded bidloaded]
                                               ? ? ? HcompMem Hin ]. 
                        ***
                          subst.
                          (** Here, we will need to use the register relation *)
                          (** between regs and s1'reg                         *)
                          destruct (Register.get R_COM regs)
                            as [|[[[perm cid] bid_regs] off] |];
                            try by rewrite in_fset0 in Hin.
                          simpl in Hin.
                          destruct (perm =? Permission.data) eqn:eperm;
                            try by rewrite in_fset0 in Hin.
                          rewrite in_fset1 in Hin.
                          assert (perm = Permission.data). by apply beq_nat_true.
                          assert ((cid'', bid) = (cid, bid_regs)) as Hsubst. by apply/eqP.
                          inversion Hsubst.
                          subst. clear Hin eperm Hsubst. simpl in *.

                          unfold memory_renames_memory_at_shared_addr,
                          sigma_shifting_wrap_bid_in_addr,
                          sigma_shifting_lefttoright_addr_bid in *.

                          destruct Hren_n_n'' as [addr'' [Haddr'' Hmem_mem'']].

                          destruct (sigma_shifting_lefttoright_option
                                      (n cid) (n'' cid) bid_regs) as [bid_regs''|]
                                                                       eqn:ebid_regs;
                            try discriminate.


                          assert (left_block_id_good_for_shifting
                                    (n cid) bid_regs) as Hspec.
                            by rewrite sigma_lefttoright_Some_spec; eexists; eauto.
                            
                            assert (exists bid',
                                       sigma_shifting_lefttoright_option
                                         (n cid)
                                         (if cid \in domm (prog_interface p)
                                          then n cid else n'' cid) bid_regs
                                       = Some bid') as G.
                              by rewrite <- sigma_lefttoright_Some_spec.
                              destruct G as [bid' G'].

                          inversion Haddr''; subst; clear Haddr''.
                          split.
                          ----
                            eexists. split.
                            ++++
                              setoid_rewrite G'.
                              reflexivity.
                            ++++
                              split.
                              ****
                                intros ? ? Hload.
                                simpl in *.

                                assert (cid \in domm(prog_interface p) \/
                                        cid \in domm(prog_interface c')
                                       ) as [Hcid | Hcid].
                                {
                                  (** Follows from Hload *)
                                  admit.
                                }

                                -----
                                rewrite Hcid in G'.
                                apply sigma_shifting_lefttoright_option_n_n_id in G'.
                                subst.
                                
                                match goal with
                                | H: mem_of_part_executing_rel_original_and_recombined
                                       p _ s1'mem n _ _ |- _ =>
                                  inversion H as [s1'mem_rel_p _]
                                end.
                                
                                specialize (s1'mem_rel_p (cid, bid_regs) Hcid)
                                  as [Hpriv1 _].

                                specialize (Hpriv1 _ _ Hload).

                                unfold rename_value_option, rename_value_template_option,
                                sigma_shifting_wrap_bid_in_addr,
                                sigma_shifting_lefttoright_addr_bid,
                                rename_addr_option in *.

                                destruct v as [| [[[vperm vcid] vbid] voff] |];
                                  try by eexists; split; eauto.

                                destruct (vperm =? Permission.data) eqn:eperm;
                                  try by eexists; split; eauto.

                                destruct (sigma_shifting_lefttoright_option
                                            (n vcid)
                                            (if vcid \in domm (prog_interface p)
                                             then n vcid else n'' vcid) vbid)
                                  as [vbid'|] eqn:evbid; rewrite evbid;
                                  rewrite evbid in Hpriv1.
                                +++++
                                  by eexists; split; eauto.
                                +++++
                                (** Obtain a contradiction to Hgood_prog *)
                                
                                specialize (Hgood_prog _ _ Hpref_) as [_ G].
                                simpl in *.
                                specialize (G _ _ _ _
                                              Logic.eq_refl
                                              Hload
                                              Logic.eq_refl
                                              Hspec
                                           ) as contra.
                                unfold left_value_good_for_shifting,
                                left_addr_good_for_shifting in *.
                                rewrite eperm in contra.
                                erewrite sigma_lefttoright_Some_spec, evbid in contra.
                                by destruct contra.

                                -----
                                  (** Here, have as assumption a load from mem0. *)
                                  (** Goal is to have a related load from s1'mem *)
                                  (** Should be able to use the "shared" part of *)
                                  (** the memory relation mem0_s1'mem.           *)
                                  (** To use it, establish that (cid, bid_regs)  *)
                                  (** must have been shared on trace t1.         *)
                                  (** This can be done by inverting              *)
                                  (** CSInvariants.wf_ptr_wrt_cid_t              *)
                                  (** (The left case is a contra to Hcid.)       *)
                                  (** (The right case is the "shared_so_far"..)  *)

                                  (** Obtain CSInvariants.wf_ptr_wrt_cid_t from  *)
                                  (** "wf_reg" and the "Register.get" precond of *)
                                  (** Hstep12.                                   *)
                                  admit.

                              ****
                                (** This is dual to the parallel case.          *)
                                (** Just make sure to destruct s1'mem_rel_p     *)
                                (** as [_ Hpriv2] instead of [Hpriv1 _]         *)
                                admit.
                                
                          ----
                            assert (left_block_id_good_for_shifting
                                    (n cid) bid_regs) as Hspec_bid.
                            by rewrite sigma_lefttoright_Some_spec; eexists; eauto.
                            
                            assert (exists bid',
                                       sigma_shifting_lefttoright_option
                                         (n cid)
                                         (if cid \in domm (prog_interface p)
                                          then n cid else n'' cid) bid_regs
                                       = Some bid') as G.
                              by rewrite <- sigma_lefttoright_Some_spec.
                              destruct G as [bid_t1' G''].
                              eexists; split.
                              ++++ by setoid_rewrite G''.
                              ++++
                                (** Probably by inverting an existing sharing *)
                                (** namely, inverting Haddr''shr              *)
                                (** Inverting sharing gives us "Reachability" *)
                                (** assumptions. Reachability assumptions     *)
                                (** mention a load from the memory (except    *)
                                (** for the refl case).                       *)
                                (** The load from memory can be helpful to    *)
                                (** instantiate memory relations.             *)

                                (** Will probably be somewhat similar to the  *)
                                (** previous ---- children.                   *)
                                admit.
                                
                        (***********************************************
                            match goal with
                            | H: mem_of_part_executing_rel_original_and_recombined
                                   p _ s1'mem n _ _ |- _ =>
                              inversion H as [_ [s1'mem_rel_p _]]
                            end.
                            
                            
                            split; first eexists. split
                            
                            destruct (Register.get R_COM )
                              as [| [[[perm' cid'] bid'] off'] |]; try discriminate.
                         destruct (perm' =? Permission.data) eqn:eperm'.
                         ----
                           destruct (sigma_shifting_lefttoright_option
                                       (n cid')
                                       (if cid' \in domm (prog_interface p)
                                        then n cid' else n'' cid')
                                       bid') as [bid'shift|] eqn:esigma;
                             rewrite esigma in Hshift;
                             try discriminate.
                           inversion Hshift. subst. clear Hshift.
                             by eapply sigma_lefttoright_Some_good; eauto.

                         ----
                           inversion Hshift. subst.
                             by rewrite <- beq_nat_refl in eperm'.
                             *****************************************************)
                        ***
                          subst cid'' bid.
                          assert (
                           (exists ptro i : Block.offset,
                               ComponentMemory.load compMem bid0 i =
                               Some (Ptr (Permission.data,
                                          cidloaded, bidloaded, ptro)))
                            ) as [offloaded [off HcompLoad]].
                          {
                            eapply ComponentMemory.load_block_load.
                            erewrite Extra.In_in in HcompMem.
                            assumption.
                          }

                          assert (
                            mem0Load:
                              Memory.load mem0 (Permission.data, cid, bid0, off) =
                              Some (Ptr (Permission.data,
                                         cidloaded,
                                         bidloaded,
                                         offloaded))
                          ).
                          {
                            unfold Memory.load. simpl.
                            by rewrite H11. (* mem0 cid = Some compMem *)
                          }
                          
                          
                          assert (
                              mem0_s1'mem_cidbidloaded:
                                memory_renames_memory_at_shared_addr
                                  n
                                  (fun cid0 : nat =>
                                     if cid0 \in domm (prog_interface p)
                                     then n cid0 else n'' cid0)
                                  (cidloaded, bidloaded) mem0 s1'mem
                            ).
                          {
                            unfold memory_renames_memory_at_shared_addr,
                            sigma_shifting_wrap_bid_in_addr,
                            sigma_shifting_lefttoright_addr_bid in *.
                            destruct Hren_n_n'' as [addr' [Haddr' Hnn'']].
                            destruct (sigma_shifting_lefttoright_option
                                        (n cidloaded)
                                        (n'' cidloaded) bidloaded)
                              as [bidloaded''|] eqn:ebidloaded;
                              try discriminate.
                            assert (left_block_id_good_for_shifting
                                      (n cidloaded) bidloaded) as bidloaded_good.
                            {
                                by rewrite sigma_lefttoright_Some_spec; eexists; eauto.
                            }
                            erewrite sigma_lefttoright_Some_spec in bidloaded_good.
                            destruct bidloaded_good as [bidloaded' ebidloaded'].
                            eexists.
                            erewrite ebidloaded'.
                            split; eauto.
                            split.
                            ++++
                              intros ? ? Hload.
                              destruct Hnn'' as [Hnn''1 _].
                              specialize (Hnn''1 _ _ Hload) as [v' [Hload' Hv]].
                              simpl in *.
                              match goal with
                              | H: mem_of_part_executing_rel_original_and_recombined
                                     p mem0 s1'mem n _ t1 |- _ =>
                                destruct H as [Hpriv_rel [Hshr_rel _]]
                              end.
                              unfold memory_shifts_memory_at_private_addr,
                              memory_renames_memory_at_private_addr,
                              memory_shifts_memory_at_shared_addr,
                              memory_renames_memory_at_shared_addr,
                              sigma_shifting_wrap_bid_in_addr,
                              sigma_shifting_lefttoright_addr_bid
                                in *.

                              destruct (cidloaded \in domm (prog_interface p))
                                       eqn:Hcidloaded.
                              ****
                                rewrite Hcidloaded in ebidloaded'.
                                apply sigma_shifting_lefttoright_option_n_n_id
                                  in ebidloaded'.
                                subst.

                                specialize (Hpriv_rel (cidloaded, bidloaded) Hcidloaded)
                                  as [Hpriv_rel_bidloaded _].
                                specialize (Hpriv_rel_bidloaded _ _ Hload).
                                
                                unfold rename_value_option,
                                rename_value_template_option, rename_addr_option in *.
                                
                                destruct v as [| [[[permv cidv] bidv] offv] |];
                                  try by eexists; eauto.
                                
                                destruct (permv =? Permission.data) eqn:epermv;
                                  eauto.

                                destruct (sigma_shifting_lefttoright_option
                                            (n cidv) (n'' cidv) bidv) eqn:esigmav;
                                  try discriminate.

                                assert (left_block_id_good_for_shifting
                                          (n cidv) bidv) as bidvgood.
                                {
                                    by rewrite sigma_lefttoright_Some_spec; eexists; eauto.
                                }

                                erewrite sigma_lefttoright_Some_spec in bidvgood.
                                destruct bidvgood as [bidv' Hrewr].
                                erewrite Hrewr in Hpriv_rel_bidloaded.
                                erewrite Hrewr.
                                  by eexists; split; eauto.

                              ****
                                rewrite Hcidloaded in ebidloaded'.
                                
                                assert (cidloaded \in domm (prog_interface c'))
                                  as Hcidloaded_c'.
                                {
                                  (** Follows from Hcidloaded and Hload *)
                                  admit.
                                }
                                
                                specialize (Coq.Logic.Classical_Prop.classic 
                                              (addr_shared_so_far
                                                 (cidloaded, bidloaded) t1)
                                           ) as [Hcidloaded_shr | Hcidloaded_notshr].
                                -----
                                  specialize (Hshr_rel _ Hcidloaded_shr)
                                  as [cidbidloaded' [Hcidbidloaded' [Hmem0s1'mem _]]].

                                specialize (Hmem0s1'mem _ _ Hload) as
                                    [vs1'mem [Hloads1'mem Hvs1'mem]].

                                destruct (sigma_shifting_lefttoright_option
                                            (n cidloaded)
                                            (if cidloaded \in domm (prog_interface p)
                                             then n cidloaded
                                             else n'' cidloaded) bidloaded)
                                         eqn:ebidloaded2;
                                  rewrite ebidloaded2 in Hcidbidloaded';
                                  try discriminate.
                                inversion Hcidbidloaded'; subst.

                                rewrite Hcidloaded in ebidloaded2.
                                rewrite ebidloaded2 in ebidloaded'.
                                inversion ebidloaded'. subst.
                                
                                  by eexists; split; eauto.

                                  -----
                                    inversion Haddr'; subst.
                                  match goal with
                                  | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                                         c' s2''mem s1'mem n''  _ t1'' |- _ =>
                                    inversion H as [Hs1'mem_s2''mem _]
                                  end.
                                  
                                  assert (~ addr_shared_so_far
                                            (cidloaded, bidloaded'') t1'') as Hnotshr.
                                  {
                                    (** Should follow from Hcidloaded_notshr     *)
                                    (** together with Hshift_tt' and Hshift_t''t'*)
                                    admit.
                                  }

                                  specialize (Hs1'mem_s2''mem
                                                (cidloaded, bidloaded'')
                                                Hcidloaded_c'
                                                Hnotshr
                                             ) as [Hpriv_rel'' _].
                                  specialize (Hpriv_rel'' _ _ Hload').
                                  unfold memory_shifts_memory_at_private_addr,
                                  memory_renames_memory_at_private_addr,
                                  sigma_shifting_wrap_bid_in_addr,
                                  sigma_shifting_lefttoright_addr_bid,
                                  rename_value_option,
                                  rename_value_template_option,
                                  rename_addr_option
                                    in *.

                                  rewrite ebidloaded' in ebidloaded.
                                  inversion ebidloaded; subst.
                                  
                                  destruct v as [| [[[permv cidv] bidv] offv] |];
                                    inversion Hv as [Hv']; subst;
                                      try by eexists; split; eauto.

                                  destruct (permv =? Permission.data) eqn:epermv.
                                  +++++
                                    destruct (sigma_shifting_lefttoright_option
                                                (n cidv) (n'' cidv) bidv)
                                    as [bidv''|] eqn:ebidv'';
                                    try discriminate.
                                  assert (left_block_id_good_for_shifting
                                            (n cidv) bidv) as bidv_good.
                                  {
                                      by rewrite sigma_lefttoright_Some_spec;
                                        eexists; eauto.
                                  }
                                  erewrite sigma_lefttoright_Some_spec in bidv_good.
                                  destruct bidv_good as [bidv' ebidv'].
                                  erewrite ebidv'.
                                  inversion Hv'. subst.
                                  rewrite epermv in Hpriv_rel''.
                                  destruct (
                                      sigma_shifting_lefttoright_option
                                        (n'' cidv)
                                        (if cidv \in domm (prog_interface p)
                                         then n cidv else n'' cidv) bidv''
                                    ) eqn:ebidv'2; rewrite ebidv'2 in Hpriv_rel'';
                                    simpl in *;
                                    destruct (cidv \in domm (prog_interface p))
                                             eqn:ecidv;
                                    rewrite ecidv in ebidv';
                                    rewrite ecidv in ebidv'2.
                                  *****
                                    apply sigma_shifting_lefttoright_option_n_n_id
                                    in ebidv'.
                                  subst.
                                  apply sigma_shifting_lefttoright_Some_inv_Some in
                                      ebidv''.
                                  rewrite ebidv'' in ebidv'2.
                                  inversion ebidv'2. by eexists; split; eauto.
                                  *****
                                    apply sigma_shifting_lefttoright_option_n_n_id
                                    in ebidv'2.
                                  subst.
                                  rewrite ebidv' in ebidv''.
                                  inversion ebidv''. by eexists; split; eauto.
                                  *****
                                    apply sigma_shifting_lefttoright_Some_inv_Some in
                                      ebidv''.
                                    by rewrite ebidv'' in ebidv'2.
                                    *****
                                      rewrite ebidv'' in ebidv'.
                                    inversion ebidv'. subst.
                                    apply sigma_shifting_lefttoright_Some_inv_Some in
                                        ebidv''.
                                    assert (left_block_id_good_for_shifting
                                              (n'' cidv) bidv') as bidv'_good.
                                    {
                                        by rewrite sigma_lefttoright_Some_spec;
                                          eexists; eauto.
                                    }
                                    erewrite sigma_lefttoright_Some_spec in bidv'_good.
                                    destruct bidv'_good as [bidv'_ ebidv'_].
                                      by erewrite ebidv'_ in ebidv'2.
                                      
                                      +++++
                                        inversion Hv'. subst.
                                      rewrite epermv in Hpriv_rel''.
                                        by eexists; split; eauto.

                            ++++
                              intros ? ? Hload.
                              (**********************************
                              destruct Hnn'' as [Hnn''1 _].
                              specialize (Hnn''1 _ _ Hload) as [v' [Hload' Hv]].
                               **********************************)
                              simpl in *.
                              match goal with
                              | H: mem_of_part_executing_rel_original_and_recombined
                                     p mem0 s1'mem n _ t1 |- _ =>
                                destruct H as [Hpriv_rel [Hshr_rel _]]
                              end.
                              unfold memory_shifts_memory_at_private_addr,
                              memory_renames_memory_at_private_addr,
                              memory_shifts_memory_at_shared_addr,
                              memory_renames_memory_at_shared_addr,
                              sigma_shifting_wrap_bid_in_addr,
                              sigma_shifting_lefttoright_addr_bid
                                in *.

                              destruct (cidloaded \in domm (prog_interface p))
                                       eqn:Hcidloaded.

                              ****
                                rewrite Hcidloaded in ebidloaded'.
                                apply sigma_shifting_lefttoright_option_n_n_id
                                  in ebidloaded'.
                                subst.

                                specialize (Hpriv_rel (cidloaded, bidloaded) Hcidloaded)
                                  as [_ Hpriv_rel_bidloaded].
                                specialize (Hpriv_rel_bidloaded _ _ Hload)
                                  as [v [vload vrel]].
                                
                                unfold rename_value_option,
                                rename_value_template_option, rename_addr_option in *.
                                
                                destruct v as [| [[[permv cidv] bidv] offv] |].

                                -----
                                  destruct vrel as [[? ?] | esubst ]; try discriminate.
                                  by eexists; split; eauto.
                                  -----
                                    destruct (permv =? Permission.data) eqn:epermv.
                                  +++++
                                    
                                    destruct (sigma_shifting_lefttoright_option
                                                (n cidv)
                                                (if cidv \in domm (prog_interface p)
                                                 then n cidv else n'' cidv) bidv)
                                    eqn:esigmav; rewrite esigmav in vrel.

                                  *****
                                    destruct vrel as [[? ?] | esubst];
                                    try discriminate.
                                  inversion esubst. subst.
                                  eexists; split; first exact vload.
                                  simpl. by rewrite epermv esigmav.
                                  *****
                                    (** Obtain a contradiction to Hgood_prog *)
                                    
                                    specialize (Hgood_prog _ _ Hpref_) as [_ G].
                                  simpl in *.
                                  assert (left_addr_good_for_shifting
                                            n
                                            (cidloaded, bidloaded)) as loadedgood.
                                  {
                                    unfold left_addr_good_for_shifting.
                                    rewrite sigma_lefttoright_Some_spec.
                                      by eexists; eauto.
                                  }
                                  specialize (G _ _ _ _
                                                Logic.eq_refl
                                                vload
                                                Logic.eq_refl
                                                loadedgood
                                             ) as contra.
                                  unfold left_value_good_for_shifting,
                                  left_addr_good_for_shifting in *.
                                  rewrite epermv in contra.
                                  erewrite sigma_lefttoright_Some_spec, esigmav
                                    in contra. by destruct contra.
                                  +++++
                                    destruct vrel as [[? ?] | esubst ]; try discriminate.
                                  eexists; split; eauto. simpl. by rewrite epermv.
                                  -----
                                    destruct vrel as [[? ?] | esubst ];
                                    try discriminate. by eexists; split; eauto.
                              ****
                                rewrite Hcidloaded in ebidloaded'.
                                rewrite ebidloaded in ebidloaded'.
                                inversion ebidloaded'. subst.
                                
                                assert (cidloaded \in domm (prog_interface c'))
                                  as Hcidloaded_c'.
                                {
                                  (** Follows from Hcidloaded and Hload *)
                                  admit.
                                }
                                
                                specialize (Coq.Logic.Classical_Prop.classic 
                                              (addr_shared_so_far
                                                 (cidloaded, bidloaded) t1)
                                           ) as [Hcidloaded_shr | Hcidloaded_notshr].
                                -----
                                  specialize (Hshr_rel _ Hcidloaded_shr)
                                  as [cidbidloaded' [Hcidbidloaded' [_ Hmem0s1'mem]]].

                                rewrite Hcidloaded in Hcidbidloaded'.

                                destruct (sigma_shifting_lefttoright_option
                                            (n cidloaded) (n'' cidloaded) bidloaded)
                                         eqn:esigma;
                                  try discriminate.
                                inversion Hcidbidloaded'. subst.
                                inversion ebidloaded. inversion Haddr'. subst.
                                
                                specialize (Hmem0s1'mem _ _ Hload) as
                                    [vs1'mem [Hloads1'mem Hvs1'mem]].

                                  by eexists; split; eauto.

                                  -----
                                    inversion Haddr'; subst.
                                  match goal with
                                  | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                                         c' s2''mem s1'mem n''  _ t1'' |- _ =>
                                    inversion H as [Hs1'mem_s2''mem _]
                                  end.
                                  
                                  assert (~ addr_shared_so_far
                                            (cidloaded, bidloaded') t1'') as Hnotshr.
                                  {
                                    (** Should follow from Hcidloaded_notshr     *)
                                    (** together with Hshift_tt' and Hshift_t''t'*)
                                    (** and ebidloaded                           *)
                                    admit.
                                  }
                                  
                                  specialize (Hs1'mem_s2''mem
                                                (cidloaded, bidloaded')
                                                Hcidloaded_c'
                                                Hnotshr
                                             ) as [_ Hpriv_rel''].
                                  specialize (Hpriv_rel'' _ _ Hload).
                                  unfold memory_shifts_memory_at_private_addr,
                                  memory_renames_memory_at_private_addr,
                                  sigma_shifting_wrap_bid_in_addr,
                                  sigma_shifting_lefttoright_addr_bid,
                                  rename_value_option,
                                  rename_value_template_option,
                                  rename_addr_option
                                    in *.

                                  destruct Hpriv_rel'' as [v [vload vrel]].
                                  destruct Hnn'' as [_ mem0s2''mem].

                                  specialize (mem0s2''mem _ _ vload)
                                    as [vG [vGload vGrel]].
                                  exists vG; split; auto.
                                  
                                  destruct vG as [| [[[permv cidv] bidv] offv] |];
                                    inversion vGrel as [Hv']; subst;
                                      try by eexists; split; eauto.

                                  +++++
                                    by destruct vrel as [[? ?]|].
                                  +++++
                                    destruct (permv =? Permission.data) eqn:epermv.
                                  *****
                                    destruct (sigma_shifting_lefttoright_option
                                                (n cidv) (n'' cidv) bidv)
                                    as [bidv'|] eqn:esigma; try discriminate.
                                  inversion Hv'. subst.
                                  rewrite epermv in vrel.
                                  apply sigma_shifting_lefttoright_Some_inv_Some
                                    in esigma.
                                  assert (
                                      left_block_id_good_for_shifting (n'' cidv) bidv'
                                    ) as bidv'good. by rewrite
                                                         sigma_lefttoright_Some_spec;
                                                      eexists; eauto.
                                  erewrite sigma_lefttoright_Some_spec in bidv'good.
                                  destruct bidv'good as [? rewr].
                                  erewrite rewr in vrel.
                                  destruct vrel as [[? ?] | eq]; try discriminate.
                                  inversion eq. subst.
                                  destruct (cidv \in domm (prog_interface p))
                                           eqn:ecidv;
                                    rewrite ecidv in rewr; rewrite ecidv.
                                  ------
                                    rewrite rewr in esigma. inversion esigma. subst.
                                  apply sigma_shifting_lefttoright_Some_inv_Some
                                    in rewr.
                                  assert (bidvgood: left_block_id_good_for_shifting
                                                      (n cidv) bidv).
                                    by rewrite
                                         sigma_lefttoright_Some_spec;
                                      eexists; eauto.
                                    erewrite sigma_lefttoright_Some_spec in bidvgood.
                                    destruct bidvgood as [? G].
                                    erewrite G.
                                    apply sigma_shifting_lefttoright_option_n_n_id in G.
                                      by subst.
                                      ------
                                        apply sigma_shifting_lefttoright_option_n_n_id
                                        in rewr.
                                      subst.
                                      apply sigma_shifting_lefttoright_Some_inv_Some
                                        in esigma.
                                      assert (bidvgood: left_block_id_good_for_shifting
                                                          (n cidv) bidv).
                                        by rewrite
                                             sigma_lefttoright_Some_spec;
                                          eexists; eauto.
                                        erewrite sigma_lefttoright_Some_spec in bidvgood.
                                        destruct bidvgood as [? G].
                                        erewrite G.
                                        rewrite esigma in G. by inversion G.
                                        *****
                                          inversion Hv'; subst.
                                        rewrite epermv in vrel. by destruct vrel as [[? ?]|].
                                        +++++
                                          by destruct vrel as [[? ?]|].

                          }
                          split.
                          ----
                            exact mem0_s1'mem_cidbidloaded.
                              

                          ----
                            (****************************************************
                            assert (bidgood: left_block_id_good_for_shifting
                                               (n cidloaded) bidloaded
                                   ). by rewrite
                                           sigma_lefttoright_Some_spec;
                                        eexists; eauto.
                            erewrite sigma_lefttoright_Some_spec in bidgood.
                            destruct bidgood as [bid' G].
                            erewrite G. eexists; split; eauto.

                            match goal with
                            | H: mem_of_part_executing_rel_original_and_recombined
                                   p mem0 s1'mem n _ t1 |- _ =>
                              inversion H as [Hpriv_rel [Hshr_rel _]]
                            end.
                            
                            eapply reachable_from_previously_shared; simpl.
                            2: {
                              eapply Reachable_step.

                              

                              
                              
                            }
                            
                            (* SearchAbout bidloaded. *)
                            **********************************************************)
                                    

                     +++
                       assert (
                           (exists ptro i : Block.offset,
                               ComponentMemory.load compMem bid i =
                               Some (Ptr (Permission.data,
                                          cidloaded, bidloaded, ptro)))
                         ) as [offloaded [off HcompLoad]].
                       {
                         eapply ComponentMemory.load_block_load.
                         erewrite Extra.In_in in Hin.
                         assumption.
                       }

                       (** Here, we need to use the goodness of program  *)
                       (** p or the goodness of program c (depending on  *)
                       (** whether cid \in domm (prog_interface p), I guess *)

                       (** In case it is, then we use the relation mem0 s1'mem *)
                       (** Otherwise, we use the relation s2''mem s1'mem       *)

                       (** In the first case, goal will follow from Hgood_prog *)
                       (** In the second case, it will follow from Hgood_prog''*)

                       unfold left_addr_good_for_shifting in IHHreach.
                       destruct (cid \in domm (prog_interface p)) eqn:Hcid;
                         rewrite Hcid in IHHreach.
                       ***
                         match goal with
                         | H: mem_of_part_executing_rel_original_and_recombined
                                p _ s1'mem n _ _ |- _ =>
                           inversion H as [s1'mem_rel_p _]
                         end.

                         specialize (s1'mem_rel_p (cid, bid) Hcid)
                           as [_ Hpriv2].

                         unfold Memory.load in Hpriv2. simpl in *.
                         rewrite HcompMem in Hpriv2.
                         specialize (Hpriv2 _ _ HcompLoad)
                           as [v [Hvload Hvshift]].
                         destruct (mem0 cid) as [compMem0|] eqn:HcompMem0;
                           try discriminate.

                         specialize (Hgood_prog _ _ Hpref_t) as [_ Ggood].
                         unfold Memory.load in Ggood.
                         specialize (Ggood
                                       mem0
                                       (Permission.data, cid, bid, off)
                                       (cid, bid)
                                       v
                                    ).
                         setoid_rewrite HcompMem0 in Ggood.
                         assert (left_value_good_for_shifting n v) as Hgoodv.
                         {
                           by apply Ggood; auto.
                         }

                         clear Ggood.

                         destruct v as [| [[[permv cidv] bidv] offv] |];
                           simpl in *;
                           destruct Hvshift as [ [Hvshift1 [Hvshift2 Hvshift3]]
                                               | Hvshift1];
                           try discriminate;

                           unfold 
                           rename_addr_option,
                           sigma_shifting_wrap_bid_in_addr,
                           sigma_shifting_lefttoright_addr_bid in *.

                         ----
                           inversion Hvshift3. subst. clear Hvshift3.
                           simpl in *.
                           erewrite sigma_lefttoright_Some_spec in Hgoodv.
                           destruct Hgoodv as [? contra].
                             by erewrite contra in Hvshift1.
                         ----
                           destruct (permv =? Permission.data) eqn:epermv.
                           ++++
                             destruct (sigma_shifting_lefttoright_option
                                         (n cidv)
                                         (if cidv \in domm (prog_interface p)
                                          then n cidv
                                          else n'' cidv) bidv) eqn:esigma;
                               rewrite esigma in Hvshift1; try discriminate.
                             inversion Hvshift1. subst.
                             rewrite sigma_lefttoright_Some_spec; eexists.
                               by erewrite
                                    sigma_shifting_lefttoright_Some_inv_Some;
                                 eauto.
                           ++++
                             inversion Hvshift1. subst.
                             by rewrite <- beq_nat_refl in epermv.

 
                      +++ admit.
                      +++ 

                       inversion Haddrtshr
                       
                       split.
                       
                   --- (* the symmetric/inverse case of renaming *)
                     admit.
                   --- constructor; eauto.
                   --- simpl in *.
                       match goal with
                       | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
                         inversion H as [Hregs]
                       end.
                       unfold shift_value in *.
                       destruct (Hregs R_COM) as [Hregs_ren _].
                       by rewrite <- Hregs_ren.
                   --- simpl in *.
                       match goal with
                       | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
                         inversion H as [Hregs]
                       end.
                       unfold inverse_shift_value in *.
                       destruct (Hregs R_COM) as [_ Hregs_invren].
                       by rewrite <- Hregs_invren.
                ** constructor. constructor; auto.
                   --- match goal with
                       | Hshift: traces_shift_each_other n'' _ t1'' t1' |- _ =>
                           by inversion Hshift
                       end.
                   --- admit.
                   --- admit.
                   --- by intuition.
                   --- simpl.
                       (* They should both be invalidated register files. *)
                       admit.
                   --- simpl.
                       (* They should both be invalidated register files. *)
                       admit.
             ++ simpl. (* SearchAbout b'. *)
                (* Need a lemma about EntryPoint.get before we are able to use
                   the following match.
                 *)
                (*match goal with
                | Hb0: _ = Some b0 |- _ =>
                  rewrite Hb' in Hb0; inversion Hb0
                end.*)
                admit.
             ++ (* SearchAbout C'0. *)
                (* should be available from Pointer.component pc0 <> C'0 *)
                admit.
             ++ simpl.
                (* prove a lemma about Register.invalidate regs_rel_of_executing_part *)
                admit.
             ++ (* memory relation executing part *)
               simpl.
               admit.
             ++ (* memory relation of the non-executing part *)
               simpl.
               admit.
               
      + (* case Return *)
        admit.
    - (* find_and_invert_mergeable_states_well_formed. *)
      simpl in *. subst.
      unfold CS.is_program_component,
      CS.is_context_component, turn_of, CS.state_turn in *.
      destruct s1 as [[[s11 s12] s13] s1pc].
      destruct s1' as [[[s1'1 s1'2] s1'3] s1'pc].
      simpl in *. subst.
      unfold negb in Hcomp1.
      match goal with
      | H: _ = Pointer.component s1pc,
           Hin: is_true (@in_mem _ (Pointer.component (CS.state_pc s1'')) _)
        |- _ =>
        rewrite H in Hin; rewrite Hin in Hcomp1
      end.
        by intuition.

    (* Derive some useful facts and begin to expose state structure. *)
  (*   inversion Hmerge1 as [??? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec ??????]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)

  (***********************************************************************************)
   (*
    pose proof threeway_multisem_event_lockstep_program_mergeable
         Hcomp1 Hmerge1 Hstep12 Hstep12'' Hrel2 as [s2' Hmerge2].
    set s1copy := s1. destruct s1 as [[[gps1 mem1] regs1] pc1].
    set s2copy := s2. destruct s2 as [[[gps2 mem2] regs2] pc2].
    destruct s1'' as [[[gps1'' mem1''] regs1''] pc1''].
    destruct s2'' as [[[gps2'' mem2''] regs2''] pc2''].
    (* Case analysis on step. *)
    inversion Hstep12 as [? t12 ? Hstep12ninf EQ Ht12 EQ']; subst.
    inversion Hstep12'' as [? t12'' ? Hstep12''ninf EQ Ht12'' EQ']; subst.
    inversion Hstep12ninf; subst; inversion Ht12; subst;
      inversion Hstep12''ninf; subst; inversion Ht12''; subst.

    - (* Call *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      assert (pc1 = pc1') by admit; subst pc1'. (* PC lockstep. *)
      assert (C' = C'0) by admit;
        assert (P = P0) by admit;
        subst C'0 P0. (* Sequence of calls and returns in lockstep. *)
      simpl in *.
      (* Take single step and have third step from program? *)
      exists
        (ECall (Pointer.component pc1) P (Register.get R_COM regs1') mem1' C').
      eexists. (* Actually, s2'? But it is tricky to step if instantiated. *)
      split.
      + (* To apply the step, we need to manipulate the goal into the
           appropriate form. At this point producing the corresponding event
           seems easiest, operating by simple substitution of parts. *)
        change
          ([ECall (Pointer.component pc1) P (Register.get R_COM regs1') mem1' C'])
          with
          (TracesInform.event_non_inform_of
             [TracesInform.ECallInform
                (Pointer.component pc1) P (Register.get R_COM regs1') mem1' regs1' C']).
        constructor. apply CS.Call; try assumption.
        * (* RB: TODO: This same snippet is use elsewhere: refactor lemma. *)
          match goal with
          | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
            pose proof execution_invariant_to_linking_recombination Hcomp1 Hmerge1 H as Hex'
          end.
          exact Hex'.
        * CS.simplify_turn.
          eapply imported_procedure_recombination; eassumption.
        * destruct (C' \in domm (prog_interface p)) eqn:Hcase.
          -- assert (Hcase' : C' \notin domm (prog_interface c')) by admit.
             (* RB: ??? The anonymous patterns interfere with the context and
                remove existing hypotheses in Coq 8.11.2! *)
             (* inversion Hmerge1 as [_ _ _ _ _ _ _ _ _ Hwfp Hwfc _ Hwfc' *)
             (*                       [Hlinkable _] Hifacep Hifacec *)
             (*                       _ _ _ _ _ _ _ _ _ _ _]. *)
             inversion Hmerge1 as [???????? [? ?] ? Hifacec].
             
             (*rewrite genv_entrypoints_program_link_left;
               try assumption; [| congruence].
             rewrite genv_entrypoints_program_link_left in H11;
               try assumption; [| now rewrite Hifacec].
             eassumption.*)

             (* AEK: The proof above broke. 
                Probably it first broke at: 
                commit 8858912fb913f4d3e3d209f44b4ad4c61f5c193b
              *)
             admit.
          
          -- (* RB: TODO: Refactor symmetric case? Too late now. *)
             admit.
        * reflexivity.
      + simpl.
        inversion Hmerge1 as [
                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel ].
        admit. (* Memories are not modified, but the argument can give access to
                  new parts of memory. *)

    - exfalso. admit. (* Contradiction: events cannot be related. *)
    - exfalso. admit. (* Contradiction: events cannot be related. *)

    - (* Return *)
      (* TODO: Call refactoring. *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      assert (pc1 = pc1') by admit; subst pc1'. (* PC lockstep. *)
      simpl in *.
      assert (Hstack : mergeable_stack p c (pc2 :: gps2) gps1'). {
        (* TODO: Adapt mergeable_states_mergeable_stack. *)
        admit.
      }
      inversion Hstack as [| ? pc1' ? gps1'_ Hcomp2 Hdomm Hstack' DUMMY DUMMY'];
        subst; rename gps1'_ into gps1'.
      (* NOTE: [Hdomm] not really necessary. *)
      (* Take single step and have third step from program? *)
      exists (ERet (Pointer.component pc1) (Register.get R_COM regs1')
                   mem1' (Pointer.component pc2)).
      eexists. (* Actually, s2'? But it is tricky to step if instantiated. *)
      split.
      + (* To apply the step, we need to manipulate the goal into the
           appropriate form. At this point producing the corresponding event
           seems easiest, operating by simple substitution of parts. *)
        change
          ([ERet (Pointer.component pc1) (Register.get R_COM regs1')
                 mem1' (Pointer.component pc2)])
          with
          (TracesInform.event_non_inform_of
             [TracesInform.ERetInform
                (Pointer.component pc1) (Register.get R_COM regs1')
                mem1' regs1' (Pointer.component pc2)]).
        constructor. rewrite Hcomp2. eapply CS.Return.
        * (* RB: TODO: This same snippet is use elsewhere: refactor lemma. *)
          match goal with
          | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
            assert (Hex' : executing (prepare_global_env prog') PC INSTR)
          end.
          {
            inversion Hmerge1
              as [Hwfp Hwfc Hwfp' Hwfc' [Hlinkable _]
                  Hifacep Hifacec Hprog_is_closed Hprog_is_closed'' _ _ _ _ _ _ _ ].
            apply execution_invariant_to_linking with c; try assumption.
            - congruence.
            - inversion Hmerge1. eapply CS.domm_partition; eauto.
              + by unfold CS.initial_state.
          }
          exact Hex'.
        * congruence.
        * reflexivity.
      + simpl.
        inversion Hmerge1 as [
                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (*[Hrel2' _]*)Hrel].
        admit.

  Admitted. (* RB: TODO: Fix statement and prove later, combine with lemma above. *)
  *)
  (***********************************************************************************)
  Admitted.  

  
(*    - (* Call: case analysis on call point. *)
      pose proof is_program_component_in_domm Hcomp1 Hmerge1 as Hdomm.
      unfold CS.state_component in Hdomm; simpl in Hdomm. unfold ip, ic.
      rewrite <- Pointer.inc_preserves_component in Hdomm.
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2;
        [ pose proof mergeable_states_program_to_context Hmerge2 Hcomp2 as Hcomp2''
        | apply negb_false_iff in Hcomp2 ];
        [ erewrite mergeable_states_merge_program
        | erewrite mergeable_states_merge_context ]; try eassumption;
        unfold merge_states_mem, merge_states_stack;
        rewrite merge_stacks_cons_program; try eassumption;
        match goal with
        | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ =>
          rewrite Heq
        end;
        [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]];
        t_threeway_multisem_event_lockstep_program_step_call Hcomp1 Hmerge1.
*)


(*
  - (* Return: case analysis on return point. *)
      match goal with
      | H1 : Pointer.component pc1'' = Pointer.component pc1,
        H2 : Pointer.component pc2'' = Pointer.component pc2 |- _ =>
        rename H1 into Heq1; rename H2 into Heq2
      end.
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2;
        [| apply negb_false_iff in Hcomp2];
        [ rewrite (mergeable_states_merge_program _ Hmerge2); try assumption
        | rewrite (mergeable_states_merge_context _ Hmerge2); try assumption ];
        unfold merge_states_mem, merge_states_stack; simpl;
        [ pose proof is_program_component_in_domm Hcomp2 Hmerge2 as Hcomp2'';
          erewrite merge_frames_program; try eassumption
        | erewrite merge_frames_context; try eassumption ];
        [ rewrite Heq1 Heq2 | rewrite Heq1 ];
        [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]];
        t_threeway_multisem_event_lockstep_program_step_return Hcomp1 Hmerge1.
  Qed.
*)

  (* RB: NOTE: [DynShare] Composing the two partial results above will not be
     possible if we cannot show that the separately proved existentials
     coincide, so modularity would decrease at this point.  *)
  (* TODO: This corollary is here because the lemma above was a helper 
     lemma. Now after changing the lemma above, we should maybe
     just get rid of the lemma above---because it is not helper
     anymore.
   *)
  Corollary threeway_multisem_event_lockstep_program
            s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    traces_shift_each_other n n'' (rcons t1 e) (rcons t1'' e'') ->
    good_trace (left_addr_good_for_shifting n) (rcons t1 e) ->
    good_trace (left_addr_good_for_shifting n'') (rcons t1'' e'') ->
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mergeable_border_states p c p' c' n n'' s2 s2' s2'' (rcons t1 e) 
           (rcons t1' e') (rcons t1'' e'').
  Proof.
    intros. eapply threeway_multisem_event_lockstep_program_step; eassumption.
  Qed.

(*
  intros Hcomp1 Hmerge1 Hstep12 Hstep12'' Hrel2.
    pose proof threeway_multisem_event_lockstep_program_step
         Hcomp1 Hmerge1 Hstep12 Hstep12'' Hrel2
      as [e' [s2' [Hstep12' Hrel2']]].
    exists e', s2'. split; first assumption.
    inversion Hmerge1.
    eapply mergeable_states_intro
      with (t := t1 ++ [e]) (t' := t1' ++ [e']) (t'' := t1'' ++ [e'']);
      try eassumption.
    - eapply star_right; try eassumption. reflexivity.
    - eapply star_right; try eassumption. reflexivity.
    - eapply star_right; try eassumption. reflexivity.
    - constructor.
      + admit. (* Should be able to compose from relations in context. *)
      + admit. (* Should be able to compose from relations in context. *)
    - admit. (* Should be able to compose from relations in context. *)
    - admit. (* Should be able to compose from relations in context. *)
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  (* Proof. *)
  (*   split. *)
  (*   - now apply threeway_multisem_event_lockstep_program_step. *)
  (*   - eapply threeway_multisem_event_lockstep_program_mergeable; eassumption. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Fix statement, redundant w.r.t. the above lemmas. *)

 *)
  
End ThreewayMultisem1.

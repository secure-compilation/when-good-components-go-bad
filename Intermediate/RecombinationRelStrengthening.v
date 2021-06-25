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

  Lemma Reachable_memrel_Reachable C'0 mem0 regs P0 pc t1 s1'mem s1'reg addrl:
    good_trace_extensional (left_addr_good_for_shifting n)
                           (rcons t1 (ECall
                                        (Pointer.component pc)
                                        P0
                                        (Register.get R_COM regs)
                                        mem0
                                        C'0
                                     )
                           )
    ->
    (
      shift_value_option
        n
        (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = Some (Register.get R_COM s1'reg)
      \/
      shift_value_option
        n
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = None /\
      shift_value_option
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        n
        (Register.get R_COM s1'reg) = None /\
      Register.get R_COM regs = Register.get R_COM s1'reg
    )
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem
      n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    Reachable mem0 (addr_of_value (Register.get R_COM regs))
              addrl
    ->
    exists addrl',
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           n
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        )
        addrl = Some addrl'
      /\
      Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
                addrl'.
  Proof.
    intros Hgoodrconst1 Hrel_R_COM mem0_s1'mem Hreach.
    unfold event_renames_event_at_shared_addr,
    mem_of_part_not_executing_rel_original_and_recombined_at_border,
    mem_of_part_executing_rel_original_and_recombined,
    mem_of_part_not_executing_rel_original_and_recombined_at_internal,
    memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
    memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
    shift_value_option, rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid
      in *.

    inversion Hgoodrconst1 as [? shared_good]; subst.
    
    destruct (Register.get R_COM regs)
        as [| [[[permv cidv] bidv] offv] |] eqn:eR_COM;
      simpl in *; try by apply Reachable_fset0 in Hreach.
    
    destruct (permv =? Permission.data) eqn:epermv;
      last by apply Reachable_fset0 in Hreach.
    


    destruct Hrel_R_COM as [HR_COM | [HR_COM [Hcontra_ Hrewr]]];
      destruct (sigma_shifting_lefttoright_option
                  (n cidv)
                  (if cidv \in domm (prog_interface p)
                   then n cidv else n'' cidv) bidv) as [bidv'|] eqn:ebidv;
      rewrite ebidv in HR_COM; try discriminate.
    - inversion HR_COM as [Hrewr]. simpl in *. rewrite epermv.
      induction Hreach as [? Hin|? ? [cidloaded bidloaded]
                             compMem Hreach IH HcompMem Hin]; subst.
      + rewrite in_fset1 in Hin.
        move : Hin => /eqP => Hin; inversion Hin; subst.
        eexists; split.
        * by setoid_rewrite ebidv.
        * by eapply Reachable_refl; rewrite in_fset1.
      + assert (addr_shared_so_far
                  (cid, bid)
                  (rcons t1 (ECall
                               (Pointer.component pc)
                               P0
                               (Register.get R_COM regs)
                               mem0
                               C'0
                            )
                  )
               ) as Hshr.
        {
            by rewrite eR_COM;
              eapply reachable_from_args_is_shared; simpl in *; rewrite epermv; auto.
        }
        rewrite eR_COM in Hshr.
        specialize (shared_good _ Hshr); simpl in *.
        destruct mem0_s1'mem as [_ [mem0s1'mem _]].
        specialize (mem0s1'mem _ Hshr) as [[cid' bid'] [ebid' [memrel _]]].
        assert (exists offl offset,
                   Memory.load mem0 (Permission.data, cid, bid, offset) =
                   Some (Ptr (Permission.data, cidloaded, bidloaded, offl))
               ) as [offl [offset Hload]].
        {
          unfold Memory.load. simpl. rewrite HcompMem.
          erewrite <- ComponentMemory.load_block_load.
          erewrite Extra.In_in in Hin. assumption.
        }
        simpl in *.
        specialize (memrel _ _ Hload) as [v' [G Hv']].
        simpl in *.
        destruct (sigma_shifting_lefttoright_option
                    (n cidloaded)
                    (if cidloaded \in domm (prog_interface p)
                     then n cidloaded else n'' cidloaded)
                    bidloaded)
          as [bidloaded'|] eqn:ebidloaded; rewrite ebidloaded in Hv'; try discriminate.
        inversion Hv'; subst; clear Hv'.
        destruct IH as [? [IH1 IH2]]; rewrite ebid' in IH1; inversion IH1; subst;
          clear IH1.
        eexists; split; first rewrite ebidloaded; eauto.
        unfold Memory.load in G. simpl in *.
        destruct (s1'mem cid') as [compMem'|] eqn:ecompMem'; try discriminate.
        eapply Reachable_step; eauto.
        rewrite Extra.In_in ComponentMemory.load_block_load.
          by eexists; eauto.
    - (** Here, derive a contradiction to ebidv. *)
      assert (exists bidv',
                 sigma_shifting_lefttoright_option
                   (n cidv)
                   (if cidv \in domm (prog_interface p)
                    then n cidv else n'' cidv) bidv = Some bidv'
             ) as [? contra].
      {
        erewrite <- sigma_lefttoright_Some_spec.
        specialize (shared_good (cidv, bidv)).
        unfold left_addr_good_for_shifting in *.
        eapply shared_good.
        eapply reachable_from_args_is_shared. simpl.
        rewrite epermv; constructor; by rewrite in_fset1.
      }
      by rewrite contra in ebidv.
  Qed.
  
  Corollary Reachable_memrel_Reachable_corollary:
    forall C'0 mem0 regs P0 pc t1 s1'mem s1'reg cidl bidl bidl',
    good_trace_extensional (left_addr_good_for_shifting n)
                           (rcons t1 (ECall
                                        (Pointer.component pc)
                                        P0
                                        (Register.get R_COM regs)
                                        mem0
                                        C'0
                                     )
                           )
    ->
    (
      shift_value_option n
                         (fun cid : nat =>
                            if cid \in domm (prog_interface p) then n cid else n'' cid
                         )
                         (Register.get R_COM regs) = Some (Register.get R_COM s1'reg)
      \/
      shift_value_option n
                         (fun cid : nat =>
                            if cid \in domm (prog_interface p) then n cid else n'' cid)
                         (Register.get R_COM regs) = None /\
      shift_value_option
        (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        n
        (Register.get R_COM s1'reg) = None /\
      Register.get R_COM regs = Register.get R_COM s1'reg
    )
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    Reachable mem0 (addr_of_value (Register.get R_COM regs)) (cidl, bidl)
              
    ->
    sigma_shifting_lefttoright_option
      (n cidl)
      (if cidl \in domm (prog_interface p) then n cidl else n'' cidl)
      bidl = Some bidl'
    ->
    Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg)) (cidl, bidl').
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? H1 H2 H3 H4.
    specialize (Reachable_memrel_Reachable H1 H2 H3 H4) as [[cidl' bidl'2] [ebidl'2 G]].
    unfold sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid in *.
    intros rewr; rewrite rewr in ebidl'2; inversion ebidl'2; by subst.
  Qed.


  Lemma Reachable_memrel_Reachable2 C'0 mem0 regs P0 pc t1 s1'mem s1'reg addrl':
    good_trace_extensional (left_addr_good_for_shifting n)
                           (rcons t1 (ECall
                                        (Pointer.component pc)
                                        P0
                                        (Register.get R_COM regs)
                                        mem0
                                        C'0
                                     )
                           )
    ->
    (
      shift_value_option
        n
        (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = Some (Register.get R_COM s1'reg)
      \/
      shift_value_option
        n
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = None /\
      shift_value_option
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        n
        (Register.get R_COM s1'reg) = None /\
      Register.get R_COM regs = Register.get R_COM s1'reg
    )
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem
      n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
              addrl'
    ->
    exists addrl,
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
           n
        )
        addrl' = Some addrl
      /\
      Reachable mem0 (addr_of_value (Register.get R_COM regs))
                addrl.
  Proof.
    intros Hgoodrconst1 Hrel_R_COM mem0_s1'mem Hreach.
    unfold event_renames_event_at_shared_addr,
    mem_of_part_not_executing_rel_original_and_recombined_at_border,
    mem_of_part_executing_rel_original_and_recombined,
    mem_of_part_not_executing_rel_original_and_recombined_at_internal,
    memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
    memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
    shift_value_option, rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid
      in *.

    inversion Hgoodrconst1 as [? shared_good]; subst.
    
    destruct (Register.get R_COM s1'reg)
        as [| [[[permv cidv] bidv] offv] |] eqn:eR_COM;
      simpl in *; try by apply Reachable_fset0 in Hreach.
    
    destruct (permv =? Permission.data) eqn:epermv;
      last by apply Reachable_fset0 in Hreach.
    


    destruct Hrel_R_COM as [HR_COM | [HR_COM [Hcontra_ Hrewr]]];
      destruct (Register.get R_COM regs)
      as [| [[[permv_regs cidv_regs] bidv_regs] offv_regs] |]
           eqn:eR_COM_regs; inversion HR_COM as [Hsubst];
        try discriminate.
      
    - destruct (permv_regs =? Permission.data) eqn:epermv_regs.
      + destruct (sigma_shifting_lefttoright_option
                    (n cidv_regs)
                    (if cidv_regs \in domm (prog_interface p)
                     then n cidv_regs else n'' cidv_regs)
                    bidv_regs) as [bidv_regs'|] eqn:ebidv_regs;
          rewrite ebidv_regs in Hsubst; try discriminate.
        inversion Hsubst; subst; clear Hsubst.
        simpl in *; rewrite epermv.
        induction Hreach as [? Hin|? ? [cidloaded bidloaded]
                               compMem Hreach IH HcompMem Hin]; subst.
        * rewrite in_fset1 in Hin.
          move : Hin => /eqP => Hin; inversion Hin; subst.
          eexists; split.
          -- apply sigma_shifting_lefttoright_Some_inv_Some in ebidv_regs.
             by rewrite ebidv_regs.
          -- by eapply Reachable_refl; rewrite in_fset1.
        * destruct IH as [[cidl bidl] [IH1 IH2]].
          destruct (sigma_shifting_lefttoright_option
                      (if cid \in domm (prog_interface p) then n cid else n'' cid) 
                      (n cid) bid) as [bid'|] eqn:ebid'; rewrite ebid' in IH1;
            try discriminate; inversion IH1; subst; clear IH1.
          assert (addr_shared_so_far
                    (cidl, bidl)
                    (rcons t1 (ECall
                                 (Pointer.component pc)
                                 P0
                                 (Register.get R_COM regs)
                                 mem0
                                 C'0
                              )
                    )
                 ) as Hshr.
        {
          rewrite eR_COM_regs;
            eapply reachable_from_args_is_shared; simpl in *; rewrite epermv; auto.
        }
        rewrite eR_COM_regs in Hshr.
        specialize (shared_good _ Hshr); simpl in *.
        destruct mem0_s1'mem as [_ [mem0s1'mem _]].
        specialize (mem0s1'mem _ Hshr) as [[cidl' bidl'] [ebidl' [_ memrel]]];
          simpl in *.
        apply sigma_shifting_lefttoright_Some_inv_Some in ebid'.
        rewrite ebid' in ebidl'. inversion ebidl'; subst; clear ebidl'.
        assert (exists offl offset,
                   Memory.load s1'mem (Permission.data, cidl', bidl', offset) =
                   Some (Ptr (Permission.data, cidloaded, bidloaded, offl))
               ) as [offl [offset Hload]].
        {
          unfold Memory.load. simpl. rewrite HcompMem.
          erewrite <- ComponentMemory.load_block_load.
          erewrite Extra.In_in in Hin. assumption.
        }
        simpl in *.
        specialize (memrel _ _ Hload) as [v' [G Hv']].
        destruct v' as [ | [[[permv' cidv'] bidv'] offv'] |]; try discriminate.
        destruct (permv' =? Permission.data) eqn:epermv'.
          --  destruct (sigma_shifting_lefttoright_option
                          (n cidv')
                          (if cidv' \in domm (prog_interface p)
                           then n cidv' else n'' cidv') bidv')
              as [bidv''|] eqn:ebidv''; rewrite ebidv'' in Hv';
                try discriminate.
              inversion Hv'; subst; clear Hv'.
              apply sigma_shifting_lefttoright_Some_inv_Some in ebidv''.
              rewrite ebidv''.
              eexists; split; eauto.
              unfold Memory.load in G. simpl in *.
              destruct (mem0 cidl') eqn:emem0; try discriminate.
              eapply Reachable_step; first exact IH2; first exact emem0.
              rewrite Extra.In_in ComponentMemory.load_block_load. by eexists; eauto.
          -- by inversion Hv'; subst.
      + inversion Hsubst; subst. by rewrite epermv in epermv_regs.
    - destruct (permv_regs =? Permission.data) eqn:epermv_regs; try discriminate.
      destruct (sigma_shifting_lefttoright_option
                  (n cidv_regs)
                  (if cidv_regs \in domm (prog_interface p)
                   then n cidv_regs else n'' cidv_regs)
                  bidv_regs) as [bidv_regs'|] eqn:ebidv_regs;
        rewrite ebidv_regs in Hsubst; try discriminate.
      inversion Hrewr; subst; clear Hrewr.

      specialize (shared_good (cidv, bidv)) as contra.
      assert (cidvbidvshr:
                addr_shared_so_far
                  (cidv, bidv)
                  (rcons t1
                         (ECall
                            (Pointer.component pc)
                            P0 (Ptr (permv, cidv, bidv, offv)) mem0 C'0))
             ).
      { econstructor; eauto; simpl; rewrite epermv; constructor; by rewrite in_fset1. }
      specialize (contra cidvbidvshr). simpl in *.
      erewrite sigma_lefttoright_Some_spec in contra.
      destruct contra as [? rewr]. by erewrite rewr in ebidv_regs. 
  Qed.
      
  Corollary Reachable_memrel_Reachable2_corollary
            C'0 mem0 regs P0 pc t1 s1'mem s1'reg addrl' addrl:
    good_trace_extensional (left_addr_good_for_shifting n)
                           (rcons t1 (ECall
                                        (Pointer.component pc)
                                        P0
                                        (Register.get R_COM regs)
                                        mem0
                                        C'0
                                     )
                           )
    ->
    (
      shift_value_option
        n
        (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = Some (Register.get R_COM s1'reg)
      \/
      shift_value_option
        n
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        (Register.get R_COM regs) = None /\
      shift_value_option
        (fun cid : nat =>
           if cid \in domm (prog_interface p) then n cid else n'' cid)
        n
        (Register.get R_COM s1'reg) = None /\
      Register.get R_COM regs = Register.get R_COM s1'reg
    )
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem
      n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
              addrl'
    ->
    sigma_shifting_wrap_bid_in_addr
      (sigma_shifting_lefttoright_addr_bid
         (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
         n
      )
      addrl' = Some addrl
    ->
    Reachable mem0 (addr_of_value (Register.get R_COM regs))
              addrl.
  Proof.
    intros H1 H2 H3 H4.
    specialize (Reachable_memrel_Reachable2 H1 H2 H3 H4)
      as [[cidl' bidl'2] [ebidl'2 G]].
    unfold sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid in *.
    intros rewr; rewrite rewr in ebidl'2; inversion ebidl'2; by subst.
  Qed.

  Lemma shared_Reachable_memrel_shared_Reachable
        C'0 mem0 regs P0 pc t1 t1' s1'mem addrl addr_shr:
    good_trace_extensional (left_addr_good_for_shifting n) t1
    ->
    traces_shift_each_other_option
      n
      (fun cid : nat => if cid \in domm (prog_interface p)
                        then n cid else n'' cid)
      t1
      t1'
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem
      n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    addr_shared_so_far addr_shr t1 ->
    Reachable mem0 (fset1 addr_shr) addrl
    ->
    exists addr_shr' addrl',
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           n
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        )
        addrl = Some addrl'
      /\
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           n
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
        )
        addr_shr = Some addr_shr'                      
      /\
      addr_shared_so_far addr_shr' t1'
      /\
      Reachable s1'mem (fset1 addr_shr') addrl'.
  Proof.
    intros t1good t1t1' mem0s1'mem Hshr Hreach.
    unfold mem_of_part_not_executing_rel_original_and_recombined_at_border,
    mem_of_part_executing_rel_original_and_recombined,
    mem_of_part_not_executing_rel_original_and_recombined_at_internal,
    memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
    memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
    shift_value_option, rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid
      in *.

    assert (Hshr_ex: addr_shared_so_far
                       addr_shr
                       (rcons t1
                              (ECall
                                 (Pointer.component pc)
                                 P0 (Register.get R_COM regs) mem0 C'0))
           ).
    {
      eapply reachable_from_previously_shared; eauto; simpl.
      constructor. by rewrite in_fset1.
    }

    inversion t1good as [? t1good_]; subst.
    specialize (t1good_ _ Hshr) as addr_shr_good.
    remember (fset1 addr_shr) as addr_shr_set.
    move: Heqaddr_shr_set.
    (**************
    ****************)
    induction Hreach as [addr Hin |
                         ? ? [cidloaded bidloaded]
                           ? ? ? HcompMem Hin ]; intros; subst.
    - rewrite in_fset1 in Hin.
      move : Hin => /eqP => Hin; subst.
      destruct addr_shr as [shrcid shrbid]. simpl in *.
      erewrite sigma_lefttoright_Some_spec in addr_shr_good.
      destruct addr_shr_good as [shrbid' eshrbid'].
      erewrite eshrbid'; do 2 eexists; split; eauto; split; eauto; split.
      + inversion t1t1' as [? ? Hren]; subst.
        inversion Hren as [| t e t' e' ? ? Htt' ? ? ?]; subst;
          try by inversion Hshr; subst; find_nil_rcons.
        specialize (Htt' _ Hshr) as [_ [? [esigma ?]]].
        unfold sigma_shifting_wrap_bid_in_addr,
        sigma_shifting_lefttoright_addr_bid in *.
        rewrite eshrbid' in esigma; inversion esigma; subst; assumption.
      + constructor; by rewrite in_fset1.
    - destruct addr_shr as [shrcid shrbid]. simpl in *.
      erewrite sigma_lefttoright_Some_spec in addr_shr_good.
      destruct addr_shr_good as [shrbid' eshrbid'].

      assert (Hcidbidshr: addr_shared_so_far
                (cid, bid)
                (rcons
                   t1
                   (ECall
                      (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
             ).
      {
        eapply reachable_from_previously_shared; eauto; simpl.
      }

      destruct mem0s1'mem as [_ [mem0s1'mem_shr _]].

      specialize (mem0s1'mem_shr _ Hcidbidshr) as [cidbid' [ecidbid' [G _]]].

      assert (exists offl offset,
                 Memory.load mem0 (Permission.data, cid, bid, offset) =
                 Some (Ptr (Permission.data, cidloaded, bidloaded, offl))
             ) as [offl [offset Hload]].
        {
          unfold Memory.load. simpl. rewrite HcompMem.
          erewrite <- ComponentMemory.load_block_load.
          erewrite Extra.In_in in Hin. assumption.
        }
        simpl in *.
        specialize (G _ _ Hload) as [v' [G Hv']].
        simpl in *.
        destruct (sigma_shifting_lefttoright_option
                    (n cidloaded)
                    (if cidloaded \in domm (prog_interface p)
                     then n cidloaded else n'' cidloaded)
                    bidloaded)
          as [bidloaded'|] eqn:ebidloaded; rewrite ebidloaded in Hv'; try discriminate.
        inversion Hv'; subst; clear Hv'.
        setoid_rewrite ebidloaded.
        setoid_rewrite eshrbid'.
        do 2 eexists; split; eauto; split; eauto.
        setoid_rewrite eshrbid' in IHHreach.
        setoid_rewrite ecidbid' in IHHreach.
        specialize (IHHreach Logic.eq_refl) as [? [cidbid'' [inv1 [inv2 [? Hreach']]]]].
        inversion inv1; inversion inv2; subst; clear inv1 inv2.
        split; auto.
        destruct cidbid'' as [cid' bid'].
        unfold Memory.load in *; simpl in *;
        destruct (s1'mem cid') as [compMem'|] eqn:e; try discriminate.
        eapply Reachable_step; first eassumption; first eassumption.
        rewrite Extra.In_in ComponentMemory.load_block_load.
        do 2 eexists; eassumption.
  Qed.
        
  Lemma shared_Reachable_memrel_shared_Reachable2
        C'0 mem0 regs P0 pc t1 t1' s1'mem addrl addr_shr:
    good_trace_extensional (left_addr_good_for_shifting n) t1
    ->
    traces_shift_each_other_option
      n
      (fun cid : nat => if cid \in domm (prog_interface p)
                        then n cid else n'' cid)
      t1
      t1'
    ->
    mem_of_part_not_executing_rel_original_and_recombined_at_border
      p mem0 s1'mem
      n
      (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
      (rcons t1 (ECall (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
    ->
    addr_shared_so_far addr_shr t1' ->
    Reachable s1'mem (fset1 addr_shr) addrl
    ->
    exists addr_shr' addrl',
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
           n
        )
        addrl = Some addrl'
      /\
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid
           (fun cid : nat => if cid \in domm (prog_interface p) then n cid else n'' cid)
           n
        )
        addr_shr = Some addr_shr'                      
      /\
      addr_shared_so_far addr_shr' t1
      /\
      Reachable mem0 (fset1 addr_shr') addrl'.
  Proof.
    intros t1good t1t1' mem0s1'mem Hshr Hreach.
    unfold mem_of_part_not_executing_rel_original_and_recombined_at_border,
    mem_of_part_executing_rel_original_and_recombined,
    mem_of_part_not_executing_rel_original_and_recombined_at_internal,
    memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
    memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
    shift_value_option, rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid
      in *.

    inversion t1t1' as [? ? Hren]; subst.
    inversion Hren as [| t e t' e' ? ? ? Ht't ? ? ? ? t1'good]; subst;
      try by inversion Hshr; subst; find_nil_rcons.
        
    specialize (Ht't _ Hshr) as [[shrcid_ shrbid_] [esigma [? ?]]].
        
    inversion t1'good as [? t1'good_]; subst.
    specialize (t1'good_ _ Hshr) as addr_shr_good.
    remember (fset1 addr_shr) as addr_shr_set.
    move: Heqaddr_shr_set.
    (**************
    ****************)
    induction Hreach as [addr Hin |
                         ? ? [cidloaded bidloaded]
                           ? ? ? HcompMem Hin ]; intros; subst.
    - rewrite in_fset1 in Hin.
      move : Hin => /eqP => Hin; subst.
      destruct addr_shr as [shrcid shrbid]. simpl in *.
      erewrite sigma_lefttoright_Some_spec in addr_shr_good.
      destruct addr_shr_good as [shrbid' eshrbid'].
      erewrite eshrbid'; do 2 eexists; split; eauto; split; eauto; split.
      + unfold sigma_shifting_wrap_bid_in_addr,
        sigma_shifting_lefttoright_addr_bid in *.
        destruct (sigma_shifting_lefttoright_option
                    (n shrcid_)
                    (if shrcid_ \in domm (prog_interface p)
                     then n shrcid_ else n'' shrcid_) shrbid_) eqn:esigma2;
          rewrite esigma2 in esigma; try discriminate; inversion esigma; subst.
        apply sigma_shifting_lefttoright_Some_inv_Some in esigma2.
        setoid_rewrite esigma2 in eshrbid'. inversion eshrbid'; by subst.
      + constructor; by rewrite in_fset1.
    - destruct addr_shr as [shrcid shrbid]. simpl in *.
      erewrite sigma_lefttoright_Some_spec in addr_shr_good.
      destruct addr_shr_good as [shrbid' eshrbid'].

      specialize (IHHreach Logic.eq_refl) as [? [[cid'' bid'']
                                                   [inv1 [inv2 [? Hreach']]]]].
      rewrite eshrbid' in inv2. inversion inv2; subst.
      
      assert (Hcidbidshr: addr_shared_so_far
                (cid'', bid'')
                (rcons
                   (rcons t e)
                   (ECall
                      (Pointer.component pc) P0 (Register.get R_COM regs) mem0 C'0))
             ).
      {
        eapply reachable_from_previously_shared; eauto; simpl.
      }

      destruct mem0s1'mem as [_ [mem0s1'mem_shr _]].

      specialize (mem0s1'mem_shr _ Hcidbidshr) as [cidbid' [ecidbid' [_ G]]].
      destruct (sigma_shifting_lefttoright_option
             (if cid \in domm (prog_interface p) then n cid else n'' cid) 
             (n cid) bid) eqn:esigma2; rewrite esigma2 in inv1; inversion inv1; subst.
      apply sigma_shifting_lefttoright_Some_inv_Some in esigma2.
      rewrite esigma2 in ecidbid'; inversion ecidbid'; subst; clear inv1 ecidbid'.
      
      assert (exists offl offset,
                 Memory.load s1'mem (Permission.data, cid'', bid, offset) =
                 Some (Ptr (Permission.data, cidloaded, bidloaded, offl))
             ) as [offl [offset Hload]].
      {
        unfold Memory.load. simpl. rewrite HcompMem.
        erewrite <- ComponentMemory.load_block_load.
        erewrite Extra.In_in in Hin. assumption.
      }
      simpl in *.
      specialize (G _ _ Hload) as [v' [G Hv']].
      destruct v' as [| [[[permv' cidv'] bidv'] offv'] |]; try discriminate.
      destruct (permv' =? Permission.data) eqn:epermv'.
      + destruct (sigma_shifting_lefttoright_option
                    (n cidv')
                    (if cidv' \in domm (prog_interface p)
                     then n cidv' else n'' cidv') bidv') as [bidv''|] eqn:ebidv'';
          rewrite ebidv'' in Hv'; inversion Hv'; subst.
        apply sigma_shifting_lefttoright_Some_inv_Some in ebidv''.
        setoid_rewrite ebidv''. setoid_rewrite eshrbid'.
        do 2 eexists; split; first reflexivity; split; first reflexivity; split;
          first assumption.

        unfold Memory.load in *. simpl in *.
        destruct (mem0 cid'') eqn:emem0; try discriminate.
        eapply Reachable_step; first eassumption; first eassumption.
        rewrite Extra.In_in ComponentMemory.load_block_load.
        do 2 eexists; eassumption.

      + inversion Hv'; subst; clear Hv'; by auto.
  Qed.
        
      
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

    assert (Hpc_in: Pointer.component (CS.state_pc s1) \in domm (prog_interface p)).
    {
      by eapply is_program_component_pc_in_domm; eauto.
    }
    
    inversion Hstep12. subst.
    find_and_invert_mergeable_internal_states.
    find_and_invert_mergeable_states_well_formed.
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

          assert (s2'mem = s1'mem).
          {
            inversion Hstep12' as [? ? ? ? Hstep12'inform]; subst.
            unfold TracesInform.event_non_inform_of in *.
            destruct t eqn:eqt; try discriminate.
            destruct e; try discriminate.
            - by inversion Hstep12'inform; try discriminate.
            - by inversion Hstep12'inform; try discriminate.
          }
          subst.
          
 
          assert (s2''mem_s1'mem:
                    mem_of_part_executing_rel_original_and_recombined
                      c'
                      s2''mem
                      s1'mem
                      n''
                      (fun cid : nat_ordType =>
                         if cid \in domm (prog_interface p) then n cid else n'' cid
                      )
                      (rcons
                         t1''
                         (ECall
                            (Pointer.component pc)
                            P0
                            (Register.get R_COM regs0)
                            s2''mem
                            C'0
                         )
                      )
                 ).
          {
            unfold mem_of_part_executing_rel_original_and_recombined,
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
            memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid, rename_addr_option
              in *.

            destruct Hmemc' as [Hmemc'_ next_block_s2''mem_s1'mem].
            destruct Hmemp as [mem0s1'mem_priv [mem0s1'mem_shr next_block_mem0s1'mem]].

            split; last split; auto; simpl in *.
            - intros [cidorig bidorig] Hcidorig; simpl in *.
              assert (Hcidorigp: cidorig \in domm (prog_interface p) = false).
              {
                rewrite <- Hifc_cc' in Hcidorig.
                unfold mergeable_interfaces, linkable in *.
                assert (contra: cidorig \in domm (prog_interface p) ->
                                    cidorig \notin domm (prog_interface c)).
                by apply/fdisjointP; intuition.
                destruct (cidorig \in domm (prog_interface p)); auto.
                assert (false). { rewrite Hcidorig in contra. by apply contra. }
                by auto.
              }
                
              specialize (Coq.Logic.Classical_Prop.classic 
                              (addr_shared_so_far (cidorig, bidorig) t1'')
                         ) as [Hshr'' | Hnotshr''].
              + assert (Hshr''_ext:
                          addr_shared_so_far
                            (cidorig, bidorig)
                            (rcons
                               t1''
                               (
                                 ECall
                                   (Pointer.component pc)
                                   P0
                                   (Register.get R_COM regs0)
                                   s2''mem
                                   C'0
                               )
                            )
                       ).
                {
                  eapply reachable_from_previously_shared; eauto.
                  constructor. by rewrite in_fset1.
                }
                specialize (Hr3 _ Hshr''_ext) as [[cidorig_prog bidorig_prog]
                                                    [Hbidorig_prog
                                                       [e'e'' Hshr_prog]]].
                destruct (sigma_shifting_lefttoright_option
                            (n cidorig_prog) 
                            (n'' cidorig_prog) bidorig_prog) eqn:ebidorig_prog;
                  try discriminate.
                inversion Hbidorig_prog; subst. clear Hbidorig_prog.

                inversion Hshift_t''t' as [? ? Hren]; subst.
                inversion Hren as [| t'' e'' t' e' ? ? Ht''t' ? ? ?]; subst;
                  try by inversion Hshr''; subst; find_nil_rcons.
                specialize (Ht''t' _ Hshr'') as
                    [He''e' [[cid' bid'] [ecid'bid' Hshrcid'bid']]].

                unfold event_renames_event_at_shared_addr,
                memory_renames_memory_at_shared_addr,
                rename_value_option, rename_value_template_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid, rename_addr_option
                  in *.

                rewrite Hcidorigp in ecid'bid'.
                destruct (sigma_shifting_lefttoright_option
                            (n'' cidorig) (n'' cidorig) bidorig) eqn:ebidorig;
                  try discriminate.
                inversion ecid'bid'; subst; clear ecid'bid'.
                apply sigma_shifting_lefttoright_option_n_n_id in ebidorig.
                subst.
                
                simpl in *.
                
                destruct e'e'' as [[cidorig_ bidorig_]
                                     [Hbidorig_
                                        [mem0_s2''mem s2''mem_mem0]
                                     ]
                                  ].

                rewrite ebidorig_prog in Hbidorig_.
                inversion Hbidorig_. subst. clear Hbidorig_.


                inversion Hshift_tt' as [? ? Hrentt']; subst.
                inversion Hrentt' as [| t e t'_ e'_ ? ? ? Ht't ? ?]; subst;
                  try by inversion Hshrcid'bid'; subst; find_nil_rcons.

                match goal with
                | H24: rcons _ _ = rcons _ _ |- _ =>
                  apply rcons_inj in H24; inversion H24; subst; clear H24
                end.
                
                specialize (Ht't _ Hshrcid'bid') as
                    [[cid bid] [ecidbid [He'e Hshrcidbid]]].

                specialize (mem0s1'mem_shr _ Hshrcidbid)
                  as [[cid' bid'] [ecid'bid' [mem0_s1'mem s1'mem_mem0]]].

                destruct (sigma_shifting_lefttoright_option
                            (n cid)
                            (if cid \in domm (prog_interface p)
                             then n cid else n'' cid) bid) eqn:ebid';
                  rewrite ebid' in ecid'bid'; try discriminate.
                inversion ecid'bid'; subst; clear ecid'bid'.


                unfold event_renames_event_at_shared_addr,
                memory_renames_memory_at_shared_addr,
                rename_value_option, rename_value_template_option,
                sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid, rename_addr_option
                  in *.


                destruct (sigma_shifting_lefttoright_option
                            (n cid')
                            (if cid' \in domm (prog_interface p)
                             then n cid' else n'' cid') bid) eqn:ebidorig_;
                  rewrite ebidorig_ in ecidbid; try discriminate.
                inversion ecidbid. subst. clear ecidbid.

                rewrite Hcidorigp in ebidorig_.
                specialize (sigma_shifting_lefttoright_option_Some_inj
                              _ _ _ _ _ ebidorig_prog ebidorig_) as G.
                inversion ebid'.
                subst.
                clear ebid'.
                
                split; intros ? ? Hload; simpl in *.
                * specialize (s2''mem_mem0 _ _ Hload)
                    as [vprog [Hloadmem0 Hvprog]].
                  
                  specialize (mem0_s1'mem _ _ Hloadmem0)
                    as [v' [Hloads1'mem Hv']].

                  destruct vprog as [| [[[permvp cidvp] bidvp] offvp] |];
                    inversion Hv'; inversion Hvprog; subst; auto.

                  destruct (permvp =? Permission.data) eqn:epermvp;
                    inversion Hv'; inversion Hvprog; subst; last by rewrite epermvp.

                  destruct (sigma_shifting_lefttoright_option
                              (n cidvp) (n'' cidvp) bidvp) as [bidvp'|] eqn:ebidvp;
                    try discriminate.

                  inversion Hvprog; subst. rewrite epermvp.

                  specialize (sigma_lefttoright_Some_good _ _ _ _ ebidvp)
                    as G.
                  assert (left_block_id_good_for_shifting (n'' cidvp) bidvp').
                    by unfold right_block_id_good_for_shifting in *.
                    
                  erewrite sigma_lefttoright_Some_spec in G.
                  destruct G as [bidvp'' G'].
                  erewrite G'.

                  destruct (sigma_shifting_lefttoright_option
                              (n cidvp)
                              (if cidvp \in domm (prog_interface p)
                               then n cidvp else n'' cidvp) bidvp)
                    as [bidvp'''|] eqn:ebidvp_;
                    rewrite ebidvp_ in Hv'; try discriminate.
                  inversion Hv'. subst.

                  destruct (cidvp \in domm (prog_interface p)) eqn:ecidvp;
                    rewrite ecidvp in G'.
                  -- apply sigma_shifting_lefttoright_option_n_n_id in ebidvp_.
                     subst.
                     apply sigma_shifting_lefttoright_Some_inv_Some in ebidvp.
                     rewrite ebidvp in G'. inversion G'. by subst.
                  -- apply sigma_shifting_lefttoright_option_n_n_id in G'.
                     subst.
                     rewrite ebidvp in ebidvp_. by inversion ebidvp_.
                  
                  
                * specialize (s1'mem_mem0 _ _ Hload)
                    as [vprog [Hloadprog Hvprog]].

                  specialize (mem0_s2''mem _ _ Hloadprog)
                    as [v'' [Hload'' Hv'']].

                  destruct vprog as [| [[[permvp cidvp] bidvp] offvp] |];
                    inversion Hvprog; inversion Hv''; subst; try by eexists; eauto.

                  destruct (permvp =? Permission.data) eqn:epermvp;
                    inversion Hvprog; inversion Hv''; subst;
                      last (rewrite epermvp).
                  -- destruct (sigma_shifting_lefttoright_option
                                 (n cidvp) (n'' cidvp) bidvp) as [bidvp''|] eqn:ebidvp;
                       try discriminate.
                     inversion Hv''. subst. clear Hv''.

                     destruct (sigma_shifting_lefttoright_option
                                 (n cidvp)
                                 (if cidvp \in domm (prog_interface p)
                                  then n cidvp else n'' cidvp) bidvp)
                       as [bidvp'|] eqn:ebidvp''; rewrite ebidvp'' in Hvprog;
                       try discriminate.

                     inversion Hvprog; subst; clear Hvprog.
                     eexists; split; first eassumption. simpl.
                     rewrite epermvp.

                     destruct (cidvp \in domm (prog_interface p)) eqn:ecidvp;
                       rewrite ecidvp.
                     ++
                       remember ebidvp'' as Hrewr.
                       pose proof (sigma_shifting_lefttoright_option_n_n_id
                                     _ _ _ ebidvp'').
                       subst.
                       apply sigma_shifting_lefttoright_Some_inv_Some in ebidvp.
                         by rewrite ebidvp ebidvp''; right.
                     ++
                       apply sigma_shifting_lefttoright_Some_inv_Some in ebidvp.
                       assert (G: left_block_id_good_for_shifting (n'' cidvp) bidvp'').
                       by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                       erewrite sigma_lefttoright_Some_spec in G.
                       destruct G as [? G'].
                       erewrite G'.
                       apply sigma_shifting_lefttoright_option_n_n_id in G'. subst.
                       rewrite ebidvp''; right.
                       apply sigma_shifting_lefttoright_Some_inv_Some in ebidvp.
                       by rewrite ebidvp in ebidvp''; inversion ebidvp''.
                     
                  -- eexists; split; first eassumption. simpl. rewrite epermvp.
                     by right.
                  
              + split; intros ? ? Hload;
                  specialize (Hmemc'_ (cidorig, bidorig) Hcidorig Hnotshr'')
                  as [s2''mem_s1'mem s1'mem_s2''mem].
                * by specialize (s2''mem_s1'mem _ _ Hload).
                * by specialize (s1'mem_s2''mem _ _ Hload).
            - intros [cidorig bidorig] Hshr''_ext.

              specialize (Hr3 _ Hshr''_ext) as [[cidorig_prog bidorig_prog]
                                                  [Hbidorig_prog
                                                     [e'e'' Hshr_prog]]].
              destruct (sigma_shifting_lefttoright_option
                          (n cidorig_prog) 
                          (n'' cidorig_prog) bidorig_prog) eqn:ebidorig_prog;
                try discriminate.
              inversion Hbidorig_prog; subst. clear Hbidorig_prog.
              
              destruct e'e'' as [[cidorig_ bidorig_]
                                   [Hbidorig_
                                      [mem0_s2''mem s2''mem_mem0]
                                   ]
                                ].
              simpl in *.
              unfold rename_value_option, rename_value_template_option,
              sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid, rename_addr_option
                in *.

              rewrite ebidorig_prog in Hbidorig_.
              inversion Hbidorig_. subst. clear Hbidorig_.

              pose proof (sigma_shifting_lefttoright_Some_inv_Some
                            _ _ _ _ ebidorig_prog) as G.
              assert (left_block_id_good_for_shifting (n'' cidorig_) bidorig_) as G'.
                by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
              erewrite sigma_lefttoright_Some_spec in G'. destruct G' as [bidorig' G''].
              erewrite G''.
              eexists. split; first reflexivity; split; intros ? ? Hload.
              + assert (vGood: left_value_good_for_shifting n'' v).
                {
                  eapply Hgood_prog''.
                  3: { exact Hload. }
                  3: { reflexivity. }
                  3: { simpl. by erewrite sigma_lefttoright_Some_spec; eauto. }
                  eauto. eauto.
                }
                

                specialize (s2''mem_mem0 _ _ Hload) as [vprog [Hloadprog Hvprog]].

                assert (vprogGood: left_value_good_for_shifting n vprog).
                {
                  destruct vprog as [| [[[perm cid] bid] off] |]
                                      eqn:evprog; simpl; auto.
                  destruct (perm =? Permission.data) eqn:eperm; auto.
                  destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                           eqn:esigma; try discriminate.
                  by erewrite sigma_lefttoright_Some_spec; eexists; eauto. 
                }

                
                destruct (cidorig_ \in domm (prog_interface p)) eqn:ecidorig_;
                  rewrite ecidorig_ in G''; simpl in *.
                *
                  rewrite G'' in G; inversion G; subst; clear G.
                  specialize (mem0s1'mem_priv
                                 (cidorig_, bidorig_prog)
                                 ecidorig_) as [mem0s1'mem ?].
                  specialize (mem0s1'mem _ _ Hloadprog).
                  destruct vprog
                    as [| [[[permvprog cidvprog] bidvprog] offvprog] |];
                    inversion Hvprog; subst;
                      try by eexists; split; eauto.
                  destruct (permvprog =? Permission.data) eqn:epermvprog;
                    inversion Hvprog; subst.
                  -- destruct (sigma_shifting_lefttoright_option
                                 (n cidvprog) (n'' cidvprog) bidvprog) eqn:esigma;
                       try discriminate.
                     inversion Hvprog. subst. rewrite epermvprog.
                     simpl in vGood. rewrite epermvprog in vGood.
                     erewrite sigma_lefttoright_Some_spec in vGood.
                     destruct vGood as [? erewr]. erewrite erewr.
                     eexists; split; eauto.
                     destruct (cidvprog \in domm (prog_interface p)) eqn:ecidvprog;
                       rewrite ecidvprog in erewr; rewrite ecidvprog in mem0s1'mem.
                     ++
                       assert (exists bidvprog',
                                  sigma_shifting_lefttoright_option
                                    (n cidvprog) (n cidvprog) bidvprog
                                  = Some bidvprog'
                              ) as [bidvprog' ebidvprog'].
                       {
                         erewrite <- sigma_lefttoright_Some_spec.
                           by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                       }
                       pose proof (sigma_shifting_lefttoright_option_n_n_id
                                     _ _ _ ebidvprog').
                       subst.
                       rewrite ebidvprog' in mem0s1'mem.
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       rewrite esigma in erewr. by inversion erewr; subst.
                     ++
                       rewrite esigma in mem0s1'mem.
                       apply sigma_shifting_lefttoright_option_n_n_id in erewr.
                         by subst.
                  -- rewrite epermvprog; by eexists; split; eauto.

                * assert (cidorig_ \in domm (prog_interface c')) as ecidorig_c'.
                    (** Follows from Hloadprog and ecidorig_ *) by admit.

                  apply sigma_shifting_lefttoright_option_n_n_id in G''. subst.
                       
                  specialize (Coq.Logic.Classical_Prop.classic 
                              (addr_shared_so_far (cidorig_, bidorig_prog) t1)
                             ) as [Hshrt1 | Hnotshrt1].
                  
                  --
                    specialize (mem0s1'mem_shr _ Hshrt1)
                      as [[cidorig' bid_prog'] [ebid_prog' [mem0s1'mem ?]]].
                    specialize (mem0s1'mem _ _ Hloadprog) as [v' [Hloads1'mem Hv']].
                    
                    rewrite ecidorig_ ebidorig_prog in ebid_prog'.
                    inversion ebid_prog'; subst; clear ebid_prog'. simpl in *.
                    
                    destruct vprog
                      as [| [[[permvprog cidvprog] bidvprog] offvprog] |];
                      inversion Hvprog; inversion Hv'; subst;
                        try by eexists; split; eauto.
                    destruct (permvprog =? Permission.data) eqn:epermvprog;
                      inversion Hvprog; inversion Hv'; subst.
                    ++
                      destruct (sigma_shifting_lefttoright_option
                                  (n cidvprog)
                                  (if cidvprog \in domm (prog_interface p)
                                   then n cidvprog else n'' cidvprog)
                                  bidvprog) eqn:ebidvprog;
                        rewrite ebidvprog in Hv'; try discriminate.
                      inversion Hv'; subst; clear Hv'.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cidvprog) (n'' cidvprog) bidvprog)
                               eqn:ebidvprog2; try discriminate.
                      inversion Hvprog; subst; clear Hvprog.
                      rewrite epermvprog.
                      eexists; split; eauto.
                      destruct (cidvprog \in domm (prog_interface p)) eqn:ecidvprog;
                        rewrite ecidvprog.
                      **
                        apply sigma_shifting_lefttoright_option_n_n_id in ebidvprog.
                        subst.
                        apply sigma_shifting_lefttoright_Some_inv_Some in ebidvprog2.
                          by rewrite ebidvprog2.
                      **
                        rewrite ebidvprog in ebidvprog2. inversion ebidvprog2. subst.
                        apply sigma_shifting_lefttoright_Some_inv_Some in ebidvprog.
                        assert (exists blk, sigma_shifting_lefttoright_option
                                              (n'' cidvprog)
                                              (n'' cidvprog) i0 = Some blk)
                          as [blk Hblk].
                          by erewrite <- sigma_lefttoright_Some_spec;
                            erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                          rewrite Hblk.
                            by apply sigma_shifting_lefttoright_option_n_n_id in Hblk;
                              subst.
                            
                    ++ rewrite epermvprog. by eexists; split; eauto.

                  -- (** Here, want to use Hmemc'_. *)
                    
                    assert (~ addr_shared_so_far (cidorig_, bidorig_) t1'')
                      as Hnotshrt1''.
                    {
                      intros contra.
                      inversion Hshift_t''t' as [? ? Hren]; subst.
                      inversion Hren as [| t'' e'' t' e' ? ? Ht''t' ? ? ?]; subst;
                        try by inversion contra; subst; find_nil_rcons.
                      specialize (Ht''t' _ contra) as
                          [He''e' [[cid' bid'] [ecid'bid' Hshrcid'bid']]].

                      apply Hnotshrt1.

                      inversion Hshift_tt' as [? ? Hren2]; subst.
                      inversion Hren2 as [| t e t'2 e'2 ? ? ? Ht't ? ?]; subst;
                        try by inversion Hshrcid'bid'; subst; find_nil_rcons.
                      
                      match goal with
                      | H11: rcons _ _ = rcons _ _ |- _ =>
                        apply rcons_inj in H11; inversion H11; subst; clear H11
                      end.

                      specialize (Ht't _ Hshrcid'bid') as
                          [[cidren bidren] [ebidren [? G_]]].

                      unfold sigma_shifting_wrap_bid_in_addr,
                      sigma_shifting_lefttoright_addr_bid in *.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cidren)
                                  (if cidren \in domm (prog_interface p)
                                   then n cidren else n'' cidren) bidren) eqn:esigma;
                        rewrite esigma in ebidren; try discriminate.
                      inversion ebidren; subst; clear ebidren.

                      destruct (sigma_shifting_lefttoright_option
                                  (n'' cidorig_)
                                  (if cidorig_ \in domm (prog_interface p)
                                   then n cidorig_ else n'' cidorig_)
                                  bidorig_) eqn:esigma2;
                        rewrite esigma2 in ecid'bid'; try discriminate.
                      inversion ecid'bid'; subst; clear ecid'bid'.

                      rewrite ecidorig_ in esigma.
                      rewrite ecidorig_ in esigma2.
                      apply sigma_shifting_lefttoright_option_n_n_id in esigma2. subst.
                      apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                      rewrite esigma in G; inversion G; subst.
                      exact G_.
                    }

                    specialize (Hmemc'_ (cidorig_, bidorig_) ecidorig_c' Hnotshrt1'')
                      as [s2''mems1'mem _].
                    specialize (s2''mems1'mem _ _ Hload).

                    destruct vprog
                      as [| [[[permvprog cidvprog] bidvprog] offvprog] |];
                      inversion Hvprog; subst;
                        try by eexists; split; eauto.
                    destruct (permvprog =? Permission.data) eqn:epermvprog;
                      inversion Hvprog; subst.
                    ++
                      destruct (sigma_shifting_lefttoright_option
                                  (n cidvprog)
                                  (n'' cidvprog)
                                  bidvprog) as [bidvprog'|] eqn:ebidvprog;
                        try discriminate.
                      inversion Hvprog; subst; clear Hvprog.

                      
                      rewrite epermvprog. rewrite epermvprog in s2''mems1'mem.
                      destruct (cidvprog \in domm (prog_interface p)) eqn:ecidvprog;
                        rewrite ecidvprog; rewrite ecidvprog in s2''mems1'mem;
                          simpl in *.
                      **
                        apply sigma_shifting_lefttoright_Some_inv_Some in ebidvprog.
                        rewrite ebidvprog. rewrite ebidvprog in s2''mems1'mem.
                        by eexists; split; eauto.
                      **
                        apply sigma_shifting_lefttoright_Some_inv_Some in ebidvprog.
                        assert (exists blk, sigma_shifting_lefttoright_option
                                              (n'' cidvprog) (n'' cidvprog) bidvprog'
                                            = Some blk) as [blk eblk].
                        {
                          by erewrite <- sigma_lefttoright_Some_spec;
                            erewrite sigma_lefttoright_Some_spec; eexists; eauto. 
                        }
                        rewrite eblk. rewrite eblk in s2''mems1'mem.
                        by eexists; split; eauto.
                            
                    ++ rewrite epermvprog. rewrite epermvprog in s2''mems1'mem.
                         by eexists; split; eauto.


              + assert (vGood: forall v,
                           Memory.load
                             s2''mem
                             (Permission.data, cidorig_, bidorig_, offset) = Some v
                           ->
                           left_value_good_for_shifting n'' v).
                {
                  intros ? Hloads2''mem.
                  eapply Hgood_prog''.
                  3: { exact Hloads2''mem. }
                  3: { reflexivity. }
                  3: { simpl. by erewrite sigma_lefttoright_Some_spec; eauto. }
                  eauto. eauto.
                }
                
                
                destruct (cidorig_ \in domm (prog_interface p)) eqn:ecidorig_;
                  rewrite ecidorig_ in G''; simpl in *.
                *
                  rewrite G'' in G; inversion G; subst; clear G.
                  specialize (mem0s1'mem_priv
                                 (cidorig_, bidorig_prog)
                                 ecidorig_) as [? s1'mem_mem0].
                  specialize (s1'mem_mem0 _ _ Hload)
                    as [vprog [Hloadprog Hvprog]].

                  specialize (mem0_s2''mem _ _ Hloadprog) as [v'' [Hloads2''mem Hv'']].
                  
                  assert (vprogGood: 
                            left_value_good_for_shifting n vprog).
                  {
                    destruct vprog as [| [[[perm cid] bid] off] |]
                                        eqn:evprog; simpl; auto.
                    destruct (perm =? Permission.data) eqn:eperm; auto.
                    destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                             eqn:esigma; try discriminate.
                    by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                  }
                  
                  destruct vprog
                    as [| [[[permvprog cidvprog] bidvprog] offvprog] |];
                    inversion Hv''; subst;
                      try by inversion Hvprog as [[contra ?] | ]; eexists; split; eauto.
                  destruct (permvprog =? Permission.data) eqn:epermvprog;
                    inversion Hv''; subst.
                  -- destruct (sigma_shifting_lefttoright_option
                                 (n cidvprog) (n'' cidvprog) bidvprog) as [bidvprog'|]
                                                                            eqn:esigma;
                       try discriminate.
                     inversion Hv''; subst.
                     simpl in vprogGood. rewrite epermvprog in vprogGood.
                     erewrite sigma_lefttoright_Some_spec in vprogGood.
                     destruct vprogGood as [? erewr]. erewrite erewr in Hvprog.
                     destruct Hvprog as [[contra ?] | Hv']; first discriminate.
                     inversion Hv'. subst. clear Hv' Hv''.
                     eexists; split; eauto; simpl. rewrite epermvprog.
                     
                     destruct (cidvprog \in domm (prog_interface p)) eqn:ecidvprog;
                       rewrite ecidvprog in erewr; rewrite ecidvprog.
                     ++
                       pose proof (sigma_shifting_lefttoright_option_n_n_id
                                     _ _ _ erewr).
                       subst.
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       by rewrite esigma.
                     ++
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       assert (exists blk,
                                  sigma_shifting_lefttoright_option
                                    (n'' cidvprog) (n'' cidvprog) bidvprog'
                                  = Some blk
                              ) as [blk ebidvprog'].
                       {
                         erewrite <- sigma_lefttoright_Some_spec.
                         erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                       }
                       erewrite ebidvprog'.
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       rewrite erewr in esigma. inversion esigma. subst.
                       
                       by apply sigma_shifting_lefttoright_option_n_n_id
                         in ebidvprog'; subst.
                       
                  -- eexists; split; eauto. simpl. rewrite epermvprog.
                     by destruct Hvprog as [[? ?] | ?].
                       

                * assert (cidorig_ \in domm (prog_interface c')) as ecidorig_c'.
                    (** Follows from Hloadprog and ecidorig_ *) by admit.

                  apply sigma_shifting_lefttoright_option_n_n_id
                    in G''; subst.

                  
                  specialize (Coq.Logic.Classical_Prop.classic 
                                (addr_shared_so_far (cidorig_, bidorig_prog) t1)
                             ) as [Hshrt1 | Hnotshrt1].

                  --
                  specialize (mem0s1'mem_shr
                                (cidorig_, bidorig_prog)
                                Hshrt1) as [[cidorig_' bidorig_prog']
                                              [esigma [_ s1'mem_mem0]]].
                  simpl in *.

                  destruct (sigma_shifting_lefttoright_option
                              (n cidorig_)
                              (if cidorig_ \in domm (prog_interface p)
                               then n cidorig_ else n'' cidorig_)
                              bidorig_prog) eqn:esigma'; rewrite esigma' in esigma;
                    try discriminate.
                  inversion esigma; subst; clear esigma.
                  rewrite ecidorig_ in esigma'.
                  apply sigma_shifting_lefttoright_Some_inv_Some in G.
                  rewrite G in esigma'. inversion esigma'; subst; clear esigma'.

                  
                  specialize (s1'mem_mem0 _ _ Hload)
                    as [vprog [Hloadprog Hvprog]].

                  specialize (mem0_s2''mem _ _ Hloadprog) as [v'' [Hloads2''mem Hv'']].
                  
                  assert (vprogGood: 
                            left_value_good_for_shifting n vprog).
                  {
                    destruct vprog as [| [[[perm cid] bid] off] |]
                                        eqn:evprog; simpl; auto.
                    destruct (perm =? Permission.data) eqn:eperm; auto.
                    destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                             eqn:esigma; try discriminate.
                    by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                  }
                  
                  destruct vprog
                    as [| [[[permvprog cidvprog] bidvprog] offvprog] |];
                    inversion Hvprog; inversion Hv''; subst;
                      try by eexists; split; eauto.
                  destruct (permvprog =? Permission.data) eqn:epermvprog;
                    inversion Hvprog; inversion Hv''; subst.
                  
                  ++ destruct (sigma_shifting_lefttoright_option
                                 (n cidvprog) (n'' cidvprog) bidvprog) as [bidvprog'|]
                                                                            eqn:esigma;
                       try discriminate.
                     inversion Hv''; subst.
                     simpl in vprogGood. rewrite epermvprog in vprogGood.
                     erewrite sigma_lefttoright_Some_spec in vprogGood.
                     destruct vprogGood as [? erewr]. erewrite erewr in Hvprog.
                     inversion Hvprog. subst. clear Hvprog Hv''.
                     eexists; split; eauto; simpl. rewrite epermvprog.
                     
                     destruct (cidvprog \in domm (prog_interface p)) eqn:ecidvprog;
                       rewrite ecidvprog in erewr; rewrite ecidvprog.
                     **
                       pose proof (sigma_shifting_lefttoright_option_n_n_id
                                     _ _ _ erewr).
                       subst.
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       by rewrite esigma erewr.
                     **
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       assert (exists blk,
                                  sigma_shifting_lefttoright_option
                                    (n'' cidvprog) (n'' cidvprog) bidvprog'
                                  = Some blk
                              ) as [blk ebidvprog'].
                       {
                         erewrite <- sigma_lefttoright_Some_spec.
                         erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                       }
                       erewrite ebidvprog'.
                       apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                       rewrite erewr in esigma. inversion esigma. subst.
                       rewrite erewr.
                       
                       by apply sigma_shifting_lefttoright_option_n_n_id
                         in ebidvprog'; subst.
                       
                  ++ eexists; split; eauto. simpl. by rewrite epermvprog.

                  --
                    assert (Hnotshr: ~ addr_shared_so_far (cidorig_, bidorig_) t1'').
                    {
                      intros Hshr.
                      inversion Hrel2 as [? ? Hren]; subst.
                      inversion Hren as [| t e t'' e'' ? Htt''  _ _ _ _]; subst;
                        try by inversion Hshr; subst; find_nil_rcons.
                      repeat match goal with
                             | H18: rcons _ _ = rcons _ _ |- _ =>
                               apply rcons_inj in H18; inversion H18; subst; clear H18
                             end.
                      inversion Htt'' as [| t e t'' e'' ? ?  ? Htt''_ ? ? ?]; subst;
                        try by inversion Hshr; subst; find_nil_rcons.
                      specialize (Htt''_ _ Hshr) as [[cid bid] [ebid [_ econtra]]].
                      unfold sigma_shifting_wrap_bid_in_addr,
                      sigma_shifting_lefttoright_addr_bid in *.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid) (n'' cid) bid) eqn:esigma; try discriminate.
                      inversion ebid; subst; clear ebid.
                      apply sigma_shifting_lefttoright_Some_inv_Some in G.
                      specialize (sigma_shifting_lefttoright_option_Some_inj
                                    _ _ _ _ _ G esigma) as ?; subst.
                      by apply Hnotshrt1.
                    }

                    specialize (Hmemc'_ (cidorig_, bidorig_) ecidorig_c' Hnotshr)
                      as [_ s1'mem_s2''mem].
                    specialize (s1'mem_s2''mem _ _ Hload) as [v [Hloadv Hv]].

                    specialize (vGood _ Hloadv).

                    eexists; split; first exact Hloadv.
                    destruct v as [| [[[permv cidv] bidv] offv] |];
                      destruct Hv as [[contra ?] | rewr]; try discriminate;
                        try by inversion rewr; subst.
                    destruct (permv =? Permission.data) eqn:epermv; try discriminate.
                    simpl in *. rewrite epermv in vGood.
                    erewrite sigma_lefttoright_Some_spec in vGood.
                    destruct vGood as [? G_]. by erewrite G_ in contra.
          }



          assert (mem0_s1'mem:
                    mem_of_part_not_executing_rel_original_and_recombined_at_border
                      p
                      mem0
                      s1'mem
                      n
                      (fun cid : nat_ordType =>
                         if cid \in domm (prog_interface p) then n cid else n'' cid)
                      (rcons
                         t1
                         (ECall
                            (Pointer.component pc)
                            P0
                            (Register.get R_COM regs)
                            mem0
                            C'0
                         )
                      )
                 ).
          {
            unfold event_renames_event_at_shared_addr,
            mem_of_part_not_executing_rel_original_and_recombined_at_border,
            mem_of_part_executing_rel_original_and_recombined,
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
            memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid, rename_addr_option
              in *.

            destruct Hmemc' as [Hmemc'_ next_block_s2''mem_s1'mem].
            destruct Hmemp as [mem0s1'mem_priv [mem0s1'mem_shr next_block_mem0s1'mem]].
            destruct s2''mem_s1'mem
              as [s2''mems1'mem_priv [s2''mems1'mem_shr next_block_s2''mems1'mem]].
            
            split; last split; auto; simpl in *.

            intros [cidorig bidorig] Hshr.
            specialize (Hr2 _ Hshr)
              as [[[cidorig'' bidorig''] [ebidorig'' [mem0s2''mem s2''mem_mem0]]]
                    [[cidorig''2 bidorig''2] [ebidorig''2 Hshr'']]
                 ].

            destruct (sigma_shifting_lefttoright_option
                        (n cidorig) (n'' cidorig) bidorig) eqn:esigma; try discriminate.
            inversion ebidorig''2; subst; inversion ebidorig''; subst.
            clear ebidorig'' ebidorig''2.

            assert (exists bidorig', sigma_shifting_lefttoright_option
                                       (n cidorig'')
                                       (if cidorig'' \in domm (prog_interface p)
                                        then n cidorig'' else n'' cidorig'') bidorig
                                     = Some bidorig') as [bidorig' ebidorig'].
            {
              erewrite <- sigma_lefttoright_Some_spec.
              erewrite sigma_lefttoright_Some_spec.
              eexists; eassumption.
            }

            rewrite ebidorig'. eexists; split; first reflexivity.
            split; intros ? ? Hload; simpl in *.

            - specialize (mem0s2''mem _ _ Hload) as [v' [Hloadv' Hv']].

              assert (v'Good: left_value_good_for_shifting n'' v').
              {
                destruct v as [| [[[perm cid] bid] off] |]
                                eqn:ev; inversion Hv'; simpl; auto.
                destruct (perm =? Permission.data) eqn:eperm; inversion Hv'; subst;
                  simpl in *.
                - destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                           eqn:esigma2; try discriminate.
                  inversion Hv'; subst. simpl. rewrite eperm.
                  erewrite sigma_lefttoright_Some_spec; eexists; eauto. 
                  erewrite sigma_shifting_lefttoright_Some_inv_Some;
                    last eassumption; reflexivity.
                - by rewrite eperm. 
              }

              specialize (s2''mems1'mem_shr _ Hshr'')
                as [[cidorig''2 bidorig''2] [ebidorig''2 [s2''mems1'mem _]]].
              specialize (s2''mems1'mem _ _ Hloadv') as [vG [G1 G2]].

              destruct (sigma_shifting_lefttoright_option
                          (n'' cidorig'')
                          (if cidorig'' \in domm (prog_interface p)
                           then n cidorig'' else n'' cidorig'')
                          bidorig'') eqn:ebidorig'';
                rewrite ebidorig'' in ebidorig''2; try discriminate.
              inversion ebidorig''2; subst; clear ebidorig''2.

              eexists; split.
              +
                destruct (cidorig''2 \in domm (prog_interface p)) eqn:ecid;
                  rewrite ecid in ebidorig'.
                * pose proof (sigma_shifting_lefttoright_option_n_n_id
                                _ _ _ ebidorig').
                  subst.
                  eapply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                  rewrite ebidorig'' in esigma. inversion esigma. subst.
                  eassumption.
                * pose proof (sigma_shifting_lefttoright_option_n_n_id
                                _ _ _ ebidorig'').
                  subst.
                  rewrite esigma in ebidorig'. inversion ebidorig'. subst.
                  eassumption.
              +
                destruct v as [| [[[permv cidv] bidv] offv] |];
                  inversion Hv' as [Hv'_]; subst; inversion G2 as [G2_]; subst; auto.
                destruct (permv =? Permission.data) eqn:epermv.
                * destruct (sigma_shifting_lefttoright_option (n cidv) (n'' cidv) bidv)
                           as [bidv'|] eqn:ebidv; try discriminate.
                  inversion Hv'_; subst; clear Hv'_. rewrite epermv in G2_.
                  rewrite epermv.
                  destruct (cidv \in domm (prog_interface p)) eqn:ecidv;
                    rewrite ecidv; rewrite ecidv in G2_.
                  --
                    rewrite G2_.
                    destruct (sigma_shifting_lefttoright_option
                                (n'' cidv) (n cidv) bidv') as [bidv2|] eqn:ebidv2;
                      try discriminate.
                    inversion G2_; subst; clear G2_ G2.
                    eapply sigma_shifting_lefttoright_Some_inv_Some in ebidv.
                    rewrite ebidv in ebidv2. inversion ebidv2; subst; clear ebidv2.
                    eapply sigma_shifting_lefttoright_Some_inv_Some in ebidv.
                    assert (sigma_shifting_lefttoright_option (n cidv) (n cidv)
                                                              bidv2 = Some bidv2) as G.
                    {
                      suffices: (exists bidv', sigma_shifting_lefttoright_option
                                                 (n cidv) (n cidv) bidv2 = Some bidv').
                      - intros [? Hsome].
                        pose proof (sigma_shifting_lefttoright_option_n_n_id
                                      _ _ _ Hsome); by subst.
                      - erewrite <- sigma_lefttoright_Some_spec.
                        erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                    }

                    by rewrite G.
                    
                    
                  -- 
                    destruct (sigma_shifting_lefttoright_option
                                (n'' cidv) (n'' cidv) bidv') as [bidv2|] eqn:ebidv2;
                      try discriminate.
                    inversion G2_; subst; clear G2_ G2.
                    eapply sigma_shifting_lefttoright_option_n_n_id in ebidv2; subst.
                    by rewrite ebidv.

                * inversion Hv'_. by rewrite epermv.

            - specialize (s2''mems1'mem_shr _ Hshr'')
                as [[cidorig' bidorig'_] [ebidorig'_ [_ s1'mems2''mem]]].
              destruct (sigma_shifting_lefttoright_option
                          (n'' cidorig'')
                          (if cidorig'' \in domm (prog_interface p)
                           then n cidorig'' else n'' cidorig'')
                          bidorig'') eqn:esigma_; rewrite esigma_ in ebidorig'_;
                try discriminate.
              inversion ebidorig'_; subst; clear ebidorig'_.

              assert (bidorig' = bidorig'_).
              {
                destruct (cidorig' \in domm (prog_interface p)) eqn:e;
                  rewrite e in ebidorig'.
                - apply sigma_shifting_lefttoright_option_n_n_id in ebidorig'. subst.
                  apply sigma_shifting_lefttoright_Some_inv_Some in esigma_.
                  by eapply sigma_shifting_lefttoright_option_Some_inj; eauto.
                - apply sigma_shifting_lefttoright_option_n_n_id in esigma_. subst.
                  rewrite esigma in ebidorig'. by inversion ebidorig'.
              }
              subst.

              specialize (s1'mems2''mem _ _ Hload) as [v'' [Hloadv'' Hv'']].
              specialize (s2''mem_mem0 _ _ Hloadv'') as [v [Hloadv Hv]].

              eexists; split; eauto.

              destruct v as [| [[[permv cidv] bidv] offv] |];
                inversion Hv; subst; inversion Hv''; subst; simpl; auto.

              destruct (permv =? Permission.data) eqn:epermv; simpl in *.
              + destruct (sigma_shifting_lefttoright_option (n cidv) (n'' cidv) bidv)
                         as [bidv''|] eqn:esigmav; try discriminate.
                inversion Hv; subst. rewrite epermv in Hv''.
                destruct (sigma_shifting_lefttoright_option
                            (n'' cidv)
                            (if cidv \in domm (prog_interface p)
                             then n cidv else n'' cidv) bidv'')
                  as [bidv'|] eqn:esigmav';
                  rewrite esigmav' in Hv''; try discriminate.
                inversion Hv''; subst.
                rewrite esigmav' epermv.
                assert (left_block_id_good_for_shifting (n cidv) bidv) as G.
                  by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                erewrite sigma_lefttoright_Some_spec in G.
                destruct G as [bidv'_ rewr].
                erewrite rewr.
                destruct (cidv \in domm (prog_interface p)) eqn:ecidv.
                * rewrite ecidv in rewr.
                  apply sigma_shifting_lefttoright_option_n_n_id in rewr. subst.
                  apply sigma_shifting_lefttoright_Some_inv_Some in esigmav.
                  rewrite esigmav' in esigmav. by inversion esigmav.
                * rewrite ecidv in rewr.
                  apply sigma_shifting_lefttoright_option_n_n_id in esigmav'. subst.
                  rewrite rewr in esigmav. by inversion esigmav.
              + inversion Hv; subst. rewrite epermv in Hv''. by rewrite epermv.
                                
          }

          assert (reachmem0_reachs1'mem: forall cidl bidl bidl',
                     Reachable mem0 (addr_of_value (Register.get R_COM regs))
                               (cidl, bidl) ->
                     sigma_shifting_lefttoright_option
                       (n cidl)
                       (if cidl \in domm (prog_interface p) then n cidl else n'' cidl)
                       bidl = Some bidl' ->
                     Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
                               (cidl, bidl')
                 ).
          {
            intros cidl bidl bidl' Hreach Hsigma.
            eapply Reachable_memrel_Reachable_corollary; eauto.
          }


          assert (reachs1'mem_reachmem0: forall cidl bidl,
                     Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
                               (cidl, bidl) ->
                     exists bidl',
                     sigma_shifting_lefttoright_option
                       (if cidl \in domm (prog_interface p) then n cidl else n'' cidl)
                       (n cidl)
                       bidl = Some bidl'
                     /\
                     Reachable mem0 (addr_of_value (Register.get R_COM regs))
                               (cidl, bidl')
                 ).
          {
            intros cidl bidl Hreach.
            pose proof Reachable_memrel_Reachable2 as G.
            unfold sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            specialize (G _ _ _ _ _ _ _ _ _ Hgood2 Hrel_R_COM mem0_s1'mem Hreach)
              as [[? ?] [rewr ?]].
            destruct (sigma_shifting_lefttoright_option
                        (if cidl \in domm (prog_interface p) then n cidl else n'' cidl) 
                        (n cidl) bidl) eqn:ebidl;
              rewrite ebidl in rewr; try discriminate; inversion rewr; subst.
            by eexists; split; eauto.
          }


          
          assert (shrt1_shrt1'_ext: forall (addr : addr_t),
                     addr_shared_so_far
                       addr
                       (rcons
                          t1
                          (ECall
                             (Pointer.component pc)
                             P0
                             (Register.get R_COM regs)
                             mem0
                             C'0
                          )
                       )
                     ->
                     event_renames_event_at_shared_addr
                       n
                       (fun cid : nat => if cid \in domm (prog_interface p)
                                         then n cid else n'' cid)
                       addr
                       (ECall (Pointer.component pc) P0 (Register.get R_COM regs)
                              mem0 C'0)
                       (ECall (Pointer.component pc) P0 (Register.get R_COM s1'reg)
                              s1'mem C'0)
                     /\
                     (exists addr' : addr_t,
                         sigma_shifting_wrap_bid_in_addr
                           (sigma_shifting_lefttoright_addr_bid
                              n
                              (fun cid : nat => if cid \in domm (prog_interface p)
                                                then n cid else n'' cid)
                           )
                           addr =
                         Some addr'
                         /\
                         addr_shared_so_far
                           addr'
                           (rcons
                              t1'
                              (ECall (Pointer.component pc)
                                     P0
                                     (Register.get R_COM s1'reg)
                                     s1'mem
                                     C'0
                              )
                           )
                     )
                 ).
          {
            unfold event_renames_event_at_shared_addr,
            mem_of_part_not_executing_rel_original_and_recombined_at_border,
            mem_of_part_executing_rel_original_and_recombined,
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
            memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid, rename_addr_option
              in *.

            intros [cidorig bidorig] Hshr.

            inversion Hgood2 as [? Hgood2_]; subst.
            specialize (Hgood2_ _ Hshr) as Hbidorig_good.

            simpl in *;
              erewrite sigma_lefttoright_Some_spec in Hbidorig_good;
              destruct Hbidorig_good as [bidorig' rewr_];
              erewrite rewr_.

            split; eexists; (split; first reflexivity).
            - destruct mem0_s1'mem as [_ [G _]].
              specialize (G _ Hshr) as [[cidorig'_ bidorig'_] [ebidorig' G_]].
              simpl in *. rewrite rewr_ in ebidorig'.
              inversion ebidorig'; subst; clear ebidorig'.
              exact G_.
            - inversion Hshr as [? ? ? Hreach|
                                 ? [addr'cid addr'bid] ? ? Haddr'shr Hreach]; subst;
                match goal with
                | H11: rcons _ _ = rcons _ _ |- _ =>
                  apply rcons_inj in H11; inversion H11; subst; clear H11
                end; clear Hshr; simpl in *.
              + assert (Reachable s1'mem (addr_of_value (Register.get R_COM s1'reg))
                                  (cidorig, bidorig')
                       ) as Hreach'.
                {
                  eapply reachmem0_reachs1'mem; eauto.
                }
                eapply reachable_from_args_is_shared; eauto.
              + (*pose proof (@shared_Reachable_memrel_shared_Reachable
                              C'0 mem0 regs P0 pc 
                              Hgood_t
                              Hshift_tt'
                              mem0_s1'mem
                ) as G.*)
                inversion Hgood_t as [? goodt1]; subst.
                specialize (goodt1 _ Haddr'shr). simpl in *.
                erewrite sigma_lefttoright_Some_spec in goodt1.
                destruct goodt1 as [bidG' ebidG'].
                
                apply reachable_from_previously_shared
                  with (addr' := (addr'cid, bidG')); auto; simpl;
                specialize (shared_Reachable_memrel_shared_Reachable
                              Hgood_t
                              Hshift_tt'
                              mem0_s1'mem
                              Haddr'shr
                              Hreach
                           ) as [? [? [esigma1 [esigma2 [? ?]]]]];
                unfold sigma_shifting_wrap_bid_in_addr,
                sigma_shifting_lefttoright_addr_bid in *;
                erewrite ebidG' in esigma2; inversion esigma2; subst;
                rewrite rewr_ in esigma1; inversion esigma1; subst.
                * assumption. 
                * assumption.
          }
          
              

          assert (shrt1'_shrt1_ext: forall addr' : addr_t,
                     addr_shared_so_far
                       addr'
                       (rcons
                          t1'
                          (ECall
                             (Pointer.component pc)
                             P0 (Register.get R_COM s1'reg) s1'mem C'0)) ->
                     exists addr : addr_t,
                       sigma_shifting_wrap_bid_in_addr
                         (sigma_shifting_lefttoright_addr_bid
                            n
                            (fun cid : nat => if cid \in domm (prog_interface p)
                                              then n cid else n'' cid)) addr =
                       Some addr' /\
                       event_renames_event_at_shared_addr
                         n
                         (fun cid : nat => if cid \in domm (prog_interface p)
                                           then n cid else n'' cid)
                         addr
                         (ECall (Pointer.component pc)
                                P0 (Register.get R_COM regs) mem0 C'0)
                         (ECall (Pointer.component pc)
                                P0 (Register.get R_COM s1'reg) s1'mem C'0) /\
                       addr_shared_so_far
                         addr
                         (rcons
                            t1
                            (ECall
                               (Pointer.component pc)
                               P0 (Register.get R_COM regs) mem0 C'0))).
          {
            unfold event_renames_event_at_shared_addr,
            mem_of_part_not_executing_rel_original_and_recombined_at_border,
            mem_of_part_executing_rel_original_and_recombined,
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
            memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid, rename_addr_option
              in *.

            intros [cidorig bidorig] Hshr.

            (* inversion Hgood2 as [? Hgood2_]; subst.
               specialize (Hgood2_ _ Hshr) as Hbidorig_good.*)

            simpl in *.

            
            inversion Hshr as [? ? ? Hreach|
                               ? [addr'cid addr'bid] ? ? Haddr'shr Hreach]; subst;
              match goal with
              | H11: rcons _ _ = rcons _ _ |- _ =>
                apply rcons_inj in H11; inversion H11; subst; clear H11
              end; clear Hshr; simpl in *.
            - specialize (reachs1'mem_reachmem0 _ _ Hreach)
                as [bidl' [ebidl' Hreach_mem0]].
              apply sigma_shifting_lefttoright_Some_inv_Some in ebidl'.
              exists (cidorig, bidl'); rewrite ebidl'; split; first reflexivity.
              assert (Hshrt1_rcons: addr_shared_so_far
                        (cidorig, bidl')
                        (rcons t1 (ECall
                                     (Pointer.component pc)
                                     P0 (Register.get R_COM regs) mem0 C'0))).
              {
                eapply reachable_from_args_is_shared; eauto. 
              }
              split; eauto.
              eexists; split; first reflexivity.
              destruct mem0_s1'mem as [_ [G _]].
              specialize (G _ Hshrt1_rcons) as [[cidorig'_ bidorig'_] [ebidorig' G_]].
              rewrite ebidl' in ebidorig'.
              inversion ebidorig'; subst; exact G_.
            - inversion Hgood_t' as [? goodt1']; subst.
              specialize (goodt1' _ Haddr'shr). simpl in *.
              erewrite sigma_lefttoright_Some_spec in goodt1'.
              destruct goodt1' as [bidG' ebidG'].

              specialize (shared_Reachable_memrel_shared_Reachable2
                              Hgood_t
                              Hshift_tt'
                              mem0_s1'mem
                              Haddr'shr
                              Hreach
                           ) as [? [? [esigma1 [esigma2 [? ?]]]]].

              unfold sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.

              erewrite ebidG' in esigma2; inversion esigma2; subst; clear esigma2.

              destruct (sigma_shifting_lefttoright_option
                          (if cidorig \in domm (prog_interface p)
                           then n cidorig else n'' cidorig)
                          (n cidorig) bidorig) as [bidorig'|] eqn:ebidorig';
                rewrite ebidorig' in esigma1; try discriminate;
                  inversion esigma1; subst.
              apply sigma_shifting_lefttoright_Some_inv_Some in ebidorig'.
              exists (cidorig, bidorig').
              rewrite ebidorig'.
              split; first reflexivity.
              assert (Hshrt1_rcons: addr_shared_so_far
                        (cidorig, bidorig')
                        (rcons t1 (ECall
                                     (Pointer.component pc)
                                     P0 (Register.get R_COM regs) mem0 C'0))).
              {
                apply reachable_from_previously_shared
                  with (addr' := (addr'cid, bidG')); auto; simpl.
              }
              split; last assumption.
              eexists; split; first reflexivity.
              destruct mem0_s1'mem as [_ [G _]].
              specialize (G _ Hshrt1_rcons) as [[cidorig'_ bidorig'_] [ebidorig'2 G_]].
              rewrite ebidorig' in ebidorig'2.
              inversion ebidorig'2; subst; exact G_.
          }

          assert (Hgoodt1'_rcons:
                    good_trace_extensional
                      (right_addr_good_for_shifting
                         (fun cid : nat => if cid \in domm (prog_interface p)
                                           then n cid else n'' cid))
                      (rcons t1' (ECall (Pointer.component pc)
                                        P0 (Register.get R_COM s1'reg) s1'mem C'0))
                 ).
          {
            constructor. intros [cid bid] Hshr. simpl.
            specialize (shrt1'_shrt1_ext _ Hshr) as [[cid' bid'] [G _]].
            unfold sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            destruct (sigma_shifting_lefttoright_option
                        (n cid')
                        (if cid' \in domm (prog_interface p) then
                           n cid' else n'' cid') bid') eqn:ebid';
              rewrite ebid' in G; try discriminate.
            inversion G; subst.
              by eapply sigma_lefttoright_Some_good; eauto.
          }


          assert (Hshift_t1rcons_t1'rcons:
                    traces_shift_each_other_option
                      n
                      (fun cid : nat => if cid \in domm (prog_interface p)
                                        then n cid else n'' cid)
                      (rcons t1 (ECall (Pointer.component pc)
                                       P0 (Register.get R_COM regs) mem0 C'0))
                      (rcons t1' (ECall (Pointer.component pc)
                                        P0 (Register.get R_COM s1'reg) s1'mem C'0))
                 ).
          {
            constructor; econstructor; eauto.
            - by inversion Hshift_tt' as [? ? Hrentt']; subst.
            - by simpl.
            - simpl.
              unfold shift_value_option,
              rename_value_option, rename_value_template_option,
              rename_addr_option, sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
              destruct (Register.get R_COM regs)
                as [| [[[perm cid] bid] off] |]eqn:eR_COM;
                inversion Hrel_R_COM as [G | [contra [rewr rewr2]]];
                try assumption;
                try discriminate.
              rewrite <- rewr2.
              destruct (perm =? Permission.data) eqn:eperm; auto.
              assert (Hshr: addr_shared_so_far
                              (cid, bid)
                              (rcons t1 (ECall (Pointer.component pc)
                                               P0 (Ptr (perm, cid, bid, off)) mem0 C'0))
                     ).
              {
                econstructor; simpl; rewrite eperm; constructor;
                  by rewrite in_fset1. 
              }
              inversion Hgood2 as [? good]; subst.
              specialize (good _ Hshr).
              simpl in *.
              erewrite sigma_lefttoright_Some_spec in good.
              destruct good as [? rewr3].
                by erewrite rewr3 in contra.
          }

          assert (Hshift_t1''rcons_t1'rcons:
                    traces_shift_each_other_option
                      n''
                      (fun cid : nat => if cid \in domm (prog_interface p)
                                        then n cid else n'' cid)
                      (rcons t1'' (ECall (Pointer.component pc)
                                         P0 (Register.get R_COM regs0) s2''mem C'0))
                      (rcons t1' (ECall (Pointer.component pc)
                                        P0 (Register.get R_COM s1'reg) s1'mem C'0))
                 ).
          {
            inversion Hrel2 as [? ? Hren2]; subst.
            inversion Hren2 as [| t'' e'' t' e' ? Ht''t'  Ht1t1'' Ht1''t1 _ _]; subst;
              try find_nil_rcons;
              repeat match goal with
                     | H18: rcons _ _ = rcons _ _ |- _ =>
                       apply rcons_inj in H18; inversion H18; subst; clear H18
                     end;
              unfold sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
            
            constructor; econstructor; eauto;
              unfold event_renames_event_at_shared_addr,
              mem_of_part_not_executing_rel_original_and_recombined_at_border,
              mem_of_part_executing_rel_original_and_recombined,
              mem_of_part_not_executing_rel_original_and_recombined_at_internal,
              memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
              memory_renames_memory_at_private_addr,
              memory_renames_memory_at_shared_addr,
              rename_value_option, rename_value_template_option,
              sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid, rename_addr_option
              in *; simpl in *.

            - by inversion Hshift_t''t'; subst.
            - intros [cid'' bid''] Hshr''.
              specialize (Ht1''t1 _ Hshr'') as [[cid bid] [ebid G]].
              destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                as [bid''_|] eqn:esigma; try discriminate.
              inversion ebid; subst; clear ebid.
              destruct G as [[? [inv [mem0_s2''mem s2''mem_mem0]]] Hshr].
              inversion inv; subst; clear inv.
              inversion Hshift_t1rcons_t1'rcons as [? ? Hren]; subst.
              inversion Hren as [| t e t'_ e'_ ? Htt'  Ht1t1' Ht1't1 _ _]; subst;
              try find_nil_rcons;
              repeat match goal with
                     | H18: rcons _ _ = rcons _ _ |- _ =>
                       apply rcons_inj in H18; inversion H18; subst; clear H18
                     end;
              unfold sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
              specialize (Ht1t1' _ Hshr) as [mem0_s1'mem_shr
                                               [[cid' bid'] [ebid' Hshr']]].
              destruct (sigma_shifting_lefttoright_option
                          (n cid'')
                          (if cid'' \in domm (prog_interface p)
                           then n cid'' else n'' cid'') bid) eqn:esigma2;
                rewrite esigma2 in ebid'; try discriminate;
                  inversion ebid'; subst; clear ebid'; simpl in *.
              apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
              assert (bid''good: left_block_id_good_for_shifting (n'' cid') bid'').
              { by erewrite sigma_lefttoright_Some_spec; eexists; eauto. }
              erewrite sigma_lefttoright_Some_spec in bid''good.
              destruct bid''good as [bid'_ rewr].
              setoid_rewrite rewr.
              assert (bid'_ = bid'); subst.
              {
                destruct (cid' \in domm (prog_interface p)) eqn:ecid';
                  rewrite ecid' in esigma2; rewrite ecid' in rewr.
                - apply sigma_shifting_lefttoright_option_n_n_id in esigma2; subst.
                  rewrite esigma in rewr; by inversion rewr.
                - apply sigma_shifting_lefttoright_option_n_n_id in rewr; subst.
                  apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                  rewrite esigma in esigma2. by inversion esigma2.
              }
              split.
              2: {
                eexists; split; first reflexivity; assumption.
              }
              eexists; split; first reflexivity.
              destruct s2''mem_s1'mem as [_ [s2''mem_s1'mem_shr _]].
              specialize (s2''mem_s1'mem_shr _ Hshr'') as [[cid'_ bid'_] [esigma3 G]].
              rewrite rewr in esigma3; inversion esigma3; subst; clear esigma3.
              simpl in *. exact G.
            - intros [cid' bid'] Hshr'.
              inversion Hshift_t1rcons_t1'rcons as [? ? Hren]; subst.
              inversion Hren as [| t e t'_ e'_ ? Htt'  Ht1t1' Ht1't1 _ _]; subst;
              try find_nil_rcons;
              repeat match goal with
                     | H18: rcons _ _ = rcons _ _ |- _ =>
                       apply rcons_inj in H18; inversion H18; subst; clear H18
                     end;
              unfold sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
              specialize (Ht1't1 _ Hshr') as [[cid bid] [ebid [mem0_s1'mem_shr
                                                                 Hshr]]].
              destruct (sigma_shifting_lefttoright_option
                          (n cid)
                          (if cid \in domm (prog_interface p)
                           then n cid else n'' cid) bid) eqn:esigma2;
                rewrite esigma2 in ebid; try discriminate;
                  inversion ebid; subst; clear ebid; simpl in *.
              specialize (Ht1t1'' _ Hshr) as [_ [[cid'' bid''] [ebid'' Hshr'']]].
              destruct (sigma_shifting_lefttoright_option (n cid') (n'' cid') bid)
                as [bid''_|] eqn:esigma; try discriminate.
              inversion ebid''; subst; clear ebid''.
              apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
              assert (bid''good: left_block_id_good_for_shifting (n'' cid'') bid'').
              { by erewrite sigma_lefttoright_Some_spec; eexists; eauto. }
              erewrite sigma_lefttoright_Some_spec in bid''good.
              destruct bid''good as [bid'_ rewr].
              exists (cid'', bid'').
              setoid_rewrite rewr.
              assert (bid'_ = bid'); subst.
              {
                destruct (cid'' \in domm (prog_interface p)) eqn:ecid';
                  rewrite ecid' in esigma2; rewrite ecid' in rewr.
                - apply sigma_shifting_lefttoright_option_n_n_id in esigma2; subst.
                  rewrite esigma in rewr; by inversion rewr.
                - apply sigma_shifting_lefttoright_option_n_n_id in rewr; subst.
                  apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                  rewrite esigma in esigma2. by inversion esigma2.
              }
              split; first reflexivity.
              split; last assumption.
              eexists; split; first reflexivity.
              simpl in *.
              destruct s2''mem_s1'mem as [_ [G _]].
              specialize (G _ Hshr'') as [[cid' bid'_] [ebid' G']].
              rewrite rewr in ebid'; inversion ebid'; subst; simpl in *.
              exact G'.
            - by auto.
            - simpl.
              unfold shift_value_option,
              rename_value_option, rename_value_template_option,
              rename_addr_option, sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
              destruct (Register.get R_COM regs)
                as [| [[[perm cid] bid] off] |]eqn:eR_COM;
                inversion Hrel_R_COM as [G | [contra [rewr rewr2]]];
                inversion Harg as [rewr3];
                try assumption;
                try discriminate;
                destruct (perm =? Permission.data) eqn:eperm; auto.
              + destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                  as [bid''|]
                       eqn:ebid; try discriminate; inversion rewr3; rewrite eperm.
                destruct (sigma_shifting_lefttoright_option
                            (n cid)
                            (if cid \in domm (prog_interface p)
                             then n cid else n'' cid) bid) as [bid'|] eqn:ebid';
                  rewrite ebid' in G; inversion G.
                apply sigma_shifting_lefttoright_Some_inv_Some in ebid.
                assert (bid''good: left_block_id_good_for_shifting (n'' cid) bid'').
                { by erewrite sigma_lefttoright_Some_spec; eexists; eauto. }
                erewrite sigma_lefttoright_Some_spec in bid''good.
                destruct bid''good as [bid'_ rewr].
                setoid_rewrite rewr.
                assert (bid'_ = bid'); subst.
                {
                  destruct (cid \in domm (prog_interface p)) eqn:ecid';
                    rewrite ecid' in rewr.
                  - apply sigma_shifting_lefttoright_option_n_n_id in ebid'; subst.
                    rewrite ebid in rewr; by inversion rewr.
                  - apply sigma_shifting_lefttoright_option_n_n_id in rewr; subst.
                    apply sigma_shifting_lefttoright_Some_inv_Some in ebid.
                    rewrite ebid in ebid'. by inversion ebid'.
                }
                reflexivity.
              + inversion rewr3; rewrite eperm. assumption.
              + destruct (sigma_shifting_lefttoright_option
                            (n cid)
                            (if cid \in domm (prog_interface p)
                             then n cid else n'' cid) bid) eqn:econtra;
                  rewrite econtra in contra; try discriminate.
                destruct (sigma_shifting_lefttoright_option (n cid) (n'' cid) bid)
                  as [bid''|] eqn:ebid''; try discriminate.
                assert (bidgood: left_block_id_good_for_shifting (n cid) bid).
                { by erewrite sigma_lefttoright_Some_spec; eexists; eauto. }
                erewrite sigma_lefttoright_Some_spec in bidgood.
                destruct bidgood as [bid' G]; by erewrite G in econtra.
              + inversion rewr3; rewrite eperm; by rewrite rewr2.
          }

          assert (regs0_s2'reg:
                    regs_rel_of_executing_part
                      (Register.invalidate regs0) s2'reg
                      n''
                      (fun cid : nat => if cid \in domm (prog_interface p)
                                        then n cid else n'' cid)
                 ).
          {
            inversion Hstep12' as [? ? ? ? Hstep' Hcontra']; subst.
            inversion Hstep'; subst; simpl in Hcontra'; try discriminate.
            inversion Hcontra'; subst.

            unfold Register.invalidate in *.
            constructor.
            intros reg0; destruct reg0 eqn:ereg0;
              try by unfold Register.get; rewrite !setmE; simpl; left.
            (** R_COM remains. *)
            simpl. 
            unfold Register.get in *.
            simpl in Hrel_R_COM, Harg.
            unfold shift_value_option, rename_value_option,
            rename_value_template_option, rename_addr_option,
            sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid
              in *.
            rewrite !setmE; simpl.
            destruct (regs0 1) as [vregs0_1|] eqn:eregs0_1; simpl in *.
            ** destruct (regs 1) as [vregs1|] eqn:eregs1; simpl in *.
               ---
                 destruct vregs1
                   as [| [[[permvregs cidvregs] bidvregs] offvregs] |] eqn:evregs1;
                   inversion Harg as [rewr];
                   inversion Hrel_R_COM as [G | [contra [? ?]]];
                   try by left; try discriminate.
                 +++
                   destruct (permvregs =? Permission.data) eqn:epermvregs.
                   ***
                     destruct (sigma_shifting_lefttoright_option
                                 (n cidvregs) (n'' cidvregs) bidvregs)
                       as [bidvregs''| ] eqn:esigma;
                       try discriminate.
                     inversion rewr; subst. rewrite epermvregs.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cidvregs)
                                 (if cidvregs \in domm (prog_interface p)
                                  then n cidvregs else n'' cidvregs) bidvregs)
                       as [bidvregs'|] eqn:ebidvregs'; rewrite ebidvregs' in G;
                       try discriminate.
                     left. rewrite <- G.
                     apply sigma_shifting_lefttoright_Some_inv_Some in esigma.
                     assert (good:left_block_id_good_for_shifting (n'' cidvregs)
                                                                  bidvregs'').
                     {
                         by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                     }
                     erewrite sigma_lefttoright_Some_spec in good.
                     destruct good as [bid' G'].
                     erewrite G'.
                     assert (bid' = bidvregs').
                     {
                       destruct (cidvregs \in domm (prog_interface p)) eqn:ecid;
                         rewrite ecid in G'.
                       - apply sigma_shifting_lefttoright_option_n_n_id
                           in ebidvregs'; subst.
                         rewrite esigma in G'; by inversion G'.
                       - apply sigma_shifting_lefttoright_option_n_n_id
                           in G'; subst.
                         apply sigma_shifting_lefttoright_Some_inv_Some
                           in esigma.
                         rewrite ebidvregs' in esigma. by inversion esigma.
                     }
                       by subst.
                   *** left. rewrite <- G. inversion rewr. by rewrite epermvregs.
                 +++ destruct (permvregs =? Permission.data); try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cidvregs) (n'' cidvregs) bidvregs)
                       as [bidvregs''|] eqn:ebidvregs''; try discriminate.
                     assert (good:left_block_id_good_for_shifting (n cidvregs)
                                                                  bidvregs).
                     {
                         by erewrite sigma_lefttoright_Some_spec; eexists; eauto.
                     }
                     erewrite sigma_lefttoright_Some_spec in good.
                     destruct good as [bid' G'].
                     erewrite G' in contra; discriminate.
               --- inversion Harg; subst. left. by destruct Hrel_R_COM as [?|[? _]].
            ** left. destruct (regs 1) as [vregs1|] eqn:eregs1; simpl in *.
               --- destruct vregs1 as [| [[[perm cid] bid] ?] |];
                     inversion Harg as [rewr]; try discriminate;
                       last by destruct Hrel_R_COM as [?|[? _]].
                   destruct (perm =? Permission.data); try discriminate.
                   destruct (sigma_shifting_lefttoright_option
                               (n cid) (n'' cid) bid) as [bid''|] eqn:ebid'';
                     try discriminate.
               --- by destruct Hrel_R_COM as [?|[? _]].       
          }


          assert (regs_s2'reg: regs_rel_of_executing_part
                                 (Register.invalidate regs) s2'reg n
                                 (fun cid : nat => if cid \in domm (prog_interface p)
                                                   then n cid else n'' cid)).
          {
            inversion Hstep12' as [? ? ? ? Hstep' Hcontra']; subst.
            inversion Hstep'; subst; simpl in Hcontra'; try discriminate.
            inversion Hcontra'; subst.

            unfold Register.invalidate in *.
            constructor.
            intros reg0; destruct reg0 eqn:ereg0;
              try by unfold Register.get; rewrite !setmE; simpl; left.
            (** R_COM remains. *)
            simpl. 
            unfold Register.get in *.
            simpl in Hrel_R_COM, Harg.
            unfold shift_value_option, rename_value_option,
            rename_value_template_option, rename_addr_option,
            sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid
              in *.
            rewrite !setmE; simpl.
            assumption.
          }
          
          assert (stk_p_recombined:
                    stack_of_program_part_rel_stack_of_recombined
                      p (Pointer.inc pc :: gps) s2'stk
                 ).
          {
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
          }

          assert (stk_c'_recombined:
                    stack_of_program_part_rel_stack_of_recombined
                      c' (Pointer.inc pc0 :: gps0) s2'stk
                 ).
          {
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
          }

          assert (Hisprefix1: CSInvariants.is_prefix
                                (s2'stk, s1'mem, s2'reg, s2'pc) (program_link p c')
                                (rcons t1' (ECall (Pointer.component pc)
                                                  P0 (Register.get R_COM s1'reg)
                                                  s1'mem C'0))).
          {
            unfold CSInvariants.is_prefix.
            eapply star_right; try eassumption.
              by rewrite <- cats1.
          }

          assert (Hcomps2'pc: Pointer.component s2'pc = C'0).
          {
            inversion Hstep12'; subst.
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
          }

          assert (C'0 \in domm (prog_interface c') \/ C'0 \in domm (prog_interface p))
            as [C'0_ctx | C'0_prog].
          {
            admit.
          }
         
          -- apply mergeable_border_states_c'_executing.
             5: { exact s2''mem_s1'mem. }
             5: { exact mem0_s1'mem. }
             ++ constructor; auto; simpl.
                 
                ** (* is_prefix *)
                  unfold CSInvariants.is_prefix.
                  eapply star_right; try eassumption.
                    by rewrite <- cats1.

             ++ simpl.
                inversion Hstep12' as [? ? ? ? Hstep' Hcontra']; subst.
                inversion Hstep'; subst; simpl in Hcontra'; try discriminate.
                inversion Hcontra'; subst.

                match goal with
                | E': EntryPoint.get C' P (genv_entrypoints (prepare_global_env prog'))
                      = _ |- _ =>
                  specialize (EntryPoint.get_some Hb') as C'in
                end.

                rewrite domm_genv_entrypoints in C'in.

                assert (C' \in domm (prog_interface p) \/
                               C' \in domm (prog_interface c')) as [C'p | C'c'].
                {
                  (** Using C'in somehow. *)
                  admit.
                }
                
                ** assert (Hb: EntryPoint.get
                             C' P
                             (genv_entrypoints (prepare_global_env (prog'))) = Some b).
                   {
                     eapply genv_entrypoints_recombination_left
                       with (c := c) (c' := c'); eauto.
                   }
                   match goal with | Hb1: _ = Some b1 |- _ => rewrite Hb1 in Hb end.
                   inversion Hb; subst; clear Hb.
                   simpl in *.
                   unfold mergeable_interfaces, linkable in *.
                   destruct Hmerge_ipic as [[_ contra] _].
                   rewrite Hifc_cc' in contra.
                   by specialize (fdisjoint_partition_notinboth contra C'0_ctx C'p).
                ** assert (Hb: EntryPoint.get
                             C' P
                             (genv_entrypoints (prepare_global_env (prog'))) = Some b0).
                   {
                     eapply genv_entrypoints_recombination_right
                       with (p := p) (p' := p')
                            (c := c) (c' := c'); eauto.
                     by rewrite Hifc_cc'.
                   }
                   match goal with | Hb1: _ = Some b1 |- _ => rewrite Hb1 in Hb end.
                     by inversion Hb.

             ++ unfold CS.is_context_component, turn_of, CS.state_turn.
                by rewrite Hifc_cc' Hcomps2'pc.

             ++ (** regs0_s2'reg *)
               simpl. exact regs0_s2'reg.

          -- apply mergeable_border_states_p_executing;
               unfold mem_of_part_not_executing_rel_original_and_recombined_at_border
               in *.
             5: { exact mem0_s1'mem. }
             5: { exact s2''mem_s1'mem. }
             ++ constructor; auto; simpl.
                
                ** (* is_prefix *)
                  unfold CSInvariants.is_prefix.
                  eapply star_right; try eassumption.
                    by rewrite <- cats1.

             ++ simpl.
                inversion Hstep12' as [? ? ? ? Hstep' Hcontra']; subst.
                inversion Hstep'; subst; simpl in Hcontra'; try discriminate.
                inversion Hcontra'; subst.

                match goal with
                | E': EntryPoint.get C' P (genv_entrypoints (prepare_global_env prog'))
                      = _ |- _ =>
                  specialize (EntryPoint.get_some Hb') as C'in
                end.

                rewrite domm_genv_entrypoints in C'in.

                assert (C' \in domm (prog_interface p) \/
                               C' \in domm (prog_interface c')) as [C'p | C'c'].
                {
                  (** Using C'in somehow. *)
                  admit.
                }

                ** assert (Hb: EntryPoint.get
                                 C' P
                                 (genv_entrypoints (prepare_global_env (prog'))) =
                               Some b).
                   {
                     eapply genv_entrypoints_recombination_left
                       with (p := p) 
                            (c := c) (c' := c'); eauto.
                   }
                   simpl.
                   match goal with | Hb1: _ = Some b1 |- _ => rewrite Hb1 in Hb end.
                     by inversion Hb.

                ** assert (Hb: EntryPoint.get
                                 C' P
                                 (genv_entrypoints (prepare_global_env (prog'))) =
                               Some b0).
                   {
                     eapply genv_entrypoints_recombination_right
                       with (c := c) (c' := c') (p := p) (p' := p'); eauto.
                     by rewrite Hifc_cc'.
                   }
                   match goal with | Hb1: _ = Some b1 |- _ => rewrite Hb1 in Hb end.
                   inversion Hb; subst; clear Hb.
                   simpl in *.
                   unfold mergeable_interfaces, linkable in *.
                   destruct Hmerge_ipic as [[_ contra] _].
                   rewrite Hifc_cc' in contra.
                   by specialize (fdisjoint_partition_notinboth contra C'c' C'0_prog).


             ++ unfold CS.is_program_component,
                CS.is_context_component, turn_of, CS.state_turn.
                rewrite Hcomps2'pc.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ contra] _].
                destruct (C'0 \in domm (prog_interface c)) eqn:econtra; auto.
                specialize (fdisjoint_partition_notinboth contra econtra C'0_prog).
                  by intros.
             ++ (** regs_s2'reg *)
               simpl. exact regs_s2'reg.


               
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

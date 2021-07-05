Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Reachability.
Require Import Common.RenamingOption.
(** From Renaming, only addr_shared_so_far is used. Consider refactoring it out
    into a file called Sharing.v to get rid of the dependency on Renaming.
    Keep CSInvariants for only unary invariants; hence, do not depend on "renaming". 
*)
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect eqtype ssrfun.
From mathcomp Require ssrbool.
From extructures Require Import fmap fset.

Set Bullet Behavior "Strict Subproofs".

Module CSInvariants.

(** Unary invariants about the intermediate semantics *)

  
Import Intermediate.
  
Definition is_prefix (s: CS.state) (p: program) t : Prop :=
  Star (CS.sem_non_inform p) (CS.initial_machine_state p) t s.

Inductive wf_ptr_wrt_cid_t (cid: Component.id) (t: trace event) : Pointer.t -> Prop
  :=
  | wf_ptr_own:
      forall p b o,
        wf_ptr_wrt_cid_t cid t (p, cid, b, o)
  | wf_ptr_shared:
      forall p c_other b o,
      addr_shared_so_far (c_other, b) t -> wf_ptr_wrt_cid_t cid t (p, c_other, b, o)
.

Inductive wf_load_wrt_t_pc
          (load_at: Pointer.t)
          (t: trace event)
          (pc_comp: Component.id) : Pointer.t -> Prop :=
| wrt_load_ptr_wf_load:
    forall ptr,
      wf_ptr_wrt_cid_t (Pointer.component load_at) t ptr ->
      wf_load_wrt_t_pc load_at t pc_comp ptr
| wrt_pc_wf_load:
    (** This case takes care of the situation where in the internal execution,
        a new pointer is placed in a shared location, where this placing
        constitutes a violation wrt the last shared set.

        Consider the following scenario:
        P -> shares ptr_p
        C -> gets control, and writes *ptr_p := ptr_c
        This case states which "ptr_c" is allowed.

        The trick is that "ptr_c" is now foreign to P's memory, and it has not yet
        been recorded as shared. So, this case takes care of allowing this
        temporary state of sharing (i.e., state of the internal execution).
     *)
    forall ptr,
      addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
      wf_ptr_wrt_cid_t pc_comp t ptr ->
      wf_load_wrt_t_pc load_at t pc_comp ptr.

Definition wf_mem_wrt_t_pc (mem: Memory.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
forall load_at ptr,
  Memory.load mem load_at = Some (Ptr ptr) ->
  wf_load_wrt_t_pc load_at t pc_comp ptr.

Definition wf_reg_wrt_t_pc (reg: Register.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
  forall r ptr,
    Register.get r reg = Ptr ptr ->
    wf_ptr_wrt_cid_t pc_comp t ptr.

Definition wf_state_t (s: CS.state) (t: trace event) : Prop :=
  wf_mem_wrt_t_pc (CS.state_mem s) t (Pointer.component (CS.state_pc s)) /\
  wf_reg_wrt_t_pc (CS.state_regs s) t (Pointer.component (CS.state_pc s)).

Lemma is_prefix_wf_state_t s p t:
  well_formed_program p ->
  is_prefix s p t ->
  wf_state_t s t.
Proof.
  unfold is_prefix. simpl.
  intros Hwf Hstar.
  remember (prepare_global_env p) as G eqn:HG.
  remember (CS.initial_machine_state p) as s0 eqn:Hs0.
  revert HG Hs0.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros; subst.
  - (* Base case. *)
    unfold CS.initial_machine_state. simpl.
    (* TODO: Does this apply to closed programs only? If not, we need to handle
       additional cases. *)
    assert (Hmain : prog_main p) by admit. rewrite Hmain.
    split; simpl.
    + (* No pointers in static buffers. *)
      intros aptr vptr Hload.
      Check wfprog_well_formed_buffers.
      Print Buffer.well_formed_buffer.
      Check wf_ptr_own.
      admit. (* Should be easy once connected to the environment. *)
    + (* All registers are uninitialized. *)
      intros reg ptr Hget.
      destruct reg; discriminate.
  - (* Inductive step. *)
    specialize (IHstar Logic.eq_refl Logic.eq_refl).
    split.
    + (* Memory. *)
      admit.
    + (* Registers. *)
      admit.
Admitted.

Lemma wf_state_wf_reg s regs pc pc_comp t:
  wf_state_t s t ->
  CS.state_regs s = regs ->
  CS.state_pc s = pc ->
  Pointer.component pc = pc_comp ->
  wf_reg_wrt_t_pc regs t pc_comp.
Proof.
    unfold wf_state_t; intros [? ?] H1 H2 H3. rewrite <- H3, <- H2, <- H1. auto.
Qed.

Lemma wf_state_wf_mem s mem pc pc_comp t:
  wf_state_t s t ->
  CS.state_mem s = mem ->
  CS.state_pc s = pc ->
  Pointer.component pc = pc_comp ->
  wf_mem_wrt_t_pc mem t pc_comp.
Proof.
    unfold wf_state_t; intros [? ?] H1 H2 H3. rewrite <- H3, <- H2, <- H1. auto.
Qed.

Lemma wf_reg_wf_ptr_wrt_cid_t reg t pc_comp r ptr:
  wf_reg_wrt_t_pc reg t pc_comp ->
  Register.get r reg = Ptr ptr ->
  wf_ptr_wrt_cid_t pc_comp t ptr.
Proof.
    by (unfold wf_reg_wrt_t_pc; intros H ?; apply (H r)).
Qed.

Lemma wf_mem_wrt_t_pc_wf_load_wrt_t_pc mem t pc_comp load_at ptr:
  wf_mem_wrt_t_pc mem t pc_comp ->
  Memory.load mem load_at = Some (Ptr ptr) ->
  wf_load_wrt_t_pc load_at t pc_comp ptr.
Proof.
    by (unfold wf_mem_wrt_t_pc; intros H ?; eapply H).
Qed.

Lemma mem_comp_in_domm_prog_interface_some s p t mem cid:
  well_formed_program p ->
  closed_program p ->
  is_prefix s p t ->
  CS.state_mem s = mem ->
  cid \in domm (prog_interface p) ->
  exists compMem, mem cid = Some compMem.
Proof.
  unfold is_prefix. simpl.
  intros Hwf Hclosed Hstar Hmem Hdomm.
  apply /dommP.
  remember (CS.initial_machine_state p) as s0 eqn:Hs0.
  remember (prepare_global_env p) as G eqn:HG.
  revert mem Hs0 HG Hwf Hclosed Hmem Hdomm.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros mem Hs0 HG Hwf Hclosed Hmem Hdomm; subst.
  - unfold CS.initial_machine_state. simpl.
    destruct (prog_main p) as [main |] eqn:Hmain.
    + simpl.
      rewrite domm_map (domm_prepare_procedures_initial_memory_aux p).
      assumption.
    + destruct (cprog_main_existence Hclosed) as [_ [Hcontra _]].
      rewrite Hmain in Hcontra. discriminate.
  - specialize
      (IHstar _ Logic.eq_refl Logic.eq_refl Hwf Hclosed Logic.eq_refl Hdomm)
      as Hmem.
    inversion Hstep12 as [? ? ? ? Hstep12']; subst.
    inversion Hstep12'; subst;
      try assumption.
    + simpl. erewrite <- Memory.domm_store; eassumption.
    + simpl. erewrite <- Memory.domm_alloc; eassumption.
Qed.

Lemma mem_comp_some_link_in_left_or_in_right s p c t mem compMem cid:
  well_formed_program p ->
  well_formed_program c ->
  is_prefix s (program_link p c) t ->
  CS.state_mem s = mem ->
  mem cid = Some compMem ->
  (cid \in domm (prog_interface p) \/ cid \in domm (prog_interface c)).
Proof.
  (* Set up induction on star from left to right. *)
  unfold is_prefix. simpl.
  intros Hwfp Hwfc Hstar Hmem HcompMem.
  assert (Hdomm : cid \in domm mem) by (apply /dommP; eauto).
  clear HcompMem.
  set prog := program_link p c. fold prog in Hstar.
  remember (CS.initial_machine_state prog) as s0 eqn:Hs0.
  remember (prepare_global_env prog) as G eqn:HG.
  revert mem cid compMem Hs0 HG Hmem Hdomm.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros mem cid Hs0 HG Hmem HcompMem Hdomm; subst.
  - (* Base case. *)
    unfold CS.initial_machine_state in Hdomm.
    destruct (prog_main prog) as [main |] eqn:Hmain;
      simpl in Hdomm.
    + (* If we assume a closed program and linkable interfaces, this is easy
         (and the contradictory case on [prog_main] goes away). As is, we need
         to be a little more involved. *)
      rewrite domm_map domm_prepare_procedures_initial_memory_aux in Hdomm.
      unfold prog, program_link in Hdomm.
      simpl in Hdomm.
      destruct (cid \in domm (prog_interface p)) eqn:Hcase1;
        destruct (cid \in domm (prog_interface c)) eqn:Hcase2;
        auto. (* Only the contradictory case is left. *)
      apply negb_true_iff in Hcase1. apply negb_true_iff in Hcase2.
      destruct (dommP Hdomm) as [v Hcontra].
      rewrite unionmE (dommPn Hcase1) (dommPn Hcase2) in Hcontra.
      discriminate.
    + rewrite domm0 in Hdomm. discriminate.
  - (* Inductive case. *)
    inversion Hstep12 as [? ? ? ? Hstep12']; subst.
    inversion Hstep12'; subst;
      eapply IHstar;
      try eauto; (* Solve most goals. *)
      simpl; simpl in Hdomm.
    + (* Store *)
      erewrite Memory.domm_store; eassumption.
    + (* Alloc *)
      erewrite Memory.domm_alloc; eassumption.
Qed.

End CSInvariants.

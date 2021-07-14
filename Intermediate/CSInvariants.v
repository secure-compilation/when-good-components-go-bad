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

(* NOTE: DO we have similar/redundant definitions to unify? *)
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

(* TODO: Move to Pointer module. *)
Remark pointer_proj ptr :
  ptr = (Pointer.permission ptr, Pointer.component ptr, Pointer.block ptr, Pointer.offset ptr).
Proof.
  destruct ptr as [[[? ?] ?] ?]. reflexivity.
Qed.

(* TODO: Move to Pointer module. *)
Remark pointer_refl ptr1 ptr2 :
  Pointer.eq ptr1 ptr2 = true ->
  ptr1 = ptr2.
Proof.
  destruct ptr1 as [[[P1 C1] b1] o1].
  destruct ptr2 as [[[P2 C2] b2] o2].
  (* Decompose pointer component equalities... *)
  move => /andP => [[]] => /andP => [[]] => /andP => [[]] =>
  (* ... then reflect each of them and substitute the equality... *)
  /ssrnat.eqnP => -> =>
  /ssrnat.eqnP => -> =>
  /ssrnat.eqnP => -> =>
  /eqP ->
  (* ... and we're done. *)
  //.
Qed.

(* TODO: Relocate. *)
Remark Eapp_rcons {T} l (x : T) : l ** [x] = seq.rcons l x.
Admitted.

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
      destruct IHstar as [Hmem1 Hregs1].
      inversion Hstep12 as [? ? ? ? Hstep12']; subst.
      inversion Hstep12'; subst; simpl in *;
        (* A few useful simplifications. *)
        try rewrite E0_right;
        try rewrite Pointer.inc_preserves_component;
        (* Many goals follow directly from the IH now. *)
        try assumption.
      * (* Store *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        destruct (Pointer.eq addr_load ptr) eqn:Heq.
        -- (* We load from the address we just stored to. The information can
              only come from the registers and not from the memory. *)
           apply pointer_refl in Heq; subst addr_load. (* As reflection? *)
           rewrite (Memory.load_after_store_eq _ _ _ _ H1) in Hload.
           injection Hload as Hload.
           assert (Hr1 := Hregs1 _ _ H0).
           assert (Hr2 := Hregs1 _ _ Hload).
           (* By case analysis on the well-formedness of the address pointer. *)
           destruct ptr as [[[Pptr Cptr] bptr] optr].
           destruct val_load as [[[Pval Cval] bval] oval].
           inversion Hr1 as [| ? ? ? ? Hshared1]; subst.
           ++ apply wrt_load_ptr_wf_load; assumption.
           ++ apply wrt_pc_wf_load; assumption.
        -- (* For any other address, this follows directly from the IH. *)
           assert (Hneq : ptr <> addr_load) by admit.
           rewrite -> (Memory.load_after_store_neq _ _ _ _ _ Hneq H1) in Hload.
           exact (Hmem1 _ _ Hload).
      * (* IJal *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        (* Since we dot change components, this follows from the IH. *)
        rewrite <- (find_label_in_component_1 _ _ _ _ H0).
        exact (Hmem1 _ _ Hload).
      * (* IJump *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        (* Since we dot change components, this follows from the IH. *)
        rewrite -> H2.
        exact (Hmem1 _ _ Hload).
      * (* IBnz *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        (* Since we dot change components, this follows from the IH. *)
        rewrite <- (find_label_in_procedure_1 _ _ _ _ H2).
        exact (Hmem1 _ _ Hload).
      * (* IAlloc *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        destruct (addr_eq (Pointer.component addr_load, Pointer.block addr_load)
                          (Pointer.component ptr,       Pointer.block ptr))
                 eqn:Heq.
        -- (* If we read from the newly allocated block, the load cannot find
             any pointers and we conclude by contradiction. *)
           assert (Heq' :
                     (Pointer.component addr_load, Pointer.block addr_load) =
                     (Pointer.component ptr,       Pointer.block ptr))
            by admit.
           rewrite (Memory.load_after_alloc_eq _ _ _ _ _ _ H2 Heq') in Hload.
           destruct (Pointer.permission addr_load =? Permission.data);
             last discriminate.
           destruct ((Pointer.offset addr_load <? Z.of_nat (Z.to_nat size))%Z);
             last discriminate.
           destruct ((0 <=? Pointer.offset addr_load)%Z);
             discriminate.
        -- (* If we read from elsewhere, the result follows from the IH. *)
           assert (Heq' :
                     (Pointer.component addr_load, Pointer.block addr_load) <>
                     (Pointer.component ptr,       Pointer.block ptr))
            by admit.
           (* TODO: Rename lemma (add [_neq]).*)
           rewrite (Memory.load_after_alloc _ _ _ _ _ _ H2 Heq') in Hload.
           exact (Hmem1 _ _ Hload).
      * (* ICall *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        admit.
      * (* IReturn *)
        intros addr_load val_load Hload.
        clear Hstar01 Hstep12 Hstep12' H.
        admit.
    + (* Registers. *)
      destruct IHstar as [Hmem1 Hregs1].
      inversion Hstep12 as [? ? ? ? Hstep12']; subst.
      inversion Hstep12'; subst; simpl in *;
        (* A few useful simplifications. *)
        try rewrite E0_right;
        try rewrite Pointer.inc_preserves_component;
        (* A few goals follow directly from the IH. *)
        try assumption.
      * (* IConst *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct ((Register.to_nat reg) =? (Register.to_nat r)) eqn:Heq. (* HACK *)
        -- (* If we read the register we just wrote, we get the exact immediate
              value, here assumed to be a pointer. *)
           assert (reg = r) by admit; subst r.
           assert (Hget' : imm_to_val v = Ptr ptr) by admit.
           destruct v as [n | ptr']; first discriminate.
           injection Hget' as Hget'; subst ptr'.
           (* Thanks to [well_formed_instruction], we know that pointer
              constants may only refer to their own component. *)
           destruct ptr as [[[P C] b] o].
           assert (C = Pointer.component pc) by admit; subst C.
           now apply wf_ptr_own.
        -- (* For any other register, this follows directly from the IH. *)
           assert (Hget' : Register.get reg regs = Ptr ptr) by admit.
           exact (Hregs1 _ _ Hget').
      * (* IMov *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct ((Register.to_nat reg) =? (Register.to_nat r2)) eqn:Heq. (* HACK *)
        -- (* The new value comes from r1, which follows from the IH. *)
           assert (reg = r2) by admit; subst r2.
           assert (Hget' : Register.get r1 regs = Ptr ptr) by admit.
           exact (Hregs1 _ _ Hget').
        -- (* The new value comes from reg, which follows from the IH. *)
           assert (Hget' : Register.get reg regs = Ptr ptr) by admit.
           exact (Hregs1 _ _ Hget').
      * (* IBinOp *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct ((Register.to_nat reg) =? (Register.to_nat r3)) eqn:Heq. (* HACK *)
        -- (* If we read the register we just wrote, we get the result of the
              operation, which we then case analyze. *)
           assert (reg = r3) by admit; subst r3.
           assert (Hget' : result = Ptr ptr) by admit.
           unfold result, eval_binop in Hget'.
           destruct op;
             destruct (Register.get r1 regs) eqn:Hget1;
             destruct (Register.get r2 regs) eqn:Hget2;
             (* Most cases are nonsensical; a handful remain. *)
             inversion Hget'; subst.
           (* Whenever there is a pointer and an integer, the result follows
              from the IH on the pointer, albeit with a bit of work to account
              for the integer offsets. *)
           ++ assert (Hr2 := Hregs1 _ _ Hget2).
              inversion Hr2; subst. (* By the corresponding [constructor]. *)
              ** now apply wf_ptr_own.
              ** now apply wf_ptr_shared.
           ++ assert (Hr1 := Hregs1 _ _ Hget1).
              inversion Hr1; subst; (* Can be picked automatically. *)
                now constructor.
           ++ assert (Hr1 := Hregs1 _ _ Hget1).
              inversion Hr1; subst;
                now constructor.
           (* The remaining cases are contradictions requiring some additional
              but trivial analysis. *)
           ++ destruct t as [[[P1 C1] b1] o1];
                destruct t0 as [[[P2 C2] b2] o2];
                destruct (P1 =? P2);
                destruct (C1 =? C2);
                destruct (b1 =? b2);
                discriminate.
           ++ destruct (Pointer.leq t t0);
                discriminate.
        -- (* For any other register, this follows directly from the IH. *)
           assert (Hget' : Register.get reg regs = Ptr ptr) by admit.
           exact (Hregs1 _ _ Hget').
      * (* IPtrOfLabel *)
        intros reg ptr' Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct ((Register.to_nat reg) =? (Register.to_nat r)) eqn:Heq. (* HACK *)
        -- (* *)
           assert (reg = r) by admit; subst r.
           assert (ptr = ptr') by admit; subst ptr'.
           destruct ptr as [[[P C] b] o].
           rewrite (find_label_in_component_1 _ _ _ _ H0).
           now apply wf_ptr_own.
        -- (* *)
           assert (Hget' : Register.get reg regs = Ptr ptr') by admit.
           exact (Hregs1 _ _ Hget').
      * (* ILoad *)
        intros reg ptr' Hget.
        (* clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *) *)
        destruct ((Register.to_nat reg) =? (Register.to_nat r2)) eqn:Heq. (* HACK *)
        -- (*  *)
           assert (reg = r2) by admit; subst r2.
           assert (v = Ptr ptr') by admit; subst v.
           (* IH *)
           assert (Hr1 := Hregs1 _ _ H0).
           assert (Hptr := Hmem1 _ _ H1).
           (* Pre-case analysis *)
           destruct ptr as [[[P C] b] o].
           destruct ptr' as [[[P' C'] b'] o'].
           (* Cases *)
           inversion Hr1;
             inversion Hptr;
             subst;
             (* All but one of the goals are already in the context. *)
             try assumption.
           (* inversion H6; subst. *)
           inversion H7; subst.
           ++ (* *)
              destruct (Nat.eqb (Pointer.component pc) C') eqn:Hcase.
              ** assert (Pointer.component pc = C') by admit; subst C'.
                 assumption.
              ** assert (Heq' : Pointer.component pc <> C') by admit.
                 (* Is this case inconsistent with the transient condition?
                    If so, how to realize the contradiction? *)
                 apply wf_ptr_shared.
                 (* An external (C', b) has been shared.
                    A pointer in it leads to another block in the same compartment, (C', b').
                  *)
                 (* destruct t1 as [| e' t1']. *)
                 (* --- exfalso. admit. *)
                 (* --- assert (exists t1_ e_, (e' :: t1' = seq.rcons t1_ e_)) *)
                 (*       as [t1_ [e_ Hrcons]] *)
                 (*       by admit. *)
                 (*     rewrite Hrcons. rewrite Hrcons in H3. *)
                 (*     eapply reachable_from_previously_shared. *)
                 simpl in H7. admit.
           ++ now apply wf_ptr_shared.
        -- (* The new value comes from reg, which follows from the IH. *)
           assert (Hget' : Register.get reg regs = Ptr ptr') by admit.
           exact (Hregs1 _ _ Hget').
      * (* IJal *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite <- (find_label_in_component_1 _ _ _ _ H0).
        destruct ((Register.to_nat reg) =? (Register.to_nat R_RA)) eqn:Heq. (* HACK *)
        -- (* *)
           assert (reg = R_RA) by admit; subst reg.
           assert (Pointer.inc pc = ptr) by admit; subst ptr.
           destruct pc as [[[P C] b] o].
           now apply wf_ptr_own.
        -- (* *)
           assert (Hget' : Register.get reg regs = Ptr ptr) by admit.
           exact (Hregs1 _ _ Hget').
      * (* IJump *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite H2.
        exact (Hregs1 _ _ Hget).
      * (* IBnz *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite <- (find_label_in_procedure_1 _ _ _ _ H2).
        exact (Hregs1 _ _ Hget).
      * (* IAlloc *)
        intros reg ptr' Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct ((Register.to_nat reg) =? (Register.to_nat rptr)) eqn:Heq. (* HACK *)
        -- (* *)
           assert (reg = rptr) by admit; subst rptr.
           assert (ptr = ptr') by admit; subst ptr'.
           (* TODO: Refine alloc spec to provide missing information. *)
           (* destruct ptr as [[[P C] b] o]. *)
           admit.
        -- (* *)
           assert (Hget' : Register.get reg regs = Ptr ptr') by admit.
           exact (Hregs1 _ _ Hget').
      * (* ICall *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        (* Lemmas on invalidate? *)
        assert (reg = R_COM) by (destruct reg; now inversion Hget);
          subst reg.
        assert (Hget' : Register.get R_COM regs = Ptr ptr) by admit.
        rewrite Hget'.
        assert (Hrcom := Hregs1 _ _ Hget').
        destruct ptr as [[[P_ C_] b_] o_].
        apply wf_ptr_shared.
        rewrite Eapp_rcons.
        apply reachable_from_args_is_shared. simpl.
        destruct (P_ =? Permission.data) eqn:Hcase.
        -- apply Reachable_refl. apply /fset1P. reflexivity.
        -- (* TODO: We do not seem to have this invariant at hand. *)
           (* Search _ Permission.data. *)
           admit.
      * (* IReturn *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        (* Lemmas on invalidate? *)
        assert (reg = R_COM) by (destruct reg; now inversion Hget);
          subst reg.
        assert (Hget' : Register.get R_COM regs = Ptr ptr) by admit.
        rewrite Hget'.
        assert (Hrcom := Hregs1 _ _ Hget').
        destruct ptr as [[[P C] b] o].
        apply wf_ptr_shared.
        rewrite Eapp_rcons.
        apply reachable_from_args_is_shared. simpl.
        destruct (P =? Permission.data) eqn:Hcase.
        -- apply Reachable_refl. apply /fset1P. reflexivity.
        -- (* TODO: We do not seem to have this invariant at hand. *)
           (* Search _ Permission.data. *)
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
  - (* Inductive step. *)
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

Lemma value_mem_reg_domm_partition p c st t regs mem:
  is_prefix st (program_link p c) t ->
  regs = CS.state_regs st ->
  mem = CS.state_mem st ->
  (forall ptr perm cid bid off,
      Memory.load mem ptr = Some (Ptr (perm, cid, bid, off)) ->
      cid \in domm (prog_interface p) \/
      cid \in domm (prog_interface c)
  )
  /\
  (forall reg perm cid bid off,
      Register.get reg regs = Ptr (perm, cid, bid, off) ->
      cid \in domm (prog_interface p) \/
      cid \in domm (prog_interface c)
  ).
Proof.
  (* Set up induction on star from left to right. *)
  unfold is_prefix. simpl.
  intros Hstar ? ?; subst.
  set prog := program_link p c. fold prog in Hstar.
  remember (CS.initial_machine_state prog) as s0 eqn:Hs0.
  remember (prepare_global_env prog) as G eqn:HG.
  revert Hs0 HG.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros ? ?; subst.
  - (* Base case. *)
    split.
    + intros ptr perm cid bid off Hload.
      admit.
    + intros reg perm cid bid off Hget.
      unfold CS.initial_machine_state in Hget.
      destruct (prog_main prog) eqn:Hcase.
      * unfold Register.get in Hget.
        rewrite Register.reg_in_domm_init_Undef in Hget;
          first discriminate.
        admit.
      * discriminate.
  - (* Inductive step. *)
    specialize (IHstar Logic.eq_refl Logic.eq_refl) as [IHload IHget].
    split.
    + (* Memory domain. *)
      intros ptr perm cid bid off Hload.
      inversion Hstep12 as [? ? ? ? Hstep12']; subst.
      inversion Hstep12'; subst;
        try (by (eapply IHload; eauto)). (* Solve most goals. *)
      * (* IStore *)
        destruct (Pointer.eq ptr ptr0) eqn:Hcase.
        -- apply pointer_refl in Hcase; subst ptr0.
           rewrite (Memory.load_after_store_eq _ _ _ _ H1) in Hload.
           injection Hload as Hget.
           eapply IHget; eassumption.
        -- assert (Hneq : ptr0 <> ptr) by admit.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ Hneq H1) in Hload.
           eapply IHload; eassumption.
      * (* IAlloc *)
        (* destruct ptr as [[[pm C] b] o]. *)
        (* destruct ptr0 as [[[pm0 C0] b0] o0]. *)
        destruct (addr_eq (Pointer.component ptr, Pointer.block ptr) (Pointer.component ptr0, Pointer.block ptr0)) eqn:Hcase.
        -- assert (Heq : (Pointer.component ptr, Pointer.block ptr) = (Pointer.component ptr0, Pointer.block ptr0)) by admit.
           rewrite (Memory.load_after_alloc_eq _ _ _ _ _ _ H2 Heq) in Hload.
           destruct (Pointer.permission ptr =? Permission.data);
             last discriminate.
           destruct (Pointer.offset ptr <? Z.of_nat (Z.to_nat size))%Z;
             last discriminate.
           destruct (0 <=? Pointer.offset ptr)%Z;
             discriminate.
        -- assert (Hneq : (Pointer.component ptr, Pointer.block ptr) <> (Pointer.component ptr0, Pointer.block ptr0)) by admit.
           rewrite (Memory.load_after_alloc _ _ _ _ _ _ H2 Hneq) in Hload.
           eapply IHload; eassumption.
    + (* Register file domain. *)
      intros reg perm cid bid off Hget.
      inversion Hstep12 as [? ? ? ? Hstep12']; subst.
      inversion Hstep12'; subst;
        try (by (eapply IHget; eauto)). (* Solve some goals. *)
      * (* IConst *)
        destruct (Register.eqb reg r) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst r. rewrite Register.gss in Hget.
           destruct v as [| ptr]; first discriminate.
           (* By program (and instruction) well-formedness. *)
           admit.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IMov *)
        destruct (Register.eqb reg r2) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst r2. rewrite Register.gss in Hget.
           eapply IHget; eassumption.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IBinOp *)
        destruct (Register.eqb reg r3) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst r3. rewrite Register.gss in Hget. subst result.
           unfold eval_binop in Hget;
             destruct op;
             destruct (Register.get r1 regs) eqn:Hcase1;
             destruct (Register.get r2 regs) eqn:Hcase2;
             inversion Hget; subst.
           all:admit.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IPtrOfLabel *)
        destruct (Register.eqb reg r) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst r. rewrite Register.gss in Hget.
           injection Hget as Hget. subst ptr.
           setoid_rewrite <- (find_label_in_component_1 _ _ _ _ H0).
           admit.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* ILoad *)
        destruct (Register.eqb reg r2) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst r2. rewrite Register.gss in Hget. subst v.
           eapply IHload; eassumption.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IJal *)
        destruct (Register.eqb reg R_RA) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst reg. rewrite Register.gss in Hget.
           injection Hget as Hget.
           change cid with (Pointer.component (perm, cid, bid, off)).
           rewrite <- Hget, -> Pointer.inc_preserves_component.
           admit.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IAlloc *)
        destruct (Register.eqb reg rptr) eqn:Hcase;
          move: Hcase => /Register.registerP => Hcase.
        -- subst rptr. rewrite Register.gss in Hget.
           injection Hget as Hget; subst ptr.
           setoid_rewrite (Memory.component_of_alloc_ptr _ _ _ _ _ H2).
           admit.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* ICall *)
        (* assert (reg = R_COM) by admit; subst reg. *)
        assert (Hget' : Register.get R_COM regs = Ptr (perm, cid, bid, off)) by admit.
        eapply IHget; eassumption.
      * (* IReturn *)
        (* assert (reg = R_COM) by admit; subst reg. *)
        assert (Hget' : Register.get R_COM regs = Ptr (perm, cid, bid, off)) by admit.
        eapply IHget; eassumption.
Admitted.

End CSInvariants.

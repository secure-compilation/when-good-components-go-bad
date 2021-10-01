Require Import Coq.Logic.Classical_Prop.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Reachability.
Require Import Common.RenamingOption.
(** From Renaming, only addr_shared_so_far and some tactics (like find_nil_rcons, 
    and find_rcons_rcons) are used. Consider refactoring them out
    (into a file called Sharing.v, and into Common.Util)
    to get rid of the dependency on Renaming.
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

From mathcomp Require Import ssreflect eqtype ssrfun seq.
From mathcomp Require ssrbool.
From extructures Require Import fmap fset.

Set Bullet Behavior "Strict Subproofs".

Section Util.

  Lemma starR_rcons:
    forall (sem: semantics event) s1 s2 t1 e1,
      single_events sem ->
      starR (step sem) (globalenv sem) s1 (rcons t1 e1) s2 ->
      exists st1 se1,
        starR (step sem) (globalenv sem) s1 t1 st1 /\
        Step sem st1 [:: e1] se1 /\
        starR (step sem) (globalenv sem) se1 E0 s2.
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
  Qed.

End Util.


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

(**********************************************************************
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
      (* wf_ptr_wrt_cid_t pc_comp t ptr -> *)
      pc_comp = Pointer.component ptr -> (* TODO: Experimental change *)
      wf_load_wrt_t_pc load_at t pc_comp ptr.
***************************************************************************)

Inductive wf_load (pc_comp: Component.id) (t: trace event)
          : Pointer.t -> Pointer.t -> Prop
  :=
  | private_stuff_from_corresp_private_addr:
      forall load_at ptr,
        ~ addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        ~ addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
        Pointer.component ptr = Pointer.component load_at ->
        (***************
          ADD Pointer.component ptr = pc_comp?
         **************)
        (* Memory.load mem load_at = Some (Ptr ptr) -> *)
        wf_load pc_comp t load_at ptr
  | shared_stuff_from_anywhere:
      forall load_at ptr,
        addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        (* Memory.load mem load_at = Some (Ptr ptr) -> *)
        wf_load pc_comp t load_at ptr
  | private_stuff_of_current_pc_from_shared_addr:
      forall load_at ptr,
        ~ addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        Pointer.component ptr = pc_comp ->
        addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
        wf_load pc_comp t load_at ptr.
  
(** TODO: Write as an inductive. *)
Definition wf_mem_wrt_t_pc (mem: Memory.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
forall load_at ptr,
  Memory.load mem load_at = Some (Ptr ptr) ->
  Pointer.permission ptr = Permission.data ->
  wf_load pc_comp t load_at ptr.
  (***********************************************************************************
  (** TOOD: Experimental change: Ignore "wf load"! *)
  (
    (
      (** This disjunct is specifying loads that are possible by the currently-
          executing component. *)
      wf_ptr_wrt_cid_t pc_comp t load_at /\
      wf_ptr_wrt_cid_t pc_comp t ptr
    )
    \/
    (
      (** This disjunct is specifying loads from the private memories of other
          components.*)
      (***********************************
      ~ addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t
      /\
      Pointer.component load_at <> pc_comp
      *************************************)
      ~ wf_ptr_wrt_cid_t pc_comp t load_at
      /\
      wf_ptr_wrt_cid_t (Pointer.component load_at) t ptr
    )
  ).
   ***********************************************************************************)

(*wf_load_wrt_t_pc load_at t pc_comp ptr.*)

Definition wf_reg_wrt_t_pc (reg: Register.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
  forall r ptr,
    Register.get r reg = Ptr ptr ->
    Pointer.permission ptr = Permission.data ->
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
  move=> /andP [[]] /andP [[]] /andP [[]] =>
  (* Depending on the Coq version, you might need to chose one or the other
     version of the tactic. *)
  (* (* ... then reflect each of them and substitute the equality... *) *)
  (* /ssrnat.eqnP -> *)
  (* /ssrnat.eqnP -> *)
  (* /ssrnat.eqnP -> *)
  (* /eqP -> *)
  (* (* ... and we're done. *) *)
  (* //. *)
  /Permission.eqP -> /eqnP -> /eqnP -> /Z.eqb_spec -> //=.
Qed.

(* TODO: Relocate. *)
Remark Eapp_rcons {T} l (x : T) : l ** [x] = seq.rcons l x.
Proof.
  unfold Eapp. by rewrite <- cats1.
Qed.

Lemma initial_wf_mem p:
      closed_program p ->
      well_formed_program p ->
      prog_main p ->
      wf_mem_wrt_t_pc
        (mapm (T:=nat_ordType)
              (fun x : ComponentMemory.t * NMap code * NMap Block.id => x.1.1)
              (prepare_procedures_initial_memory_aux p)) E0 Component.main.
  (**
     (* No pointers in static buffers. *)
      intros aptr vptr Hload Hperm.
      
      Check wfprog_well_formed_buffers.
      Print Buffer.well_formed_buffer.
   (* Should be easy once connected to the environment. *)
   *)
Proof.
  intros Hclosed Hwf Hmain [[[perm C] b] o] ptr Hload Hperm.
  apply private_stuff_from_corresp_private_addr.
  - intros Hcontra.
    inversion Hcontra as [H1 t e H4 Hcons | H1 H2 t e H5 H6 H7 Hcons];
      destruct t as [[| ? ?] ? |]; now inversion Hcons.
  - intros Hcontra.
    inversion Hcontra as [H1 t e H4 Hcons | H1 H2 t e H5 H6 H7 Hcons];
      destruct t as [[| ? ?] ? |]; now inversion Hcons.
  - destruct (C \in domm (prog_interface p)) eqn:Hdomm.
    + destruct (prepare_procedures_memory_prog_buffers Hwf Hload)
        as [(*Cbufs [*) buf (*[HCbufs*) [Hbuf Hptr]].
      exfalso. eapply prog_buffer_ptr; eassumption.
    + rewrite (wfprog_defined_buffers Hwf) in Hdomm.
      destruct (prepare_procedures_memory_prog_buffers Hwf Hload)
        as [buf [Hbuf ?]].
      simpl in *.
      apply negb_true_iff in Hdomm.
      rewrite (dommPn Hdomm) in Hbuf.
      discriminate.
Qed.

Lemma is_prefix_wf_state_t s p t:
  closed_program p ->
  well_formed_program p ->
  is_prefix s p t ->
  wf_state_t s t.
Proof.
  unfold is_prefix. simpl.
  intros Hclosed Hwf Hstar.
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
    (** AEK: Yes, closed only. *)
    assert (Hmain : prog_main p).
    {
      rewrite <- wfprog_main_component; auto.
      specialize (cprog_main_existence Hclosed) as [? [? [Hprogproc ?]]].
      rewrite wfprog_defined_procedures; auto.
      apply/dommP. by eauto.
    }
    rewrite Hmain.
    split; simpl.
    + apply initial_wf_mem; auto.
      
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
        intros addr_load val_load Hload Hperm.
        clear Hstar01 Hstep12 Hstep12' H.
        destruct (Pointer.eqP ptr addr_load) as [Heq | Hneq].
        -- (* We load from the address we just stored to. The information can
              only come from the registers and not from the memory. *)
           subst addr_load.
           rewrite (Memory.load_after_store_eq _ _ _ _ H1) in Hload.
           injection Hload as Hload.
           destruct ptr as [[[Pptr Cptr] bptr] optr].
           destruct val_load as [[[Pval Cval] bval] oval].
           specialize (Memory.store_some_permission _ _ _ _ H1) as Hperm2.
           simpl in *; subst.
           assert (Hr1 := Hregs1 _ _ H0 Logic.eq_refl).
           assert (Hr2 := Hregs1 _ _ Hload Logic.eq_refl).
           inversion Hr2 as [|]; subst.
           ++ specialize (classic (addr_shared_so_far (Pointer.component pc, bval) t1))
               as [Hshr | Hnotshr].
              ** apply shared_stuff_from_anywhere; assumption.
              ** (** private_stuff *)
                inversion Hr1 as [|]; subst.
                ---
                  (** private stuff of current pc from ... *)
                  specialize (classic
                                (addr_shared_so_far (Pointer.component pc, bptr) t1))
                    as [Hfromshr | Hfromprivate].
                  +++ apply private_stuff_of_current_pc_from_shared_addr; auto.
                  +++ apply private_stuff_from_corresp_private_addr; auto.
                ---
                  (** shared addr *)
                  apply private_stuff_of_current_pc_from_shared_addr; auto.
           ++ (** shared stuff *)
             apply shared_stuff_from_anywhere; assumption.
        -- (* For any other address, this follows directly from the IH. *)
           rewrite -> (Memory.load_after_store_neq _ _ _ _ _ Hneq H1) in Hload.
           exact (Hmem1 _ _ Hload Hperm).
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
        
      * (* IJumpFunPtr *)
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
        destruct
          (addr_eqP (Pointer.component addr_load, Pointer.block addr_load)
                    (Pointer.component ptr,       Pointer.block ptr))
          as [Heq | Hneq].
        -- (* If we read from the newly allocated block, the load cannot find
             any pointers and we conclude by contradiction. *)
           rewrite (Memory.load_after_alloc_eq _ _ _ _ _ _ H2 Heq) in Hload.
           destruct (Permission.eqb (Pointer.permission addr_load) Permission.data);
             last discriminate.
           destruct ((Pointer.offset addr_load <? Z.of_nat (Z.to_nat size))%Z);
             last discriminate.
           destruct ((0 <=? Pointer.offset addr_load)%Z);
             discriminate.
        -- (* If we read from elsewhere, the result follows from the IH. *)
           (* TODO: Rename lemma (add [_neq]).*)
           rewrite (Memory.load_after_alloc _ _ _ _ _ _ H2 Hneq) in Hload.
           exact (Hmem1 _ _ Hload).
      * (* ICall *)
        intros addr_load val_load Hload Hperm.
        specialize (Hmem1 _ _ Hload Hperm).
        destruct val_load as  [[[vperm vcid] vbid] voff].
        destruct addr_load as  [[[aperm acid] abid] aoff].
        specialize (Memory.load_some_permission _ _ _ Hload) as Hperm2.
        simpl in *; subst.
        clear Hstep12' Hstar01 Hstep12.
        specialize (classic (addr_shared_so_far
                               (vcid, vbid)
                               (t1 ** [:: ECall
                                          (Pointer.component pc)
                                          P (Register.get R_COM regs) mem C']
                               )
                            )
                   ) as [Hshr | Hnotshr].
        -- (** shared stuff *)
          apply shared_stuff_from_anywhere; auto.
        -- (** private stuff *)
          destruct (vcid =? C') eqn:eacid.
          ++
            (** private stuff of current pc from ...*)
            assert (vcid = C'). by apply beq_nat_true. subst.
            specialize (classic (addr_shared_so_far
                                   (acid, abid)
                                   (t1 ** [:: ECall
                                              (Pointer.component pc)
                                              P (Register.get R_COM regs) mem C']
                                   )
                                )
                       ) as [Hshraddr | Hnotshraddr].
            ** apply private_stuff_of_current_pc_from_shared_addr; auto.
            ** apply private_stuff_from_corresp_private_addr; auto. simpl.
               inversion Hmem1 as [| |]; simpl in *; subst; auto.
               --- exfalso. apply Hnotshr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
               --- exfalso. apply Hnotshraddr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
          ++ (** private stuff NOT of current pc *)
            apply private_stuff_from_corresp_private_addr; simpl in *; auto; subst.
            ** intros Hshraddr.
               apply Hnotshr. rewrite Eapp_rcons. rewrite Eapp_rcons in Hshraddr.
               eapply addr_shared_so_far_load_addr_shared_so_far; simpl; eauto.
            ** inversion Hmem1 as [| |]; simpl in *; subst; auto.
               --- exfalso. apply Hnotshr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
               --- exfalso. apply Hnotshr.
                   rewrite Eapp_rcons.
                   eapply addr_shared_so_far_load_addr_shared_so_far; simpl; eauto.
                   +++
                     eapply reachable_from_previously_shared; eauto. simpl.
                     constructor. by rewrite in_fset1.
                   +++ eassumption.
          
      * (* IReturn *)
                intros addr_load val_load Hload Hperm.
        specialize (Hmem1 _ _ Hload Hperm).
        destruct val_load as  [[[vperm vcid] vbid] voff].
        destruct addr_load as  [[[aperm acid] abid] aoff].
        specialize (Memory.load_some_permission _ _ _ Hload) as Hperm2.
        simpl in *; subst.
        clear Hstep12' Hstar01 Hstep12.
        specialize (classic (addr_shared_so_far
                               (vcid, vbid)
                               (t1 ** [:: ERet
                                          (Pointer.component pc)
                                          (Register.get R_COM regs)
                                          mem (Pointer.component pc')]
                               )
                            )
                   ) as [Hshr | Hnotshr].
        -- (** shared stuff *)
          apply shared_stuff_from_anywhere; auto.
        -- (** private stuff *)
          destruct (vcid =? Pointer.component pc') eqn:eacid.
          ++
            (** private stuff of current pc from ...*)
            assert (vcid = Pointer.component pc'). by apply beq_nat_true. subst.
            specialize (classic (addr_shared_so_far
                                   (acid, abid)
                                   (t1 ** [:: ERet
                                          (Pointer.component pc)
                                          (Register.get R_COM regs)
                                          mem (Pointer.component pc')]
                                   )
                                )
                       ) as [Hshraddr | Hnotshraddr].
            ** apply private_stuff_of_current_pc_from_shared_addr; auto.
            ** apply private_stuff_from_corresp_private_addr; auto. simpl.
               inversion Hmem1 as [| |]; simpl in *; subst; auto.
               --- exfalso. apply Hnotshr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
               --- exfalso. apply Hnotshraddr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
          ++ (** private stuff NOT of current pc *)
            apply private_stuff_from_corresp_private_addr; simpl in *; auto; subst.
            ** intros Hshraddr.
               apply Hnotshr. rewrite Eapp_rcons. rewrite Eapp_rcons in Hshraddr.
               eapply addr_shared_so_far_load_addr_shared_so_far; simpl; eauto.
            ** inversion Hmem1 as [| |]; simpl in *; subst; auto.
               --- exfalso. apply Hnotshr. rewrite Eapp_rcons.
                   eapply reachable_from_previously_shared; eauto. simpl.
                   constructor. by rewrite in_fset1.
               --- exfalso. apply Hnotshr.
                   rewrite Eapp_rcons.
                   eapply addr_shared_so_far_load_addr_shared_so_far; simpl; eauto.
                   +++
                     eapply reachable_from_previously_shared; eauto. simpl.
                     constructor. by rewrite in_fset1.
                   +++ eassumption.


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
        clear Hstar01 Hstep12 Hstep12'. (* Do we need anything in here? *)
        destruct (Register.eqP reg r) as [Heq | Hneq].
        -- (* If we read the register we just wrote, we get the exact immediate
              value, here assumed to be a pointer. *)
           subst r. rewrite Register.gss in Hget.
           destruct v as [n | ptr']; first discriminate.
           injection Hget as Hget; subst ptr'.
           match goal with
           | H: executing _ _ _ |- _ =>
             destruct H as [procs [proc [Hprocs [Hproc [Hoff [Hperm Hnth]]]]]] end.
           assert (Hwf_instr: well_formed_instruction
                          p (Pointer.component pc) (Pointer.block pc)
                          (IConst (IPtr ptr) reg)).
           {
             eapply wfprog_well_formed_instructions; eauto.
             - rewrite <- CS.genv_procedures_prog_procedures; auto.
             - eapply nth_error_In; eauto.
           }
           (* Thanks to [well_formed_instruction], we know that pointer
              constants may only refer to their own component. *)
           destruct ptr as [[[P C] b] o].
           assert (C = Pointer.component pc).
           {
             inversion Hwf_instr. by simpl in *.
           }
           subst C. intros; simpl in *; subst.
           now apply wf_ptr_own.
        -- (* For any other register, this follows directly from the IH. *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* IMov *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct (Register.eqP reg rdest) as [Heq | Hneq].
        -- (* The new value comes from r1, which follows from the IH. *)
           subst rdest. rewrite Register.gss in Hget.
           exact (Hregs1 _ _ Hget).
        -- (* The new value comes from reg, which follows from the IH. *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* IBinOp *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct (Register.eqP reg r3) as [Heq | Hneq].
        -- (* If we read the register we just wrote, we get the result of the
              operation, which we then case analyze. *)
           subst r3. rewrite Register.gss in Hget.
           unfold result, eval_binop in Hget.
           destruct op;
             destruct (Register.get r1 regs) eqn:Hget1;
             destruct (Register.get r2 regs) eqn:Hget2;
             (* Most cases are nonsensical; a handful remain. *)
             inversion Hget; subst.
           (* Whenever there is a pointer and an integer, the result follows
              from the IH on the pointer, albeit with a bit of work to account
              for the integer offsets. *)
           ++ assert (Hr2 := Hregs1 _ _ Hget2).
              intros G.
              erewrite <- Pointer.add_preserves_permission in Hr2.
              specialize (Hr2 G).
              inversion Hr2; subst. (* By the corresponding [constructor]. *)
              ** now apply wf_ptr_own.
              ** now apply wf_ptr_shared.
           ++ assert (Hr1 := Hregs1 _ _ Hget1).
              intros G.
              erewrite <- Pointer.add_preserves_permission in Hr1.
              specialize (Hr1 G).
              inversion Hr1; subst; (* Can be picked automatically. *)
                now constructor.
           ++ assert (Hr1 := Hregs1 _ _ Hget1).
              intros G.
              erewrite <- Pointer.add_preserves_permission in Hr1.
              specialize (Hr1 G).
              inversion Hr1; subst;
                now constructor.
           (* The remaining cases are contradictions requiring some additional
              but trivial analysis. *)
           ++ destruct t as [[[P1 C1] b1] o1];
                destruct t0 as [[[P2 C2] b2] o2];
                destruct (Permission.eqb P1 P2);
                destruct (C1 =? C2);
                destruct (b1 =? b2);
                discriminate.
           ++ destruct (Pointer.leq t t0);
                discriminate.
        -- (* For any other register, this follows directly from the IH. *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* IPtrOfLabel *)
        intros reg ptr' Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        destruct (Register.eqP reg r) as [Heq | Hneq].
        -- (* *)
           subst r. rewrite Register.gss in Hget.
           injection Hget as Hget; subst ptr'.
           destruct ptr as [[[P C] b] o].
           rewrite (find_label_in_component_1 _ _ _ _ H0). intros.
           now apply wf_ptr_own.
        -- (* *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* ILoad *)
        intros reg ptr' Hget Hperm'.
        (* clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *) *)
        destruct (Register.eqP reg r2) as [Heq | Hneq].
        -- (*  *)
           subst r2. rewrite Register.gss in Hget. subst v.
           (* IH *)
           specialize (Memory.load_some_permission _ _ _ H1) as Hperm.
           assert (Hr1 := Hregs1 _ _ H0 Hperm).
           assert (Hptr := Hmem1 _ _ H1 Hperm').
           destruct ptr as [[[P C] b] o].
           destruct ptr' as [[[P' C'] b'] o'].
           simpl in *. subst.
           inversion Hptr as [| |]; simpl in *; subst; last by constructor.
           ++ (** private stuff from corresp private addr *)
             destruct (C =? Pointer.component pc) eqn:eC.
             ** assert (C = Pointer.component pc). by apply beq_nat_true. subst.
                by constructor.
             ** inversion Hr1 as [|]; subst; auto.
                --- by rewrite <- beq_nat_refl in eC.
                --- by apply H3 in H4.
           ++ by constructor.
           
        -- (* The new value comes from reg, which follows from the IH. *)
          specialize (Register.gso v regs Hneq) as G.
          assert (Hget' : Register.get reg regs = Ptr ptr').
          { by rewrite Hget in G. }
          exact (Hregs1 _ _ Hget' Hperm').
      * (* IJal *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite <- (find_label_in_component_1 _ _ _ _ H0).
        destruct (Register.eqP reg R_RA) as [Heq | Hneq].
        -- (* *)
           subst reg. rewrite Register.gss in Hget.
           injection Hget as Hget; subst ptr.
           rewrite <- Pointer.inc_preserves_component.
           destruct (Pointer.inc pc) as [[[perm C] b] o] eqn:Heq.
           intros.
           now apply wf_ptr_own.
        -- (* *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* IJump *)
        intros reg ptr Hget.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite H2.
        exact (Hregs1 _ _ Hget).
      * (* IJumpFunPtr *)
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
        destruct (Register.eqP reg rptr) as [Heq | Hneq].
        -- (* *)
           subst rptr. rewrite Register.gss in Hget.
           injection Hget as Hget; subst ptr'.
           specialize (Memory.component_of_alloc_ptr _ _ _ _ _ H2) as rewr.
           intros.
           destruct ptr as [[[P C] b] o]. simpl in *. subst.
           now apply wf_ptr_own.
        -- (* *)
           rewrite Register.gso in Hget; last assumption.
           exact (Hregs1 _ _ Hget).
      * (* ICall *)
        intros reg ptr Hget Hperm.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite Register.gi in Hget.
        destruct (Register.eqP reg R_COM) as [Heq | Hneq];
          last discriminate.
        subst reg. rewrite Hget.
        assert (Hrcom := Hregs1 _ _ Hget Hperm).
        destruct ptr as [[[P_ C_] b_] o_].
        simpl in *. subst.
        apply wf_ptr_shared.
        rewrite Eapp_rcons.
        apply reachable_from_args_is_shared. simpl.
        apply Reachable_refl. apply /fset1P. reflexivity.
      * (* IReturn *)
        intros reg ptr Hget Hperm.
        clear Hstar01 Hstep12 Hstep12' H. (* Do we need anything in here? *)
        rewrite Register.gi in Hget.
        destruct (Register.eqP reg R_COM) as [Heq | Hneq];
          last discriminate.
        subst reg. rewrite Hget.
        assert (Hrcom := Hregs1 _ _ Hget Hperm).
        destruct ptr as [[[P_ C_] b_] o_].
        simpl in *. subst.
        apply wf_ptr_shared.
        rewrite Eapp_rcons.
        apply reachable_from_args_is_shared. simpl.
        apply Reachable_refl. apply /fset1P. reflexivity.
Qed.

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
  Pointer.permission ptr = Permission.data ->
  wf_ptr_wrt_cid_t pc_comp t ptr.
Proof.
   unfold wf_reg_wrt_t_pc. intros H Hget Hperm. apply (H r ptr Hget Hperm).
Qed.

Lemma wf_mem_wrt_t_pc_wf_load mem t pc_comp load_at ptr:
  wf_mem_wrt_t_pc mem t pc_comp ->
  Memory.load mem load_at = Some (Ptr ptr) ->
  Pointer.permission ptr = Permission.data ->
  wf_load pc_comp t load_at ptr.
Proof.
    by (unfold wf_mem_wrt_t_pc; intros H Hload Hperm; eapply H).
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
  (* "Running" assumptions (what could be derived from the prefix run?) *)
  well_formed_program p ->
  well_formed_program c ->
  mergeable_interfaces (prog_interface p) (prog_interface c) ->
  closed_program (program_link p c) ->
  (* "Proper" assumptions *)
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
  intros Hwfp Hwfc Hlinkable Hclosed Hstar ? ?; subst.
  pose proof linking_well_formedness Hwfp Hwfc (proj1 Hlinkable) as Hwf.
  set prog := program_link p c. fold prog in Hstar.
  remember (CS.initial_machine_state prog) as s0 eqn:Hs0.
  remember (prepare_global_env prog) as G eqn:HG.
  revert Hs0 HG.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s0 t1 s1 t2 s2 t12 Hstar01 IHstar Hstep12 Ht12];
    intros ? ?; subst.
  - (* Base case. *)
    split.
    + (* Memory domain. *)
      intros ptr perm cid bid off Hload.
      unfold CS.initial_machine_state in Hload.
      destruct (cprog_main_existence Hclosed) as [main [Hmain _]].
      rewrite Hmain in Hload.
      destruct (prepare_procedures_memory_prog_buffers Hwf Hload)
        as [(*Cbufs [*)buf (*[Hbufs*) [Hbuf Hptr]].
      (* No pointers in static buffers. *)
      exfalso. eapply prog_buffer_ptr; eassumption.
    + (* Registers. *)
      intros reg perm cid bid off Hget.
      unfold CS.initial_machine_state in Hget.
      destruct (prog_main prog) eqn:Hcase.
      * unfold Register.get in Hget.
        rewrite Register.reg_in_domm_init_Undef in Hget;
          first discriminate.
        (* TODO: Lemma for sub-proof below? *)
        unfold Register.init.
        repeat rewrite domm_set.
        repeat rewrite in_fsetU1.
        now destruct reg.
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
        destruct (Pointer.eqP ptr0 ptr) as [Heq | Hneq].
        -- subst ptr0.
           rewrite (Memory.load_after_store_eq _ _ _ _ H1) in Hload.
           injection Hload as Hget.
           eapply IHget; eassumption.
        -- rewrite (Memory.load_after_store_neq _ _ _ _ _ Hneq H1) in Hload.
           eapply IHload; eassumption.
      * (* IAlloc *)
        destruct
          (addr_eqP (Pointer.component ptr, Pointer.block ptr)
                    (Pointer.component ptr0, Pointer.block ptr0))
          as [Heq | Hneq].
        -- rewrite (Memory.load_after_alloc_eq _ _ _ _ _ _ H2 Heq) in Hload.
           destruct (Permission.eqb (Pointer.permission ptr) Permission.data);
             last discriminate.
           destruct (Pointer.offset ptr <? Z.of_nat (Z.to_nat size))%Z;
             last discriminate.
           destruct (0 <=? Pointer.offset ptr)%Z;
             discriminate.
        -- rewrite (Memory.load_after_alloc _ _ _ _ _ _ H2 Hneq) in Hload.
           eapply IHload; eassumption.
    + (* Register file domain. *)
      intros reg perm cid bid off Hget.
      inversion Hstep12 as [? ? ? ? Hstep12']; subst.
      inversion Hstep12'; subst;
        try (by (eapply IHget; eauto)). (* Solve some goals. *)
      * (* IConst *)
        destruct (Register.eqb reg r) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst r. rewrite Register.gss in Hget.
           destruct v as [| ptr]; first discriminate.
           injection Hget as Hget; subst ptr.
           (* By program (and instruction) well-formedness. *)
           destruct H as [Cprocs [Pcode [HCprocs [HPcode [_ [_ Hinstr]]]]]].
           destruct (prepare_procedures_procs_prog_procedures Hwf HCprocs HPcode)
             as [Cprocs' [P' [HCprocs' HPcode']]].
           pose proof wfprog_well_formed_instructions
                Hwf HCprocs' HPcode' (nth_error_In _ _ Hinstr)
             as [Hptr Hbufs].
           simpl in Hptr; subst cid.
           apply star_iff_starR in Hstar01.
           now eapply CS.star_pc_domm_non_inform; eauto.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IMov *)
        destruct (Register.eqb reg rdest) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst rdest. rewrite Register.gss in Hget.
           eapply IHget; eassumption.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IBinOp *)
        destruct (Register.eqb reg r3) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst r3. rewrite Register.gss in Hget. subst result.
           unfold eval_binop in Hget;
             destruct op;
             destruct (Register.get r1 regs) eqn:Hcase1;
             destruct (Register.get r2 regs) eqn:Hcase2;
             inversion Hget; subst.
           ++ destruct t as [[[perm' C'] b'] o'].
              injection H1 as ? ? ? ?; subst.
              eapply IHget; eassumption.
           ++ destruct t as [[[perm' C'] b'] o'].
              injection H1 as ? ? ? ?; subst.
              eapply IHget; eassumption.
           ++ destruct t as [[[perm' C'] b'] o'].
              injection H1 as ? ? ? ?; subst.
              eapply IHget; eassumption.
           ++ destruct t as [[[perm' C'] b'] o'].
              destruct t0 as [[[perm0' C0'] b0'] o0'].
              destruct (Permission.eqb perm' perm0');
                destruct (C' =? C0');
                destruct (b' =? b0');
                discriminate.
           ++ destruct (Pointer.leq t t0); discriminate.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IPtrOfLabel *)
        destruct (Register.eqb reg r) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst r. rewrite Register.gss in Hget.
           injection Hget as Hget. subst ptr.
           setoid_rewrite <- (find_label_in_component_1 _ _ _ _ H0).
           apply star_iff_starR in Hstar01.
           now eapply CS.star_pc_domm_non_inform; eauto.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* ILoad *)
        destruct (Register.eqb reg r2) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst r2. rewrite Register.gss in Hget. subst v.
           eapply IHload; eassumption.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IJal *)
        destruct (Register.eqb reg R_RA) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst reg. rewrite Register.gss in Hget.
           injection Hget as Hget.
           change cid with (Pointer.component (perm, cid, bid, off)).
           rewrite <- Hget, -> Pointer.inc_preserves_component.
           apply star_iff_starR in Hstar01.
           now eapply CS.star_pc_domm_non_inform; eauto.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* IAlloc *)
        destruct (Register.eqb reg rptr) eqn:Hcase;
          move: Hcase => /Register.eqP => Hcase.
        -- subst rptr. rewrite Register.gss in Hget.
           injection Hget as Hget; subst ptr.
           setoid_rewrite (Memory.component_of_alloc_ptr _ _ _ _ _ H2).
           apply star_iff_starR in Hstar01.
           now eapply CS.star_pc_domm_non_inform; eauto.
        -- rewrite Register.gso in Hget; last assumption.
           eapply IHget; eassumption.
      * (* ICall *)
        rewrite Register.gi in Hget.
        destruct (Register.eqP reg R_COM) as [Heq | Hneq];
          last discriminate.
        eapply IHget; eassumption.
      * (* IReturn *)
        rewrite Register.gi in Hget.
        destruct (Register.eqP reg R_COM) as [Heq | Hneq];
          last discriminate.
        eapply IHget; eassumption.
Qed.

Definition dummy_value_of_node (n: node_t) := Ptr (Permission.data, n.1, n.2, 0%Z).

Lemma Reachable_induction_mem_invariant mem (P: value -> Prop):
  (forall c b perm off perm' off',
      P (Ptr (perm, c, b, off)) -> P (Ptr (perm', c, b, off')))
  ->
  (forall addr v, Memory.load mem addr = Some v -> P (Ptr addr) ->  P v) ->
  (
    forall (aset: {fset node_t}) (a: node_t),
      Reachable mem aset a ->
      (forall (a': node_t),
          a' \in aset -> (forall perm off, P (Ptr (perm, a'.1, a'.2, off)))) ->
      (forall perm off, P (Ptr (perm, a.1, a.2, off)))
  ).
Proof.
  intros Pproperty mem_invariant. intros ? ? Hreach.
  induction Hreach as [? Hin | ? ? ? ? Hreach' IH Hin Hcomp]; intros aset_invariant.
  - apply aset_invariant; auto.
  - intros perm off. 
    assert (exists off offv, Memory.load mem (Permission.data, cid, bid, off) =
                             Some (Ptr (Permission.data, b'.1, b'.2, offv))
           ) as [offl [offv Hload]].
    {
      destruct b' as [b'cid b'bid]; simpl in *.
      apply In_in in Hcomp. erewrite ComponentMemory.load_block_load in Hcomp.
      unfold Memory.load. simpl. rewrite Hin. destruct Hcomp as [? [? ?]]. by eauto.
    }

    specialize (IH aset_invariant Permission.data offl).
    eapply Pproperty. eapply mem_invariant; eauto.
Qed.
    
Corollary addr_shared_so_far_domm_partition p c st t a cid:
  (* "Running" assumptions (what could be derived from the prefix run?) *)
  well_formed_program p ->
  well_formed_program c ->
  mergeable_interfaces (prog_interface p) (prog_interface c) ->
  (* "Proper" assumptions *)
  is_prefix st (program_link p c) t ->
  closed_program (program_link p c) ->
  well_formed_program (program_link p c) ->
  addr_shared_so_far a t ->
  cid = a.1 ->
  (cid \in domm (prog_interface p) \/ cid \in domm (prog_interface c)).
Proof.
  generalize st.
  pose (P :=
          fun v =>
            match v with
            | Ptr (perm, cid, b, o) =>
              (cid \in domm (prog_interface p) \/ cid \in domm (prog_interface c))
            | _ => True
            end
       ).
  assert (Pproperty: forall c b perm off perm' off',
             P (Ptr (perm, c, b, off)) -> P (Ptr (perm', c, b, off'))).
  {
    by intros; auto.
  }
  revert a cid.
  induction t as [|t e] using last_ind.
  - intros ? ? ? ? ? ? ? ? ? Hshr ?; inversion Hshr; by find_nil_rcons.
  - intros ? ? ? Hwfp Hwfc Hifaces Hpref Hclosed Hwf Hshr ?.
    destruct a as [acid abid]. simpl in *; subst.
    apply star_iff_starR in Hpref. 
    apply starR_rcons in Hpref as [st1 [se1 [Ht1 [He1 HE0]]]];
      last by apply CS.singleton_traces_non_inform. 
    inversion Hshr as [? ? ? Hreach | ? ? ? ? Hshr' Hreach]; find_rcons_rcons.
    + inversion He1 as [? ? ? ? Hstepinform Hevent]; subst.
      inversion Hstepinform; subst; simpl in *; try discriminate;
        inversion Hevent; subst; simpl in *;
          apply star_iff_starR in Ht1;
          (** TODO: specialize value_mem_reg_domm_partition more before applying it. *)
          specialize (value_mem_reg_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hifaces Hclosed
                        Ht1 Logic.eq_refl Logic.eq_refl) as Hinvariants;
          destruct Hinvariants as [mem_invariant reg_invariant].
      * (** ICall *)
        assert (mem_invariant':
                  forall (addr : Pointer.t) (v : value),
                    Memory.load mem addr = Some v -> P (Ptr addr) -> P v
               ).
        {
          intros [[[? ?] ?] ?] v Hload _.
          destruct v as [| [[[? ?] ?] ?] |]; unfold P; auto.
          eapply mem_invariant; by eauto. 
        }
        
        specialize (Reachable_induction_mem_invariant mem P Pproperty mem_invariant')
          as Hinduction.
        simpl in *.
        
          specialize (Hinduction _ _ Hreach). apply Hinduction; auto; last exact Z0.
          intros ? Ha' _ _.
          destruct (Register.get R_COM regs)
            as [| [[[perm cid] bid] off] | ] eqn:ereg;
            simpl in *; try by rewrite in_fset0 in Ha'.
          destruct (Permission.eqb perm Permission.data) eqn:eperm; simpl in *;
            try by rewrite in_fset0 in Ha'.
          rewrite in_fset1 in Ha'. move : Ha' => /eqP => Ha'; inversion Ha'; subst.
          eapply reg_invariant; by eauto.
          exact Permission.data. (* FIXME: New subgoal after changing permission equality, suspect. *)
      * (** IReturn *)
        (** CAUTION: !!!!!!!!! exactly the same proof as ICall !!!!!!!!!*)
        assert (mem_invariant':
                  forall (addr : Pointer.t) (v : value),
                    Memory.load mem addr = Some v -> P (Ptr addr) -> P v
               ).
        {
          intros [[[? ?] ?] ?] v Hload _.
          destruct v as [| [[[? ?] ?] ?] |]; unfold P; auto.
          eapply mem_invariant; by eauto. 
        }
        
        specialize (Reachable_induction_mem_invariant mem P Pproperty mem_invariant')
          as Hinduction.

        simpl in *.
        specialize (Hinduction _ _ Hreach). apply Hinduction; auto; last exact Z0.
        intros ? Ha' _ _.
        destruct (Register.get R_COM regs)
          as [| [[[perm cid] bid] off] | ] eqn:ereg;
          simpl in *; try by rewrite in_fset0 in Ha'.
        destruct (Permission.eqb perm Permission.data) eqn:eperm; simpl in *;
          try by rewrite in_fset0 in Ha'.
        rewrite in_fset1 in Ha'. move : Ha' => /eqP => Ha'; inversion Ha'; subst.
        eapply reg_invariant; by eauto.
          exact Permission.data. (* FIXME: New subgoal after changing permission equality, suspect. *)
        
    + inversion He1 as [? ? ? ? Hstepinform Hevent]; subst.
      inversion Hstepinform; subst; simpl in *; try discriminate;
        inversion Hevent; subst; simpl in *;
          apply star_iff_starR in Ht1;
          (** TODO: specialize value_mem_reg_domm_partition more before applying it. *)
          specialize (value_mem_reg_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hifaces Hclosed
                        Ht1 Logic.eq_refl Logic.eq_refl) as Hinvariants;
          destruct Hinvariants as [mem_invariant reg_invariant].

      * (** ICall *)
        assert (mem_invariant':
                  forall (addr : Pointer.t) (v : value),
                    Memory.load mem addr = Some v -> P (Ptr addr) -> P v
               ).
        {
          intros [[[? ?] ?] ?] v Hload _.
          destruct v as [| [[[? ?] ?] ?] |]; unfold P; auto.
          eapply mem_invariant; by eauto. 
        }
        
        specialize (Reachable_induction_mem_invariant mem P Pproperty mem_invariant')
          as Hinduction.
        
        specialize (IHt _ addr'.1 _ Hwfp Hwfc Hifaces Ht1 Hclosed Hwf Hshr' Logic.eq_refl).
        specialize (Hinduction _ _ Hreach). apply Hinduction; auto; last exact Z0.
        intros ? Ha'? ?.
        rewrite in_fset1 in Ha'. move : Ha' => /eqP => Ha'; inversion Ha'; subst.
        eapply IHt; eauto.
        exact Permission.data. (* FIXME: New subgoal after changing permission equality, suspect. *)

      * (** IReturn *)
        assert (mem_invariant':
                  forall (addr : Pointer.t) (v : value),
                    Memory.load mem addr = Some v -> P (Ptr addr) -> P v
               ).
        {
          intros [[[? ?] ?] ?] v Hload _.
          destruct v as [| [[[? ?] ?] ?] |]; unfold P; auto.
          eapply mem_invariant; by eauto. 
        }
        
        specialize (Reachable_induction_mem_invariant mem P Pproperty mem_invariant')
          as Hinduction.
        
        specialize (IHt _ addr'.1 _ Hwfp Hwfc Hifaces Ht1 Hclosed Hwf Hshr' Logic.eq_refl).
        specialize (Hinduction _ _ Hreach). apply Hinduction; auto; last exact Z0.
        intros ? Ha'? ?.
        rewrite in_fset1 in Ha'. move : Ha' => /eqP => Ha'; inversion Ha'; subst.
        eapply IHt; eauto.
        exact Permission.data. (* FIXME: New subgoal after changing permission equality, suspect. *)
Qed.

Lemma not_executing_can_not_share s p t e C b:
  well_formed_program p ->
  closed_program p ->
  is_prefix s p (rcons t e) ->
  C <> cur_comp_of_event e ->
  (forall b', ~ addr_shared_so_far (C, b') t) ->
  ~ addr_shared_so_far (C, b) (rcons t e).
Proof.
  intros Hwf Hclosed Hprefix HC Hnot.
  intros Hshared.
  CS.unfold_states. unfold is_prefix in *.
  rewrite -cats1 in Hprefix.  
  apply star_app_inv in Hprefix as [s [Hstar1 Hstar2]];
    last by apply CS.singleton_traces_non_inform.
  apply star_cons_inv in Hstar2 as [s1' [s2' [Hstar_before [Hstep Hstar_after]]]];
    last by apply CS.singleton_traces_non_inform.
  assert (Hprefbefore_e: is_prefix s1' p t).
  {
    eapply star_trans; eauto. by rewrite E0_right.
  }
  (*assert (Hstar_e: is_prefix s2' p (t ++ [:: e])).
  {
    eapply star_right; last reflexivity; last exact Hstep.
    eapply star_trans; eauto. by rewrite E0_right.
  }*)
  specialize (is_prefix_wf_state_t _ _ _ Hclosed Hwf Hprefbefore_e)
    as [Hwf_mem Hwf_reg].
  CS.unfold_state s1'. simpl in *.
  inversion Hstep as [? ? ? ? Hstep']; subst.
  inversion Hstep'; subst; try discriminate; simpl in *; destruct e; try discriminate.
  match goal with
    | H: [:: ?x] = [:: ?y] |- _ => inversion H
    end.
  subst. clear Hstep'. destruct pc0 as [[[ppc0 cpc0] bpc0] opc0].
  simpl in *.
  - inversion Hshared as [ ? ? ? Hreach|]; find_rcons_rcons; simpl in *.
    destruct (Register.get R_COM regs0) as [| [[[[] cRCOM] bRCOM] oRCOM] |] eqn:eR_COM;
      inversion Hreach as [? Heq|]; subst; simpl in *;
        try (by eapply Reachable_fset0; eauto);
        try (rewrite in_fset1 in Heq;
             move : Heq => /eqP => Heq; inversion Heq; subst; clear Heq).
    + specialize (Hwf_reg _ _ eR_COM Logic.eq_refl).
      inversion Hwf_reg as [| ? ? ? ? Hshr]; subst;
        first (contradiction);
        first (by apply Hnot in Hshr).
    + assert (exists offv off,
                 Memory.load mem0 (Permission.data, cid, bid, off) =
                 Some (Ptr (Permission.data, C, b, offv)) 
             ) as [offv [off Hload]].
      {
        unfold Memory.load. simpl. rewrite H1.
        rewrite -ComponentMemory.load_block_load. by apply In_in in H2.
      }
      specialize (Hwf_mem _ _ Hload Logic.eq_refl);
        inversion Hwf_mem; simpl in *; subst; last contradiction.
      * specialize (Hwf_reg _ _ eR_COM Logic.eq_refl).
        inversion Hwf_reg as [| ? ? ? ? Hshr]; subst.
        (**************************
        first (contradiction);
        first (by apply Hnot in Hshr).
      Search _ cpc0.
        try by rewrite in_fset0 in Hcontra.
    Search _ Reachable fset0.
         *******************************)
Admitted.


Lemma not_shared_diff_comp_not_shared_call:
  forall p s C Cb C' P b t arg mem,
    well_formed_program p ->
    closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t (ECall C P arg mem C')) ->
    C <> Cb ->
    (forall b', ~ addr_shared_so_far (Cb, b') t) ->
    ~ addr_shared_so_far (Cb, b) (rcons t (ECall C P arg mem C')).
Proof.
  intros.
  eapply not_executing_can_not_share; eauto.
Qed.

Lemma load_Some_component_buffer:
  forall p s t e ptr v,
    well_formed_program p ->
    closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    Memory.load (mem_of_event e) ptr = Some v ->
    Pointer.component ptr \in domm (prog_interface p).
  Proof.
    admit.
    Admitted.






(********************************
  Search _ CS.sem_non_inform Component.id.
  assert (Pointer.component pc = next_comp_of_event e).
  {
    clear -Hprefix.
    rewrite -cats1 in Hprefix.
    apply star_app_inv in Hprefix as [s [Hstar1 Hstar2]];
      last by apply CS.singleton_traces_non_inform.
    apply star_cons_inv in Hstar2 as [s1' [s2' [_ [Hstep Hstar_after]]]];
      last by apply CS.singleton_traces_non_inform.
    inversion Hstep as [? ? ? ? Hstep']; subst.
    inversion Hstep'; subst; try discriminate; simpl in *; destruct e; try discriminate.
    match goal with
    | H: [:: ?x] = [:: ?y] |- _ => inversion H
    end.
    subst.
    Search _ pc0.
  }
  inversion Hshared; find_rcons_rcons.
  - 
  - 
  *************************************)
End CSInvariants.

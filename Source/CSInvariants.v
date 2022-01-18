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
Require Import Common.Values.
(** From Renaming, only addr_shared_so_far and some tactics (like find_nil_rcons,
    and find_rcons_rcons) are used. Consider refactoring them out
    (into a file called Sharing.v, and into Common.Util)
    to get rid of the dependency on Renaming.
    Keep CSInvariants for only unary invariants; hence, do not depend on "renaming".
*)
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.CompCertExtensions.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect eqtype ssrfun seq.
From mathcomp Require ssrbool ssrnat.
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

(** Unary invariants about the source semantics *)

Import Source.

Definition is_prefix (s: CS.state) (p: Source.program) t : Prop :=
  Star (CS.sem p) (CS.initial_machine_state p) t s.


Inductive wf_ptr_wrt_cid_t (cid: Component.id) (t: trace event) : Pointer.t -> Prop
  :=
  | wf_ptr_own:
      forall p b o,
        wf_ptr_wrt_cid_t cid t (p, cid, b, o)
  | wf_ptr_shared:
      forall p c_other b o,
      addr_shared_so_far (c_other, b) t -> wf_ptr_wrt_cid_t cid t (p, c_other, b, o)
.


Inductive wf_load (pc_comp: Component.id) (t: trace event)
          : Pointer.t -> Pointer.t -> Prop
  :=
  | private_stuff_from_corresp_private_addr:
      forall load_at ptr,
        ~ addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        ~ addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
        Pointer.component ptr = Pointer.component load_at ->
        wf_load pc_comp t load_at ptr
  | shared_stuff_from_anywhere:
      forall load_at ptr,
        addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        wf_load pc_comp t load_at ptr
  | private_stuff_of_current_pc_from_shared_addr:
      forall load_at ptr,
        ~ addr_shared_so_far (Pointer.component ptr, Pointer.block ptr) t ->
        Pointer.component ptr = pc_comp ->
        addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
        wf_load pc_comp t load_at ptr.

Definition wf_mem_wrt_t_pc (mem: Memory.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
forall load_at ptr,
  Memory.load mem load_at = Some (Ptr ptr) ->
  Pointer.permission ptr = Permission.data ->
  wf_load pc_comp t load_at ptr.

  Fixpoint runtime_expr_struct_invariant
           (e: expr) (val_test: value -> Prop) : Prop :=
    match e with
    | E_val v => val_test v
    | E_binop _ e1 e2 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test
    | E_seq e1 e2 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test
    | E_if e1 e2 e3 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test /\
      runtime_expr_struct_invariant e3 val_test
    | E_alloc e =>
      runtime_expr_struct_invariant e val_test
    | E_deref e =>
      runtime_expr_struct_invariant e val_test
    | E_assign e1 e2 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test
    | E_call _ _ e =>
      runtime_expr_struct_invariant e val_test
    | E_callptr e1 e2 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test
    | E_funptr _
    | E_arg
    | E_local
    | E_exit => true
    end.

  Fixpoint cont_struct_invariant (k: cont) (val_test: value -> Prop) : Prop :=
    match k with
    | Kbinop1 _ e k2 =>
      runtime_expr_struct_invariant e val_test /\
      cont_struct_invariant k2 val_test
    | Kbinop2 _ v k2 =>
      val_test v /\
      cont_struct_invariant k2 val_test
    | Kseq e k2 =>
      runtime_expr_struct_invariant e val_test /\
      cont_struct_invariant k2 val_test
    | Kif e1 e2 k3 =>
      runtime_expr_struct_invariant e1 val_test /\
      runtime_expr_struct_invariant e2 val_test /\
      cont_struct_invariant k3 val_test
    | Kalloc k2 =>
      cont_struct_invariant k2 val_test
    | Kderef k2 =>
      cont_struct_invariant k2 val_test
    | Kassign1 e k2 =>
      runtime_expr_struct_invariant e val_test /\
      cont_struct_invariant k2 val_test
    | Kassign2 v k2 =>
      val_test v /\
      cont_struct_invariant k2 val_test
    | Kcall _ _ k2 =>
      cont_struct_invariant k2 val_test
    | Kcallptr1 e k2 =>
      runtime_expr_struct_invariant e val_test /\
      cont_struct_invariant k2 val_test
    | Kcallptr2 v k2 =>
      val_test v /\
      cont_struct_invariant k2 val_test
    | Kstop => true
    end.

  Definition stack_struct_invariant (s: CS.stack) (val_test: value -> Prop) : Prop :=
    List.Forall (fun frm =>
                   val_test (CS.f_arg frm)
                   /\
                   cont_struct_invariant (CS.f_cont frm) val_test
                )
                s.

Definition wf_expr_wrt_t_pc (e: expr) (t: trace event)
           (pc_comp: Component.id): Prop :=
  runtime_expr_struct_invariant
    e
    (fun v => forall ptr,
         v = Ptr ptr ->
         Pointer.permission ptr = Permission.data ->
         wf_ptr_wrt_cid_t pc_comp t ptr).

Definition wf_cont_wrt_t_pc (k: cont) (t: trace event)
           (pc_comp: Component.id): Prop :=
  cont_struct_invariant
    k
    (fun v => forall ptr,
         v = Ptr ptr ->
         Pointer.permission ptr = Permission.data ->
         wf_ptr_wrt_cid_t pc_comp t ptr).

Definition wf_stack_wrt_t_pc (stk: CS.stack) (t: trace event)
           (pc_comp: Component.id): Prop :=
  stack_struct_invariant
    stk
    (fun v => forall ptr,
         v = Ptr ptr ->
         Pointer.permission ptr = Permission.data ->
         wf_ptr_wrt_cid_t pc_comp t ptr).

Definition wf_state_t (s: CS.state) (t: trace event) : Prop :=
  wf_expr_wrt_t_pc (CS.s_expr s) t (CS.s_component s) /\
  wf_mem_wrt_t_pc (CS.s_memory s) t (CS.s_component s) /\
  wf_cont_wrt_t_pc (CS.s_cont s) t (CS.s_component s) /\
  wf_stack_wrt_t_pc (CS.s_stack s) t (CS.s_component s) /\
  (forall ptr,
         CS.s_arg s = Ptr ptr ->
         Pointer.permission ptr = Permission.data ->
         wf_ptr_wrt_cid_t (CS.s_component s) t ptr).

Lemma initial_wf_mem p:
  well_formed_program p ->
  wf_mem_wrt_t_pc (prepare_buffers p) E0 Component.main.
Proof.
  intros Hwf. constructor.
  - unfold E0. intros contra; inversion contra; by find_nil_rcons.
  - unfold E0. intros contra; inversion contra; by find_nil_rcons.
  - unfold prepare_buffers in *. unfold Memory.load in *.
    find_if_inside_hyp H; [|discriminate].
    rewrite mapmE in H.
    destruct (prog_buffers p (Pointer.component load_at)) as [buf|] eqn:ebuf;
      [|discriminate]; simpl in H.
    rewrite ComponentMemory.load_prealloc in H.
    find_if_inside_hyp H; [|discriminate].
    rewrite setmE in H.
    find_if_inside_hyp H; [|discriminate].
    destruct buf as [sz|chunk] eqn:ebuf2.
    + find_if_inside_hyp H; discriminate.
    + inversion Hwf.
      assert (exists x, prog_interface p (Pointer.component load_at) = Some x)
        as [? Hintf'].
      {
        apply/dommP. rewrite wfprog_defined_buffers0. apply/dommP. by eauto.
      }
      assert (Hintf: prog_interface p (Pointer.component load_at)). by rewrite Hintf'.
      specialize (wfprog_well_formed_buffers0 _ Hintf) as [Hbuf1 Hbuf2].
      rewrite ebuf in Hbuf2. simpl in *.
      move : Hbuf2 => /andP => [[? G]]. move : G => /allP => G.
      apply nth_error_In, In_in in H. by apply G in H.
Qed.

Lemma values_are_integers_expr_wrt_t_pc cur_comp expr:
  values_are_integers expr ->
  forall t,
    wf_expr_wrt_t_pc expr t cur_comp.
Proof.
  induction expr; auto; intros Hvalues t; inversion Hvalues; simpl in *; auto.
  - destruct v; discriminate.
  - move : Hvalues => /andP => [[G1 G2]].
    constructor.
    + apply IHexpr1; by auto.
    + apply IHexpr2; by auto.
  - move : Hvalues => /andP => [[G1 G2]].
    constructor.
    + apply IHexpr1; by auto.
    + apply IHexpr2; by auto.
  - move : Hvalues => /andP => [[G1 G2]].
    move : G2 => /andP => [[G21 G22]].
    constructor.
    + apply IHexpr1; by auto.
    + split; [apply IHexpr2|apply IHexpr3]; by auto.
  - move : Hvalues => /andP => [[G1 G2]].
    constructor.
    + apply IHexpr1; by auto.
    + apply IHexpr2; by auto.
  - move : Hvalues => /andP => [[G1 G2]].
    constructor.
    + apply IHexpr1; by auto.
    + apply IHexpr2; by auto.
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
  - unfold CS.initial_machine_state.
    inversion Hclosed. destruct (prog_main p) eqn:emain; [|discriminate].
    constructor; simpl.
    + apply values_are_integers_expr_wrt_t_pc. inversion Hwf. 
      specialize (wfprog_well_formed_procedures0 _ _ _ emain).
      inversion wfprog_well_formed_procedures0. by intuition.
    + split; [apply initial_wf_mem; assumption | split; by constructor].
  - assert (IHstar_: wf_state_t s1 t1) by (apply IHstar; auto).
    clear IHstar. unfold wf_state_t in IHstar_.
    intuition. (** destructs IHstar_ recursively *)
    inversion Hstep12; subst; (try rewrite E0_right);
      unfold wf_state_t; simpl in *; try by intuition. 
    + (** KS_Binop1 *)
      intuition.
      (** wf_cont remains *)
      inversion H.
      constructor; [assumption|by unfold wf_cont_wrt_t_pc in H0].
    + (** KS_Binop2 *)
      intuition.
      (** wf_cont remains *)
      constructor; [by unfold wf_expr_wrt_t_pc in H |
                    unfold wf_cont_wrt_t_pc in H0; by intuition].
    + (** KS_BinopEval *)
      intuition.
      (** wf_expr remains *)
      simpl in H.
      unfold wf_cont_wrt_t_pc, wf_expr_wrt_t_pc in *. simpl in *.
      destruct H0 as [Hv1 Hk].
      clear -H Hv1.
      (** TODO: Refactor as a lemma *)
      intros ? Heval Hperm.
      destruct op; simpl in *; auto.
      * destruct v1 as [| [[[[] c1] b1] o1] |] eqn:ev1; try discriminate.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst; try discriminate.
           specialize (H _ Logic.eq_refl Logic.eq_refl).
           inversion H; subst; constructor; by auto.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst; discriminate.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst; try discriminate.
           specialize (Hv1 _ Logic.eq_refl Logic.eq_refl).
           inversion Hv1; subst; constructor; by auto.
      * destruct v1 as [| [[[[] c1] b1] o1] |] eqn:ev1; try discriminate.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst; discriminate.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst; try discriminate.
           find_if_inside_hyp Heval; discriminate.
        -- destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; simpl in *; inversion Heval;
             simpl in *; subst.
           ++ specialize (Hv1 _ Logic.eq_refl Logic.eq_refl).
              inversion Hv1; subst; constructor; by auto.
           ++ find_if_inside_hyp Heval; discriminate.
      * destruct v1 as [| [[[[] c1] b1] o1] |] eqn:ev1; try discriminate.
        destruct v2 as [| [[[[] c1] b1] o1] |] eqn:ev2; discriminate.
      * destruct v1 as [| [[[[] c1] b1] o1] |] eqn:ev1; try discriminate;
          destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; discriminate.
      * destruct v1 as [| [[[[] c1] b1] o1] |] eqn:ev1; try discriminate;
          destruct v2 as [| [[[[] c2] b2] o2] |] eqn:ev2; try discriminate.
        -- destruct (Pointer.leq (Permission.code, c1, b1, o1)
                                 (Permission.code, c2, b2, o2)); discriminate.
        -- destruct (Pointer.leq (Permission.data, c1, b1, o1)
                                 (Permission.data, c2, b2, o2)); discriminate.
    + (** KS_Seq1 *)
      intuition.
      (** wf_cont remains *)
      inversion H.
      constructor; assumption.
    + (** KS_If1 *)
      intuition.
      (** wf_cont remains *)
      inversion H. intuition.
      constructor; intuition; assumption.
    + (** KS_If2 *)
      intuition.
      (** wf_expr remains *)
      inversion H0. intuition.
      find_if_inside_goal; assumption.
    + (** KS_Arg *)
      intuition.
      (** wf_expr remains *)
      unfold wf_expr_wrt_t_pc. simpl. intros.
      inversion H3. constructor.
    + (** KS_AllocEval *)
      intuition.
      * (** wf_expr *)
        apply Memory.component_of_alloc_ptr in H5. subst.
        unfold wf_expr_wrt_t_pc. simpl. intros.
        inversion H5; subst.
        destruct ptr0 as [[[ ?] ?] ?]; simpl.
        by constructor.
      * (** wf_mem *)
        unfold wf_mem_wrt_t_pc in H1.
        intros ? ? Hload.
        destruct ((Pointer.component load_at, Pointer.block load_at) ==
                  (Pointer.component ptr, Pointer.block ptr)) eqn:e.
        -- erewrite Memory.load_after_alloc_eq in Hload; eauto.
           ++ repeat (find_if_inside_hyp Hload; [|discriminate]).
              discriminate.
           ++ by apply/eqP.
        -- erewrite Memory.load_after_alloc in Hload; eauto.
           apply/eqP. by rewrite e.
    + (** KS_DerefEval *)
      intuition.
      (** wf_expr *)
      unfold wf_expr_wrt_t_pc. simpl. intros ? ? Hperm. subst.
      destruct ptr as [[[[] cloaded] bloaded] oloaded]; [discriminate|].
      clear Hperm.
      specialize (H1 _ _ H3 Logic.eq_refl).
      unfold wf_expr_wrt_t_pc in H. simpl in H.
      assert (P' = Permission.data).
      { by apply Memory.load_some_permission in H3. }
      subst.
      specialize (H _ Logic.eq_refl Logic.eq_refl).
      inversion H1; simpl in *; subst.
      * inversion H; subst.
        -- by constructor.
        -- contradiction.
      * by constructor.
      * by constructor.
    + (** KS_FunPtr *)
      intuition.
      unfold wf_expr_wrt_t_pc. simpl. intros ? inv contra. inversion inv. subst.
      simpl in *. discriminate.
    + (** KS_Assign1 *)
      intuition.
      (** wf_cont *)
      constructor; simpl; inversion H; assumption.
    + (** KS_Assign2 *)
      intuition. inversion H0. constructor; assumption.
    + (** KS_AssignEval *)
      intuition.
      * (** wf_expr *)
        unfold wf_expr_wrt_t_pc. simpl. inversion H0; assumption.
      * (** wf_mem *)
        intros ? ? Hload Hperm.
        destruct ptr as [[[[] cptr] bptr] optr]; [discriminate|]. clear Hperm.
        erewrite Memory.load_after_store in Hload; [| by eauto].
        assert (P' = Permission.data).
        { by apply Memory.store_some_permission in H3. }
        subst. unfold wf_expr_wrt_t_pc in H. simpl in H.
        specialize (H _ Logic.eq_refl Logic.eq_refl). 
        inversion H0 as [Hv ?].
        find_if_inside_hyp Hload.
        -- move : e => /Pointer.eqP => ?. inversion Hload. subst.
           specialize (Hv _ Logic.eq_refl Logic.eq_refl).
           inversion Hv; subst.
           ++ destruct (classic (addr_shared_so_far (cptr, bptr) t1))
               as [ptrshr|ptrnotshr].
              ** apply shared_stuff_from_anywhere; assumption.
              ** destruct (classic (addr_shared_so_far (C', b') t1))
                  as [C'b'shr|C'b'notshr].
                 --- apply private_stuff_of_current_pc_from_shared_addr; by auto.
                 --- apply private_stuff_from_corresp_private_addr; auto.
                     inversion H; [by auto | contradiction].
           ++ apply shared_stuff_from_anywhere; assumption.
        -- apply H1; by auto.
    + (** KS_InitCallPtr1 *)
      intuition. inversion H.
      constructor; assumption.
    + (** KS_InitCallPtr2 *)
      intuition. unfold wf_expr_wrt_t_pc in H. simpl in *.
      inversion H0.
      constructor; assumption.
    + (** KS_InitCallPtr3 *)
      intuition. inversion H0. assumption.
    + (** KS_InternalCall *)
      intuition.
      * (** wf_expr *)
        apply values_are_integers_expr_wrt_t_pc.
        destruct Hwf.
          by specialize (wfprog_well_formed_procedures0 _ _ _ H5) as [_ [? _]].
      * (** wf_cont *)
          by constructor.
      * constructor; simpl; by intuition.
    + (** KS_ExternalCall *)
      intuition.
      * (** wf_expr *)
        apply values_are_integers_expr_wrt_t_pc.
        destruct Hwf.
          by specialize (wfprog_well_formed_procedures0 _ _ _ H6) as [_ [? _]].
      * 
Admitted.

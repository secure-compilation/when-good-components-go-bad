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

(** Unary invariants about the intermediate semantics *)

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

(** TODO: Write as an inductive. *)
Definition wf_mem_wrt_t_pc (mem: Memory.t) (t: trace event)
           (pc_comp: Component.id) : Prop :=
forall load_at ptr,
  Memory.load mem load_at = Some (Ptr ptr) ->
  Pointer.permission ptr = Permission.data ->
  wf_load pc_comp t load_at ptr.

  (* forall r ptr, *)
  (*   Register.get r reg = Ptr ptr -> *)
  (*   Pointer.permission ptr = Permission.data -> *)
(*   wf_ptr_wrt_cid_t pc_comp t *)

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

(* Definition reach_from_reg_wf_wrt_t_pc (reg: Register.t) (t: trace event) *)
(*            (mem: Memory.t) (pc_comp: Component.id) := *)
(*   forall r ptr ptr_c ptr_b v_c v_b, *)
(*     Register.get r reg = Ptr ptr -> *)
(*     Pointer.permission ptr = Permission.data -> *)
(*     Pointer.component ptr = ptr_c -> *)
(*     Pointer.block ptr = ptr_b -> *)
(*     Reachable mem (fset1 (ptr_c, ptr_b)) (v_c, v_b) -> *)
(*     (forall v_o, wf_ptr_wrt_cid_t pc_comp t (Permission.data, v_c, v_b, v_o)). *)

Definition wf_state_t (s: CS.state) (t: trace event) : Prop :=
  wf_expr_wrt_t_pc (CS.s_expr s) t (CS.s_component s) /\
  wf_mem_wrt_t_pc (CS.s_memory s) t (CS.s_component s) /\
  wf_cont_wrt_t_pc (CS.s_cont s) t (CS.s_component s) /\
  wf_stack_wrt_t_pc (CS.s_stack s) t (CS.s_component s).

Lemma initial_wf_mem p:
  closed_program p ->
  well_formed_program p ->
  prog_main p ->
  wf_mem_wrt_t_pc (prepare_buffers p) E0 Component.main.
Proof.
  Admitted.

Lemma is_prefix_wf_state_t s p t:
  closed_program p ->
  well_formed_program p ->
  is_prefix s p t ->
  wf_state_t s t.
Proof.
  Admitted.

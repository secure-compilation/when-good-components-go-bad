Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Reachability.
Require Import Common.Traces.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect eqtype ssrfun.
From mathcomp Require ssrbool.
From extructures Require Import fmap fset.

Set Bullet Behavior "Strict Subproofs".

Module CS.

Import Intermediate.

Definition stack : Type := list Pointer.t.

(* RB: TODO: [DynShare] Give names to recurring types, harmonize naming
   conventions.
   This type should probably be defined elsewhere. *)
Definition reach_addr : Type := {fmap (Component.id -> {fset (Component.id * Block.id)})}.

(* NOTE: Consider parameterizing the semantics by a type of "additional state",
   and instantiate the non-/informative semantics as specializations of the
   parametric semantics. *)
Definition state : Type := stack * Memory.t * Register.t * Pointer.t * reach_addr.

Definition update_reachability_of_component_with_value : value -> Component.id -> reach_addr -> reach_addr.
  Admitted.

Definition compute_trace_for_load_by_component : Component.id -> Pointer.t -> reach_addr -> trace event.
  Admitted.

Definition compute_trace_for_store_by_component : Component.id -> Pointer.t -> reach_addr -> trace event.
  Admitted.

Definition propagate_store_to_all_components_reach : Pointer.t -> value -> reach_addr -> reach_addr.
  Admitted.

Ltac unfold_state st :=
  let gps := fresh "gps" in
  let mem := fresh "mem" in
  let regs := fresh "regs" in
  let pc := fresh "pc" in
  let addrs := fresh "addrs" in
  destruct st as [[[[gps mem] regs] pc] addrs].

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    let '(_, _, _, pc, _) := s in
    Pointer.component pc \in domm iface
}.

Definition is_context_component (st: state) ctx := turn_of st ctx.
Definition is_program_component (st: state) ctx := negb (is_context_component st ctx).

Ltac simplify_turn :=
  unfold is_program_component, is_context_component in *;
  unfold turn_of, state_turn in *;
  simpl in *.

Definition state_stack (st : state) : stack :=
  let '(gps, _, _, _, _) := st in gps.

Definition state_mem (st : state) : Memory.t :=
  let '(_, mem, _, _, _) := st in mem.

Definition state_regs (s : CS.state) : Register.t :=
  let '(_, _, regs, _, _) := s in regs.

Definition state_pc (st : state) : Pointer.t :=
  let '(_, _, _, pc, _) := st in pc.

Definition state_addrs (st : state) : reach_addr :=
  let '(_, _, _, _, addrs) := st in addrs.

Definition state_component (st : CS.state) : Component.id :=
  Pointer.component (state_pc st).


(* [DynShare]: The assumption here is that prog_buffers themselves
 do not contain any pointer values. So, the only thing that
 counts as "program_ptrs" are the addresses of these buffers,
 not their contents.*)

Definition program_ptrs (p: program) : {fset (Component.id * Block.id)} :=
  domm (uncurrym (prog_buffers p)).

Definition component_ptrs (p: program) (cid: Component.id) : {fset (Component.id * Block.id)}
  := match (prog_buffers p) cid with
     | None => fset0
     | Some map_of_blockids => fset (map (fun bid => (cid, bid)) (domm map_of_blockids))
     end.

Definition value_to_data_pointer_err v : option (Component.id * Block.id) :=
  match v with | Ptr (perm, cid, bid, _) =>
                 if perm =? Permission.data then Some (cid, bid) else None
          | _ => None
  end.

Definition regs_data_ptrs (regs : Register.t) : {fset Component.id * Block.id} :=
  fset(
      seq.pmap
        id
        (codomm
           (filterm (fun x y => isSome y)
                    (mapm value_to_data_pointer_err regs))
        )
    ).

Definition compMem_data_ptrs (m : ComponentMemory.t) : {fset Component.id * Block.id} :=
  fset (concat (map (ComponentMemory.load_block m) (ComponentMemory.domm m))).

Definition mem_data_ptrs (m : Memory.t) : {fset Component.id * Block.id} :=
  (\bigcup_(comp_mem_ptrs <- (codomm (mapm compMem_data_ptrs m))) comp_mem_ptrs)%fset.

Definition state_data_ptrs (st: state) := fsetU (regs_data_ptrs (state_regs st))
                                           (mem_data_ptrs (state_mem st)).

Definition are_all_ptrs_in_reachable (st: state) (p: program) :=
  (fsubset (state_data_ptrs st)
           (\bigcup_(i <- program_ptrs p)
             (fset (reachable_nodes_nat (state_mem st) i))
           )
  )%fset.

Lemma Memory_load_mem_ptrs :
  forall m aP aC aB aO vC vB vO,
    Memory.load m (aP, aC, aB, aO) = Some (Ptr (Permission.data, vC, vB, vO)) ->
    (vC, vB) \in mem_data_ptrs m.
Proof.
  intros ????????. unfold Memory.load. simpl.
  destruct (aP =? Permission.data) eqn:eaP; destruct (m aC) eqn:eaC;
    intros Hload; try discriminate.
  destruct (ComponentMemory.load_block_load t aB vC vB) as [_ Honlyif].
  unfold mem_data_ptrs.
  apply/bigcupP. simpl.
  apply BigCupSpec with (i := compMem_data_ptrs t); auto.
  - apply/codommP. exists aC. rewrite mapmE. rewrite eaC. auto.
  - unfold compMem_data_ptrs. rewrite in_fset.
    rewrite <- flat_map_concat_map. rewrite In_in. rewrite in_flat_map.
    exists aB. split.
    + apply ComponentMemory.load_domm with
          (i := aO) (v := Ptr (Permission.data, vC, vB, vO)). auto.
    + apply Honlyif. exists vO. exists aO. exact Hload.
Qed.

Lemma value_to_data_pointer_err_Ptr :
  forall pc pb po,
  exists x, value_to_data_pointer_err (Ptr (Permission.data, pc, pb, po)) = Some x.
Proof.
  intros ???. by exists (pc, pb).
Qed.

Lemma mem_codomm_setm :
  forall (T S : ordType) (m : {fmap T -> S}) (k1 k2 : T) (v v' : S),
    m k1 = Some v ->
    v' \in codomm (setm m k2 v) ->
    v' \in codomm m.
Proof.
  intros T S m k1 k2 v v' Hmem Hmemcodomm.
  apply/codommP.
  pose (H' := codommP (setm m k2 v) v' Hmemcodomm).
  destruct H' as [kOfv' H'mem].
  rewrite setmE in H'mem.
  destruct (kOfv' == k2) eqn:k2kOfv'.
  - eexists k1. rewrite <- H'mem. exact Hmem.
  - eexists kOfv'. exact H'mem.
Qed.

Lemma in_fsubset :
  forall (T : ordType) (s1 s2 : {fset T}),
    (forall v, v \in s1 -> v \in s2) -> fsubset s1 s2.
Proof.
  intros ? ? ? Hinin.
  apply/fsubsetP.
  unfold sub_mem.
  exact Hinin.
Qed.

Lemma fsubset_in :
  forall (T : ordType) (s1 s2 : {fset T}) v,
    fsubset s1 s2 -> v \in s1 -> v \in s2.
Proof.
  intros ? ? ? ? Hsubset Hin.
  pose (fsubsetP s1 s2 Hsubset) as Hsubset'.
  unfold sub_mem in Hsubset'.
  apply Hsubset'.
  assumption.
Qed.

Ltac unfold_Register_set e1 k'mem :=
  unfold Register.set in k'mem; rewrite setmE in k'mem; rewrite e1 in k'mem;
  simpl in k'mem.

Ltac unfold_regs_ptrs :=
  do 2 (unfold regs_data_ptrs; rewrite in_fset; rewrite seq.mem_pmap; rewrite seq.map_id);
  intros Hin; apply/codommP; destruct (codommP _ _ Hin) as [k' k'mem].

Ltac solve_untouched_registers e1 k' k'mem :=
  exists k'; rewrite filtermE; rewrite filtermE in k'mem; simpl; simpl in k'mem;
         rewrite mapmE; rewrite mapmE in k'mem; unfold_Register_set e1 k'mem; exact k'mem.

Lemma Register_get_regs_ptrs :
  forall r1 regs ptrC ptrB ptrO,
    Register.get r1 regs = Ptr (Permission.data, ptrC, ptrB, ptrO) ->
    (ptrC, ptrB) \in regs_data_ptrs regs.
Proof.
  intros r1 regs ptrC ptrB ptrO Hget.
  unfold regs_data_ptrs; rewrite in_fset; rewrite seq.mem_pmap;
    rewrite seq.map_id. apply/codommP.
  unfold Register.get in Hget.
  destruct (regs (Register.to_nat r1)) as [v |] eqn:e.
  - exists (Register.to_nat r1).
    rewrite filtermE. rewrite mapmE. rewrite e. rewrite Hget. auto.
  - discriminate.
Qed.
         
Lemma regs_ptrs_set_get_in :
  forall (regs: Register.t) r1 r2 v,
    v \in regs_data_ptrs (Register.set r2 (Register.get r1 regs) regs) ->
    v \in regs_data_ptrs regs.
Proof.
  intros regs r1 r2 v.
  unfold_regs_ptrs.
  destruct (Some v == value_to_data_pointer_err (Register.get r1 regs)) eqn:copied;
    destruct (k' == Register.to_nat r2) eqn:e1; try solve_untouched_registers e1 k' k'mem.
  - pose (copied' := eqP copied); pose (e1' := eqP e1).
    exists (Register.to_nat r1).
    rewrite filtermE. rewrite filtermE in k'mem. simpl. simpl in k'mem.
    rewrite mapmE. rewrite mapmE in k'mem.
    destruct (regs (Register.to_nat r1)) as [vOfr1 |] eqn:e.
    + rewrite e. simpl.
      destruct vOfr1 as [| t |];
        try (
            simpl;
            unfold Register.get in copied';
            erewrite e in copied'; simpl in copied'; discriminate
          ).
      simpl.
      unfold Register.get in k'mem. rewrite e in k'mem.
      unfold_Register_set e1 k'mem. exact k'mem.
    + unfold Register.get in k'mem.
      rewrite e in k'mem.
      unfold_Register_set e1 k'mem. discriminate.
  - (* here, obtain a contradiction *)
    rewrite filtermE in k'mem. simpl in k'mem.
    rewrite mapmE in k'mem.
    unfold_Register_set e1 k'mem.
    pose (@negPf (Some v == value_to_data_pointer_err (Register.get r1 regs))) as n.
    assert (ineq : Some v != value_to_data_pointer_err (Register.get r1 regs)).
    {
      apply/n. exact copied.
    }
    pose (negP ineq) as n0. exfalso. apply n0. apply/eqP.
    destruct (value_to_data_pointer_err (Register.get r1 regs)).
    + simpl in k'mem. apply Some_inj. symmetry. exact k'mem.
    + simpl in k'mem. discriminate.
Qed.

Lemma regs_ptrs_set_get :
  forall regs r1 r2,
    fsubset (regs_data_ptrs (Register.set r2 (Register.get r1 regs) regs))
            (regs_data_ptrs regs).
Proof.
  intros. apply in_fsubset. apply regs_ptrs_set_get_in.
Qed.

(*Lemma Pointer_add_p_c_b :
  forall p z p', Pointer.add p z = p' ->
                 Pointer.permission p' = Pointer.permission p /\
                 Pointer.component p' = Pointer.component p /\
                 Pointer.block p' = Pointer.block p.
Proof.
  intros p z p' Hadd.
  destruct p as [[pc pb] po]. rewrite <- Hadd.
  simpl. auto.
Qed.

Lemma Pointer_sub_c_b :
  forall p z p', Pointer.sub p z = p' ->
                 Pointer.component p' = Pointer.component p /\
                 Pointer.block p' = Pointer.block p.
Proof.
  intros p z p' Hsub.
  destruct p as [[pc pb] po]. rewrite <- Hsub.
  simpl. auto.
Qed.
*)
Lemma eval_binop_ptr :
  forall op v1 v2 p,
    eval_binop op v1 v2 = Ptr p ->
    (exists p1, (v1 = Ptr p1 \/ v2 = Ptr p1)
                /\
                Pointer.permission p = Pointer.permission p1 /\
                Pointer.component p = Pointer.component p1 /\
                Pointer.block p = Pointer.block p1
    ).
  intros op v1 v2 p Heval.
  unfold eval_binop in Heval.
  destruct op eqn:eop; destruct v1 eqn:e1; destruct v2 eqn:e2;
    try discriminate.
  - exists t. split.
    + right. trivial.
    + inversion Heval.
      split; last split.
      apply Pointer.add_preserves_permission.
      apply Pointer.add_preserves_component.
      apply Pointer.add_preserves_block.
  - exists t. split.
    + left. trivial.
    + inversion Heval.
      split; last split.
      apply Pointer.add_preserves_permission.
      apply Pointer.add_preserves_component.
      apply Pointer.add_preserves_block.
  - exists t. split.
    + left. trivial.
    + inversion Heval.
      split; last split.
      apply Pointer.sub_preserves_permission.
      apply Pointer.sub_preserves_component.
      apply Pointer.sub_preserves_block.
  - destruct t as [[[tp tc] tb] to].
    destruct t0 as [[[t0p t0c] t0b] t0o].
    destruct ((tp =? t0p) && (tc =? t0c) && (tb =? t0b)); discriminate.
  - destruct (Pointer.leq t t0); discriminate.
Qed.    

Lemma regs_ptrs_binop :
  forall regs rdest op r1 r2,
    fsubset (regs_data_ptrs
               (Register.set rdest
                             (eval_binop op
                                         (Register.get r1 regs)
                                         (Register.get r2 regs)
                             )
                             regs)
            )
            (regs_data_ptrs regs).
Proof.
  intros regs rdest op r1 r2. apply in_fsubset. intros v.
  unfold_regs_ptrs.
  destruct (Some v == value_to_data_pointer_err (eval_binop op
                                         (Register.get r1 regs)
                                         (Register.get r2 regs)
           )) eqn:copied;
    destruct (k' == Register.to_nat rdest) eqn:e1;
    try solve_untouched_registers e1 k' k'mem.
  - pose (copied' := eqP copied); pose (e1' := eqP e1).
    destruct (eval_binop op (Register.get r1 regs) (Register.get r2 regs)) eqn:e.
    + simpl in copied'. discriminate.
    + destruct (eval_binop_ptr op (Register.get r1 regs) (Register.get r2 regs) t e)
        as [ptr [[ptrr1 | ptrr2] [permeq [cmpeq blkeq]]]];
        eexists;
        rewrite filtermE; rewrite filtermE in k'mem; simpl; simpl in k'mem;
          rewrite mapmE; rewrite mapmE in k'mem;
            destruct t as [[[tperm tcomp] tblock] toff] eqn:et;
              simpl in *; unfold_Register_set e1 k'mem.
      * assert (g : obind (fun x : option (nat * nat) => if isSome x then Some x else None)
                          (omap value_to_data_pointer_err
                                (regs (Register.to_nat r1))) = Some (Some v)).
        {
          unfold Register.get in ptrr1.
          destruct (regs (Register.to_nat r1)); try discriminate.
          simpl. rewrite ptrr1. rewrite <- (Pointer.compose ptr). simpl.
          rewrite <- k'mem, <- cmpeq, <- blkeq, permeq.
          reflexivity.
        }
        exact g.
      * assert (g : obind (fun x : option (nat * nat) => if isSome x then Some x else None)
                          (omap value_to_data_pointer_err
                                (regs (Register.to_nat r2))) = Some (Some v)).
        {
          unfold Register.get in ptrr2.
          destruct (regs (Register.to_nat r2)); try discriminate.
          simpl. rewrite ptrr2. rewrite <- (Pointer.compose ptr). simpl.
          rewrite <- k'mem, <- cmpeq, <- blkeq, permeq. reflexivity.
        }
        exact g.
    + simpl in copied'. discriminate.
  - pose (e1' := eqP e1).
    rewrite filtermE in k'mem; simpl; simpl in k'mem; rewrite mapmE in k'mem.
    unfold_Register_set e1 k'mem.
    pose (@negPf (Some v == value_to_data_pointer_err
                              (eval_binop op
                                          (Register.get r1 regs)
                                          (Register.get r2 regs)
         ))) as n.
    assert (ineq : Some v != value_to_data_pointer_err (eval_binop op
                                          (Register.get r1 regs)
                                          (Register.get r2 regs)
           )).
    {
      apply/n. exact copied.
    }
    pose (negP ineq) as n0. exfalso. apply n0. apply/eqP.
    destruct (value_to_data_pointer_err (eval_binop op
                                               (Register.get r1 regs)
                                               (Register.get r2 regs))).
    + simpl in k'mem. apply Some_inj. symmetry. exact k'mem.
    + simpl in k'mem. discriminate.
Qed.

Lemma regs_ptrs_invalidate :
  forall regs, fsubset (regs_data_ptrs (Register.invalidate regs)) (regs_data_ptrs regs).
Proof.
  intros regs. unfold Register.invalidate. apply in_fsubset. intros v.
  unfold_regs_ptrs.
  destruct (Some v == value_to_data_pointer_err (Register.get R_COM regs)) eqn:R_COMptr;
    destruct (k' == Register.to_nat R_COM) eqn:R_COMloc;
    simpl in k'mem; simpl in R_COMloc; rewrite filtermE in k'mem; rewrite mapmE in k'mem.
  - exists k'; rewrite filtermE; simpl; rewrite mapmE.
    pose (loc := eqP R_COMloc).
    rewrite loc. rewrite loc in k'mem. simpl in k'mem.
    pose (R_COMptr' := eqP R_COMptr).
    rewrite R_COMptr' in k'mem.
    destruct (value_to_data_pointer_err (Register.get R_COM regs)) eqn:contra.
    + simpl in k'mem. rewrite R_COMptr'.
      unfold Register.get in contra. simpl in contra.
      destruct (regs 1) eqn:e.
      * rewrite e. simpl. rewrite contra. auto.
      * simpl in contra. discriminate.
    + discriminate.
  - destruct (k' == 0) eqn:k'0.
    + pose (k'0' := eqP k'0). rewrite k'0' in k'mem. simpl in k'mem. discriminate.
    + destruct (k' == 1) eqn:k'1.
      * discriminate.
      * destruct (k' == 2) eqn:k'2.
        -- pose (k'2' := eqP k'2). rewrite k'2' in k'mem. simpl in k'mem. discriminate.
        -- destruct (k' == 3) eqn:k'3.
           ++ pose (k'3' := eqP k'3). rewrite k'3' in k'mem. simpl in k'mem. discriminate.
           ++ destruct (k' == 4) eqn:k'4.
              ** pose (k'4' := eqP k'4). rewrite k'4' in k'mem. simpl in k'mem. discriminate.
              ** destruct (k' == 5) eqn:k'5.
                 --- pose (k'5' := eqP k'5). rewrite k'5' in k'mem. simpl in k'mem. discriminate.
                 --- destruct (k' == 6) eqn:k'6.
                     +++ pose (k'6' := eqP k'6). rewrite k'6' in k'mem. simpl in k'mem. discriminate.
                     +++ rewrite setmE in k'mem. rewrite k'0 in k'mem.
                         rewrite setmE in k'mem. rewrite k'1 in k'mem.
                         rewrite setmE in k'mem. rewrite k'2 in k'mem.
                         rewrite setmE in k'mem. rewrite k'3 in k'mem.
                         rewrite setmE in k'mem. rewrite k'4 in k'mem.
                         rewrite setmE in k'mem. rewrite k'5 in k'mem.
                         rewrite setmE in k'mem. rewrite k'6 in k'mem.
                         simpl in k'mem. discriminate.
  - pose (loc := eqP R_COMloc). rewrite loc in k'mem. simpl in k'mem.
    pose (@negPf (Some v == value_to_data_pointer_err (Register.get R_COM regs))) as n.
    assert (ineq : Some v != value_to_data_pointer_err (Register.get R_COM regs)).
    {
      apply/n. exact R_COMptr.
    }
    destruct (value_to_data_pointer_err (Register.get R_COM regs)) eqn:contra.
    + simpl in k'mem. apply Some_inj in k'mem. rewrite k'mem in ineq.
      assert (f : false).
      {
        apply contra_eqT with (b := false) (x := Some v) (y := Some v); auto.
      }
      exfalso. apply notF. assumption.
    + simpl in k'mem. discriminate.
  - destruct (k' == 0) eqn:k'0.
    + pose (k'0' := eqP k'0). rewrite k'0' in k'mem. simpl in k'mem. discriminate.
    + destruct (k' == 1) eqn:k'1.
      * discriminate.
      * destruct (k' == 2) eqn:k'2.
        -- pose (k'2' := eqP k'2). rewrite k'2' in k'mem. simpl in k'mem. discriminate.
        -- destruct (k' == 3) eqn:k'3.
           ++ pose (k'3' := eqP k'3). rewrite k'3' in k'mem. simpl in k'mem. discriminate.
           ++ destruct (k' == 4) eqn:k'4.
              ** pose (k'4' := eqP k'4). rewrite k'4' in k'mem. simpl in k'mem. discriminate.
              ** destruct (k' == 5) eqn:k'5.
                 --- pose (k'5' := eqP k'5). rewrite k'5' in k'mem. simpl in k'mem. discriminate.
                 --- destruct (k' == 6) eqn:k'6.
                     +++ pose (k'6' := eqP k'6). rewrite k'6' in k'mem. simpl in k'mem. discriminate.
                     +++ rewrite setmE in k'mem. rewrite k'0 in k'mem.
                         rewrite setmE in k'mem. rewrite k'1 in k'mem.
                         rewrite setmE in k'mem. rewrite k'2 in k'mem.
                         rewrite setmE in k'mem. rewrite k'3 in k'mem.
                         rewrite setmE in k'mem. rewrite k'4 in k'mem.
                         rewrite setmE in k'mem. rewrite k'5 in k'mem.
                         rewrite setmE in k'mem. rewrite k'6 in k'mem.
                         simpl in k'mem. discriminate.
Qed.

Lemma regs_ptrs_set_Int_Undef :
  forall r regs vNoPtr z,
    ((vNoPtr = Int z) \/ vNoPtr = Undef) ->
    fsubset (regs_data_ptrs (Register.set r vNoPtr regs)) (regs_data_ptrs regs).
Proof.
  intros r regs vNoPtr z HvNoPtr. apply in_fsubset. intros v.
  unfold_regs_ptrs.
  destruct (Some v == value_to_data_pointer_err vNoPtr) eqn:copied;
    destruct (k' == Register.to_nat r) eqn:e1;
    try solve_untouched_registers e1 k' k'mem.
  - pose (copied' := eqP copied); pose (e1' := eqP e1).
    destruct HvNoPtr as [H | H]; erewrite H in copied'; simpl in copied'; discriminate.
  - rewrite filtermE in k'mem. rewrite mapmE in k'mem.
    unfold_Register_set e1 k'mem.
    destruct HvNoPtr as [H | H]; erewrite H in k'mem; discriminate.
Qed.

Lemma regs_ptrs_set_Ptr :
  forall r regs vCid vBid vOff,
    fsubset (regs_data_ptrs (Register.set r (Ptr (Permission.data, vCid, vBid, vOff)) regs))
            (fsetU (regs_data_ptrs regs) (fset1 (vCid, vBid))).
Proof.
  intros r regs vCid vBid vOff. apply in_fsubset. intros v.
  intros Htmp. apply/fsetUP. move: Htmp.
  do 2 (unfold regs_data_ptrs; rewrite in_fset; rewrite seq.mem_pmap; rewrite seq.map_id).
  intros Hin; destruct (codommP _ _ Hin) as [k' k'mem].
  destruct (Some v == value_to_data_pointer_err
                        (Ptr (Permission.data, vCid, vBid, vOff))) eqn:copied;
    destruct (k' == Register.to_nat r) eqn:e1;
    try (left; apply/codommP; solve_untouched_registers e1 k' k'mem).
  - right. simpl in copied. pose (eqP copied) as cpd. inversion cpd. apply/fset1P. auto.
  - rewrite filtermE in k'mem. rewrite mapmE in k'mem. unfold_Register_set e1 k'mem.
    inversion k'mem as [H0]. rewrite <- H0 in copied. simpl in copied.
    pose (@negPf (Some v == Some v)) as negrule.
    assert (Some v != Some v) as H.
    { apply/negrule. rewrite <- H0. exact copied. }
    assert ((Some v != Some v) = false) as H1.
    { apply negbF. auto. }
    exfalso. apply notF. rewrite <- H1. exact H.
Qed.

Lemma is_program_component_pc_notin_domm s ctx :
  is_program_component s ctx ->
  Pointer.component (CS.state_pc s) \notin domm ctx.
Proof.
  now destruct s as [[[[? ?] ?] ?] ?].
Qed.

(* preparing the machine for running a program *)

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | true =>
    let '(mem, _, entrypoints) := prepare_procedures_initial_memory p in
    let regs := Register.init in
    let b := match EntryPoint.get Component.main Procedure.main entrypoints with
             | Some b => b
             | None => 0 (* This case shouldn't happen for a well-formed p *)
             end in
    ([], mem, regs, (Permission.code, Component.main, b, 0%Z), emptym)
  (* this case shoudln't happen for a well-formed p *)
  | false => ([], emptym, emptym, (Permission.code, Component.main, 0, 0%Z), emptym)
  end.

(* A slightly hacky way to express the initial pc of a linked program as a
   function of its components, subject to well-formed conditions given in the
   following theorem. *)
Definition prog_main_block (p : program) : Block.id :=
  match prog_main p with
  | true =>
    match EntryPoint.get Component.main Procedure.main (prepare_procedures_entrypoints p) with
    | Some b => b
    | None => 0
    end
  | false => 0
  end.

Lemma prog_main_block_no_main:
  forall p,
    well_formed_program p ->
    Component.main \notin domm (prog_interface p) ->
    prog_main_block p = 0.
Proof.
  intros p Hwf Hdomm.
  unfold prog_main_block. (* Enable automatic rewrite on destruct. *)
  destruct (prog_main p) as [main |] eqn:Hmain'.
  - (* https://github.com/coq/coq/issues/5129 *)
    inversion Hwf as [BUGGY _ _ _ _ _ [BUGGY' Hcontra]]; clear BUGGY BUGGY'.
    rewrite Hmain' in Hcontra. specialize (Hcontra (is_true_true)).
    rewrite Hcontra in Hdomm.
    discriminate.
  - reflexivity.
Qed.

Theorem initial_machine_state_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    closed_program (program_link p c) ->
    initial_machine_state (program_link p c) =
    ([],
     unionm (prepare_procedures_memory p)
            (prepare_procedures_memory c),
     Register.init,
     (Permission.code, Component.main,
      prog_main_block p + prog_main_block c,
      0%Z),
     emptym).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hclosed.
  unfold initial_machine_state.
  inversion Hclosed as [_ [mainpc [Hmainpc [Hprocspc Hdommpc]]]];
    rewrite Hmainpc.
  rewrite -> prepare_procedures_initial_memory_after_linking;
    try assumption;
    last now apply linkable_implies_linkable_mains.
  destruct (prog_main p) as [mainp |] eqn:Hmainp;
    destruct (prog_main c) as [mainc |] eqn:Hmainc.
  - exfalso.
    pose proof proj2 (wfprog_main_component Hwfp) as Hdommp.
    rewrite Hmainp in Hdommp. specialize (Hdommp isT).
    pose proof proj2 (wfprog_main_component Hwfc) as Hdommc.
    rewrite Hmainc in Hdommc. specialize (Hdommc isT).
    inversion Hlinkable as [_ Hdisjoint].
    eapply fdisjoint_partition_notinboth; eassumption.
  - (* RB: NOTE: As usual, the following two cases are symmetric. *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc; simpl in Hmainpc.
    unfold prog_main_block, EntryPoint.get.
    rewrite Hmainp. rewrite Hmainc. rewrite unionmE.
    pose proof proj2 (wfprog_main_component Hwfp) as Hdommp.
    rewrite Hmainp in Hdommp. specialize (Hdommp isT).
    pose proof proj1 (wfprog_main_component Hwfc) as Hdommc.
    destruct (Component.main \in domm (prog_interface c)) eqn:Hcase;
      first (specialize (Hdommc isT); now rewrite Hmainc in Hdommc).
    rewrite <- domm_prepare_procedures_entrypoints in Hdommp, Hcase.
    destruct (@dommP _ _ _ _ Hdommp) as [entrypointsp Hentrypointsp].
    do 2 setoid_rewrite Hentrypointsp.
    now rewrite Nat.add_0_r.
  - (* Deal with the symmetries upfront; because of disjointness it is also
       possible to delay that and work on the "else" branch. *)
    setoid_rewrite unionmC at 1 2 3;
      try (try rewrite 2!domm_prepare_procedures_memory;
           try rewrite 2!domm_prepare_procedures_entrypoints;
           now inversion Hlinkable).
    (* Proceed (no symmetry on the hypothesis, here). *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc; rewrite Hmainc in Hmainpc; simpl in Hmainpc.
    unfold prog_main_block, EntryPoint.get.
    rewrite Hmainp. rewrite Hmainc. rewrite unionmE.
    pose proof proj2 (wfprog_main_component Hwfc) as Hdommc.
    rewrite Hmainc in Hdommc. specialize (Hdommc isT).
    pose proof proj1 (wfprog_main_component Hwfp) as Hdommp.
    destruct (Component.main \in domm (prog_interface p)) eqn:Hcase;
      first (specialize (Hdommp isT); now rewrite Hmainp in Hdommp).
    rewrite <- domm_prepare_procedures_entrypoints in Hdommc, Hcase.
    destruct (@dommP _ _ _ _ Hdommc) as [entrypointsc Hentrypointsc].
    do 2 setoid_rewrite Hentrypointsc.
    reflexivity.
  - (* Another easy/contra goal. *)
    simpl in Hmainpc. rewrite Hmainp in Hmainpc. rewrite Hmainc in Hmainpc.
    now inversion Hmainpc.
Qed.

(* transition system *)

Definition initial_state (p: program) (ics: state) : Prop :=
  ics = initial_machine_state p.

Definition final_state (G: global_env) (s: state) : Prop :=
  let '(gsp, mem, regs, pc, addrs) := s in
  executing G pc IHalt.

(* relational specification *)

(* RB: TODO: [DynShare] Integrate reachability in states, semantics. *)
Inductive step (G : global_env) : state -> trace event -> state -> Prop :=
| Nop: forall gps mem regs pc addrs,
    executing G pc INop ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs, Pointer.inc pc, addrs)

| Label: forall gps mem regs pc l addrs,
    executing G pc (ILabel l) ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs, Pointer.inc pc, addrs)

| Const: forall gps mem regs regs' pc r v addrs,
    executing G pc (IConst v r) ->
    Register.set r (imm_to_val v) regs = regs' ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs', Pointer.inc pc, addrs)

| Mov: forall gps mem regs regs' pc r1 r2 addrs,
    executing G pc (IMov r1 r2) ->
    Register.set r2 (Register.get r1 regs) regs = regs' ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs', Pointer.inc pc, addrs)

| BinOp: forall gps mem regs regs' pc r1 r2 r3 op addrs,
    executing G pc (IBinOp op r1 r2 r3) ->
    let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
    Register.set r3 result regs = regs' ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs', Pointer.inc pc, addrs)

| Load: forall gps mem regs regs' pc r1 r2 ptr v addrs,
    executing G pc (ILoad r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    (* RB: TODO [DynShare] Clarify new restriction and substitute once given a
       computable definition.
       NOTE: Even though cross-component pointer forging is possible at the
       program level, it is detected and stopped here. *)
    Pointer.component ptr = Pointer.component pc -> (* Shared memory prohibition removed *)
    Memory.load mem ptr = Some v ->
    Register.set r2 v regs = regs' ->
    (* RB: TODO: [DynShare] Furnish computational definition. It may be preferable
       to inline the expression in the conclusion. *)
    (* compute_trace_for_load_by_component (Pointer.component pc) ptr reach = e -> *)
    step G (gps, mem, regs, pc, addrs) E0 (* e *)
           (gps, mem, regs', Pointer.inc pc, addrs)

| Store: forall gps mem mem' regs pc ptr r1 r2 addrs (* v reach' e *),
    executing G pc (IStore r1 r2) ->
    Register.get r1 regs = Ptr ptr ->
    (* RB: TODO: [DynShare] Clarify new restriction and substitute once given a
       computable definition.
       NOTE: Even though cross-component pointer forging is possible at the
       program level, it is detected and stopped here. *)
    Pointer.component ptr = Pointer.component pc ->
    (* RB: TODO: [DynShare] Uncomment refactoring below while fixing existing
       proofs. *)
    (* Register.get r2 regs = v -> *)
    Memory.store mem ptr (* v *) (Register.get r2 regs) = Some mem' ->
    (* compute_trace_for_store_by_component (Pointer.component pc) ptr reach = e -> *)
    (* propagate_store_to_all_components_reach ptr v reach = reach' -> *)
    step G (gps, mem, regs, pc, addrs) (* e *) E0
           (gps, mem', regs, Pointer.inc pc, addrs) (* reach', replace addrs *)

| Jal: forall gps mem regs regs' pc pc' l addrs,
    executing G pc (IJal l) ->
    find_label_in_component G pc l = Some pc' ->
    Register.set R_RA (Ptr (Pointer.inc pc)) regs = regs' ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs', pc', addrs)

| Jump: forall gps mem regs pc pc' r addrs,
    executing G pc (IJump r) ->
    Register.get r regs = Ptr pc' ->
    Pointer.component pc' = Pointer.component pc ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs, pc', addrs)

| BnzNZ: forall gps mem regs pc pc' r l val addrs,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int val ->
    (val <> 0) % Z ->
    find_label_in_procedure G pc l = Some pc' ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs, pc', addrs)

| BnzZ: forall gps mem regs pc r l addrs,
    executing G pc (IBnz r l) ->
    Register.get r regs = Int 0 ->
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem, regs, Pointer.inc pc, addrs)

| Alloc: forall gps mem mem' regs regs' pc rsize rptr size ptr addrs (* reach' *),
    executing G pc (IAlloc rptr rsize) ->
    Register.get rsize regs = Int size ->
    (size > 0) % Z ->
    Memory.alloc mem (Pointer.component pc) (Z.to_nat size) = Some (mem', ptr) ->
    Register.set rptr (Ptr ptr) regs = regs' ->
    (* RB: TODO: [DynShare] Restore check after making it computational. *)
    (* update_reachability_of_component_with_value (Ptr ptr) (Pointer.component pc) reach = reach' -> *)
    step G (gps, mem, regs, pc, addrs) E0
           (gps, mem', regs', Pointer.inc pc, addrs) (* reach', replace addrs *)

| Call: forall gps mem regs pc b C' P call_arg addrs (* reach' *),
    executing G pc (ICall C' P) ->
    Pointer.component pc <> C' ->
    imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
    EntryPoint.get C' P (genv_entrypoints G) = Some b ->
    (* RB: TODO: [DynShare] Re-lift restriction to integer values. *)
    Register.get R_COM regs = Int call_arg ->
    (* RB: TODO: [DynShare] Restore check after making it computational. *)
    (* update_reachability_of_component_with_value call_arg C' reach = reach' -> *)
    step G (gps, mem, regs, pc, addrs)
           [ECall (Pointer.component pc) P call_arg C']
           (Pointer.inc pc :: gps, mem, Register.invalidate regs,
            (Permission.code, C', b, 0%Z), addrs) (* reach', replace addrs *)

| Return: forall gps' mem regs pc pc' ret_arg addrs (* reach' *),
    executing G pc IReturn ->
    Pointer.component pc <> Pointer.component pc' ->
    (* RB: TODO: [DynShare] Re-lift restriction to integer values. *)
    Register.get R_COM regs = Int ret_arg ->
    (* RB: TODO: [DynShare] Restore check after making it computational. *)
    (* update_reachability_of_component_with_value ret_arg (Pointer.component pc') reach = reach' -> *)
    step G (pc' :: gps', mem, regs, pc, addrs)
           [ERet (Pointer.component pc) ret_arg (Pointer.component pc')]
           (gps', mem, Register.invalidate regs, pc', addrs) (* reach', replace addrs *).

Ltac step_of_executing :=
  match goal with
  | H : executing _ _ ?INSTR |- _ =>
    match INSTR with
    | INop           => eapply Nop
    | ILabel _       => eapply Label
    | IConst _ _     => eapply Const
    | IMov _ _       => eapply Mov
    | IBinOp _ _ _ _ => eapply BinOp
    | ILoad _ _      => eapply Load
    | IStore _ _     => eapply Store
    | IAlloc _ _     => eapply Alloc
    | IBnz _ _       =>
      match goal with
      | H : Register.get _ _ = Int 0 |- _ => eapply BnzZ
      | _                                 => eapply BnzNZ
      end
    | IJump _        => eapply Jump
    | IJal _         => eapply Jal
    | ICall _ _      => eapply Call
    | IReturn        => eapply Return
    | IHalt          => fail
    end
  end.

(* executable specification *)

Import MonadNotations.
Open Scope monad_scope.

Definition eval_step (G: global_env) (s: state) : option (trace event * state) :=
  let '(gps, mem, regs, pc, addrs) := s in
  (* fetch the next instruction to execute *)
  do C_procs <- getm (genv_procedures G) (Pointer.component pc);
  do P_code <- getm C_procs (Pointer.block pc);
  if (Pointer.offset pc <? 0) % Z then
    None
  else
    do instr <- nth_error P_code (Z.to_nat (Pointer.offset pc));
    (* decode and execute the instruction *)
    match instr with
    | ILabel l =>
      ret (E0, (gps, mem, regs, Pointer.inc pc, addrs))
    | INop =>
      ret (E0, (gps, mem, regs, Pointer.inc pc, addrs))
    | IConst v r =>
      let regs' := Register.set r (imm_to_val v) regs in
      ret (E0, (gps, mem, regs', Pointer.inc pc, addrs))
    | IMov r1 r2 =>
      let regs' := Register.set r2 (Register.get r1 regs) regs in
      ret (E0, (gps, mem, regs', Pointer.inc pc, addrs))
    | IBinOp op r1 r2 r3 =>
      let result := eval_binop op (Register.get r1 regs) (Register.get r2 regs) in
      let regs' := Register.set r3 result regs in
      ret (E0, (gps, mem, regs', Pointer.inc pc, addrs))
    | ILoad r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do v <- Memory.load mem ptr;
          let regs' := Register.set r2 v regs in
          ret (E0, (gps, mem, regs', Pointer.inc pc, addrs))
        else
          None
      | _ => None
      end
    | IStore r1 r2 =>
      match Register.get r1 regs with
      | Ptr ptr =>
        if Component.eqb (Pointer.component ptr) (Pointer.component pc) then
          do mem' <- Memory.store mem ptr (Register.get r2 regs);
          ret (E0, (gps, mem', regs, Pointer.inc pc, addrs))
        else
          None
      | _ => None
      end
    | IJal l =>
      do pc' <- find_label_in_component G pc l;
      let regs' := Register.set R_RA (Ptr (Pointer.inc pc)) regs in
      ret (E0, (gps, mem, regs', pc', addrs))
    | IJump r =>
      match Register.get r regs with
      | Ptr pc' =>
        if Component.eqb (Pointer.component pc') (Pointer.component pc) then
          ret (E0, (gps, mem, regs, pc', addrs))
        else
          None
      | _ => None
      end
    | IBnz r l =>
      match Register.get r regs with
      | Int 0 =>
        ret (E0, (gps, mem, regs, Pointer.inc pc, addrs))
      | Int val =>
        do pc' <- find_label_in_procedure G pc l;
        ret (E0, (gps, mem, regs, pc', addrs))
      | _ => None
      end
    | IAlloc rptr rsize =>
      match Register.get rsize regs with
      | Int size =>
        if (size <=? 0) % Z then
          None
        else
          do (mem', ptr) <- Memory.alloc mem (Pointer.component pc) (Z.to_nat size);
          let regs' := Register.set rptr (Ptr ptr) regs in
          ret (E0, (gps, mem', regs', Pointer.inc pc, addrs))
      | _ => None
      end
    | ICall C' P =>
      if negb (Component.eqb (Pointer.component pc) C') then
        if imported_procedure_b (genv_interface G) (Pointer.component pc) C' P then
          do b <- EntryPoint.get C' P (genv_entrypoints G);
          match Register.get R_COM regs with
          | Int rcomval =>
            let pc' := (Permission.code, C', b, 0%Z) in
            let t := [ECall (Pointer.component pc) P rcomval C'] in
            ret (t, (Pointer.inc pc :: gps, mem, Register.invalidate regs, pc', addrs))
          | _ => None
          end
        else
          None
      else
        None
    | IReturn =>
      match gps with
      | pc' :: gps' =>
        if negb (Component.eqb (Pointer.component pc) (Pointer.component pc')) then
          match Register.get R_COM regs with
          | Int rcomval =>
            let t := [ERet (Pointer.component pc) rcomval (Pointer.component pc')] in
            ret (t, (gps', mem, Register.invalidate regs, pc', addrs))
          | _ => None
          end
        else
          None
      | _ => None
      end
    | IHalt => None
    end.

Fixpoint execN (n: nat) (G: global_env) (st: state) : option Z :=
  match n with
  | O => None
  | S n' =>
    match eval_step G st with
    | None =>
      let '(_, _, regs, _, _) := st in
      match Register.get R_COM regs with
      | Int i => Some i
      | _ => None
      end
    | Some (_, st') => execN n' G st'
    end
  end.

Close Scope monad_scope.

(* equivalence between relational and executable specification *)

Theorem eval_step_complete:
  forall G st t st',
    step G st t st' -> eval_step G st = Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst;
    (* extract information about the state *)
    match goal with
    | Hexec: executing _ _ _ |- _ =>
      destruct Hexec as [procs [P_code [Hprocs [HP_code [? Hinstr]]]]]
    end;
    (* simplify *)
    simpl; unfold code in *; rewrite -> Hprocs, HP_code, Hinstr;
    (* the program counter is good *)
    match goal with
    | Hpc: (Pointer.offset _ >= 0) % Z |- _ =>
      apply Z.ge_le in Hpc; apply Z.ltb_ge in Hpc;
      rewrite Hpc
    end;
    (* solve simple cases *)
    try reflexivity.

  - match goal with
    | Hregs_update: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_update, Hsame_component, Nat.eqb_refl
    end.
    unfold Memory.load in *.
    destruct ptr as [[C' b'] o'].
    rewrite H2. reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_value, Hsame_component, Nat.eqb_refl
    end.
    unfold Memory.store in *.
    destruct ptr as [[C' b'] o'].
    rewrite H2. reflexivity.

  - match goal with
    | Hfind: find_label_in_component _ _ _ = _ |- _ =>
      rewrite Hfind
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hsame_component: Pointer.component _ = Pointer.component _ |- _ =>
      rewrite -> Hregs_value, Hsame_component, Nat.eqb_refl
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hfind: find_label_in_procedure _ _ _ = _ |- _ =>
      rewrite -> Hregs_value, Hfind
    end.
    destruct val;
      try contradiction;
      try reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite Hregs_value
    end.
    reflexivity.

  - match goal with
    | Hregs_value: Register.get _ _ = _,
      Hpositive_size: (size > 0) % Z |- _ =>
      rewrite Hregs_value;
      apply Zgt_not_le in Hpositive_size; apply Z.leb_nle in Hpositive_size;
      rewrite Hpositive_size
    end.
    unfold Memory.alloc in *.
    rewrite H2. reflexivity.

  - match goal with
    | Hentrypoint: EntryPoint.get _ _ _ = _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      rewrite -> Hentrypoint, Hregs_value
    end.
    apply Nat.eqb_neq in H0. unfold Component.eqb. rewrite H0. simpl.
    apply imported_procedure_iff in H1. rewrite H1.
    reflexivity.

  - unfold Component.eqb.
    match goal with
    | Hdifferent_target: Pointer.component _ <> Pointer.component _,
      Hregs_value: Register.get _ _ = _ |- _ =>
      apply Nat.eqb_neq in Hdifferent_target; rewrite Hdifferent_target;
      rewrite Hregs_value; simpl
    end.
    reflexivity.
Qed.

Theorem eval_step_sound:
  forall G st t st',
    eval_step G st = Some (t, st') -> step G st t st'.
Proof.
  intros G st t st' Heval_step.
  repeat unfold_states.
  destruct (getm (genv_procedures G) (Pointer.component pc0))
    as [C_procs | ] eqn:HC_procs.
  - destruct (getm C_procs (Pointer.block pc0))
      as [P_code | ] eqn:HP_code.
    + destruct ((Pointer.offset pc0 >=? 0) % Z) eqn:Hpc.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        (* case analysis on the fetched instruction *)
        ** assert ((Pointer.offset pc0 <? 0) % Z = false). {
             destruct (Pointer.offset pc0); auto.
           }
           assert ((Pointer.offset pc0 >= 0) % Z). {
             destruct (Pointer.offset pc0); discriminate.
           }
           simpl in Heval_step. unfold code in *.
           rewrite -> HC_procs, HP_code, Hinstr in Heval_step.
           destruct instr; inversion Heval_step; subst; clear Heval_step.
             (*; try (match goal with
                  | Hpcfalse: (Pointer.offset ?PC <? 0) % Z = false,
                    Heq: (if (Pointer.offset ?PC <? 0) % Z then None else Some _) = Some _
                    |- _ =>
                    rewrite Hpcfalse in Heq; inversion Heq; subst; clear Heq Hpcfalse
                  end).
              *)
           *** rewrite H in H2; inversion H2; subst; clear H2 H.
               eapply Nop.
               eexists. eexists. eauto.

           *** rewrite H in H2; inversion H2; subst; clear H2 H.
               eapply Label;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** rewrite H in H2; inversion H2; subst; clear H2 H.
               eapply Const;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** rewrite H in H2; inversion H2; subst; clear H2 H.
               eapply Mov;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** rewrite H in H2; inversion H2; subst; clear H2 H.
               eapply BinOp;
                 try reflexivity;
                 try (eexists; eexists; eauto).

           *** rewrite H in H2.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcomp;
                 try discriminate.
               unfold Memory.load in *.
               destruct (Pointer.permission t0 =? Permission.data) eqn:Hperm;
                 try discriminate.
               destruct (mem0 (Pointer.component t0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.load t1 (Pointer.block t0) (Pointer.offset t0))
                        eqn:Hload;
                 try discriminate.
               inversion H2; subst.
               eapply Load with (ptr:=t0);
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** assumption.
               **** apply Nat.eqb_eq. assumption.
               **** unfold Memory.load.
                    rewrite Hmem. rewrite Hperm. assumption.

           *** rewrite H in H2.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcomp;
                 try discriminate.
               unfold Memory.store in *.
               destruct (Pointer.permission t0 =? Permission.data) eqn:Hperm;
                 try discriminate.
               destruct (mem0 (Pointer.component t0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.store t1 (Pointer.block t0) (Pointer.offset t0)
                                               (Register.get r0 regs0))
                        eqn:Hstore;
                 try discriminate.
               inversion H2; subst.
               eapply Store with (ptr:=t0);
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** assumption.
               **** apply Nat.eqb_eq. assumption.
               **** unfold Memory.store.
                    rewrite Hmem. rewrite Hstore. rewrite Hperm. reflexivity.

           *** rewrite H in H2.
               destruct (Register.get r0 regs0) eqn:Hreg;
                 try discriminate.
               destruct ((z <=? 0) % Z) eqn:Hzpos;
                 try discriminate.
               unfold Memory.alloc in *.
               destruct (mem0 (Pointer.component pc0)) eqn:Hmem;
                 try discriminate.
               destruct (ComponentMemory.alloc t0 (Z.to_nat z)) eqn:Halloc;
                 try discriminate.
               inversion H2; subst.
               eapply Alloc;
                 try reflexivity;
                 try (eexists; eexists; eauto).
               **** eassumption.
               **** apply Z.lt_gt. apply Z.leb_gt. assumption.
               **** unfold Memory.alloc.
                    rewrite Hmem. rewrite Halloc. reflexivity.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct z eqn:Hn.
               **** inversion H2. subst.
                    eapply BnzZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H2. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ***** eexists. eexists. eauto.
                    ***** eassumption.
                    ***** intro contra. discriminate.
                    ***** assumption.
               **** destruct (find_label_in_procedure G pc0 l) eqn:Hlabel;
                      try discriminate.
                    inversion H2. subst.
                    eapply BnzNZ;
                      try reflexivity.
                    ****** eexists. eexists. eauto.
                    ****** eassumption.
                    ****** intro contra. discriminate.
                    ****** assumption.

           *** match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false,
                 Hcond: (if (Pointer.offset _ <? 0) % Z then None else _) = Some _ |- _ =>
                 rewrite Hpositive_offset in Hcond
               end.
               destruct (Register.get r regs0) eqn:Hreg;
                 try discriminate.
               destruct (Component.eqb (Pointer.component t0) (Pointer.component pc0))
                        eqn:Hcompcheck;
                 try discriminate.
               inversion H2; subst.
               eapply Jump with (pc':=pc);
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.
               **** apply Nat.eqb_eq. assumption.

           *** rewrite H in H2.
               (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
               destruct (find_label_in_component G pc0 l) eqn:Hlabel;
                 try discriminate.
               inversion H2; subst.
               eapply Jal;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** assumption.

           *** rewrite H in H2.
               (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
               destruct (Component.eqb (Pointer.component pc0) i) eqn:Hcomp;
                 try discriminate; simpl in *.
               destruct (imported_procedure_b (genv_interface G)
                                              (Pointer.component pc0) i i0)
                        eqn:Himport;
                 try discriminate.
               destruct (EntryPoint.get i i0 (genv_entrypoints G)) eqn:Hentrypoint;
                 try discriminate.
               destruct (Register.get R_COM regs0) eqn:Hreg;
                 try discriminate.
               simpl in *. inversion H2. subst.
               eapply Call;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Nat.eqb_neq. assumption.
               **** apply imported_procedure_iff. auto.
               **** assumption.
               **** assumption.

           *** rewrite H in H2.
               (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
               destruct gps0;
                 try discriminate.
               destruct (Component.eqb (Pointer.component pc0) (Pointer.component t0))
                        eqn:Hcomp;
                 try discriminate.
               simpl in *.
               destruct (Register.get R_COM regs0) eqn:Hreg;
                 try discriminate.
               inversion H2. subst.
               eapply Return;
                 try reflexivity.
               **** eexists. eexists. eauto.
               **** apply Nat.eqb_neq. assumption.
               **** assumption.

           *** rewrite H in H2.
               (*match goal with
               | Hpositive_offset: (Pointer.offset _ <? 0) % Z = false |- _ =>
                 rewrite Hpositive_offset in *
               end.*)
               discriminate.

        ** simpl in Heval_step. unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); discriminate.
      * destruct (nth_error P_code (Z.to_nat (Pointer.offset pc0)))
          as [instr | ] eqn:Hinstr.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z) eqn:Hpc';
             try discriminate.
           exfalso. unfold Z.geb in Hpc.
           destruct (Pointer.offset pc0);
             try discriminate.
        ** simpl in Heval_step.
           unfold code in *.
           rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step.
           rewrite Hinstr in Heval_step.
           destruct ((Pointer.offset pc0 <? 0) % Z); discriminate.
    + simpl in Heval_step.
      unfold code in *.
      rewrite HC_procs in Heval_step. rewrite HP_code in Heval_step. discriminate.
  - simpl in Heval_step.
    unfold code in *.
    rewrite HC_procs in Heval_step.
    discriminate.
Qed.

Theorem eval_step_correct:
  forall G st t st',
    step G st t st' <-> eval_step G st = Some (t, st').
Proof.
  split.
  - apply eval_step_complete.
  - apply eval_step_sound.
Qed.

(* complete semantics and some properties *)

Corollary step_deterministic:
  forall G st t st1 st2,
    step G st t st1 -> step G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hstep1 Hstep2.
  apply eval_step_correct in Hstep1.
  apply eval_step_correct in Hstep2.
  rewrite Hstep1 in Hstep2.
  inversion Hstep2; subst.
  reflexivity.
Qed.

Section Semantics.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem :=
    @Semantics_gen event state global_env step (initial_state p) (final_state G) G.

  Lemma determinate_step:
    forall s t1 s1 t2 s2,
      step G s t1 s1 ->
      step G s t2 s2 ->
      match_traces t1 t2 /\ (t1 = t2 -> s1 = s2).
  Proof.
    intros s t1 s21 t2 s2 Hstep1 Hstep2.
    inversion Hstep1; subst; inversion Hstep2; subst;
      (* extract information about the instruction we are executing *)
      try (match goal with
             Hexec1: executing ?G ?PC ?INSTR1,
             Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
             destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
             destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
             rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
             rewrite HP_code in HP_code'; inversion HP_code'; subst;
             rewrite Hinstr in Hinstr'; inversion Hinstr'; subst
           end);
      (* solve simple cases *)
      try (split; [ constructor |
                    intro Hsame_trace; eapply step_deterministic; eauto ]).

    (* external calls *)
    - split.
      + match goal with
        | Hcall_arg1: Register.get R_COM regs = Int ?CALL_ARG1,
          Hcall_arg2: Register.get R_COM regs = Int ?CALL_ARG2 |- _ =>
          rewrite Hcall_arg1 in Hcall_arg2; inversion Hcall_arg2; subst
        end; constructor.
      + intros Hsame_trace.
        match goal with
        | Hentrypoint1: EntryPoint.get _ _ _ = Some ?B1,
          Hentrypoint2: EntryPoint.get _ _ _ = Some ?B2 |- _ =>
          rewrite Hentrypoint1 in Hentrypoint2; inversion Hentrypoint2; subst
        end; reflexivity.

    (* external return *)
    - split.
      + match goal with
        | Hret_arg1: Register.get R_COM regs = Int ?RET_ARG1,
          Hret_arg2: Register.get R_COM regs = Int ?RET_ARG2 |- _ =>
          rewrite Hret_arg1 in Hret_arg2; inversion Hret_arg2; subst
        end; constructor.
      + intros Hsame_trace. reflexivity.
  Qed.

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; simpl; auto.
  Qed.

  Lemma determinate_initial_states:
    forall s1 s2,
      initial_state p s1 -> initial_state p s2 ->
      s1 = s2.
  Proof.
    intros s1 s2 Hs1_init Hs2_init.
    unfold initial_state in *. subst.
    reflexivity.
  Qed.

  Lemma final_states_stuckness:
    forall s,
      final_state G s ->
      nostep step G s.
  Proof.
    intros s Hs_final.
    unfold nostep.
    unfold_states.
    unfold final_state in Hs_final.
    intros t s'. unfold not. intro Hstep.
    inversion Hstep; subst;
    try (match goal with
         | Hexec1: executing ?G ?PC ?INSTR1,
           Hexec2: executing ?G' ?PC' ?INSTR2 |- _ =>
           destruct Hexec1 as [C_procs [P_code [HC_procs [HP_code [? Hinstr]]]]];
           destruct Hexec2 as [C_procs' [P_code' [HC_procs' [HP_code' [? Hinstr']]]]];
           rewrite HC_procs in HC_procs'; inversion HC_procs'; subst;
           rewrite HP_code in HP_code'; inversion HP_code'; subst;
           rewrite Hinstr in Hinstr'; inversion Hinstr'
         end).
  Qed.

  Lemma determinacy:
    determinate sem.
  Proof.
    constructor.
    - apply determinate_step.
    - apply singleton_traces.
    - apply determinate_initial_states.
    - apply final_states_stuckness.
  Qed.

  Lemma program_behaves_inv:
    forall b,
      program_behaves sem b ->
    exists s,
      initial_state p s /\ state_behaves sem s b.
  Proof.
    intros b [s b' Hini Hbeh | Hini]; subst.
    - now exists s.
    - simpl in Hini.
      specialize (Hini (initial_machine_state p)).
      unfold initial_state in Hini.
      contradiction.
  Qed.

Import ssreflect eqtype.

Definition stack_state_of (cs:CS.state) : stack_state :=
  let '(gps, mem, regs, pc, addrs) := cs in
  StackState (Pointer.component pc) (List.map Pointer.component gps).

Lemma intermediate_well_bracketed_trace t cs cs' :
  Star sem cs t cs' ->
  well_bracketed_trace (stack_state_of cs) t.
Proof.
elim: cs t cs' / => [|cs1 t1 cs2 t2 cs3 t Hstep _ IH ->] //=.
case: cs1 t1 cs2 / Hstep IH => /=;
try by move=> *; match goal with
| [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
        rewrite Pointer.inc_preserves_component in H end.
- by move=> ????????? /find_label_in_component_1 ->.
- by move=> ????????? ->.
- by move=> ???????????? /find_label_in_procedure_1 ->.
- by move=> ????????????; rewrite eqxx Pointer.inc_preserves_component.
- by move=> ??????????; rewrite !eqxx.
Qed.

Canonical ssrnat.nat_eqType.

Lemma intermediate_well_formed_events st t st' :
  Star sem st t st' ->
  seq.all (well_formed_event (Intermediate.prog_interface p)) t.
Proof.
elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
rewrite seq.all_cat IH andbT {Hstar}.
case: st1 t1 st2 / Hstep => //=.
- move=> ?????????? /eqP ->.
  by move=> /imported_procedure_iff /= ->.
- by move=> ???????? /eqP ->.
Qed.

Lemma intermediate_well_formed_trace : forall t cs cs',
  Star sem cs t cs' ->
  CS.initial_state p cs ->
  Intermediate.prog_main p ->
  Intermediate.well_formed_program p ->
  well_formed_trace (Intermediate.prog_interface p) t.
Proof.
  intros t cs cs' H H' H'' H'''.
  unfold well_formed_trace. apply/andP; split; last by apply: intermediate_well_formed_events H.
  apply intermediate_well_bracketed_trace in H.
  suffices <- : stack_state_of cs = stack_state0 by [].
  rewrite /initial_state /initial_machine_state in H'.
  by rewrite H' H''.
Qed.

End Semantics.

(* RB: TODO: Use SSR imports consistently (we use SSR exclusively for the next
   lemma). *)
Import ssreflect.
Remark step_preserves_mem_domm G s t s' :
  CS.step G s t s' ->
  domm (state_mem s) = domm (state_mem s').
Proof.
  intros Hstep.
  inversion Hstep; subst;
    try reflexivity. (* Most operations do not modify the memory. *)
  - (* Preservation by Memory.store. *)
    match goal with
    | Hstore : Memory.store _ ?PTR (Register.get ?REG ?REGS) = _ |- _ =>
      unfold Memory.store in Hstore;
        destruct (Pointer.permission PTR =? Permission.data) eqn:Hperm;
        [| discriminate];
        destruct (mem (Pointer.component PTR)) as [memC |] eqn:Hcase1;
        [| discriminate];
        destruct (ComponentMemory.store
                    memC (Pointer.block PTR) (Pointer.offset PTR) (Register.get REG REGS))
          as [memC' |] eqn:Hcase2;
        [| discriminate];
        inversion Hstore as [Hsetm];
        simpl; rewrite domm_set fsetU1in;
          [reflexivity |];
          apply /dommP; now eauto
    end.
  - (* Preservation by Memory.alloc. *)
    match goal with
    | Halloc : Memory.alloc _ _ _ = _ |- _ =>
      unfold Memory.alloc in Halloc;
      destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase;
        [| discriminate];
      destruct (ComponentMemory.alloc memC (Z.to_nat size)) as [memC' b];
      inversion Halloc; subst; simpl;
      rewrite domm_set fsetU1in; [reflexivity |];
      apply /dommP; now eauto
    end.
Qed.

Definition comes_from_initial_state (s: state) (iface : Program.interface) : Prop :=
  exists p s0 t,
    well_formed_program p /\
    prog_main p /\
    prog_interface p = iface /\
    initial_state p s0 /\
    Star (sem p) s0 t s.

Remark comes_from_initial_state_mem_domm s ctx :
  comes_from_initial_state s ctx ->
  domm (state_mem s) = domm ctx.
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hiface [Hini Hstar]]]]]]].
  apply star_iff_starR in Hstar.
  revert ctx Hwf Hmain Hiface Hini.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros ctx Hwf Hmain Hiface Hini.
  - unfold initial_state, initial_machine_state in Hini; subst s.
    rewrite Hmain. simpl.
    rewrite domm_map domm_prepare_procedures_initial_memory_aux. congruence.
  - specialize (IHHstar _ Hwf Hmain Hiface Hini).
    apply step_preserves_mem_domm in Hstep23. congruence.
Qed.

Lemma comes_from_initial_state_stack_domm s ctx :
  comes_from_initial_state s ctx ->
  All (fun frame => Pointer.component frame \in domm ctx) (state_stack s).
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hiface [Hini Hstar]]]]]]].
  apply star_iff_starR in Hstar.
  revert ctx Hwf Hmain Hiface Hini.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros ctx Hwf Hmain Hiface Hini.
  - unfold initial_state, initial_machine_state in Hini; subst s.
    now rewrite Hmain.
  - specialize (IHHstar _ Hwf Hmain Hiface Hini).
    (* Case analysis on the step. Most operations do not modify the stack, and
       returns only pop. *)
    inversion Hstep23; subst;
      simpl in *;
      try easy.
    (* The only semi-interesting cases is the call instruction. *)
    split; [| assumption].
    rewrite Pointer.inc_preserves_component.
    match goal with
    | Himp : imported_procedure _ _ _ _ |- _ =>
      destruct Himp as [CI [Hhas_comp Himp]];
      exact (has_component_in_domm_prog_interface Hhas_comp)
    end.
Qed.

(* RB: TODO: This result admits more general formulations (see above).
   Replace this with those whenever convenient, including the "bootstrapping"
   on the stack in the result for the domain of the PC, just below. *)
Corollary comes_from_initial_state_stack_cons_domm frame gps mem regs pc addrs iface :
  comes_from_initial_state (frame :: gps, mem, regs, pc, addrs) iface ->
  Pointer.component frame \in domm iface.
Proof.
  intros Hcomes_from.
  apply comes_from_initial_state_stack_domm in Hcomes_from.
  now simpl in Hcomes_from.
Qed.

Lemma comes_from_initial_state_pc_domm s ctx :
  comes_from_initial_state s ctx ->
  Pointer.component (state_pc s) \in domm ctx.
Proof.
  intros [p [s0 [t [Hwf [Hmain [Hctx [Hinitial Hstar]]]]]]].
  revert Hwf Hmain Hctx Hinitial.
  apply star_iff_starR in Hstar.
  induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
    subst;
    intros Hwf Hmain Hctx Hinitial.
  - unfold initial_state, initial_machine_state in Hinitial; subst.
    rewrite Hmain.
    apply (wfprog_main_component Hwf). now rewrite Hmain.
  - specialize (IHHstar Hwf Hmain Hctx Hinitial).
    inversion Hstep23; subst; simpl;
      match goal with
      | Hlabel : find_label_in_component _ _ _ = _
        |- _=>
        now rewrite <- (find_label_in_component_1 _ _ _ _ Hlabel)
      | Hlabel : find_label_in_procedure _ _ _ = _
        |- _=>
        now rewrite <- (find_label_in_procedure_1 _ _ _ _ Hlabel)
      | Heq : Pointer.component _ = Pointer.component _
        |- _ =>
        now rewrite -> Heq
      | Hentry : EntryPoint.get _ _ _ = _
        |- _ =>
        change (genv_entrypoints _)
          with (genv_entrypoints (prepare_global_env p))
          in Hentry;
        pose proof EntryPoint.get_some Hentry as Hdomm;
        now rewrite domm_genv_entrypoints in Hdomm
      | Hop : executing _ _ IReturn
        |- _ =>
        eapply comes_from_initial_state_stack_cons_domm;
        unfold comes_from_initial_state;
        apply star_iff_starR in Hstar12;
        now eauto 9
      | |- _ =>
        now rewrite -> Pointer.inc_preserves_component
      end.
Qed.

Lemma silent_step_preserves_component G s s' :
  CS.step G s E0 s' ->
  Pointer.component (state_pc s) = Pointer.component (state_pc s').
Proof.
  intros Hstep.
  inversion Hstep; subst; simpl;
    try now rewrite Pointer.inc_preserves_component.
  - erewrite find_label_in_component_1; try eassumption. reflexivity.
  - congruence.
  - erewrite find_label_in_procedure_1; try eassumption. reflexivity.
Qed.

Lemma silent_step_preserves_program_component : forall s1 s2 G ctx,
  CS.is_program_component s1 ctx ->
  CS.step G s1 E0 s2 ->
  CS.is_program_component s2 ctx.
Proof.
  intros [[[[? ?] ?] pc1] ?] [[[[? ?] ?] pc2] ?] G ctx Hcomp1 Hstep12.
  pose proof CS.silent_step_preserves_component _ _ _ Hstep12 as Heq.
  simplify_turn. now rewrite <- Heq.
Qed.

(* RB: TODO: Remove reliance on auto-names. Also note that this follows from
   silent_step_preserves_program_component, posed below. *)
Lemma epsilon_star_preserves_program_component p c s1 s2 :
  CS.is_program_component s1 (prog_interface c) ->
  Star (CS.sem (program_link p c)) s1 E0 s2 ->
  CS.is_program_component s2 (prog_interface c).
Proof.
  intros Hprg_component Hstar.
  remember E0 as t.
  induction Hstar.
  - assumption.
  - subst; assert (t1 = E0) by now induction t1.
    assert (t2 = E0) by now induction t1. subst.
    apply IHHstar; try assumption.
    clear H0 IHHstar Hstar.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in *.
    inversion H;
      try (match goal with
           | Heq : (_, _, _, _) = s1 |- _ => rewrite -Heq in Hprg_component
           end);
      try now rewrite Pointer.inc_preserves_component.
    + erewrite <- find_label_in_component_1; eassumption.
    + now rewrite H2.
    + erewrite <- find_label_in_procedure_1; eassumption.
Qed.

(* RB: Could be phrased in terms of does_prefix. *)
Theorem behavior_prefix_star {p b m} :
  program_behaves (CS.sem p) b ->
  prefix m b ->
exists s1 s2,
  CS.initial_state p s1 /\
  Star (CS.sem p) s1 (finpref_trace m) s2.
Proof.
  destruct m as [tm | tm | tm].
  - intros Hb Hm.
    destruct b as [t | ? | ? | ?];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh |]; subst.
    inversion Hbeh as [? s2 Hstar Hfinal | | |]; subst.
    eexists; eexists; split; now eauto.
  - intros Hb Hm.
    destruct b as [? | ? | ? | t];
      simpl in Hm; try contradiction;
      subst t.
    inversion Hb as [s1 ? Hini Hbeh | Hini]; subst.
    + inversion Hbeh as [| | | ? s2 Hstar Hnostep Hfinal]; subst.
      eexists; eexists; split; now eauto.
    + specialize (Hini (CS.initial_machine_state p)).
      congruence.
  - revert b.
    induction tm as [| e t IHt] using rev_ind;
      intros b Hb Hm;
      simpl in *.
    + exists (CS.initial_machine_state p), (CS.initial_machine_state p).
      split; [congruence | now apply star_refl].
    + pose proof behavior_prefix_app_inv Hm as Hprefix.
      specialize (IHt _ Hb Hprefix).
      destruct IHt as [s1 [s2 [Hini Hstar]]].
      inversion Hm as [b']; subst.
      inversion Hb as [s1' ? Hini' Hbeh' | Hini' Hbeh']; subst.
      * assert (Heq : s1 = s1')
          by now (inversion Hini; inversion Hini').
        subst s1'.
        inversion Hbeh' as [ t' s2' Hstar' Hfinal' Heq
                           | t' s2' Hstar' Hsilent' Heq
                           | T' Hreact' Heq
                           | t' s2' Hstar' Hstep' Hfinal' Heq];
          subst.
        (* RB: TODO: Refactor block. *)
        -- destruct b' as [tb' | ? | ? | ?];
             simpl in Heq;
             try discriminate.
           inversion Heq; subst t'; clear Heq.
           destruct (star_app_inv (CS.singleton_traces p) _ _ Hstar')
             as [s' [Hstar'1 Hstar'2]].
           now eauto.
        -- (* Same as Terminates case. *)
          destruct b' as [? | tb' | ? | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
        -- (* Similar to Terminates and Diverges, but on an infinite trace.
              Ltac can easily take care of these commonalities. *)
          destruct b' as [? | ? | Tb' | ?];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst T'; clear Heq.
          destruct (forever_reactive_app_inv (CS.singleton_traces p) _ _ Hreact')
            as [s' [Hstar'1 Hreact'2]].
          now eauto.
        -- (* Same as Terminate and Diverges. *)
          destruct b' as [? | ? | ? | tb'];
            simpl in Heq;
            try discriminate.
          inversion Heq; subst t'; clear Heq.
          destruct (star_app_inv (CS.singleton_traces p) _ _ Hstar')
            as [s' [Hstar'1 Hstar'2]].
          now eauto.
      * specialize (Hini' (CS.initial_machine_state p)).
        congruence.
Qed.

(* RB: TODO: These domain lemmas should now be renamed to reflect their
   operation on linked programs. *)
Section ProgramLink.
  Variables p c : program.
  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).
  Hypothesis Hprog_is_closed  : closed_program (program_link p c).

  (* RB: NOTE: Check with existing results.
     Possibly rewrite in terms of state_pc. *)
  Lemma star_pc_domm : forall {s st mem reg pc addrs t},
    initial_state (program_link p c) s ->
    Star (sem (program_link p c)) s t (st, mem, reg, pc, addrs) ->
    Pointer.component pc \in domm (prog_interface p) \/
    Pointer.component pc \in domm (prog_interface c).
  Proof.
    intros s st mem reg pc addrs t Hini Hstar.
    assert (H : Pointer.component pc \in domm (prog_interface (program_link p c))).
    { replace pc with (CS.state_pc (st, mem, reg, pc, addrs)); try reflexivity.
      apply CS.comes_from_initial_state_pc_domm.
      destruct (cprog_main_existence Hprog_is_closed) as [_ [? _]].
      exists (program_link p c), s, t.
      split; first (destruct Hmergeable_ifaces; now apply linking_well_formedness).
      repeat split; eauto. }
    move: H. simpl. rewrite domm_union. now apply /fsetUP.
  Qed.
End ProgramLink.


(* [DynShare] *)
(*
SearchAbout prepare_procedures_initial_memory_aux.
Check prepare_procedures_initial_memory_aux.
SearchAbout prog_procedures.
SearchAbout program.
Check mem_domm.
Check getm.
SearchAbout getm.
*)
Lemma genv_procedures_prog_procedures_in p cid fid instlst :
  well_formed_program p ->
  (omap (fun m => getm m fid)
        ((genv_procedures (globalenv (sem p))) cid) = Some (Some instlst)
   <->
   omap (fun m => getm m fid) ((prog_procedures p) cid) = Some (Some instlst)).
Proof.
  intros Hwfp.
  pose (domm_domm := wfprog_defined_procedures Hwfp).
  pose (domm_domm1 := domm_prepare_procedures_initial_memory_aux p).
  unfold sem. simpl. rewrite mapmE. rewrite mkfmapfE. simpl.
  destruct (cid \in domm (prog_interface p)) eqn:e; rewrite e; erewrite domm_domm in e;
    simpl; pose (mem_domm (prog_procedures p) cid) as e1; erewrite e1 in e;
      unfold isSome in e1;
      destruct (@getm nat_ordType
                      (NMap code)
                      (*(Phant (forall _ : Ord.sort nat_ordType, NMap code))*) _
                      (prog_procedures p)
                      cid) eqn:contra.
  (* unable to use the destruct equation due to type inference problems. *)
        (*erewrite contra in e1. try discriminate; split; auto; clear e1;
          unfold reserve_component_blocks; intros H.*)

  (*
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose (dommP (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0]; rewrite e1 in H0; discriminate).
    destruct (ComponentMemoryExtra.reserve_blocks
         (ComponentMemory.prealloc (odflt emptym ((prog_buffers p) cid)))
         (length (elementsm (odflt emptym (Some n)))))
             as [compMem bs] eqn:rsvblk.
    rewrite rsvblk in H.
    simpl in H. rewrite <- H.
   *)
Admitted.
Lemma genv_procedures_prog_procedures p cid proc :
  well_formed_program p ->
  (genv_procedures (globalenv (sem p))) cid = proc <-> (prog_procedures p) cid = proc.
Proof.
  intros Hwfp.
  pose (domm_domm := wfprog_defined_procedures Hwfp).
  pose (domm_domm1 := domm_prepare_procedures_initial_memory_aux p).
  unfold sem. simpl. rewrite mapmE. rewrite mkfmapfE. simpl.
  destruct (cid \in domm (prog_interface p)) eqn:e; rewrite e; erewrite domm_domm in e;
    simpl; pose (mem_domm (prog_procedures p) cid) as e1; erewrite e in e1;
      unfold isSome in e1; destruct ((prog_procedures p) cid) eqn:contra; auto;
        rewrite contra in e1; try discriminate; split; auto; clear e1;
          unfold reserve_component_blocks; intros H.
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose (dommP (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0]; rewrite e1 in H0; discriminate).
    destruct (ComponentMemoryExtra.reserve_blocks
         (ComponentMemory.prealloc (odflt emptym ((prog_buffers p) cid)))
         (length (elementsm (odflt emptym (Some n)))))
             as [compMem bs] eqn:rsvblk.
    rewrite rsvblk in H.
    simpl in H. rewrite <- H.
    assert (g: n = mkfmap (T:=nat_ordType) (seq.zip bs (seq.unzip2 (elementsm n)))).
    {
      (* This goal is hard.
         n is a map. So, it is better if the lemma were stated in terms of
       equality of the contents rather than just equality.*)
      admit.
    }
    rewrite <- g. auto.
  - assert (etmp : is_true (cid \in domm (prog_interface p))).
    { erewrite domm_domm; rewrite e; auto. }
    pose (dommP (prog_interface p) cid etmp) as e0.
    destruct ((prog_interface p) cid) eqn:e1;
      try (destruct e0 as [x H0]; rewrite e1 in H0; discriminate).

Admitted.

Lemma are_all_ptrs_in_reachable_star_step p st t st' :
  Star (sem p) st t st' ->
  well_formed_program p ->
  are_all_ptrs_in_reachable st p ->
  are_all_ptrs_in_reachable st' p.
Proof.
  unfold are_all_ptrs_in_reachable, state_mem, state_data_ptrs.
  intros Hstar Hwellformed.
  do 2 rewrite fsubUset.
  induction Hstar; auto.
  unfold_state s1. unfold_state s2. unfold_state s3.
  intros H_s_ptrs. destruct (andP H_s_ptrs) as [Hsptrs_regs Hsptrs_mem].
  inversion H; subst; auto; apply IHHstar; clear IHHstar;
    (* extract information about the state *)
    match goal with
    | Hexec: executing _ _ _ |- _ =>
      destruct Hexec as [procs [P_code [Hprocs [HP_code [? Hinstr]]]]]
    end;
    apply/andP; split; auto.
  - (* Use Hwellformed, Hprocs, HP_code and Hinstr *)
    (* TODO: Replace genv_procedures_prog_procedures with the \in version of it *)
    destruct (genv_procedures_prog_procedures p
                                          (Pointer.component pc)
                                          (Some procs)
                                          Hwellformed
             ) as [Hprocsif _].
    inversion Hwellformed.
    pose (wfprog_well_formed_instructions0
            (Pointer.component pc) procs (Hprocsif Hprocs) (Pointer.block pc) P_code HP_code
            (IConst v r)
         ) as Hwfi.
    pose (Hwfi (nth_error_In P_code (Z.to_nat (Pointer.offset pc)) Hinstr)) as Hwfi'.
    unfold well_formed_instruction in Hwfi'.
    destruct v as [vInt | vPtr].
    + simpl.
      apply (@fsubset_trans _
                            (regs_data_ptrs regs)
                            (regs_data_ptrs (Register.set r (Int vInt) regs))
                            (\bigcup_(i <- program_ptrs p)
                              fset (reachable_nodes_nat mem0 i)
                            )%fset
            ).
      * apply regs_ptrs_set_Int_Undef with (z := vInt). left. trivial.
      * assumption.
    + simpl.
      assert (vPtrgood: forall cid bid,
                 value_to_data_pointer_err (Ptr vPtr) = Some (cid, bid) ->
                 (cid, bid) \in (program_ptrs p)).
      {
        intros cid bid HvPtrSome. destruct vPtr as [[[permv cidv] bidv]?]. simpl in HvPtrSome.
        destruct (permv =? Permission.data) eqn:epermv; try discriminate.
        inversion HvPtrSome. subst cid bid.
        simpl in Hwfi'.
        destruct Hwfi' as [_ [bufs [Hprog_buffers Hbidv]]].
        unfold program_ptrs.
        rewrite mem_domm. rewrite uncurrymE. simpl.
        rewrite Hprog_buffers. simpl. rewrite <- mem_domm.
        rewrite <- In_in with (s := (seq.map fst bufs)) in Hbidv.
        unfold domm. unfold seq.unzip1. rewrite in_fset. exact Hbidv.
      }
      destruct vPtr as [[[vPtrp vPtrc] vPtrb] vPtro].
      pose (regs_ptrs_set_Ptr r regs vPtrc vPtrb vPtro) as l.
      assert (rtrans:  (fsubset (regs_data_ptrs regs
                                      :|:
                                      fset1
                                      (T:=prod_ordType nat_ordType nat_ordType)
                                      (vPtrc, vPtrb))
                           (\bigcup_(i <- program_ptrs p)
                                     fset (reachable_nodes_nat mem0 i))%fset
                       )%fset).
      {
        rewrite fsubUset. apply/andP. split; auto.
        rewrite fsub1set.
        apply/bigcupP. simpl.
        assert (vPtr_program_ptrs: (vPtrc, vPtrb) \in program_ptrs p).
        {
          admit. (* This proof broke after adding the permissions field. *)
          (*apply vPtrgood.
          destruct (vPtrp =? Permission.data) eqn:evPtrp; try discriminate.
          auto.*)
        }
        apply BigCupSpec with (i := (vPtrc, vPtrb)); auto.
        destruct (reachable_nodes_nat_expansive (vPtrc, vPtrb) mem0) as [x [x_in xeq]].
        rewrite xeq in x_in. rewrite in_fset. exact x_in.
      }
      apply (@fsubset_trans _ (regs_data_ptrs regs
                                              :|:
                                              fset1
                                              (T:=prod_ordType nat_ordType nat_ordType)
                                              (vPtrc, vPtrb))%fset _ _); auto.
      admit. (* This proof broke after adding the permissions field. *)
      
  - apply (@fsubset_trans _
                          (regs_data_ptrs regs)
                          (regs_data_ptrs (Register.set r2 (Register.get r1 regs) regs))
                          (\bigcup_(i <- program_ptrs p)
                            fset (reachable_nodes_nat mem0 i)
                          )%fset
          ).
    + apply regs_ptrs_set_get.
    + assumption.
  - apply (@fsubset_trans _
                          (regs_data_ptrs regs)
                          (regs_data_ptrs (Register.set r3 result regs))
                          (\bigcup_(i <- program_ptrs p)
                            fset (reachable_nodes_nat mem0 i)
                          )%fset
          ).
    + apply regs_ptrs_binop.
    + assumption.
  - destruct ptr as [[[ptrP ptrC] ptrB] ptrO].
    assert (addrInreach : (ptrC, ptrB) \in
               (\bigcup_(i <- program_ptrs p) fset (reachable_nodes_nat mem0 i))%fset).
    {
      apply fsubset_in with (s1 := regs_data_ptrs regs).
      + assumption.
      + apply Register_get_regs_ptrs with (r1 := r1) (ptrO := ptrO).
        assert (Pointer.permission (ptrP, ptrC, ptrB, ptrO) = Permission.data) as eptrP.
        { apply Memory.load_some_permission with (mem := mem0) (v := v). assumption. }
        simpl in eptrP. rewrite eptrP in H13.
        assumption.
    }
    destruct v as [z | [[[vP vC] vB] vO] |] eqn:ve.
    + apply (@fsubset_trans _
                            (regs_data_ptrs regs)
                            (regs_data_ptrs (Register.set r2 (Int z) regs))
                            (\bigcup_(i <- program_ptrs p)
                              fset (reachable_nodes_nat mem0 i)
                            )%fset
            ).
      -- apply regs_ptrs_set_Int_Undef with (z := z). auto.
      -- assumption.
    + pose (regs_ptrs_set_Ptr r2 regs vC vB vO) as l.
      apply (@fsubset_trans _
                            (regs_data_ptrs regs
                                       :|: fset1
                                       (T:=prod_ordType nat_ordType nat_ordType)
                                       (vC, vB))%fset _ _).
      * admit. 
        (* auto *) (* This broke after introducing the permissions field. *)
      * rewrite fsubUset. apply/andP; split; auto.
        apply (@fsubset_trans _
                              (mem_data_ptrs (state_mem (gps0, mem0, regs, pc, addrs0))) _ _).
        -- simpl. rewrite fsub1set.
           apply Memory_load_mem_ptrs with
               (aP := ptrP) (aC := ptrC) (aB := ptrB) (aO := ptrO) (vO := vO). auto.
    (* Should follow from H15 after proving that vP is Permission.data *)
           admit.
        -- (* This broke after introducing the permissions field. *)
          admit.
    + apply (@fsubset_trans _
                            (regs_data_ptrs regs)
                            (regs_data_ptrs (Register.set r2 Undef regs))
                            (\bigcup_(i <- program_ptrs p)
                              fset (reachable_nodes_nat mem0 i)
                            )%fset
            ).
      * apply regs_ptrs_set_Int_Undef with (z := 0%Z). auto.
      * assumption.
  - simpl.
    (* store*) (* The goal here is actually false. The store may destroy pointer values
                that used to exist in the old memory mem, rendering mem0 free of
                pointers, and thus rendering the set "regs_ptrs regs0" bigger than
                the reachability set that starts from the program buffers. *)
    admit.
  - simpl.
    (* store*) (* The goal here is also false. In particular, if the stored value clears
                a pointer, and hence leads to two islands that are not connected.
                One island, for example, would contain all pointers to the static buffers,
                and another island would still contain some more (dynamically-allocated)
                pointers that were (before the disconnection) reachable by the static
                buffers. *)
    admit.
  - (* IJal*) admit. (* Need an invariant about pc that ensures that pc does not point to
              any component memory? But moreover, probably need to change the definition
              of regs_ptrs and mem_ptrs to exclude code pointers?? *)
  - (* IAlloc *) admit. (* Need to weaken the lemma. In particular, need to allow the reachable
              pointers to include also allocations.. Not sure yet what is the right way
              to specify this. The right way to specify it depends on how we want to
              use this lemma.*)
  - (* IAlloc *) admit. (* Same as above *)
  - apply (@fsubset_trans _
                          (regs_data_ptrs regs)
                          (regs_data_ptrs (Register.invalidate regs))
                          (\bigcup_(i <- program_ptrs p)
                            fset (reachable_nodes_nat mem0 i)
                          )%fset);
      auto; apply regs_ptrs_invalidate.
  - apply (@fsubset_trans _
                          (regs_data_ptrs regs)
                          (regs_data_ptrs (Register.invalidate regs))
                          (\bigcup_(i <- program_ptrs p)
                            fset (reachable_nodes_nat mem0 i)
                          )%fset);
      auto; apply regs_ptrs_invalidate.
Abort.

Definition reachable_from_component_static_buffers
           (ptr: Component.id * Block.id)
           (mem_st: Memory.t)
           (p: program) (c: Component.id) :=
  ptr \in (\bigcup_(i <- component_ptrs p c) fset (reachable_nodes_nat mem_st i))%fset.

Definition reachable_from_reg_file
           (ptr: Component.id * Block.id)
           (mem_st: Memory.t)
           (regs: Register.t) :=
  ptr \in (\bigcup_(i <- regs_data_ptrs regs) fset (reachable_nodes_nat mem_st i))%fset.

End CS.

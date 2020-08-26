Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.Reachability.
Require Import CompCert.Events.

Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrnat eqtype path ssrfun seq fingraph fintype.

Section Renaming.

Definition addr_t : Type := (Component.id * Block.id).
  (* It seems only Block.id will need to be renamed *)
Variable sigma: {fmap addr_t -> addr_t}.
Hypothesis sigma_injective: injective sigma.

Definition inverse_sigma (addr: addr_t) : addr_t :=
  let dom_sigma := domm sigma in
  if has (fun y => sigma y == Some addr) dom_sigma
  then nth (0,0) dom_sigma (find (fun y => sigma y == Some addr) dom_sigma)
  else addr.

Definition rename_addr (addr: addr_t) : addr_t :=
  match sigma addr with
  | Some addr' => addr'
  | None => addr
  end.

Definition inverse_rename_addr (addr: addr_t) := inverse_sigma addr.

Definition rename_value_template (rnm_addr : addr_t -> addr_t) (v: value) : value :=
  match v with
  | Ptr (perm, cid, bid, off) =>
    let (cid', bid') := rnm_addr (cid, bid) in
    Ptr (perm, cid', bid', off)
  | _ => v
  end.

Definition rename_value (v: value) : value := rename_value_template rename_addr v.
              
Definition inverse_rename_value (v: value) : value :=
  rename_value_template inverse_rename_addr v.

Definition rename_list_values (s: list value) : list value := map rename_value s.

Definition inverse_rename_list_values (s: list value) : list value :=
  map inverse_rename_value s.

Lemma inverse_rename_addr_left_inverse addr:
  addr \in domm sigma -> (*Is this precondition ok?*)
  inverse_rename_addr (rename_addr addr) = addr.
  (* This lemma 
     without the precondition "addr \in domm sigma"
     is not really provable because the rename_addr function can actually cause
     two addresses addr1 and addr2 to clash at some addr' when still sigma itself is injective.

    This lemma only holds for "addr \in domm sigma".

    However, under the "addr \in domm sigma" precondition,
    it is not very clear whether the lemma will be usable.
    It will be comfortably usable when we have a "complete" sigma, i.e., when
    we only call rename_addr on some addr \in sigma.
   *)
Proof.
  intros Haddr.
  unfold inverse_rename_addr, inverse_sigma. simpl.
  unfold rename_addr.
  destruct (sigma addr) as [addr'|] eqn:e_sigma_addr.
  - destruct (has (fun y => sigma y == Some addr') (domm sigma)) eqn:e_has; rewrite e_has.
    + pose proof (nth_find (0,0) e_has) as Hnth. simpl in Hnth.
      apply/inj_eqAxiom.
      * exact sigma_injective.
      * rewrite e_sigma_addr. exact Hnth.
    + pose proof (mem_domm sigma addr) as Hin_domm.
      pose proof (@hasP _ (fun y => sigma y == Some addr') (domm sigma)) as H.
      rewrite e_has in H.
      apply elimF in H; auto.
      assert (exists2 x, x \in domm sigma & sigma x == Some addr') as contra.
      {
        eexists addr.
        * rewrite mem_domm e_sigma_addr. auto.
        * rewrite e_sigma_addr. auto.
      }
      apply H in contra. exfalso. assumption.
  - rewrite mem_domm in Haddr. rewrite e_sigma_addr in Haddr. easy.
Qed.

Lemma inverse_rename_addr_right_inverse addr_pre addr:
  sigma addr_pre = Some addr ->
  rename_addr (inverse_rename_addr addr) = addr.
Proof.
  intros Haddr.
  unfold inverse_rename_addr, inverse_sigma. simpl. unfold rename_addr.
  destruct (has (fun y : nat * nat => sigma y == Some addr) (domm sigma)) eqn:e_has.
  - pose proof (nth_find (0,0) e_has) as H. simpl in H.
    pose proof (@eqP _ _ _ H) as H'. rewrite H'. reflexivity.
  - pose proof (@hasP _ (fun y => sigma y == Some addr) (domm sigma)) as H.
    rewrite e_has in H. apply elimF in H; auto.
    assert (exists2 x, x \in domm sigma & sigma x == Some addr) as contra.
    {
      eexists addr_pre.
      + rewrite mem_domm Haddr. auto.
      + rewrite Haddr. auto.
    }
    apply H in contra. exfalso. assumption.
Qed.  

(*Check Reachable.
Inductive shared_so_far : addr_t -> trace event -> Prop :=
| shared_by_call: forall cid bid t c1 p1 c2 o,
    Reachable ... ->
    shared_so_far (cid, bid) (rcons t ((ECall c1 p1 (Ptr (Permission.data, cid, bid, o)) c2))).
*)
Definition rename_memory_content_at_addr (m: Memory.t) (addr: Component.id * Block.id)
  : Memory.t :=
  match omap rename_list_values (Memory.load_all m addr) with
  | Some vs => match Memory.store_all m addr vs with
               | Some m' => m'
               | None => m
               end
  | None => m
  end.

Fixpoint rename_memory_content_at_addrs (m: Memory.t) (addrs: list (Component.id * Block.id))
  : Memory.t :=
  match addrs with
  | nil => m
  | cb :: cbs => rename_memory_content_at_addrs (rename_memory_content_at_addr m cb) cbs
  end.

Definition rename_memory_addrs (m: Memory.t) (addrs: list (Component.id * Block.id))
  : Memory.t :=
  Memory.transfer_memory_blocks m addrs m (map rename_addr addrs).

Definition rename_memory_subgraph (m: Memory.t) (addrs: list (Component.id * Block.id))
  : Memory.t :=
  rename_memory_content_at_addrs (rename_memory_addrs m addrs) (map rename_addr addrs).

(* [DynShare]: TODO:
   Is this lemma needed?
   This lemma may be a bit too tedious to prove.

   Alternatively, I will experiment with representing the trace renaming
   as a Prop. Such a Trace_Renames_Trace Prop 
   will use the definitions of the following Prop's:
   * Mem_Renames_Mem
   * Addr_shared_so_far, which itself will use the definition of
   * Reachable
*)
Lemma reachable_nodes_nat_rename m start:
  fset (
      reachable_nodes_nat
        (rename_memory_subgraph m (reachable_nodes_nat m start))
        (rename_addr start)
    )
  =
  fset (map rename_addr (reachable_nodes_nat m start)).
Admitted.

(*SearchAbout path. Check path.
Check reachable_nodes_nat.
Check dfs_path.
SearchAbout dfs_path.
SearchAbout path.

SearchAbout injective.

SearchAbout nth map.
SearchAbout in_mem.
Check iter.
Check traject.
Check ssrfun.monomorphism_2.
*)
End Renaming.

Definition mem_of_event (e: event) : Memory.t :=
  match e with
  | ECall _ _ _ mem _ => mem
  | ERet _ _ mem _ => mem
  end.

Definition arg_of_event (e: event) : value :=
  match e with
  | ECall _ _ v _ _ => v
  | ERet _ v _ _ => v
  end.

Definition addr_of_value (v: value) : {fset addr_t} :=
  match v with
  | Ptr (perm, cid, bid, _) =>
    if perm =? Permission.data then fset1 (cid, bid) else fset0
  | _ => fset0
  end.

Inductive addr_shared_so_far : addr_t -> trace event -> Prop :=
| reachable_from_args_is_shared:
    forall addr t e,
      Reachable (mem_of_event e) (addr_of_value (arg_of_event e)) addr ->
      addr_shared_so_far addr (rcons t e)
| reachable_from_previously_shared:
    forall addr addr' t e,
      addr_shared_so_far addr' t ->
      Reachable (mem_of_event e) (fset1 addr') addr ->
      addr_shared_so_far addr (rcons t e).

(* [DynShare] 
   This definition is NOT needed when we define a trace relation that
   (implicitly) specifies the shared part of the memory.
   
   It would be needed though if instead we define a trace semantics
   that (explicitly) emits only the shared memory rather than the whole memory.
*)
Definition shared_part_of_memory
           (mshr: Memory.t)
           (m: Memory.t)
           (t: trace event)
  : Prop :=
  forall addr offset, (addr_shared_so_far addr t ->
                       Memory.load mshr (Permission.data, addr.1, addr.2, offset)
                       =
                       Memory.load m (Permission.data, addr.1, addr.2, offset)
                      )
                      /\
                      (~ addr_shared_so_far addr t) ->
                      Memory.load mshr (Permission.data, addr.1, addr.2, offset) = None.
                                  
Definition option_rename_value sigma option_v :=
  match option_v with
  | Some v => Some (rename_value sigma v)
  | None => None
  end.

Definition option_inverse_rename_value sigma option_v :=
  match option_v with
  | Some v => Some (inverse_rename_value sigma v)
  | None => None
  end.

Definition event_renames_event_at_addr sigma addr e e' : Prop :=
  forall offset,
  Memory.load (mem_of_event e')
              (
                Permission.data,
                (rename_addr sigma addr).1,
                (rename_addr sigma addr).2,
                offset
              )
  =
  option_rename_value sigma
                      (
                        Memory.load (mem_of_event e)
                                    (Permission.data,
                                     addr.1,
                                     addr.2,
                                     offset)
                      ).

Definition event_inverse_renames_event_at_addr sigma addr' e e' : Prop :=
  forall offset,
    option_inverse_rename_value sigma
                                (
                                  Memory.load (mem_of_event e')
                                              (Permission.data,
                                               addr'.1,
                                               addr'.2,
                                               offset
                                              )
                                )
    =
    Memory.load (mem_of_event e)
                (Permission.data,
                 (inverse_rename_addr sigma addr').1,
                 (inverse_rename_addr sigma addr').2,
                 offset
                ).
                      
Inductive traces_rename_each_other
          (sigma: {fmap addr_t -> addr_t}) :
  trace event -> trace event -> Prop :=
| nil_renames_nil: traces_rename_each_other sigma nil nil
| rcons_renames_rcons:
    forall tprefix e tprefix' e',
      traces_rename_each_other sigma tprefix tprefix' ->
      (
        forall addr, addr_shared_so_far addr (rcons tprefix e) ->
                     (
                       event_renames_event_at_addr sigma addr e e'
                       /\
                       addr_shared_so_far (rename_addr sigma addr) (rcons tprefix' e')
                     )
      )
      ->
      (
        forall addr', addr_shared_so_far addr' (rcons tprefix' e') ->
                      (
                        event_inverse_renames_event_at_addr sigma addr' e e'
                        /\
                        addr_shared_so_far (inverse_rename_addr sigma addr')
                                           (rcons tprefix e)
                      )
      )
      ->
      traces_rename_each_other sigma (rcons tprefix e) (rcons tprefix' e').

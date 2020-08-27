Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.Reachability.
Require Import Common.Renaming.
Require Import CompCert.Events.

Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrnat eqtype path ssrfun seq fingraph fintype.

Definition pointer_value_is_allocated v mem :=
  match v with
  | Ptr ptr => (Pointer.component ptr, Pointer.block ptr) \in Memory.addresses_of_mem mem
  | _ => true
  end.

Definition mem_content_pointers_are_allocated mem :=
  forall ptr loaded_value,
    Memory.load mem ptr = Some loaded_value -> pointer_value_is_allocated loaded_value mem.

Definition event_pointers_are_allocated e :=
  match e with
  | ECall _ _ v mem _ =>
    pointer_value_is_allocated v mem /\ mem_content_pointers_are_allocated mem
  | ERet _ v mem _ =>
    pointer_value_is_allocated v mem /\ mem_content_pointers_are_allocated mem
  end.

Inductive trace_pointers_are_allocated : trace event -> Prop :=
| nil_trace_pointers_are_allocated : trace_pointers_are_allocated nil
| rcons_trace_pointers_are_allocated :
    forall tpref e,
      trace_pointers_are_allocated tpref ->
      event_pointers_are_allocated e ->
      trace_pointers_are_allocated (rcons tpref e).

Definition memory_lt m1 m2 :=
  fsubset (Memory.addresses_of_mem m1) (Memory.addresses_of_mem m2).

Definition event_with_empty_mem := ERet 0 Undef emptym 0.

Inductive trace_memories_no_dealloc : trace event -> Prop :=
| nil_trace_memories_no_dealloc : trace_memories_no_dealloc nil
| rcons_trace_memories_no_dealloc :
    forall tpref e,
      trace_memories_no_dealloc tpref ->
      memory_lt (mem_of_event (last event_with_empty_mem tpref))
                (mem_of_event e) ->
      trace_memories_no_dealloc (rcons tpref e).

Definition traces_related t t' :=
  exists sigma (*: {fmap addr_t -> addr_t}*),
    injective sigma /\ traces_rename_each_other sigma t t'.

Lemma addr_shared_so_far_allocated addr t e:
  trace_pointers_are_allocated (rcons t e) ->
  trace_memories_no_dealloc (rcons t e) ->
  addr_shared_so_far addr (rcons t e) ->
  addr \in Memory.addresses_of_mem (mem_of_event e).
Admitted.

Section TraceRelationProperties.

  Variable t1 t2 t3: trace event.
  
  Hypothesis t1_pointers_are_allocated: trace_pointers_are_allocated t1.
  Hypothesis t2_pointers_are_allocated: trace_pointers_are_allocated t2.
  Hypothesis t3_pointers_are_allocated: trace_pointers_are_allocated t3.

  Hypothesis t1_memories_no_dealloc: trace_memories_no_dealloc t1.
  Hypothesis t2_memories_no_dealloc: trace_memories_no_dealloc t2.
  Hypothesis t3_memories_no_dealloc: trace_memories_no_dealloc t3.
    
  Definition id_sigma_of_trace (t: trace event) := @id addr_t.
  (*mkfmap
        (zip
        (union_of_memory_domains_of_trace t)
        (union_of_memory_domains_of_trace t)
        ).
   *)

  (* [DynShare] Proving that the identity function that is constructed
   using mkfmap is actually identity was a bit too difficult, so I decided
   I would go for sigma being just a function rather than a fmap.
   *)

  Lemma traces_related_reflexive t : traces_related t t.
  Proof.
    unfold traces_related. eexists (id_sigma_of_trace t). split.
    - unfold id_sigma_of_trace. apply inj_id.
    - induction t using last_ind.
      + apply nil_renames_nil.
      + apply rcons_renames_rcons; auto.
        * intros addr Hshrsfr. split.
          -- unfold event_renames_event_at_addr. intros off.
             unfold id_sigma_of_trace, rename_addr, option_rename_value, rename_value,
             rename_value_template, rename_addr.
             destruct (Memory.load (mem_of_event x) (Permission.data, addr.1, addr.2, off));
               auto.
             destruct v as [|ptr|]; auto. destruct ptr as [[[perm c] b] o]; auto.
          -- unfold rename_addr, id_sigma_of_trace. assumption.
        * intros addr Hshrsfr. split.
          -- unfold event_renames_event_at_addr. intros off.
             unfold id_sigma_of_trace, inverse_rename_addr,
             option_inverse_rename_value, inverse_rename_value,
             rename_value_template, inverse_rename_addr.
             destruct (Memory.load (mem_of_event x) (Permission.data, addr.1, addr.2, off));
               auto.
             destruct v as [|ptr|]; auto. destruct ptr as [[[perm c] b] o]; auto.
          -- unfold rename_addr, id_sigma_of_trace. assumption.
  Qed.

  Lemma traces_related_symmetric : traces_related t1 t2 -> traces_related t2 t1.
  Admitted.

  Lemma traces_related_transitive :
    traces_related t1 t2 ->
    traces_related t2 t3 ->
    traces_related t1 t3.
  Admitted.
  
End TraceRelationProperties.
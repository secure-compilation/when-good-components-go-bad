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

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

From mathcomp Require Import ssreflect ssrnat ssrint ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

Ltac invert_non_eagerly_mergeable_border_states Hmergeborder :=
  let Hmergewf := fresh "Hmergewf" in
  let Hpc      := fresh "Hpc"      in
  let H_p      := fresh "H_p"      in
  let Hregsp   := fresh "Hregsp"   in
  let Hmemp    := fresh "Hmemp"    in
  let Hmemc'   := fresh "Hmemc'"   in
  let Hregsc'  := fresh "Hregsc'"  in
  inversion Hmergeborder as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp].


Section UnaryHelpersForMergeable.

  (* An inductive definition to relate a program with the pointers found in its
     buffers and procedures. A computational definition can be given as well.
     NOTE: Unnecessary? *)

  (**********************************************************************************
  Inductive prog_addrs (p : program) (addrs : addr_t) : Prop :=
  (* this is the data part. These are the static buffers defined by the program. *)
  (* My question is, why don't we just define this as: 
     bufs b' = Some _ ->
     prog_addrs p (C, b').
 *)
  | prog_addrs_buffers : forall C b o perm C' b' bufs buf,
      addrs = (C, b) ->
      (prog_buffers p) C' = Some bufs ->
      bufs b' = Some (inr buf) ->
      In (Ptr (C, b, o, perm)) buf ->
      prog_addrs p addrs
  | prog_addrs_procedures : forall C b o perm r C' P procs proc,
      (* Pointers may appear encode, but point to local buffers?
         Requires renaming in programs!
         And in principle renaming should only affect shared addresses. *)
      addrs = (C, b) ->
      (prog_procedures p) C' = Some procs ->
      procs P = Some proc ->
      In (IConst (IPtr (C, b, o, perm)) r) proc ->
      prog_addrs p addrs.

  Definition static_addresses_of_component
             (p: program) (c: Component.id) : {fset node_t} :=
    CS.component_ptrs p c.
   ***********************************************************************************)
  
End UnaryHelpersForMergeable.

Section BinaryHelpersForMergeable.

  (* n is the metadata size of the LHS program, n' of the RHS program. *)
  Variables n n': Component.id -> nat.
  
  (* Assume t is a prefix. Reason: addr_shared_so_far also assumes t is a prefix. *)
  Definition trace_addrs_rel t m m' :=
    forall addr,
      addr_shared_so_far addr t ->
      memory_shifts_memory_at_shared_addr n n' addr m m'.

  Definition memtrace : Type := eqtype.Equality.sort Memory.t * trace event.

  (* 1- exclude reachable addresses for current cid. *)
  (* by (1) the weak relation is strong enough, i.e., we should expect that *)
  (* by (1) we can prove a strengthening lemma.                             *)

  (* 2- (need to?) exclude shared addresses.         *)

  Inductive regs_rel_of_executing_part
            (r_original r_recombined: Register.t)
            n_original n_recombined
            (*t_original t_recombined*) :=
  | regs_rel_of_executing_part_intro:
      (
        forall reg,
          (
            shift_value_option n_original n_recombined (Register.get reg r_original) =
            Some (Register.get reg r_recombined)
          )
          \/
          (
            shift_value_option
              n_original
              n_recombined
              (Register.get reg r_original) =
            None
            /\
            shift_value_option
              n_recombined
              n_original
              (Register.get reg r_recombined) = None
            /\
            Register.get reg r_original = Register.get reg r_recombined
            (*/\
            (
              forall a,
                a \in addr_of_value (Register.get reg r_original) ->
                ~ addr_shared_so_far a t_original
            )
            /\
            (
              forall a,
                a \in addr_of_value (Register.get reg r_recombined) ->
                ~ addr_shared_so_far a t_recombined
            )*)
          )
      )
      ->
      regs_rel_of_executing_part
        r_original r_recombined n_original n_recombined
        (*t_original t_recombined*).
        
  Inductive stack_of_program_part_rel_stack_of_recombined
            (part: program) : CS.stack -> CS.stack -> Prop :=
  | stack_of_program_part_rel_stack_of_recombined_nil:
      stack_of_program_part_rel_stack_of_recombined part nil nil
  | stack_of_program_part_rel_stack_of_recombined_cons:
      forall (ptr_part ptr_recombined: Pointer.t) (stk_part stk_recombined: CS.stack),
        stack_of_program_part_rel_stack_of_recombined part stk_part stk_recombined ->
        (
          if Pointer.component ptr_part \in domm (prog_interface part)
          then ptr_part = ptr_recombined
          else Pointer.component ptr_part = Pointer.component ptr_recombined
        )
        ->
        stack_of_program_part_rel_stack_of_recombined
          part (ptr_part :: stk_part) (ptr_recombined :: stk_recombined).     
        
End BinaryHelpersForMergeable.

(* AEK: Ignore this section for now. *)
(********************************************************************************
Section RelateElectedProgramPartInOriginalAndRecombined.
  
  Definition original_and_recombined_memories_internal_relation
             (elected_prog_part: program)
             (* i.e., p or c' *)
             original_mem recombined_mem
             (* i.e., (s.mem or s''.mem) and s'.mem *)
             (original_t   recombined_t  : trace event)
             (* i.e., (t or t'') and t' *)
             (original_n   recombined_n  : Component.id -> nat)
             (* i.e., (n or n'') and n' *)
             (cur_comp: Component.id) : Prop
             (* i.e., the component id of s'.pc *)
    :=

      (
        forall original_addr,
          ~ addr_shared_so_far original_addr original_t ->
          (*~ original_addr.1 == cur_comp ->*)
          (*~ Reachable
            original_mem
            (static_addresses_of_component elected_prog_part cur_comp)
            original_addr ->*)
          memory_shifts_memory_at_addr_all_cids
            original_n
            recombined_n
            original_addr
            original_mem
            recombined_mem
      )
      /\
      (
        forall recombined_addr,
          ~ addr_shared_so_far recombined_addr recombined_t ->
          ~ Reachable
            recombined_mem
            (static_addresses_of_component elected_prog_part cur_comp)
            recombined_addr ->
          memory_inverse_shifts_memory_at_addr_all_cids
            original_n
            recombined_n
            recombined_addr
            original_mem
            recombined_mem
      ).

  Definition original_and_recombined_memories_border_relation
             (elected_prog_part: program)
             (* i.e., p or c' depending on the component id before the border *)
             original_mem recombined_mem
             (* i.e., (s.mem or s''.mem) and s'.mem *)
             (original_t   recombined_t  : trace event)
             (* i.e., (t or t'') and t' *)
             (original_n   recombined_n  : Component.id -> nat)
             (* i.e., (n or n'') and n' *)
             (comp_before_border: Component.id)
             (* i.e., the component id before the border event *)
    : Prop
    :=
      original_and_recombined_memories_internal_relation
        elected_prog_part
        original_mem
        recombined_mem
        original_t
        recombined_t
        original_n
        recombined_n
        comp_before_border
      /\
      trace_addrs_rel
        original_n
        recombined_n
        original_t
        original_mem
        recombined_mem
      /\
      trace_addrs_rel_inv
        original_n
        recombined_n
        recombined_t
        original_mem
        recombined_mem.

(*  Lemma original_and_recombined_memories_relation_weakening
        p_part m m_recomb t t_recomb n n_recomb cid:
    original_and_recombined_memories_border_relation
*)  
End RelateElectedProgramPartInOriginalAndRecombined.
************************************************************************************)

(* An inductive notion of pairs of states for which merging is well-defined. *)
(* RB: TODO: Harmonize naming conventions. *)
Section Mergeable.
  Variables p c p' c' : program.

  Variables n n'': Component.id -> nat.

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

  (* NOTE: [DynShare] Towards a more intensional definition of mergeable states.

      - For three states, s (p, c), s' (p, c'), and s'' (p', c').

      - Split (strong vs. weak) relation? Unlikely: there are no significant
        asymmetries.

      - Memories: starting from some @s, there is a reachable region of the
        memory, which is a renaming of the corresponding reachable region:

          @ <-> @' @'' <-> @'

        (The third relation should be retrievable from the two given ones.)

        Re: addr_shared_so_far (definitions should coincide, but note that at
        the moment we do not have a trace in this relation; perhaps we should).

        Adding the trace prefix as a parameter of the relation should not be a
        problem; the prefix is or can easily be made available in the proofs.

        Things reachable from local buffers AND from the addresses shared so
        far. (I.e., from the POV of P, all the memory except the memory that is
        still private to C).

        Taking this set, loads can only evaluate from addresses in this set.

        Moreover, if we load from s, we will be able to load from s'', and the
        addresses will be renamings one of another.

      - Stacks: ...

      - Registers: ...

      - PC: ...

      - Role of the trace relation: at some points we will need to prove that
        the state relation implies the trace relation.

      *)
  

  (* RB: NOTE: We may need a PC later to keep things simple. *)
  Definition event_comp (e : event) : Component.id :=
    match e with
    | ECall _ _ _ _ C | ERet _ _ _ C => C
    end.

  Definition trace_comp (t : trace event) : Component.id :=
    match t with
    | [] => Component.main
    | e :: t' => fold_left (fun _ e => event_comp e) t' (event_comp e)
    end.

      (* (R1) m   \\ reach(p)  ~ m' \\ reach(p)
         (R2) m'' \\ reach(c') ~ m' \\ reach(c')

         Projection on reachability. Value-renaming "equality" relation.

         These hold conditionally:

         if pc \in domm p
         then (R1) holds
         else (R2) holds

         + having the "same" event occur (modulo renaming)

         => this will be a goal at some point in the proofs

         The memory relations in the trace state the shared parts are equal.
      *)

  Definition regtrace : Type := Register.t * trace event.

  (* This "extensional" reading of compatible states depends directly on the
     partial programs concerned (implicitly through the section mechanism) and
     two runs synchronized by their traces. It is a rather strong notion, easy
     to work with and well suited to the purposes of the proof. *)

  (* NOTE: Should the relation also speak about traces? This could simplify
     some of the simulation lemmas below. This could postpone the question
     of provenance until use time. *)

  (* "part_executing" really means the part that is picked in the recombined run. *)
  Definition mem_of_part_executing_rel_original_and_recombined
             (part_executing: program)
             (* part_executing should be either p or c' *)
             original_mem recombined_mem
             original_n   recombined_n
             original_t   (*recombined_t*)
    : Prop :=
    (
      forall original_addr,
        original_addr.1 \in domm (prog_interface part_executing) ->
        memory_shifts_memory_at_private_addr
          original_n
          recombined_n
          original_addr
          original_mem
          recombined_mem
    )
    /\
    (
      forall original_addr,
        addr_shared_so_far original_addr original_t ->
        memory_shifts_memory_at_shared_addr
          original_n
          recombined_n
          original_addr
          original_mem
          recombined_mem
    )
    /\
    forall cid,
      cid \in domm (prog_interface part_executing) ->
      omap ComponentMemory.next_block (original_mem cid) =
      omap ComponentMemory.next_block (recombined_mem cid).

  Definition mem_of_part_not_executing_rel_original_and_recombined_at_internal
             (part_not_executing: program)
             original_mem recombined_mem
             original_n   recombined_n
             original_t   (*recombined_t*)
    : Prop :=
    (
      forall original_addr,
        original_addr.1 \in domm (prog_interface part_not_executing) ->
        ~ addr_shared_so_far original_addr original_t ->
        memory_shifts_memory_at_private_addr
          original_n
          recombined_n
          original_addr
          original_mem
          recombined_mem
    )
    /\
    forall cid,
      cid \in domm (prog_interface part_not_executing) ->
      omap ComponentMemory.next_block (original_mem cid) =
      omap ComponentMemory.next_block (recombined_mem cid).

  Definition mem_of_part_not_executing_rel_original_and_recombined_at_border
             (part_not_executing: program)
             original_mem recombined_mem
             original_n   recombined_n
             original_t   (*recombined_t*)
    : Prop :=
    mem_of_part_executing_rel_original_and_recombined
      part_not_executing
      original_mem recombined_mem
      original_n   recombined_n
      original_t   (*recombined_t*).

  Inductive mergeable_states_well_formed
            (s s' s'' : CS.state) t t' t'' : Prop :=
    mergeable_states_well_formed_intro:
      well_formed_program p ->
      well_formed_program c ->
      well_formed_program p' ->
      well_formed_program c' ->
      mergeable_interfaces ip ic ->
      prog_interface p  = prog_interface p' ->
      prog_interface c  = prog_interface c' ->
      closed_program prog   ->
      closed_program prog'' ->
      (* Good programs are programs whose memory is always "good". *)
      (* A good memory means every "potentially shareable" location *)
      (* never contains "unshareable" pointers. A pointer is unshareable *)
      (* when it points to a metadata location (as specified by n, n'' resp.) *)
      (forall ss tt,
          CSInvariants.is_prefix ss prog tt ->
          good_trace_extensional
            (left_addr_good_for_shifting n)
            tt
          /\
          forall mem ptr addr v,
            CS.state_mem ss = mem ->
            Memory.load mem ptr = Some v ->
            addr = (Pointer.component ptr, Pointer.block ptr) ->
            left_addr_good_for_shifting n addr ->
            left_value_good_for_shifting n v   
      ) ->
      (forall ss'' tt'',
          CSInvariants.is_prefix ss'' prog'' tt'' ->
          good_trace_extensional
            (left_addr_good_for_shifting n'')
            tt''
          /\
          forall mem ptr addr v,
            CS.state_mem ss'' = mem ->
            Memory.load mem ptr = Some v ->
            addr = (Pointer.component ptr, Pointer.block ptr) ->
            left_addr_good_for_shifting n'' addr ->
            left_value_good_for_shifting n'' v
      ) ->
      CSInvariants.is_prefix s   prog   t ->
      CSInvariants.is_prefix s'  prog'  t' ->
      CSInvariants.is_prefix s'' prog'' t'' ->
      (*good_memory (left_addr_good_for_shifting n)   (CS.state_mem s) ->
      good_memory (left_addr_good_for_shifting n'') (CS.state_mem s'') ->
      good_memory (left_addr_good_for_shifting n')  (CS.state_mem s') ->*)
      good_trace_extensional (left_addr_good_for_shifting n) t ->
      good_trace_extensional (left_addr_good_for_shifting n'') t'' ->
      good_trace_extensional (left_addr_good_for_shifting n') t' ->
      stack_of_program_part_rel_stack_of_recombined
        p (CS.state_stack s) (CS.state_stack s') ->
      stack_of_program_part_rel_stack_of_recombined
        c' (CS.state_stack s'') (CS.state_stack s') ->
      Pointer.component (CS.state_pc s') = Pointer.component (CS.state_pc s) ->
      Pointer.component (CS.state_pc s') = Pointer.component (CS.state_pc s'') ->
      traces_shift_each_other_option n   n' t   t' ->
      traces_shift_each_other_option n'' n' t'' t' ->
      mergeable_states_well_formed s s' s'' t t' t''.
  
  Inductive mergeable_internal_states
            (s s' s'' : CS.state) t t' t'' : Prop :=
  | mergeable_internal_states_p_executing:
      mergeable_states_well_formed s s' s'' t t' t'' ->
      CS.state_pc s' = CS.state_pc s ->
      CS.is_program_component s' ic ->
      (*Pointer.component (CS.state_pc s') \in domm (prog_interface p) ->*)
      regs_rel_of_executing_part (CS.state_regs s) (CS.state_regs s') n n'
                                 (*t t'*) ->
      mem_of_part_executing_rel_original_and_recombined
        p                  (* Here, the part executing is p. *)
        (CS.state_mem s)   (* Thus, the original memory comes from s. *)
        (CS.state_mem s')
        n
        n'
        t ->
      mem_of_part_not_executing_rel_original_and_recombined_at_internal
        c'                 (* Here, the part not executing is c'. *)
        (CS.state_mem s'') (* Thus, the original memory comes from s''. *)
        (CS.state_mem s')
        n''
        n'
        t'' ->
      mergeable_internal_states s s' s'' t t' t''
  | mergeable_internal_states_c'_executing:
      mergeable_states_well_formed s s' s'' t t' t'' ->
      CS.state_pc s' = CS.state_pc s'' ->
      CS.is_context_component s' ic ->      
      (*Pointer.component (CS.state_pc s') \in domm (prog_interface c') ->*)
      regs_rel_of_executing_part (CS.state_regs s'') (CS.state_regs s') n'' n'
                                 (*t'' t'*) ->
      mem_of_part_executing_rel_original_and_recombined
        c'                  (* Here, the part executing is c'. *)
        (CS.state_mem s'')  (* Thus, the original memory comes from s''. *)
        (CS.state_mem s')
        n''
        n'
        t'' ->
      mem_of_part_not_executing_rel_original_and_recombined_at_internal
        p                  (* Here, the part not executing is p. *)
        (CS.state_mem s)   (* Thus, the original memory comes from s. *)
        (CS.state_mem s')
        n
        n'
        t ->
      mergeable_internal_states s s' s'' t t' t''.

  Inductive mergeable_border_states
            (s s' s'' : CS.state) t t' t'' : Prop :=
  | mergeable_border_states_p_executing:
      mergeable_states_well_formed s s' s'' t t' t'' ->
      CS.state_pc s' = CS.state_pc s ->
      CS.is_program_component s' ic ->
      (*Pointer.component (CS.state_pc s') \in domm (prog_interface p) ->*)
      regs_rel_of_executing_part (CS.state_regs s) (CS.state_regs s') n n'
                                 (*t t'*) ->
      mem_of_part_executing_rel_original_and_recombined
        p                  (* Here, the part executing is p. *)
        (CS.state_mem s)   (* Thus, the original memory comes from s. *)
        (CS.state_mem s')
        n
        n'
        t ->
      mem_of_part_not_executing_rel_original_and_recombined_at_border
        c'                 (* Here, the part not executing is c'. *)
        (CS.state_mem s'') (* Thus, the original memory comes from s''. *)
        (CS.state_mem s')
        n''
        n'
        t'' ->
      mergeable_border_states s s' s'' t t' t''
  | mergeable_border_states_c'_executing:
      mergeable_states_well_formed s s' s'' t t' t'' ->
      CS.state_pc s' = CS.state_pc s'' ->
      CS.is_context_component s' ic ->      
      (*Pointer.component (CS.state_pc s') \in domm (prog_interface c') ->*)
      regs_rel_of_executing_part (CS.state_regs s'') (CS.state_regs s') n'' n'
                                 (*t'' t'*) ->
      mem_of_part_executing_rel_original_and_recombined
        c'                  (* Here, the part executing is c'. *)
        (CS.state_mem s'')  (* Thus, the original memory comes from s''. *)
        (CS.state_mem s')
        n''
        n'
        t'' ->
      mem_of_part_not_executing_rel_original_and_recombined_at_border
        p                 (* Here, the part not executing is p. *)
        (CS.state_mem s)  (* Thus, the original memory comes from s. *)
        (CS.state_mem s')
        n
        n'
        t ->
      mergeable_border_states s s' s'' t t' t''.

  Lemma mergeable_border_mergeable_internal s s' s'' t t' t'':
    mergeable_border_states s s' s'' t t' t'' ->
    mergeable_internal_states s s' s'' t t' t''.
  Proof.
    intros Hmergeborder.
    invert_non_eagerly_mergeable_border_states Hmergeborder.
    - apply mergeable_internal_states_p_executing; try eassumption.
      destruct Hmemc' as [Hshift [Hinvshift Hnextblock]].
      unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal.
      intuition.
    - apply mergeable_internal_states_c'_executing; try eassumption.
      destruct Hmemp as [Hshift [Hinvshift Hnextblock]].
      unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal.
      intuition.
  Qed.

  (* Inversion pattern:
inversion Hmerg as [s0 s0' s0'' t t' t'' n n' n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed'' Hini Hini' Hini'' Hstar Hstar' Hstar'' Hmrel Htrel Htrel''].
  *)

  (* Relations between mergeable states and program components. *)
  Lemma mergeable_states_pc_same_component s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) = Pointer.component (CS.state_pc s'').
  Proof.
    intros [[] | []]; congruence.
  Qed.

  Lemma mergeable_states_program_to_program s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t''->
    CS.is_program_component s   ic ->
    CS.is_program_component s'' ic.
  Proof.
    destruct s   as [[[? ?] ?] pc  ].
    destruct s'' as [[[? ?] ?] pc''].
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    intros Hmerge Hpc.
    pose proof mergeable_states_pc_same_component Hmerge as Hcomp. simpl in Hcomp.
    congruence.
  Qed.

  (* [DynShare] Identical sub-proofs. No contradiction! *)
  Lemma mergeable_states_context_to_program s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.is_context_component s ic ->
    CS.is_program_component s'' ip.
  Proof.
    intros [ [_ _ _ _ Hmerge_ifaces _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomp Hcomp'' _ _] _ _ _ _ _
           | [_ _ _ _ Hmerge_ifaces _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomp Hcomp'' _ _] _ _ _ _ _] Hin.
    - CS.unfold_states. CS.simplify_turn.
      eapply domm_partition_notin.
      + eassumption.
      + now rewrite <- Hcomp'', -> Hcomp.
    - CS.unfold_states. CS.simplify_turn.
      eapply domm_partition_notin.
      + eassumption.
      + now rewrite <- Hcomp'', -> Hcomp.
  Qed.

  (* [DynShare] Identical sub-proofs. No contradiction! *)
  Lemma mergeable_states_program_to_context s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.is_program_component s ic ->
    CS.is_context_component s'' ip.
  Proof.
    intros Hmerg Hnotin.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack mem] reg] pc];
      destruct s'' as [[[stack'' mem''] reg''] pc''].
    pose proof mergeable_states_pc_same_component Hmerg as Hpc; simpl in Hpc.
    rewrite <- Hpc.

    inversion Hmerg
      as [ [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _
         | [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _ ].
    - CS.unfold_states.
      pose proof (CS.star_pc_domm_non_inform
                    _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Logic.eq_refl Hstar) as Hpc'.
      destruct Hpc' as [Hprg | Hctx].
      + assumption.
      + CS.simplify_turn. now rewrite Hctx in Hnotin.
    - CS.unfold_states.
      pose proof (CS.star_pc_domm_non_inform
                    _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Logic.eq_refl Hstar) as Hpc'.
      destruct Hpc' as [Hprg | Hctx].
      + assumption.
      + CS.simplify_turn. now rewrite Hctx in Hnotin.
  Qed.
    (*inversion Hmerg as [ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces H_iface H_iface'
                        Hprog_is_closed Hctx_is_closed Hpref Hpref' Hpref''
                        Hmemrel Hregsrel Hstar Hstar''].*)
(*    pose proof (CS.star_pc_domm_non_inform
                  _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar).
    intros Hn; destruct H.
    assumption.
    rewrite H in Hn. inversion Hn.
  Qed.*)

  (* RB: NOTE: Try to phrase everything either as CS.is_XXX_component, or as
     \[not]in. This is the equivalent of the old [PS.domm_partition].
     [DynShare] There are now two identical sub-proofs, which could be
     simplified. *)
  Lemma mergeable_states_notin_to_in s s' s'' t t' t'' pc :
    mergeable_internal_states s s' s'' t t' t'' ->
    pc = CS.state_pc s ->
    Pointer.component pc \notin domm ip ->
    Pointer.component pc \in domm ic.
  Proof.
    intros Hmerg Hpc Hpc_notin. subst.
    inversion Hmerg
      as [ [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _
         | [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _ ].
    - CS.unfold_states.
      pose proof (CS.star_pc_domm_non_inform
                    _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Logic.eq_refl Hstar) as Hpc.
      destruct Hpc as [Hprg | Hctx].
      + now rewrite Hprg in Hpc_notin.
      + now assumption.
    - CS.unfold_states.
      pose proof (CS.star_pc_domm_non_inform
                    _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Logic.eq_refl Hstar) as Hpc.
      destruct Hpc as [Hprg | Hctx].
      + now rewrite Hprg in Hpc_notin.
      + now assumption.
  Qed.

  Lemma mergeable_states_in_to_notin s s' s'' t t' t'' pc :
    mergeable_internal_states s s' s'' t t' t'' ->
    pc = CS.state_pc s ->
    Pointer.component pc \in domm ic ->
    Pointer.component pc \notin domm ip.
  Proof.
    intros Hmerg ? Hpc_in. subst. CS.unfold_states.
    inversion Hmerg
      as [ [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _
         | [Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ _ _ Hstar _ _ _ _ _ _ _ _ _ _ _] _ _ _ _ _ ];
      CS.simplify_turn;
      destruct Hmergeable_ifaces as [[_ Hdisj] _];
      rewrite fdisjointC in Hdisj;
      move : Hdisj => /fdisjointP => Hdisj;
      by specialize (Hdisj _ Hpc_in).
  Qed.

  Lemma mergeable_states_notin_to_in2 s s' s'' t t' t'' pc :
    mergeable_internal_states s s' s'' t t' t'' ->
    pc = CS.state_pc s ->
    Pointer.component pc \notin domm ic ->
    Pointer.component pc \in domm ip.
  Proof. intros Hmerge ? contra. subst.
         destruct (Pointer.component (CS.state_pc s) \in domm ip) eqn:e; auto.
         destruct (Pointer.component (CS.state_pc s) \notin domm ip) eqn:e2.
         - specialize (mergeable_states_notin_to_in Hmerge Logic.eq_refl e2) as rewr.
             by rewrite rewr in contra.
         - by rewrite e in e2.
  Qed.
  
  Lemma mergeable_states_in_to_notin2 s s' s'' t t' t'' pc :
    mergeable_internal_states s s' s'' t t' t'' ->
    pc = CS.state_pc s ->
    Pointer.component pc \in domm ip ->
    Pointer.component pc \notin domm ic.
  Proof.
    intros Hmerge ? Hpc_in. subst.
    destruct (Pointer.component (CS.state_pc s) \in domm ic) eqn:e; auto.
    specialize (mergeable_states_in_to_notin Hmerge Logic.eq_refl e) as contra.
    by rewrite Hpc_in in contra.
  Qed.  

  
  (* RB: NOTE: Consider if the core of the lemma could be moved to CS, as is the
     case of its simpler variant, is_program_component_pc_notin_domm. *)
  Lemma is_program_component_pc_in_domm s s' s'' t t' t'':
    CS.is_program_component s ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) \in domm ip.
  Proof.
    intros Hpc Hmerge.
    assert (Hcc := Hmerge);
      apply mergeable_states_program_to_context in Hcc; try assumption.
    unfold CS.is_context_component, turn_of, CS.state_turn in Hcc.
    rewrite (mergeable_states_pc_same_component Hmerge).
    now destruct s'' as [[[? ?] ?] ?].
  Qed.

  Lemma mergeable_states_program_component_domm
        mem gps regs pc s' s'' t t' t'':
    mergeable_internal_states (mem, gps, regs, pc) s' s'' t t' t'' ->
    CS.is_program_component (mem, gps, regs, pc) ic ->
    Pointer.component pc \in domm ip.
  Proof.
    intros Hmerge Hcomp.
    change pc with (CS.state_pc (mem, gps, regs, pc)).
    eapply is_program_component_pc_in_domm; last eassumption; assumption.
  Qed.

  (* TODO: Explain the interest of this construct, as it is only used as a proxy
     to prove the symmetry of merge_states from mergeable_states, and the
     following lemma gives the impression of crossing the bridge only to cross
     it back. *)
  Inductive mergeable_stack : CS.stack -> CS.stack -> Prop :=
  | mergeable_stack_nil : mergeable_stack [] []
  | mergeable_stack_cons : forall frame frame'' gps gps'',
      Pointer.component frame = Pointer.component frame'' ->
      Pointer.component frame \in domm ic \/ Pointer.component frame \in domm ip ->
      mergeable_stack gps gps'' ->
      mergeable_stack (frame :: gps) (frame'' :: gps'').

  (* [DynShare] Identical sub-proofs. No contradiction! *)
  Lemma find_label_in_component_mergeable_internal_states
        s s' s'' t t' t'' l spc pc:
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc = CS.state_pc s' ->
    find_label_in_component (globalenv sem) spc l = Some pc ->
    find_label_in_component (globalenv sem') spc l = Some pc.
  Proof.
    intros Hprog_comp Hmerge Hspc Hfind.
    inversion Hmerge as [Hwf _ _ _ _ _ | Hwf _ _ _ _ _];
      inversion Hwf as [Hwfp Hwfc _ Hwfc' Hmerge_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    - rewrite find_label_in_component_program_link_left; try assumption.
      + rewrite find_label_in_component_program_link_left in Hfind; try assumption.
        * CS.simplify_turn. CS.unfold_states. now subst spc.
        * now destruct Hmerge_ifaces.
      + rewrite <- Hifacec.
        CS.simplify_turn. CS.unfold_states. now subst spc.
      + rewrite <- Hifacec. now destruct Hmerge_ifaces.
    - rewrite find_label_in_component_program_link_left; try assumption.
      + rewrite find_label_in_component_program_link_left in Hfind; try assumption.
        * CS.simplify_turn. CS.unfold_states. now subst spc.
        * now destruct Hmerge_ifaces.
      + rewrite <- Hifacec.
        CS.simplify_turn. CS.unfold_states. now subst spc.
      + rewrite <- Hifacec. now destruct Hmerge_ifaces.
  Qed.

  (* [DynShare] Identical sub-proofs. No contradiction! *)
  Lemma find_label_in_procedure_mergeable_internal_states
        s s' s'' t t' t'' l spc pc:
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc = CS.state_pc s' ->
    find_label_in_procedure (globalenv sem) spc l = Some pc ->
    find_label_in_procedure (globalenv sem') spc l = Some pc.
  Proof.
    intros Hprog_comp Hmerge Hspc Hfind.
    inversion Hmerge as [Hwf _ _ _ _ _ | Hwf _ _ _ _ _];
      inversion Hwf as [Hwfp Hwfc _ Hwfc' Hmerge_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    - rewrite find_label_in_procedure_program_link_left; try assumption.
      + rewrite find_label_in_procedure_program_link_left in Hfind; try assumption.
        * CS.simplify_turn. CS.unfold_states. now subst spc.
        * now destruct Hmerge_ifaces.
      + rewrite <- Hifacec.
        CS.simplify_turn. CS.unfold_states. now subst spc.
      + rewrite <- Hifacec. now destruct Hmerge_ifaces.
    - rewrite find_label_in_procedure_program_link_left; try assumption.
      + rewrite find_label_in_procedure_program_link_left in Hfind; try assumption.
        * CS.simplify_turn. CS.unfold_states. now subst spc.
        * now destruct Hmerge_ifaces.
      + rewrite <- Hifacec.
        CS.simplify_turn. CS.unfold_states. now subst spc.
      + rewrite <- Hifacec. now destruct Hmerge_ifaces.
  Qed.

  Lemma mergeable_internal_states_executing_prog
        s s' s'' t t' t'' instr spc spc':
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc = CS.state_pc s ->
    executing (globalenv sem) spc instr ->
    spc' = CS.state_pc s' ->
    executing (globalenv sem') spc' instr.
  Proof.
    intros Hcomp Hmerge Hsubst1 Hexec Hsubst2.
    inversion Hmerge as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp]; subst;
      inversion Hmergewf
      as [
          Hwfp
            Hwfc
            Hwfp'
            Hwfc'
            Hmerge_ipic
            Hifc_pp'
            Hifc_cc'
            Hclosed_prog
            Hclosed_prog''
            Hgood_prog
            Hgood_prog''
            Hpref_t
            Hpref_t'
            Hpref_t''
            Hgood_t
            Hgood_t''
            Hgood_t'
            Hstack_s_s'
            Hstack_s''_s'
            Hpccomp_s'_s
            Hpccomp_s'_s''
            Hshift_tt'
            Hshift_t''t'];
      unfold mergeable_interfaces in *;
      destruct s as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc']; CS.simplify_turn.

    - inversion Hexec
        as [P_code [proc_code [Hgenv_proc [Hblock [Hoff [Hperm Hinstr]]]]]].
      econstructor.
      rewrite Hpc.
      rewrite genv_procedures_program_link_left_notin in Hgenv_proc; auto;
        last intuition.
      + rewrite genv_procedures_program_link_left_notin; auto.
        * by eexists; eauto.
        * by rewrite <- Hpccomp_s'_s, <- Hifc_cc'.
        * by rewrite <- Hifc_cc'; intuition.
      + by rewrite <- Hpccomp_s'_s.
    - by rewrite H_c' in Hcomp.
  Qed.


  Lemma mergeable_internal_states_executing_prog'_prog
        s s' s'' t t' t'' instr spc spc':
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc' = CS.state_pc s' ->
    executing (globalenv sem') spc' instr ->
    spc = CS.state_pc s ->
    executing (globalenv sem) spc instr.
  Proof.
    intros Hcomp Hmerge Hsubst1 Hexec Hsubst2.
    inversion Hmerge as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp]; subst;
      inversion Hmergewf
      as [
          Hwfp
            Hwfc
            Hwfp'
            Hwfc'
            Hmerge_ipic
            Hifc_pp'
            Hifc_cc'
            Hclosed_prog
            Hclosed_prog''
            Hgood_prog
            Hgood_prog''
            Hpref_t
            Hpref_t'
            Hpref_t''
            Hgood_t
            Hgood_t''
            Hgood_t'
            Hstack_s_s'
            Hstack_s''_s'
            Hpccomp_s'_s
            Hpccomp_s'_s''
            Hshift_tt'
            Hshift_t''t'];
      unfold mergeable_interfaces in *;
      destruct s as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc']; CS.simplify_turn.

    - inversion Hexec
        as [P_code [proc_code [Hgenv_proc [Hblock [Hoff [Hperm Hinstr]]]]]].
      subst.
      econstructor.
      rewrite genv_procedures_program_link_left_notin in Hgenv_proc; auto;
        last intuition.
      + rewrite genv_procedures_program_link_left_notin; auto.
        * by eexists; eauto.
        * by intuition.
      + by rewrite <- Hifc_cc'.
      + by rewrite <- Hifc_cc'.
    - by rewrite H_c' in Hcomp.
  Qed.

  
  Lemma mergeable_internal_states_executing_prog''
        s s' s'' t t' t'' instr spc'' spc':
    CS.is_context_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc'' = CS.state_pc s'' ->
    executing (globalenv sem'') spc'' instr ->
    spc' = CS.state_pc s' ->
    executing (globalenv sem') spc' instr.
  Proof.
    intros Hcomp Hmerge Hsubst1 Hexec Hsubst2.
    inversion Hmerge as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp]; subst;
      inversion Hmergewf
      as [
          Hwfp
            Hwfc
            Hwfp'
            Hwfc'
            Hmerge_ipic
            Hifc_pp'
            Hifc_cc'
            Hclosed_prog
            Hclosed_prog''
            Hgood_prog
            Hgood_prog''
            Hpref_t
            Hpref_t'
            Hpref_t''
            Hgood_t
            Hgood_t''
            Hgood_t'
            Hstack_s_s'
            Hstack_s''_s'
            Hpccomp_s'_s
            Hpccomp_s'_s''
            Hshift_tt'
            Hshift_t''t'];
      unfold mergeable_interfaces in *;
      destruct s'' as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc']; CS.simplify_turn.

    - by rewrite Hcomp in H_p.
    - inversion Hexec
        as [P_code [proc_code [Hgenv_proc [Hblock [Hoff [Hperm Hinstr]]]]]]; subst.
      econstructor.
      rewrite genv_procedures_program_link_right_in in Hgenv_proc; auto;
        last intuition.
      + rewrite genv_procedures_program_link_right_in; auto.
        * eexists; eauto.
        * by rewrite <- Hifc_cc'.
        * by rewrite <- Hifc_cc'; intuition.
      + by rewrite <- Hifc_cc'.
      + by rewrite <- Hifc_pp', <- Hifc_cc'.
  Qed.


  Lemma mergeable_internal_states_executing_prog'_prog''
        s s' s'' t t' t'' instr spc'' spc':
    CS.is_context_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc' = CS.state_pc s' ->
    executing (globalenv sem') spc' instr ->
    spc'' = CS.state_pc s'' ->
    executing (globalenv sem'') spc'' instr.
  Proof.
    intros Hcomp Hmerge Hsubst1 Hexec Hsubst2.
    inversion Hmerge as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp]; subst;
      inversion Hmergewf
      as [
          Hwfp
            Hwfc
            Hwfp'
            Hwfc'
            Hmerge_ipic
            Hifc_pp'
            Hifc_cc'
            Hclosed_prog
            Hclosed_prog''
            Hgood_prog
            Hgood_prog''
            Hpref_t
            Hpref_t'
            Hpref_t''
            Hgood_t
            Hgood_t''
            Hgood_t'
            Hstack_s_s'
            Hstack_s''_s'
            Hpccomp_s'_s
            Hpccomp_s'_s''
            Hshift_tt'
            Hshift_t''t'];
      unfold mergeable_interfaces in *;
      destruct s'' as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc']; CS.simplify_turn.

    - by rewrite Hcomp in H_p.
    - inversion Hexec
        as [P_code [proc_code [Hgenv_proc [Hblock [Hoff [Hperm Hinstr]]]]]]; subst.
      econstructor.
      rewrite genv_procedures_program_link_right_in in Hgenv_proc; auto;
        last intuition.
      + rewrite genv_procedures_program_link_right_in; auto.
        * eexists; eauto.
        * by rewrite <- Hifc_cc'.
        * by rewrite <- Hifc_cc', <- Hifc_pp'; intuition.
      + by rewrite <- Hifc_cc'.
      + by rewrite <- Hifc_cc'.
  Qed.


  Corollary mergeable_internal_states_final_state_prog
    s s' s'' t t' t'':
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.final_state (globalenv sem) s ->
    CS.final_state (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hfinal;
      destruct s as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc'];
        unfold CS.final_state in *.
    eapply mergeable_internal_states_executing_prog; by eauto.
  Qed.

  Corollary mergeable_internal_states_final_state_prog''
    s s' s'' t t' t'':
    CS.is_context_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.final_state (globalenv sem'') s'' ->
    CS.final_state (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hfinal;
      destruct s'' as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc'];
        unfold CS.final_state in *.
    eapply mergeable_internal_states_executing_prog''; by eauto.
  Qed.


  Corollary mergeable_internal_states_nofinal_prog
            s s' s'' t t' t'':
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    ~ CS.final_state (globalenv sem) s ->
    ~ CS.final_state (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hnofinal Hfinal;
      destruct s as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc'];
        unfold CS.final_state in *.
    eapply mergeable_internal_states_executing_prog'_prog in Hfinal; by eauto.
  Qed.

  
  Corollary mergeable_internal_states_nofinal_prog''
            s s' s'' t t' t'':
    CS.is_context_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    ~ CS.final_state (globalenv sem'') s'' ->
    ~ CS.final_state (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hnofinal Hfinal;
      destruct s'' as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc'];
        unfold CS.final_state in *.
    eapply mergeable_internal_states_executing_prog'_prog'' in Hfinal; by eauto.
  Qed.



  Corollary mergeable_internal_states_nostep_prog
            s s' s'' t t' t'':
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    nostep CS.step_non_inform (globalenv sem) s ->
    nostep CS.step_non_inform (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hnostep tcontra scontra Hcontra;
      destruct s as [[[? ?] ?] pc]; destruct s' as [[[? ?] ?] pc'];
        unfold nostep in *.
    (** TODO: It seems we need an inverse lock-step simulation lemma! *)
    (**       to be able to use Hcontra and get a contra to Hnostep.  *)
  Abort.

  
  Corollary mergeable_internal_states_nostep_prog''
            s s' s'' t t' t'':
    CS.is_context_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    nostep CS.step_non_inform (globalenv sem'') s'' ->
    nostep CS.step_non_inform (globalenv sem') s'.
  Proof.
    intros Hcomp Hmerge Hnostep tcontra scontra Hcontra;
      destruct s'' as [[[? ?] ?] pc'']; destruct s' as [[[? ?] ?] pc'];
        unfold nostep in *.
    (** TODO: It seems we need an inverse lock-step simulation lemma FOR prog''  *)
    (**       in order to be able to use Hcontra and get a contra to Hnostep.    *)
  Abort.

  (* Search _ find_label_in_component. *)

  (*
  Lemma find_label_in_component_recombination
        s s' s'' t t' t'' l pc :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' t t' t'' ->
    find_label_in_component (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_component (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    (*
    inversion Hmerge as [_ _ _ _ _ _ _ _ _ Hwfp Hwfc _ Hwfc' Hmergeable_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof find_label_in_component_1 _ _ _ _ Hlabel as Hpc_.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hdomm; simpl in Hdomm.
    rewrite find_label_in_component_program_link_left in Hlabel;
      try assumption.
    unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    unfold ip, ic in Hlinkable.
    rewrite (find_label_in_component_program_link_left Hdomm Hwfp);
      congruence.
  Qed.*)
  Admitted.
  *)

  (*
  (* Search _ find_label_in_procedure. *)
  Lemma find_label_in_procedure_recombination
        s s' s'' t t' t'' l pc :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' t t' t'' ->
    find_label_in_procedure (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_procedure (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    (*
    inversion Hmerge as [_ _ _ _ _ _ _ _ _ Hwfp Hwfc _ Hwfc' Hmergeable_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof find_label_in_procedure_1 _ _ _ _ Hlabel as Hpc_.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hdomm; simpl in Hdomm.
    rewrite find_label_in_procedure_program_link_left in Hlabel;
      try assumption.
    unfold find_label_in_procedure in *.
    destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc_))
      as [C_procs |] eqn:Hcase; last discriminate.
    unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    rewrite genv_procedures_program_link_left_notin;
      try assumption.
    now rewrite Hcase.
  Qed.*)
  Admitted.

  (* Search _ PS.is_program_component Pointer.component. *)
  Lemma is_program_component_in_domm s s' s'' t t' t'' :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' t t' t'' ->
    CS.state_component s \in domm (prog_interface p).
  Proof.
    intros Hcomp Hmerge.
    unfold CS.is_program_component, CS.is_context_component, CS.state_turn, turn_of in Hcomp.
    destruct s as [[[gps1 mem1] regs1] pc1].
    (*
    inversion Hmerge as [s0 _ _ t _ _ _ _ _ Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ Hini _ _ Hstar _ _ _ _ _ _].
    destruct (CS.star_pc_domm_non_inform _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hip | Hic].
    - assumption.
    - now rewrite Hic in Hcomp.
  Qed.*)
  Admitted. *)
End Mergeable.

Ltac invert_mergeable_states_well_formed H :=
  let Hwfp               := fresh "Hwfp" in
  let Hwfc               := fresh "Hwfc" in
  let Hwfp'              := fresh "Hwfp'" in
  let Hwfc'              := fresh "Hwfc'" in
  let Hmerge_ipicq       := fresh "Hmerge_ipicq" in
  let Hifc_pp'           := fresh "Hifc_pp'" in
  let Hifc_cc'           := fresh "Hifc_cc'" in
  let Hclosed_prog       := fresh "Hclosed_prog" in
  let Hclosed_prog''     := fresh "Hclosed_prog'" in
  let Hgood_prog         := fresh "Hgood_prog" in
  let Hgood_prog''       := fresh "Hgood_prog''" in
  let Hpref_t            := fresh "Hpref_t" in
  let Hpref_t'           := fresh "Hpref_t'" in
  let Hpref_t''          := fresh "Hpref_t''" in
  (*let Hgood_mem          := fresh "Hgood_mem" in
  let Hgood_mem''        := fresh "Hgood_mem''" in
  let Hgood_mem'         := fresh "Hgood_mem'" in*)
  let Hgood_t            := fresh "Hgood_t" in
  let Hgood_t''          := fresh "Hgood_t''" in
  let Hgood_t'           := fresh "Hgood_t'" in
  let Hstack_s_s'        := fresh "Hstack_s_s'" in
  let Hstack_s''_s'      := fresh "Hstack_s''_s'" in
  let Hpccomp_s'_s       := fresh "Hpccomp_s'_s" in
  let Hpccomp_s'_s''     := fresh "Hpccomp_s'_s''" in
  let Hshift_tt'         := fresh "Hshift_tt'" in
  let Hshift_t''t'       := fresh "Hshift_t''t'" in
  inversion H
    as [
        Hwfp
          Hwfc
          Hwfp'
          Hwfc'
          Hmerge_ipic
          Hifc_pp'
          Hifc_cc'
          Hclosed_prog
          Hclosed_prog''
          Hgood_prog
          Hgood_prog''
          Hpref_t
          Hpref_t'
          Hpref_t''
          (*Hgood_mem
          Hgood_mem''
          Hgood_mem'*)
          Hgood_t
          Hgood_t''
          Hgood_t'
          Hstack_s_s'
          Hstack_s''_s'
          Hpccomp_s'_s
          Hpccomp_s'_s''
          Hshift_tt'
          Hshift_t''t'].

Ltac find_and_invert_mergeable_states_well_formed :=
  match goal with
  | H: mergeable_states_well_formed _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    invert_mergeable_states_well_formed H
  end.


Ltac invert_non_eagerly_mergeable_internal_states Hmergeinternal :=
  let Hmergewf := fresh "Hmergewf" in
  let Hpc      := fresh "Hpc"      in
  let H_p      := fresh "H_p"      in
  let Hregsp   := fresh "Hregsp"   in
  let Hmemp    := fresh "Hmemp"    in
  let Hmemc'   := fresh "Hmemc'"   in
  let Hregsc'  := fresh "Hregsc'"  in
  inversion Hmergeinternal as
      [Hmergewf Hpc H_p Hregsp Hmemp Hmemc' |
       Hmergewf Hpc H_c' Hregsc' Hmemc' Hmemp].


Ltac find_and_invert_mergeable_internal_states :=
  match goal with
  | H: mergeable_internal_states _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    invert_non_eagerly_mergeable_internal_states H
  end.

Section MergeableSymHelpers.

  Lemma if_sym {T: Type} P (eif: T) (eelse: T):
    (if P then eif else eelse) = (if ~~P then eelse else eif).
  Proof.
      by destruct P eqn:eP.
  Qed.

  Lemma if_sym_lambda {T: Type} P (eif eelse: nat_ordType -> T):
    (fun cid : nat_ordType =>
       if P cid then eif cid else eelse cid) =
    (fun cid : nat_ordType =>
       if ~~P cid then eelse cid else eif cid).
  Proof.
    apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
    intros ?. by apply if_sym.
  Qed.

  Lemma if_sym_lambda_prop {T: Type} PP P (eif eelse: nat_ordType -> T):
    PP (fun cid : nat_ordType =>
          if P cid then eif cid else eelse cid)
    <->
    PP (fun cid : nat_ordType =>
          if ~~P cid then eelse cid else eif cid).
  Proof.
    split; intros; rewrite if_sym_lambda; simpl; auto.
    assert (G: (fun cid : nat => if ~~ ~~ P cid then eif cid else eelse cid) =
               (fun cid : nat_ordType => if P cid then eif cid else eelse cid)
           ).
    {
      apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
      intros ?. by destruct (P x).
    }
    by rewrite G.
  Qed.

  Lemma if_sym_lambda_traces_rename_each_other P eif eelse:
    forall n t1 t2,
      traces_rename_each_other_option
        n
        (fun cid : nat_ordType =>
           if P cid then eif cid else eelse cid)
        t1
        t2
      <->
      traces_rename_each_other_option
        n
        (fun cid : nat_ordType =>
           if ~~P cid then eelse cid else eif cid)
        t1
        t2.
  Proof.
    intros.
    specialize (if_sym_lambda_prop
                  (fun lam => traces_rename_each_other_option n lam t1 t2)
                  P
                  eif
                  eelse
               ) as [Hsym1 Hsym2].
    split. intros PPlam; first (by apply Hsym1). by apply Hsym2.
  Qed.
      
  
  Lemma traces_rename_each_other_option_n'_if InP n n'' t'':
    forall t',
      traces_rename_each_other_option n''
                                      (fun cid : nat_ordType =>
                                         if InP cid
                                         (*\in domm (prog_interface p)*)
                                         then n cid else n'' cid)
                                      t'' t'
      ->
      forall InC',
        (forall addr, addr_shared_so_far addr t'' -> (InP addr.1 = negb (InC' addr.1)))
        ->
        (forall addr, addr_shared_so_far addr t' -> (InP addr.1 = negb (InC' addr.1)))
        ->
        traces_rename_each_other_option n''
                                        (fun cid : nat_ordType =>
                                           if InC' cid
                                           (*\in domm (prog_interface c')*)
                                           then n'' cid else n cid) t'' t'.
  Proof.
    induction t'' as [|t'' e''] using last_ind; intros t' Hren ? HPC'1 HPC'2;
      induction t' as [|t' e'] using last_ind.
    - constructor. 
    - by apply traces_rename_each_other_option_nil_rcons in Hren.
    - by apply traces_rename_each_other_option_rcons_nil in Hren.
    - inversion Hren as [| ? ? ? ? ? HrenIH Hshr1 Hshr2 ? Hval ? ? Hgood2];
        try by find_nil_rcons.
      repeat find_rcons_rcons.
      assert (HPC'1weak:
                forall addr : addr_t,
                  addr_shared_so_far addr t'' -> InP addr.1 = ~~ InC' addr.1).
      {
        intros ? Hshr.
        apply HPC'1. eapply reachable_from_previously_shared.
        - exact Hshr.
        - constructor. by rewrite in_fset1.
      }
      assert (HPC'2weak:
                forall addr : addr_t,
                  addr_shared_so_far addr t' -> InP addr.1 = ~~ InC' addr.1).
      {
        intros ? Hshr.
        apply HPC'2. eapply reachable_from_previously_shared.
        - exact Hshr.
        - constructor. by rewrite in_fset1.
      }
      specialize (IHt'' t' HrenIH _ HPC'1weak HPC'2weak).
      econstructor; auto.
      + intros [cid bid] Hshr.
        specialize (HPC'1 _ Hshr) as HPC'1a.
        specialize (Hshr1 _ Hshr) as [Hevent [[cid' bid'] [Hbid' Hshr']]].
        assert (exists addr' : addr_t,
                   sigma_shifting_wrap_bid_in_addr
                     (sigma_shifting_lefttoright_addr_bid
                        n''
                        (fun cid0 : nat_ordType =>
                           if InC' cid0 then n'' cid0 else n cid0))
                     (cid, bid) = Some addr'
                   /\ addr_shared_so_far addr' (rcons t' e'))
          as [[cid'_ bid'_] [Hcid'bid'_ Hshr'_]].
        {
          unfold sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          simpl in *. rewrite HPC'1a in Hbid'.
          destruct (sigma_shifting_lefttoright_option
                      (n'' cid)
                      (if ~~ InC' cid then n cid else n'' cid) bid) eqn:ebid;
            try discriminate; inversion Hbid'; subst.
          destruct (InC' cid') eqn:ecid'; simpl in *;
            rewrite ebid; eexists; split; by eauto.
        }
        split.
        * econstructor.
          split; first eauto.
          unfold
            event_renames_event_at_shared_addr,
          memory_renames_memory_at_shared_addr,
          rename_value_option, rename_value_template_option,
          rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          destruct Hevent as [? [eclear [G1 G2]]].
          rewrite Hbid' in eclear.
          inversion eclear; subst. clear eclear.
          rewrite HPC'1a in Hbid'.
          assert (cid'_ = cid' /\ bid'_ = bid') as [? ?]; subst.
          {
            destruct (InC' cid) eqn:ecid; rewrite ecid in Hbid'; simpl in *;
              rewrite Hbid' in Hcid'bid'_;
              symmetry in Hcid'bid'_;
              inversion Hcid'bid'_; subst; clear Hcid'bid'_; by auto.
          }
          split; intros ? ? Hload; simpl in *.
          -- specialize (G1 _ _ Hload) as [v' [Hloadv' Hv]].
             eexists; split; eauto.
             destruct v as [| [[[permv cidv] bidv] offv] |] eqn:ev; auto.
             destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
             assert (permv = Permission.data); subst. by apply/Permission.eqP.
             assert (Hshrv: addr_shared_so_far (cidv, bidv) (rcons t'' e'')).
             {
               inversion Hshr; subst; repeat find_rcons_rcons.
               - eapply reachable_from_args_is_shared.
                 unfold Memory.load in Hload; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G1; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
               - eapply reachable_from_previously_shared; eauto.
                 unfold Memory.load in Hload; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G1; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
             }
             specialize (HPC'1 _ Hshrv) as HPC'1v.
             rewrite HPC'1v in Hv.
             destruct (InC' cidv) eqn:ecidv; rewrite ecidv in Hv;
               by rewrite Hv.
          -- specialize (G2 _ _ Hload) as [v [Hloadv Hv]].
             eexists; split; eauto.
             destruct v as [| [[[permv cidv] bidv] offv] |] eqn:ev; auto.
             destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
             assert (permv = Permission.data); subst. by apply/Permission.eqP.
             assert (Hshrv: addr_shared_so_far (cidv, bidv) (rcons t'' e'')).
             {
               inversion Hshr; subst; repeat find_rcons_rcons.
               - eapply reachable_from_args_is_shared.
                 unfold Memory.load in Hloadv; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
               - eapply reachable_from_previously_shared; eauto.
                 unfold Memory.load in Hloadv; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
             }
             specialize (HPC'1 _ Hshrv) as HPC'1v.
             rewrite HPC'1v in Hv.
             destruct (InC' cidv) eqn:ecidv; rewrite ecidv in Hv;
               by rewrite Hv.
        * by eexists; split; eauto.
      + intros [cid bid] Hshr.
        specialize (HPC'2 _ Hshr) as HPC'2a.
        specialize (Hshr2 _ Hshr) as [[cid' bid'] [Hbid' [Hevent Hshr']]].
        unfold sigma_shifting_wrap_bid_in_addr,
        sigma_shifting_lefttoright_addr_bid in *.
        simpl in *.
        destruct (sigma_shifting_lefttoright_option
                    (n'' cid')
                    (if InP cid' then n cid' else n'' cid') bid') eqn:ebid';
          try discriminate; inversion Hbid'; subst.
        rewrite HPC'2a in ebid'.
        exists (cid, bid').
        split.
        * destruct (InC' cid) eqn:ecid; simpl in *;
            rewrite ebid'; by eauto.
        * split; last assumption.
          econstructor.
          split.
          -- unfold sigma_shifting_wrap_bid_in_addr,
             sigma_shifting_lefttoright_addr_bid in *.
             destruct (InC' cid); rewrite ebid'; eauto.
          -- unfold
               event_renames_event_at_shared_addr,
             memory_renames_memory_at_shared_addr,
             rename_value_option, rename_value_template_option,
             rename_addr_option,
             sigma_shifting_wrap_bid_in_addr,
             sigma_shifting_lefttoright_addr_bid in *.
             destruct Hevent as [? [eclear [G1 G2]]].
             rewrite HPC'2a in eclear.
             assert (x = (cid, bid)); subst.
             {
               destruct (InC' cid); rewrite ebid' in eclear; by inversion eclear.
             }
             split; intros ? ? Hload; simpl in *.
             ++ specialize (G1 _ _ Hload) as [v' [Hloadv' Hv]].
                eexists; split; eauto.
                destruct v as [| [[[permv cidv] bidv] offv] |] eqn:ev; auto.
                destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
                assert (permv = Permission.data); subst. by apply/Permission.eqP.
                assert (Hshrv: addr_shared_so_far (cidv, bidv) (rcons t'' e'')).
                {
                  inversion Hshr'; subst; repeat find_rcons_rcons.
                  - eapply reachable_from_args_is_shared.
                    unfold Memory.load in Hload; simpl in *.
                    destruct (mem_of_event e'' cid) eqn:G1; try discriminate.
                    eapply Reachable_step; eauto.
                    rewrite Extra.In_in.
                    apply ComponentMemory.load_block_load.
                    do 2 eexists. by eauto.
                  - eapply reachable_from_previously_shared; eauto.
                    unfold Memory.load in Hload; simpl in *.
                    destruct (mem_of_event e'' cid) eqn:G1; try discriminate.
                    eapply Reachable_step; eauto.
                    rewrite Extra.In_in.
                    apply ComponentMemory.load_block_load.
                    do 2 eexists. by eauto.
                }
                specialize (HPC'1 _ Hshrv) as HPC'1v.
                rewrite HPC'1v in Hv.
                destruct (InC' cidv) eqn:ecidv; rewrite ecidv in Hv;
                  by rewrite Hv.
             ++ specialize (G2 _ _ Hload) as [v [Hloadv Hv]].
             eexists; split; eauto.
             destruct v as [| [[[permv cidv] bidv] offv] |] eqn:ev; auto.
             destruct (Permission.eqb permv Permission.data) eqn:epermv; auto.
             assert (permv = Permission.data); subst. by apply/Permission.eqP.
             assert (Hshrv: addr_shared_so_far (cidv, bidv) (rcons t'' e'')).
             {
               inversion Hshr'; subst; repeat find_rcons_rcons.
               - eapply reachable_from_args_is_shared.
                 unfold Memory.load in Hloadv; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
               - eapply reachable_from_previously_shared; eauto.
                 unfold Memory.load in Hloadv; simpl in *.
                 destruct (mem_of_event e'' cid) eqn:G; try discriminate.
                 eapply Reachable_step; eauto.
                 rewrite Extra.In_in.
                 apply ComponentMemory.load_block_load.
                 do 2 eexists. by eauto.
             }
             specialize (HPC'1 _ Hshrv) as HPC'1v.
             rewrite HPC'1v in Hv.
             destruct (InC' cidv) eqn:ecidv; rewrite ecidv in Hv;
               by rewrite Hv.
      + destruct (arg_of_event e'') as [| [[[perm cid] bid] off] |] eqn:ev.
        * rewrite rename_value_option_arg_Int.
          by rewrite rename_value_option_arg_Int in Hval.
        * unfold rename_value_option, rename_value_template_option,
          rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          destruct (Permission.eqb perm Permission.data) eqn:eperm; last assumption.
          assert (Hshr: addr_shared_so_far (cid, bid) (rcons t'' e'')).
          {
            apply reachable_from_args_is_shared.
            rewrite ev. simpl. rewrite eperm. constructor.
            by rewrite in_fset1.
          }
          specialize (HPC'1 _ Hshr). simpl in *. rewrite HPC'1 in Hval.
          destruct (sigma_shifting_lefttoright_option
                      (n'' cid)
                      (if ~~ InC' cid then n cid else n'' cid) bid) eqn:ebid;
            last discriminate.
          rewrite <- Hval.
          destruct (InC' cid) eqn:ecid; simpl in *; by rewrite ebid.
        * rewrite rename_value_option_arg_Undef.
          by rewrite rename_value_option_arg_Undef in Hval.
      + constructor. intros [cid bid] Hshr. specialize (HPC'2 _ Hshr).
        inversion Hgood2 as [? G]; subst. specialize (G _ Hshr).
        simpl in *. unfold right_block_id_good_for_shifting in *.
        rewrite HPC'2 in G. by destruct (InC' cid).
  Qed.


  Lemma regs_rel_of_executing_part_sym InP n n'' regs regs':
    regs_rel_of_executing_part
      regs
      regs'
      n
      (fun cid : nat_ordType => if InP cid then n cid else n'' cid)
    ->
    forall InC',
      (
        forall (reg : register) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Register.get reg regs = Ptr (perm, cid, bid, off) ->
          InP cid = negb (InC' cid)
      )
      ->
      (
        forall (reg : register) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Register.get reg regs' = Ptr (perm, cid, bid, off) ->
          InP cid = negb (InC' cid)
      )
      ->
      regs_rel_of_executing_part
        regs
        regs'
        n
        (fun cid : nat_ordType => if InC' cid then n'' cid else n cid).
  Proof.
    intros Hregsp InC' Hreg Hreg'.
    constructor.
    inversion Hregsp as [Hregsrel].
    unfold
      shift_value_option,
    rename_value_option,
    rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid in *.

    simpl in *. intros reg. specialize (Hregsrel reg).
    destruct (Register.get reg regs)
      as [| [[[perm1 cid1] bid1] off1] | ] eqn:eregs1; try by left; intuition.
    destruct (Permission.eqb perm1 Permission.data) eqn:eperm; try by left; intuition.
    destruct (sigma_shifting_lefttoright_option
                (n cid1)
                (if InC' cid1
                 then n'' cid1 else n cid1) bid1) as [bid1'|] eqn:ebid1'.
    * specialize (Hreg _ _ _ _ _ eregs1) as Hcid1_eqn.
      destruct (InP cid1) eqn:Hcid1.
      -- assert (Hc: InC' cid1 = false).
         {
             by destruct (InC' cid1) eqn:e; auto.
         }
         rewrite Hc in ebid1'. rewrite ebid1' in Hregsrel.
         destruct Hregsrel as [inv| [Hcontra ?]]; last discriminate.
         inversion inv as [rewr]. by left.
      -- assert (Hc: InC' cid1 = true).
         {
           by destruct (InC' cid1) eqn:e; auto.
         }
         rewrite Hc in ebid1'. rewrite ebid1' in Hregsrel.
         destruct Hregsrel as [inv| [Hcontra ?]]; last discriminate.
         inversion inv as [rewr]. by left.
         
    * assert (HNone2: sigma_shifting_lefttoright_option
                        (n cid1)
                        (if InP cid1
                         then n cid1 else n'' cid1) bid1 = None).
      { by eapply sigma_shifting_lefttoright_option_None_None; eauto. }
      rewrite HNone2 in Hregsrel.
      assert (rewr: Register.get reg regs' = Ptr (perm1, cid1, bid1, off1)).
      {
          by destruct Hregsrel as [| [? [? ?]]]; try discriminate; auto.
      }
      destruct Hregsrel as [| [? [G2 G3]]]; try discriminate.
      rewrite rewr eperm in G2. rewrite rewr eperm.
      right. split; last split; auto.
      specialize (Hreg' _ _ _ _ _ rewr).
      destruct (InP cid1) eqn:Hcid1.
      --
        assert (Hc: InC' cid1 = false).
        {
           by destruct (InC' cid1) eqn:e; auto.
        }
        rewrite Hc in ebid1'. by rewrite Hc ebid1'.
      --
        assert (Hc: InC' cid1 = true).
        {
           by destruct (InC' cid1) eqn:e; auto.
        }
        by rewrite Hc.
  Qed.
    
  Lemma memory_shifts_memory_at_private_addr_sym InP n n'' mem mem' original_addr:
    memory_shifts_memory_at_private_addr
      n
      (fun cid : nat_ordType =>
         if InP cid then n cid else n'' cid)
      original_addr
      mem
      mem'
    ->
    forall (InC': nat_ordType -> bool),
      (
        forall (ptr : Pointer.t) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Memory.load mem ptr = Some (Ptr (perm, cid, bid, off)) ->
          InP cid = negb (InC' cid)
      )
      ->
      (
        forall (ptr : Pointer.t) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Memory.load mem' ptr = Some (Ptr (perm, cid, bid, off)) ->
          InP cid = negb (InC' cid)
      )
      ->
      memory_shifts_memory_at_private_addr
        n
        (fun cid : nat_ordType =>
           if InC' cid then n'' cid else n cid)
        original_addr
        mem
        mem'.
  Proof.
  intros [G1a G1b] InC' Hmem Hmem'.
  constructor; intros ? ? Hload;
    unfold rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid in *;
    simpl in *.
  * specialize (G1a _ _ Hload) as Hvv'.
    destruct v as [| [[[perm cid] bid] off] |]; auto.
    destruct (Permission.eqb perm Permission.data) eqn:eperm; auto.
    specialize (Hmem _ _ _ _ _ Hload) as Hcid_eqn.
    destruct (InP cid) eqn:Hcid.
    -- assert (InC' cid = false) as Hc'.
       {
         destruct (InC' cid) eqn:e; auto.
       }
         by rewrite Hc'.
    -- assert (InC' cid = true) as Hc'.
       {
         destruct (InC' cid) eqn:e; auto.
       }
         by rewrite Hc'.
  * specialize (G1b _ _ Hload) as [v [Hloadv Hvv']].
    eexists; split; first eassumption.
    destruct v as [| [[[perm cid] bid] off] |];
      try by (destruct Hvv' as [[Hcontra _]|];
              first discriminate; right).
    destruct (Permission.eqb perm Permission.data) eqn:eperm;
      try by (destruct Hvv' as [[Hcontra _]|];
              first discriminate; right).
    destruct Hvv' as [[G [G' ?]]|G]; subst.
    -- left. specialize (Hmem' _ _ _ _ _ Hload) as Hcid_eqn.
       destruct (InP cid) eqn:Hcid.
       ++
         rewrite eperm in G'. 
         assert (InC' cid = false) as Hc'.
         {
           destruct (InC' cid) eqn:e; auto.
         }
           by rewrite Hc' G eperm.
       ++
         assert (InC' cid = true) as Hc'.
         {
           destruct (InC' cid) eqn:e; auto.
         }
       
         rewrite eperm in G'. rewrite Hc'. rewrite eperm G'.
           by rewrite G.
    -- right. specialize (Hmem _ _ _ _ _ Hloadv) as Hcid_eqn.
       destruct (InP cid) eqn:Hcid.
       ++
         assert (InC' cid = false) as Hc'.
         {
           destruct (InC' cid) eqn:e; auto.
         }
           by rewrite Hc'.
       ++
         assert (InC' cid = true) as Hc'.
         {
           destruct (InC' cid) eqn:e; auto.
         }
           by rewrite Hc'.
  Qed.

  Lemma memory_shifts_memory_at_shared_addr_sym InP n n'' mem mem' cidorig bidorig:
    memory_shifts_memory_at_shared_addr
      n
      (fun cid : nat_ordType => if InP cid then n cid else n'' cid)
      (cidorig, bidorig)
      mem
      mem'
    ->
    forall InC',
      InP cidorig = negb (InC' cidorig)
      ->
            (
        forall (ptr : Pointer.t) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Memory.load mem ptr = Some (Ptr (perm, cid, bid, off)) ->
          InP cid = negb (InC' cid)
      )
      ->
      (
        forall (ptr : Pointer.t) (perm : Permission.id) (cid : Component.id) 
               (bid : Block.id) (off : Block.offset),
          Memory.load mem' ptr = Some (Ptr (perm, cid, bid, off)) ->
          InP cid = negb (InC' cid)
      )
      ->
      memory_shifts_memory_at_shared_addr
        n
        (fun cid : nat_ordType => if InC' cid then n'' cid else n cid)
        (cidorig, bidorig)
        mem
        mem'.
  Proof.
    intros [[cidorig' bidorig'] [G2a [G2b G2c]]] InC' Hshr_partition_eqn Hmem Hmem'.
    unfold rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid in *.
    simpl in *.
    
    destruct (sigma_shifting_lefttoright_option
                (n cidorig)
                (if InP cidorig
                 then n cidorig
                 else n'' cidorig) bidorig)
      as [bidorig'_|] eqn:ebidorig';
      last discriminate.
    inversion G2a; subst; clear G2a.

    econstructor.
    unfold rename_value_option, rename_value_template_option,
    rename_addr_option,
    sigma_shifting_wrap_bid_in_addr,
    sigma_shifting_lefttoright_addr_bid in *.
    simpl in *.

    split; last split.
    --
      destruct (InP cidorig') eqn:Hcid.
      ++ assert (InC' cidorig' = false) as Hc'.
         { by destruct (InC' cidorig'); auto. }
           by rewrite Hc' ebidorig'.
      ++ assert (InC' cidorig' = true) as Hc'.
         { by destruct (InC' cidorig'); auto. }
           by rewrite Hc' ebidorig'.
    -- intros ? ? Hload.
       specialize (G2b _ _ Hload) as [v' [Hloadv' Hvv']].
       exists v'. split; first assumption.
       destruct v as [ | [[[perm cid] bid] off] | ];
         first assumption; last assumption.
       destruct (Permission.eqb perm Permission.data) eqn:eperm; last assumption.
       specialize (Hmem _ _ _ _ _ Hload) as Hcid_eqn.
       destruct (InP cid) eqn:Hcid.
       ++ assert (InC' cid = false) as Hc'.
          { by destruct (InC' cid); auto. }
            by rewrite Hc'.
       ++ assert (InC' cid = true) as Hc'.
          { by destruct (InC' cid); auto. }
          by rewrite Hc'.
    -- intros ? ? Hload.
       specialize (G2c _ _ Hload) as [v [Hloadv Hvv']].
       exists v. split; first assumption.
       destruct v as [ | [[[perm cid] bid] off] | ];
         first assumption; last assumption.
       destruct (Permission.eqb perm Permission.data) eqn:eperm; last assumption.
       destruct (sigma_shifting_lefttoright_option
                   (n cid)
                   (if InP cid
                    then n cid else n'' cid) bid) as [bid'|] eqn:ebid';
         last discriminate.
       inversion Hvv'; subst; clear Hvv'.
       specialize (Hmem' _ _ _ _ _ Hload) as Hcid_eqn.
       destruct (InP cid) eqn:Hcid.
       ++ assert (InC' cid = false) as Hc'.
          { by destruct (InC' cid); auto. }
            by rewrite Hc' ebid'.
       ++ assert (InC' cid = true) as Hc'.
          { by destruct (InC' cid); auto. }
          by rewrite Hc' ebid'.
  Qed.          
    
End MergeableSymHelpers.

Section MergeableSym.

  Variables p c p' c' : program.

  Variables n n'': Component.id -> nat.

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

  Lemma mergeable_states_well_formed_sym s s' s'' t t' t'':
    mergeable_states_well_formed p c p' c' n n'' s s' s'' t t' t'' ->
    mergeable_states_well_formed c' p' c p n'' n s'' s' s t'' t' t.
  Proof.
    intros Hwf. find_and_invert_mergeable_states_well_formed.
    assert (Hlinkable: linkable (prog_interface p) (prog_interface c)).
    { unfold mergeable_interfaces in *; intuition. }
    assert (Hmergeable_ifcs: mergeable_interfaces
                               (prog_interface c')
                               (prog_interface p')).
    { apply mergeable_interfaces_sym. by rewrite <- Hifc_cc', <- Hifc_pp'. }
    assert (Hmergeable_ifcs2: mergeable_interfaces
                                (prog_interface c)
                                (prog_interface p)).
    { by apply mergeable_interfaces_sym. }
    assert (eprog'': program_link c' p' = program_link p' c').
    { rewrite program_linkC; auto. by unfold mergeable_interfaces in *; intuition. }
    assert (eprog: program_link c p = program_link p c).
    { rewrite program_linkC; auto. by unfold mergeable_interfaces in *; intuition. }
    assert (eprog': program_link c' p = program_link p c').
    {
      rewrite program_linkC; auto.
      by rewrite <- Hifc_cc'; unfold mergeable_interfaces in *; intuition.
    }

    assert (prog'_closed: closed_program (program_link p c')).
    {
      eapply interface_preserves_closedness_r; eauto.
      - eapply linkable_implies_linkable_mains; eauto.
      - eapply interface_implies_matching_mains; eauto.
    }
    
    assert (prog_wf: well_formed_program prog).
    {
      eapply linking_well_formedness; eauto.
    }
    
    assert (prog'_wf: well_formed_program (program_link p c')).
    {
      eapply linking_well_formedness; eauto. by rewrite <- Hifc_cc'. 
    }

    assert (prog''_wf: well_formed_program prog'').
    {
      eapply linking_well_formedness; eauto. by rewrite <- Hifc_cc', <- Hifc_pp'.
    }

    assert (Hdisj: fdisjoint (domm (prog_interface p)) (domm (prog_interface c'))).
    {
      unfold linkable in *. by rewrite <- Hifc_cc'; intuition.
    }
    constructor; auto.
    - by rewrite eprog''.
    - by rewrite eprog.
    - by rewrite eprog''.
    - by rewrite eprog.
    - by rewrite eprog''.
    - by rewrite eprog'.
    - by rewrite eprog.
    - (** tricky *)
      (** We will likely need a CSInvariant that ensures *)
      (** all the addresses appearing in the memory      *)
      (** have a cid \in unionm (domm (prog_interface p))*)
      (**                       (domm (prog_interface c))*)
      constructor.
      intros [acid abid] Hshr.
      rewrite Hifc_cc' in Hmerge_ipic.
      specialize (CSInvariants.addr_shared_so_far_domm_partition
                    _ _ _ _ _ _ Hwfp Hwfc' Hmerge_ipic Hpref_t' prog'_closed prog'_wf Hshr Logic.eq_refl)
        as [Hacid | Hacid]; simpl in *.
      + move : Hdisj => /fdisjointP => Hdisj.
        specialize (Hdisj _ Hacid).
        assert (cond: acid \in domm (prog_interface c') = false).
        {
            by destruct (acid \in domm (prog_interface c')) eqn:e; auto;
            by rewrite e in Hdisj.
        }
        rewrite cond.
        inversion Hgood_t' as [? G]; subst.
        specialize (G _ Hshr). simpl in *. by rewrite Hacid in G.
      + rewrite fdisjointC in Hdisj.
        move : Hdisj => /fdisjointP => Hdisj.
        specialize (Hdisj _ Hacid).
        rewrite Hacid.
        inversion Hgood_t' as [? G]; subst.
        specialize (G _ Hshr). simpl in *.
        assert (cond: acid \in domm (prog_interface p) = false).
        {
            by destruct (acid \in domm (prog_interface p)) eqn:e; auto;
            by rewrite e in Hdisj.
        }
        by rewrite cond in G.
        
    - (** tricky for the same reason as above.            *)
      constructor.
      eapply traces_rename_each_other_option_n'_if.
      + inversion Hshift_t''t' as [? ? Hren]; subst.
        exact Hren.
      + intros [cid bid] Hshr''. simpl.
        rewrite Hifc_pp' Hifc_cc' in Hmerge_ipic.
        destruct (cid \in domm (prog_interface p)) eqn:ecid; rewrite ecid.
        * move : Hdisj => /fdisjointP => Hdisj.
          by apply Hdisj in ecid.
        * rewrite fdisjointC in Hdisj.
          move : Hdisj => /fdisjointP => Hdisj.
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic Hpref_t'' Hclosed_prog' prog''_wf Hshr'' Logic.eq_refl)
            as [Hacid | Hacid]; simpl in *.
          -- by rewrite Hifc_pp' Hacid in ecid.
          -- by rewrite Hacid.
      + intros [cid bid] Hshr'. simpl.
        destruct (cid \in domm (prog_interface p)) eqn:ecid; rewrite ecid.
        * move : Hdisj => /fdisjointP => Hdisj.
          by apply Hdisj in ecid.
        * rewrite fdisjointC in Hdisj.
          move : Hdisj => /fdisjointP => Hdisj.
          rewrite Hifc_cc' in Hmerge_ipic.
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc' Hmerge_ipic Hpref_t' prog'_closed prog'_wf Hshr' Logic.eq_refl)
            as [Hacid | Hacid]; simpl in *.
          -- by rewrite Hacid in ecid.
          -- by rewrite Hacid.
    - (** tricky for the same reason as above + the need to use
          if_sym_lambda_traces_rename_each_other
       *)
      constructor.
      specialize (if_sym_lambda_traces_rename_each_other
                    (fun cid: nat_ordType => cid \in domm (prog_interface c'))
                    n''
                    n
                 ) as rewr.
      simpl in rewr. rewrite rewr.
      eapply traces_rename_each_other_option_n'_if.
      + inversion Hshift_tt' as [? ? Hren]; subst.
        apply if_sym_lambda_traces_rename_each_other in Hren.
        exact Hren.
      + intros [cid bid] Hshr. simpl.
        destruct (cid \in domm (prog_interface p)) eqn:ecid; rewrite ecid; simpl.
        * move : Hdisj => /fdisjointP => Hdisj.
          apply Hdisj in ecid. by rewrite ecid.
        * rewrite fdisjointC in Hdisj.
          move : Hdisj => /fdisjointP => Hdisj.
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hpref_t Hclosed_prog
                        prog_wf Hshr Logic.eq_refl)
            as [Hacid | Hacid]; simpl in *.
          -- by rewrite Hacid in ecid.
          -- by rewrite <- Hifc_cc', Hacid.
      + intros [cid bid] Hshr'. simpl.
        destruct (cid \in domm (prog_interface p)) eqn:ecid; rewrite ecid; simpl.
        * move : Hdisj => /fdisjointP => Hdisj.
          apply Hdisj in ecid. by rewrite ecid.
        * rewrite fdisjointC in Hdisj.
          move : Hdisj => /fdisjointP => Hdisj.
          rewrite Hifc_cc' in Hmerge_ipic.
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc' Hmerge_ipic Hpref_t' prog'_closed
                        prog'_wf Hshr' Logic.eq_refl)
            as [Hacid | Hacid]; simpl in *.
          -- by rewrite Hacid in ecid.
          -- by rewrite Hacid.
  Qed.

  Lemma mergeable_internal_states_sym s s' s'' t t' t'':
    mergeable_internal_states p c p' c' n n'' s s' s'' t t' t'' ->
    mergeable_internal_states c' p' c p n'' n s'' s' s t'' t' t.
  Proof.
    intros Hmerge.
    find_and_invert_mergeable_internal_states;
      (
        find_and_invert_mergeable_states_well_formed;
        unfold mergeable_interfaces in *;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hclosed_prog Hpref_t Logic.eq_refl Logic.eq_refl
                   ) as [Hmem Hreg];
        assert (Hclosed_pc' : closed_program (program_link p c'))
        by (
            eapply interface_preserves_closedness_r; eauto;
            first (intuition);
            first (eapply linkable_implies_linkable_mains; intuition);
            eapply interface_implies_matching_mains; intuition
          );
        rewrite Hifc_cc' in Hmerge_ipic;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp Hwfc' Hmerge_ipic Hclosed_pc' Hpref_t' Logic.eq_refl Logic.eq_refl
                   ) as [Hmem' Hreg'];
        rewrite Hifc_pp' in Hmerge_ipic;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic Hclosed_prog' Hpref_t'' Logic.eq_refl Logic.eq_refl
                   ) as [Hmem'' Hreg''];
        rewrite -Hifc_pp' -Hifc_cc' in Hmerge_ipic
      ).

    - apply mergeable_internal_states_c'_executing; auto.
      + by apply mergeable_states_well_formed_sym.
      + CS.unfold_states.
        CS.simplify_turn. subst. simpl in *.
        rewrite <- Hifc_pp'. by eapply mergeable_states_notin_to_in2; eauto.
      + (** Follows from Hregsp            *)
        apply regs_rel_of_executing_part_sym
          with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg _ _ _ _ _ Hget) as [G | G].
          -- rewrite -Hifc_cc'. 
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
             destruct (cid \in domm (prog_interface p)) eqn:e; auto.
               by rewrite e in G'.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'. 
          -- rewrite -Hifc_cc' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
             destruct (cid \in domm (prog_interface p)) eqn:e; auto.
               by rewrite e in G'.
      + (** Follows from Hmemp.     *)
        assert (prog_wf: well_formed_program prog).
          { apply linking_well_formedness; auto.
              by unfold mergeable_interfaces in *; intuition. }
        destruct Hmemp as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. 
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr).
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hpref_t Hclosed_prog
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. 
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
                
      + (** Follows from Hmemc'            *)
        destruct Hmemc' as [G1 G2].
        constructor; auto.
        intros [cidorig bidorig] Hcidorig Hnotshr''.
        specialize (G1 _  Hcidorig Hnotshr'').
        rewrite if_sym_lambda.
        rewrite if_sym_lambda in G1.
        apply memory_shifts_memory_at_private_addr_sym
          with (InP := fun cid => cid \notin domm (prog_interface p));
          first assumption.
        * intros ? ? ? ? ? Hload.
          specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
          -- rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- rewrite -Hifc_cc' in G. rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
        * intros ? ? ? ? ? Hload.
          specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
          -- rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'. 
          -- rewrite -Hifc_cc' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite -Hifc_cc' G G'.

    - apply mergeable_internal_states_p_executing; auto.
      + by apply mergeable_states_well_formed_sym.
      + CS.unfold_states.
        CS.simplify_turn. subst.
        rewrite <- Hifc_pp', Hpccomp_s'_s. eapply mergeable_states_in_to_notin; eauto.
        by rewrite <- Hpccomp_s'_s.
      +
        (** Follows from Hregsc'            *)
        rewrite if_sym_lambda. rewrite if_sym_lambda in Hregsc'.
        apply regs_rel_of_executing_part_sym
          with (InP := fun cid => cid \notin domm (prog_interface p)); first assumption.

        * intros ? ? ? ? ? Hget.
          specialize (Hreg'' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- rewrite -Hifc_cc' in G. rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'. 
          -- rewrite -Hifc_cc' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite -Hifc_cc' G G'.

      + (** tricky for the same reason as above,            *)
        (** but should follow from Hmemc'                   *)
        assert (prog_wf: well_formed_program prog'').
          { apply linking_well_formedness; auto.
              by rewrite -Hifc_cc' -Hifc_pp';
                unfold mergeable_interfaces in *; intuition. }
        destruct Hmemc' as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          rewrite if_sym_lambda.
          rewrite if_sym_lambda in G1.
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G. rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite -Hifc_cc' G G'.
        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr). 
          assert (Hmerge_ipic'':
                    mergeable_interfaces (prog_interface p') (prog_interface c')).
          {
              by rewrite -Hifc_cc' -Hifc_pp'; unfold mergeable_interfaces.
          }
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic'' Hpref_t''
                        Hclosed_prog'
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          rewrite if_sym_lambda. rewrite if_sym_lambda in G2.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                
      + destruct Hmemp as [G1 G2].
        constructor; auto.
        intros [cidorig bidorig] Hcidorig Hnotshr''.
        specialize (G1 _  Hcidorig Hnotshr'').
        eapply memory_shifts_memory_at_private_addr_sym; first exact G1.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'. 
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'.
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'. 
           ++ rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.
  Qed.

  Lemma mergeable_border_states_sym s s' s'' t t' t'':
    mergeable_border_states p c p' c' n n'' s s' s'' t t' t'' ->
    mergeable_border_states c' p' c p n'' n s'' s' s t'' t' t.
  Proof.
    intros Hmerge.
    specialize (mergeable_border_mergeable_internal Hmerge) as Hmerge_internal.
    invert_non_eagerly_mergeable_border_states Hmerge;

      (
        find_and_invert_mergeable_states_well_formed;
        unfold mergeable_interfaces in *;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hclosed_prog Hpref_t Logic.eq_refl Logic.eq_refl
                   ) as [Hmem Hreg];
        assert (Hclosed_pc' : closed_program (program_link p c'))
        by (
            eapply interface_preserves_closedness_r; eauto;
            first (intuition);
            first (eapply linkable_implies_linkable_mains; intuition);
            eapply interface_implies_matching_mains; intuition
          );
        rewrite Hifc_cc' in Hmerge_ipic;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp Hwfc' Hmerge_ipic Hclosed_pc' Hpref_t' Logic.eq_refl Logic.eq_refl
                   ) as [Hmem' Hreg'];
        rewrite Hifc_pp' in Hmerge_ipic;
        specialize (CSInvariants.value_mem_reg_domm_partition
                      _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic Hclosed_prog' Hpref_t'' Logic.eq_refl Logic.eq_refl
                   ) as [Hmem'' Hreg''];
        rewrite -Hifc_pp' -Hifc_cc' in Hmerge_ipic
      ).


    - apply mergeable_border_states_c'_executing; auto.
      + by apply mergeable_states_well_formed_sym.
      + CS.unfold_states.
        CS.simplify_turn. subst.
        rewrite <- Hifc_pp'. by eapply mergeable_states_notin_to_in2; eauto.
      + (** Follows from Hregsp.            *)
        apply regs_rel_of_executing_part_sym
          with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg _ _ _ _ _ Hget) as [G | G].
          -- rewrite -Hifc_cc'. 
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
             destruct (cid \in domm (prog_interface p)) eqn:e; auto.
               by rewrite e in G'.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'. 
          -- rewrite -Hifc_cc' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
             destruct (cid \in domm (prog_interface p)) eqn:e; auto.
               by rewrite e in G'.

      + (** Follows from Hmemp.           *)
        assert (prog_wf: well_formed_program prog).
        { apply linking_well_formedness; auto.
            by unfold mergeable_interfaces in *; intuition. }
        destruct Hmemp as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'. 
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'.
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'. 
           ++ rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.

        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr).
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hpref_t Hclosed_prog
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. 
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
                  

      + (** tricky for the same reason as above,            *)
        (** but should follow from Hmemc'                   *)
        assert (prog_wf: well_formed_program prog'').
        { apply linking_well_formedness; auto.
            by rewrite -Hifc_cc' -Hifc_pp';
              unfold mergeable_interfaces in *; intuition. }
        destruct Hmemc' as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          rewrite if_sym_lambda. rewrite if_sym_lambda in G1.
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'.
           ++ rewrite -Hifc_cc'. rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'. 
           ++ rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.

        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr). 
          assert (Hmerge_ipic'':
                    mergeable_interfaces (prog_interface p') (prog_interface c')).
          {
              by rewrite -Hifc_cc' -Hifc_pp'; unfold mergeable_interfaces.
          }
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic'' Hpref_t''
                        Hclosed_prog'
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          rewrite if_sym_lambda. rewrite if_sym_lambda in G2.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
          

    - apply mergeable_border_states_p_executing; auto.
      + by apply mergeable_states_well_formed_sym.
      + CS.unfold_states.
        CS.simplify_turn. subst.
        rewrite <- Hifc_pp'.
        rewrite Hpccomp_s'_s.
        eapply mergeable_states_in_to_notin; eauto.
        by rewrite <- Hpccomp_s'_s.
      + (** Follows from Hregsc'            *)
        rewrite if_sym_lambda. rewrite if_sym_lambda in Hregsc'.
        apply regs_rel_of_executing_part_sym
          with (InP := fun cid => cid \notin domm (prog_interface p)); first assumption.

        * intros ? ? ? ? ? Hget.
          specialize (Hreg'' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
          -- rewrite -Hifc_cc' in G. rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'.
        * intros ? ? ? ? ? Hget.
          specialize (Hreg' _ _ _ _ _ Hget) as [G|G].
          -- rewrite -Hifc_cc'.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite G G'. 
          -- rewrite -Hifc_cc' in G.
             unfold mergeable_interfaces, linkable in *.
             destruct Hmerge_ipic as [[_ Hdisj] _].
             rewrite fdisjointC in Hdisj.
             move : Hdisj => /fdisjointP => Hdisj.
             specialize (Hdisj _ G) as G'. by rewrite -Hifc_cc' G G'.

      + (** tricky for the same reason as above,            *)
        (** but should follow from Hmemc'                   *)
        assert (prog_wf: well_formed_program prog'').
        { apply linking_well_formedness; auto.
            by rewrite -Hifc_cc' -Hifc_pp';
              unfold mergeable_interfaces in *; intuition. }
        destruct Hmemc' as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          rewrite if_sym_lambda. rewrite if_sym_lambda in G1.
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'.
           ++ rewrite -Hifc_cc'. rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'. 
           ++ rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.

        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr). 
          assert (Hmerge_ipic'':
                    mergeable_interfaces (prog_interface p') (prog_interface c')).
          {
              by rewrite -Hifc_cc' -Hifc_pp'; unfold mergeable_interfaces.
          }
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp' Hwfc' Hmerge_ipic'' Hpref_t''
                        Hclosed_prog'
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          rewrite if_sym_lambda. rewrite if_sym_lambda in G2.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \notin domm (prog_interface p));
            first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem'' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. rewrite -Hifc_pp' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
          
      + (** tricky for the same reason as above,            *)
        (** but should follow from Hmemp                    *)
        assert (prog_wf: well_formed_program prog).
        { apply linking_well_formedness; auto.
            by unfold mergeable_interfaces in *; intuition. }
       
        destruct Hmemp as [G1 [G2 G3]].
        split; last split; last assumption.
        * intros ? Horig.
          specialize (G1 _ Horig).
          apply memory_shifts_memory_at_private_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'. 
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'.
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.
        -- intros ? ? ? ? ? Hload.
           specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
           ++ rewrite -Hifc_cc'.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. by rewrite G G'. 
           ++ rewrite -Hifc_cc' in G.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hdisj] _].
              rewrite fdisjointC in Hdisj.
              move : Hdisj => /fdisjointP => Hdisj.
              specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
              destruct (cid \in domm (prog_interface p)) eqn:e; auto.
              by rewrite e in G'.

        * intros [cidorig bidorig] Hshr.
          specialize (G2 _ Hshr).
          specialize (CSInvariants.addr_shared_so_far_domm_partition
                        _ _ _ _ _ _ Hwfp Hwfc Hmerge_ipic Hpref_t Hclosed_prog
                        prog_wf Hshr Logic.eq_refl
                     ) as Hshr_partition.
          apply memory_shifts_memory_at_shared_addr_sym
            with (InP := fun cid => cid \in domm (prog_interface p)); first assumption.
          -- simpl in *. rewrite -Hifc_cc'.
             destruct Hshr_partition as [G | G].
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite G.
                destruct (cidorig \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'. 
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'. 
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'.
             ++ unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
          -- intros ? ? ? ? ? Hload.
             specialize (Hmem' _ _ _ _ _ Hload) as [G|G].
             ++ rewrite -Hifc_cc'.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. by rewrite G G'. 
             ++ rewrite -Hifc_cc' in G.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hdisj] _].
                rewrite fdisjointC in Hdisj.
                move : Hdisj => /fdisjointP => Hdisj.
                specialize (Hdisj _ G) as G'. rewrite -Hifc_cc' G.
                destruct (cid \in domm (prog_interface p)) eqn:e; auto.
                by rewrite e in G'.
                  
  Qed.

End MergeableSym.

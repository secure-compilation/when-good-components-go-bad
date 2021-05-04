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

Section UnaryHelpersForMergeable.

  (* An inductive definition to relate a program with the pointers found in its
     buffers and procedures. A computational definition can be given as well.
     NOTE: Unnecessary? *)
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
  
End UnaryHelpersForMergeable.

Section BinaryHelpersForMergeable.

  (* n is the metadata size of the LHS program, n' of the RHS program. *)
  Variables n n': Component.id -> nat.
  
  (* Assume t is a prefix. Reason: addr_shared_so_far also assumes t is a prefix. *)
  Definition trace_addrs_rel t m m' :=
    forall addr,
      addr_shared_so_far addr t ->
      memory_shifts_memory_at_shared_addr n n' addr m m'.

  (*Definition trace_addrs_rel_inv t m m' :=
    forall addr,
      addr_shared_so_far addr t ->
      memory_shifts_memory_at_shared_addr n' n addr m' m.*)

  (*Definition prog_addrs_rel p m m' :=
    forall addr,
      prog_addrs p addr ->
      (* XXX -> *) (* TODO: Find renaming relation, add parameters to state relation. *)
      memory_shifts_memory_at_addr n n' addr m m'.

  Definition prog_addrs_rel_inv p m m' :=
    forall addr,
      prog_addrs p addr ->
      (* ... *)
      memory_inverse_shifts_memory_at_addr n n' addr m m'.
  *)
  Definition memtrace : Type := eqtype.Equality.sort Memory.t * trace event.

  (*Inductive mem_rel2 (mt mt' : memtrace) (p: program) : Prop :=
  | mem_rel2_intro : forall m t m' t',
      mt  = (m , t ) ->
      mt' = (m', t') ->
      (* shared memory renames shared memory *)
      trace_addrs_rel     t  m m' ->
      trace_addrs_rel_inv t' m m' ->
      (* TODO: Are these next two assumptions necessary or do they make 
         the relation too strong?
      *)
      prog_addrs_rel      p  m m' ->
      prog_addrs_rel_inv  p  m m' ->
      mem_rel2 mt mt' p.*)

  (* 1- exclude reachable addresses for current cid. *)
  (* by (1) the weak relation is strong enough, i.e., we should expect that *)
  (* by (1) we can prove a strengthening lemma.                             *)

  (* 2- (need to?) exclude shared addresses.         *)
  
  (*Inductive mem_rel_2_not_reachable ()*)
  
  (* RB: TODO: Use [omap] to make relation more conservative,
     as suggested by AEK. *)
  (*Inductive regs_rel2 (r r' : Register.t) :=
  | regs_rel2_intro : forall i v v',
      r  i = Some v  ->
      r' i = Some v' ->
      shift_value n n' v = v' ->
      (* TODO: probably inverse_shift is redundant with shift. *)
      inverse_shift_value n n' v' = v ->
      regs_rel2 r r'.*)

  Inductive regs_rel_of_executing_part
            (r_original r_recombined: Register.t)
            n_original n_recombined
            t_original t_recombined :=
  | regs_rel_of_executing_part_shift_Some:
      (
        forall reg,
          (
            shift_value_option n_original n_recombined (Register.get reg r_original) =
            Some (Register.get reg r_recombined)
          )
          \/
          (
            shift_value_option n_original n_recombined (Register.get reg r_original) =
            None
            /\
            Register.get reg r_original = Register.get reg r_recombined
            /\
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
            )
          )
      )
      ->
      regs_rel_of_executing_part
        r_original r_recombined n_original n_recombined t_original t_recombined.
        
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

  (* Pairwise relations between the original runs and the combined run. *)
  (*Inductive mem_rel3 (mt mt' mt'' : memtrace) : Prop :=
  | mem_rel3_program :
      trace_comp (snd mt) \in domm (prog_interface p) ->
      mem_rel2 n n' mt mt' p ->
      mem_rel3 mt mt' mt''
  | mem_rel3_context :
      trace_comp (snd mt) \in domm (prog_interface c) ->
      mem_rel2 n'' n' mt'' mt' c' ->
      mem_rel3 mt mt' mt''.
   *)
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

      (* As a sort of conclusion... *)
      (* memory_renames_memory_at_addr addr (CS.state_mem s) (CS.state_mem s') *)

      (* Local buffers on P's side *)
      (* behavior_rel_behavior_all_cids n n'  (FTbc t) (FTbc t' ) -> *)
      (* behavior_rel_behavior_all_cids n n'' (FTbc t) (FTbc t'') -> *)

  Definition regtrace : Type := Register.t * trace event.

  (*Inductive regs_rel3 (rt rt' rt'' : regtrace) :=
  | regs_rel3_program :
      trace_comp (snd rt) \in domm (prog_interface p) ->
      regs_rel2 n n' (fst rt) (fst rt') ->
      regs_rel3 rt rt' rt''
  | regs_rel3_context :
      trace_comp (snd rt) \in domm (prog_interface c) ->
      regs_rel2 n'' n' (fst rt'') (fst rt') ->
      regs_rel3 rt rt' rt''.
   *)
  (* Sketch a simple state relation based on the memory-trace relation, for the
     sake of expediency. *)
  (* Inductive mergeable_states (s s' s'' : CS.state) : Prop := *)
  (* | mergeable_states_intro : forall t t' t'', *)
  (*     mem_rel3 (CS.state_mem s, t) (CS.state_mem s', t') (CS.state_mem s'', t'') -> *)
  (*     mergeable_states s s' s''. *)

  (* This "extensional" reading of compatible states depends directly on the
     partial programs concerned (implicitly through the section mechanism) and
     two runs synchronized by their traces. It is a rather strong notion, easy
     to work with and well suited to the purposes of the proof. *)

  (* NOTE: Should the relation also speak about traces? This could simplify
     some of the simulation lemmas below. This could postpone the question
     of provenance until use time. *)

  (*Definition mem_of_part_executing_rel_original_and_recombined
             (part_executing: program)
             (* part_executing should be either p or c' *)
             original_mem recombined_mem
             original_n   recombined_n
             original_t   recombined_t
    : Prop :=
    (
      forall original_addr,
        (
          original_addr.1 \in domm (prog_interface part_executing) \/
          addr_shared_so_far original_addr original_t
        )
        ->
        memory_shifts_memory_at_addr
          original_n
          recombined_n
          original_addr
          original_mem
          recombined_mem
    )
    /\
    (
      forall recombined_addr,
        (
          recombined_addr.1 \in domm (prog_interface part_executing) \/
          addr_shared_so_far recombined_addr recombined_t
        )
        ->
        memory_inverse_shifts_memory_at_addr
          original_n
          recombined_n
          recombined_addr
          original_mem
          recombined_mem      
    )
    /\
    forall cid,
      cid \in domm (prog_interface part_executing) ->
      omap ComponentMemory.next_block (original_mem cid) =
      omap ComponentMemory.next_block (recombined_mem cid).
   *)

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
      (forall ss tt,     CSInvariants.is_prefix ss prog tt ->
                         good_trace_extensional
                           (left_addr_good_for_shifting n)
                           tt
      ) ->
      (forall ss'' tt'', CSInvariants.is_prefix ss'' prog'' tt'' ->
                         good_trace_extensional
                           (left_addr_good_for_shifting n'')
                           tt''
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
      regs_rel_of_executing_part (CS.state_regs s) (CS.state_regs s') n n' t t' ->
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
      regs_rel_of_executing_part (CS.state_regs s'') (CS.state_regs s') n'' n' t'' t' ->
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
      regs_rel_of_executing_part (CS.state_regs s) (CS.state_regs s') n n' t t' ->
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
      regs_rel_of_executing_part (CS.state_regs s'') (CS.state_regs s') n'' n' t'' t' ->
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
  
  (*
  Inductive mergeable_states
            (s s' s'' : CS.state) t t' t'' : Prop :=
    mergeable_states_intro :
      (* Well-formedness conditions. *)
      well_formed_program p ->
      well_formed_program c ->
      well_formed_program p' ->
      well_formed_program c' ->
      mergeable_interfaces ip ic ->
      prog_interface p  = prog_interface p' ->
      prog_interface c  = prog_interface c' ->
      closed_program prog   ->
      closed_program prog'' ->
      (* "Proper" definition. *)
      CSInvariants.is_prefix s   prog   t ->
      CSInvariants.is_prefix s'  prog'  t' ->
      CSInvariants.is_prefix s'' prog'' t'' ->
      (* Sharing conditions.
         NOTE: Think about possible redundancies. *)
      mem_rel3 (CS.state_mem s, t) (CS.state_mem s', t') (CS.state_mem s'', t'') ->
      regs_rel3 (CS.state_regs s, t) (CS.state_regs s', t') (CS.state_regs s'', t'') ->
      behavior_rel_behavior n n'  (FTbc t) (FTbc t' ) ->
      behavior_rel_behavior n n'' (FTbc t) (FTbc t'') ->
      mergeable_states s s' s'' t t' t''.
   *)
  
  (* RB: NOTE: This induction principle is currently used only in the proofs of
     mergeable_states_pc_same_component and mergeable_states_mergeable_stack. It
     would be interesting to see if (other) proofs benefit from its use, or what
     a conventional star induction does to the lone proof.
     TODO: Remove automatic names, refactor symmetries. *)
  (* Lemma mergeable_states_ind' : forall P : CS.state -> CS.state -> Prop, *)
  (*     (forall (s s'' : CS.state), *)
  (*         initial_state (CS.sem_non_inform (program_link p c)) s -> *)
  (*         initial_state (CS.sem_non_inform (program_link p' c')) s'' -> *)
  (*         P s s'') -> *)
  (*     (forall (s1 s2 s'' : CS.state), *)
  (*         mergeable_states s1 s'' -> *)
  (*         Step (CS.sem_non_inform (program_link p c)) s1 E0 s2 -> *)
  (*         P s1 s'' -> *)
  (*         P s2 s'') -> *)
  (*     (forall (s s1'' s2'' : CS.state), *)
  (*         mergeable_states s s1'' -> *)
  (*         Step (CS.sem_non_inform (program_link p' c')) s1'' E0 s2'' -> *)
  (*         P s s1'' -> *)
  (*         P s s2'') -> *)
  (*     (forall (s1 s2 s1'' s2'' : CS.state) (t : trace CompCert.Events.event), *)
  (*         t <> E0 -> *)
  (*         mergeable_states s1 s1'' -> *)
  (*         Step (CS.sem_non_inform (program_link p c)) s1 t s2 -> *)
  (*         Step (CS.sem_non_inform (program_link p' c')) s1'' t s2'' -> *)
  (*         P s1 s1'' -> *)
  (*         P s2 s2'') -> *)
  (*     forall (s s'' : CS.state), mergeable_states s s'' -> P s simpl''. *)
  (* Proof. *)
  (*   intros P. *)
  (*   intros Hindini HindE0l HindE0r Hindstep. *)
  (*   intros s s'' Hmerg. *)
  (*   inversion Hmerg *)
  (*     as [s0 s0'' t t'' ? ? ? ? ? ? ? ? ? ? ? Hini Hini'' Hstar Hstar'']. *)
  (*   apply star_iff_starR in Hstar. apply star_iff_starR in Hstar''. *)
  (*   generalize dependent s''. *)
  (*   induction Hstar *)
  (*     as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23 Ht12]; *)
  (*     intros s'' Hmerg Hstar''. *)
  (*   - remember E0 as t. *)
  (*     induction Hstar''. *)
  (*     + now apply Hindini. *)
  (*     + subst. *)
  (*       (* assert (Ht1 : t1 = E0) by now destruct t1. *) *)
  (*       (* assert (Ht2 : t2 = E0) by now destruct t1. *) *)
  (*       assert (Ht1 : t1 = E0) by admit. *)
  (*       assert (Ht2 : t2 = E0) by admit. *)
  (*       subst. *)
  (*       specialize (IHHstar'' eq_refl HindE0l HindE0r Hindstep). *)
  (*       assert (Hmergss2 : mergeable_states s s2). *)
  (*       { apply star_iff_starR in Hstar''. *)
  (*         econstructor; try eassumption. now apply star_refl. } *)
  (*       specialize (IHHstar'' Hini'' Hmergss2). eapply HindE0r; eauto. *)
  (*   - pose proof (CS.singleton_traces_non_inform (program_link p c) _ _ _ Hstep23) as Hlen. *)
  (*     assert (t2 = E0 \/ exists ev, t2 = [ev]) as [Ht2E0 | [ev Ht2ev]]. *)
  (*     { clear -Hlen. *)
  (*       inversion Hlen. *)
  (*       - right. destruct t2. simpl in *. congruence. *)
  (*         simpl in *. destruct t2; eauto. simpl in *. congruence. *)
  (*       - left. subst. destruct t2; simpl in *. reflexivity. *)
  (*         omega. } *)
  (*     + subst. *)
  (*       unfold Eapp in Hstar''; rewrite app_nil_r in Hstar''. *)
  (*       assert (Hmergs2s'' : mergeable_states s2 s''). *)
  (*       { econstructor; try eassumption. *)
  (*         apply star_iff_starR in Hstar12. apply Hstar12. *)
  (*         apply star_iff_starR in Hstar''. apply Hstar''. } *)
  (*       specialize (IHstar Hini s'' Hmergs2s'' Hstar''). *)
  (*       eapply HindE0l; eauto. *)
  (*     + subst. *)
  (*       remember (t1 ** [ev]) as t. *)
  (*       induction Hstar''; subst. *)
  (*       * assert (E0 <> t1 ** [ev]) by now induction t1. contradiction. *)
  (*       * subst. *)
  (*         specialize (IHHstar'' Hini'' IHstar). *)
  (*         pose proof (CS.singleton_traces_non_inform (program_link p' c') _ _ _ H8) as Hlen2. *)
  (*         assert (t2 = E0 \/ exists ev, t2 = [ev]) as [ht2E0 | [ev' Ht2ev']]. *)
  (*         { clear -Hlen2. *)
  (*           inversion Hlen2. *)
  (*           - right. destruct t2. simpl in *; congruence. *)
  (*             simpl in *. destruct t2; eauto. simpl in *. congruence. *)
  (*           - left. inversion H0. destruct t2; simpl in *. reflexivity. *)
  (*             congruence. } *)
  (*         ** subst. *)
  (*            unfold Eapp in H9; rewrite app_nil_r in H9; subst. *)
  (*            assert (Hmergs3s4 : mergeable_states s3 s4). *)
  (*            { econstructor; eauto. *)
  (*              apply star_iff_starR. *)
  (*              eapply starR_step. *)
  (*              apply Hstar12. *)
  (*              eauto. reflexivity. *)
  (*              apply star_iff_starR in Hstar''; apply Hstar''. } *)
  (*            specialize (IHHstar'' Hmergs3s4 eq_refl). *)
  (*            eapply HindE0r; eauto. *)
  (*         ** subst. *)
  (*            assert (t1 = t0 /\ ev = ev') as [Ht1t0 Hevev'] by now apply app_inj_tail. *)
  (*            subst. clear IHHstar''. *)
  (*            specialize (IHstar Hini s4). *)
  (*            assert (Hmerge : mergeable_states s2 s4). *)
  (*            { econstructor; try eassumption. apply star_iff_starR in Hstar12; apply Hstar12. *)
  (*              apply star_iff_starR in Hstar''; apply Hstar''. } *)
  (*            specialize (IHstar Hmerge Hstar''). *)
  (*            eapply Hindstep with (t := [ev']); eauto. unfold E0. congruence. *)
  (* Qed. *)

(*
  (* Attempt to rewrite the auxiliary lemmas for recombination. *)
  Lemma merge_mergeable_states_regs_program s s' s'' t t' t'' :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' t t' t'' ->
    merge_states_regs ip s s'' = CS.state_regs s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[|stack mem] reg] pc] addrs].
    destruct s'' as [[[[|stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_regs. simpl.
    CS.simplify_turn.
    inversion Hmerg as [ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces H_iface H_iface'
                        Hprog_is_closed Hctx_is_closed Hpref Hpref' Hpref''
                        Hmemrel Hregsrel Hstar Hstar''].
Check CS.star_pc_domm_non_inform.
    destruct (CS.star_pc_domm_non_inform _ _ 
                Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hpref Hstar) as [H | H].
    - now rewrite H.
    - now rewrite H in Hcomp.
  Qed. *)


(*
  (* The following lemmas establish the connection between the mergeability
     relation and the application of the state merging functions. *)
  Lemma merge_mergeable_states_regs_program s s' s'' t t' t'' :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' t t' t'' ->
    merge_states_regs ip s s'' = CS.state_regs s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[|stack mem] reg] pc] addrs].
    destruct s'' as [[[[|stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_regs. simpl.
    CS.simplify_turn.
    inversion Hmerg as [s0 s0'' t0 t0'' _ _
                        Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _
                        Hini Hini'' Hstar Hstar'' _].
    destruct (CS.star_pc_domm_non_inform
                _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [H | H].
    - now rewrite H.
    - now rewrite H in Hcomp.
  Qed.

  Lemma merge_mergeable_states_regs_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states_regs ip s s'' = CS.state_regs s''.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[stack mem] reg] pc] addrs]; destruct s'' as [[[[stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_regs. simpl.
    unfold merge_registers.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmerg as [_ _ _ _ _ _ _ _ _ _ Hmergeable_ifaces _ _ _ _ _ _ _ _ _].
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct Hlinkable as [_ Hdisj].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    specialize (Hdisj (Pointer.component pc) Hcomp).
    move: Hdisj => /negP => Hdisj.
    destruct (Pointer.component pc \in domm ip) eqn:Heq; now rewrite Heq.
  Qed.

  Lemma merge_mergeable_states_pc_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states_pc ip s s'' = CS.state_pc s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[stack mem] reg] pc] addrs]; destruct s'' as [[[[stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_pc. simpl.
    unfold merge_pcs.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmerg as [s0 s0'' t t'' _ _
                        Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _
                        Hini Hini'' Hstar Hstar'' _].
    destruct (CS.star_pc_domm_non_inform
                _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [H | H].
    - now rewrite H.
    - now rewrite H in Hcomp.
  Qed.

  Lemma merge_mergeable_states_pc_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states_pc ip s s'' = CS.state_pc s''.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[stack mem] reg] pc] addrs]; destruct s'' as [[[[stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_pc. simpl.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmerg as [_ _ _ _ _ _ _ _ _ _ Hmergeable_ifaces _ _ _ _ _ _ _ _ _].
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct Hlinkable as [_ Hdisj].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    specialize (Hdisj (Pointer.component pc) Hcomp).
    move: Hdisj => /negP => Hdisj.
    destruct (Pointer.component pc \in domm ip) eqn:Heq; now rewrite Heq.
  Qed.

  Lemma mergeable_states_merge_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states ip ic s s'' =
    (merge_states_stack ip s s'', merge_states_mem ip ic s s'', CS.state_regs s, CS.state_pc s, CS.state_addrs s (* [DynShare] TODO *)).
  Proof.
    intros Hcomp Hmerg.
    rewrite merge_states_unfold.
    rewrite merge_mergeable_states_pc_program; try assumption.
    rewrite merge_mergeable_states_regs_program; try assumption.
    reflexivity.
  Qed.

  Lemma mergeable_states_merge_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states ip ic s s'' =
    (merge_states_stack ip s s'', merge_states_mem ip ic s s'', CS.state_regs s'', CS.state_pc s'', CS.state_addrs s (* [DynShare] TODO *)).
  Proof.
    intros Hcomp Hmerg.
    rewrite merge_states_unfold.
    rewrite merge_mergeable_states_pc_context; try assumption.
    rewrite merge_mergeable_states_regs_context; try assumption.
    reflexivity.
  Qed.
*)

  (* Inversion pattern:
inversion Hmerg as [s0 s0' s0'' t t' t'' n n' n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed'' Hini Hini' Hini'' Hstar Hstar' Hstar'' Hmrel Htrel Htrel''].
  *)

  (* Relations between mergeable states and program components. *)
  Lemma mergeable_states_pc_same_component s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) = Pointer.component (CS.state_pc s'').
  (* Proof. *)
  (*   intros Hmerg. *)
  (*   induction Hmerg *)
  (*     as [ s s'' Hini Hini'' *)
  (*        | s1 s2 s'' Hmerg Hstep IH *)
  (*        | s s1'' s2'' Hmerg Hstep IH *)
  (*        | s1 s2 s1'' s2'' t Hdiff Hmerg Hstep Hstep'' IH] *)
  (*     using mergeable_states_ind'. *)
  (*   - (* Initial state *) *)
  (*     inversion Hini; inversion Hini''; subst. *)
  (*     unfold CS.state_pc. unfold CS.initial_machine_state. *)
  (*     destruct (prog_main (program_link p c)); destruct (prog_main (program_link p' c')); eauto. *)
  (*   - (* Silent step on the left *) *)
  (*     now rewrite <- IH, (CS.silent_step_non_inform_preserves_component _ _ _ Hstep). *)
  (*   - (* Silent step on the right *) *)
  (*     now rewrite -> IH, (CS.silent_step_non_inform_preserves_component _ _ _ Hstep). *)
  (*   - (* Non-silent step *) *)
  (*     inversion Hstep; subst; try contradiction; *)
  (*       inversion Hstep''; subst; try contradiction; *)
  (*       try match goal with *)
  (*         HE0: E0 = ?x, Hx: ?x <> E0 |- _ => *)
  (*         rewrite <- HE0 in Hx; contradiction *)
  (*       end; *)
  (*       match goal with *)
  (*         Hstp : CS.step _ _ ?e _, *)
  (*         Hstp' : CS.step _ _ ?e0 _ |- _ => *)
  (*         inversion Hstp; *)
  (*         match goal with *)
  (*           Hexec: executing ?G ?pc ?i, *)
  (*           Hexec': executing ?G ?pc ?i' |- _ => *)
  (*           pose proof *)
  (*                executing_deterministic *)
  (*                G pc i i' Hexec Hexec' as cntr; *)
  (*           try discriminate *)
  (*         end; *)
  (*         inversion Hstp'; *)
  (*         match goal with *)
  (*           Hexec: executing ?G ?pc ?i, *)
  (*           Hexec': executing ?G ?pc ?i' |- _ => *)
  (*           pose proof *)
  (*                executing_deterministic *)
  (*                G pc i i' Hexec Hexec' as cntra; *)
  (*           try discriminate *)
  (*         end *)
  (*       end; *)
  (*       inversion cntra; inversion cntr; subst; simpl in *; *)
  (*       match goal with *)
  (*         Heveq: [_] = [_] |- _ => inversion Heveq; subst; reflexivity *)
  (*       end. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Should be fairly easy. *)

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

  Lemma mergeable_states_context_to_program s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.is_context_component s ic ->
    CS.is_program_component s'' ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack1 mem1] reg1] pc1];
      destruct s'' as [[[stack2 mem2] reg2] pc2].
    pose proof mergeable_states_pc_same_component Hmerg as Hpc; simpl in Hpc.
    rewrite <- Hpc; clear Hpc.
    inversion Hmerg.
    destruct H3 as [_ Hdisj].
    move: Hdisj.
    (*
    rewrite fdisjointC => /fdisjointP Hdisj.
    now auto.
  Qed.*)
    Admitted.

  Lemma mergeable_states_program_to_context s s' s'' t t' t'':
    mergeable_internal_states s s' s'' t t' t'' ->
    CS.is_program_component s ic ->
    CS.is_context_component s'' ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack mem] reg] pc];
      destruct s'' as [[[stack'' mem''] reg''] pc''].
    pose proof mergeable_states_pc_same_component Hmerg as Hpc; simpl in Hpc.
    rewrite <- Hpc.
  Admitted.
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
     \[not]in. This is the equivalent of the old [PS.domm_partition]. *)
  Lemma mergeable_states_notin_to_in s s' s'' t t' t'' :
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) \notin domm ip ->
    Pointer.component (CS.state_pc s) \in domm ic.
  Proof.
    intros Hmerg Hpc_notin.
    (*
    inversion Hmerg as [[[[? ?] ?] ?] _ ? ? _ ? _ _ _
                        Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _
                        Hini _ _ Hstar _ _ _ _ _ _].
    CS.unfold_states.
    pose proof (CS.star_pc_domm_non_inform
                  _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as Hpc.
    destruct Hpc as [Hprg | Hctx].
    - now rewrite Hprg in Hpc_notin.
    - now assumption.
  Qed.*)
  Admitted.

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

(*  Lemma mergeable_states_mergeable_stack
        gps1   mem1   regs1   pc1
        st1'
        gps1'' mem1'' regs1'' pc1''
        t t' t'':
    mergeable_states (gps1  , mem1  , regs1  , pc1  )
                     st1'
                     (gps1'', mem1'', regs1'', pc1'')
                     t t' t''
    ->
    mergeable_stack gps1 gps1''.*)
  (* Proof. *)
  (*   intros Hmerg. *)
  (*   inversion Hmerg *)
  (*     as [s_init s_init' t_init Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces *)
  (*         Hifacep Hifacec Hprog_is_closed Hprog_is_closed' Hinit Hinit' Hstar Hstar']. *)
  (*   remember (gps1, mem1, regs1, pc1, addrs1) as s1. *)
  (*   remember (gps1'', mem1'', regs1'', pc1'', addrs1'') as s1''. *)
  (*   revert gps1 mem1 regs1 pc1 addrs1 gps1'' mem1'' regs1'' pc1'' addrs1'' Heqs1 Heqs1''. *)
  (*   induction Hmerg as [ s1 s1'' Hini Hini'' *)
  (*                      | s1 s2 s1'' Hmerg Hstep IH *)
  (*                      | s1 s1'' s2'' Hmerg Hstep'' IH *)
  (*                      | s1 s2 s1'' s2'' t Ht Hmerg Hstep Hstep'' IH] *)
  (*     using mergeable_states_ind'. *)
  (*   - (* Initial state *) *)
  (*     intros. *)
  (*     subst. inversion Hini as [Hini1]; inversion Hini'' as [Hini1'']. *)
  (*     destruct Hmergeable_ifaces. *)
  (*     rewrite CS.initial_machine_state_after_linking in Hini1; try assumption. *)
  (*     rewrite CS.initial_machine_state_after_linking in Hini1''; try assumption. *)
  (*     inversion Hini1; inversion Hini1''. now constructor. *)
  (*     now rewrite -Hifacec -Hifacep. *)
  (*   - intros; inversion Hstep; subst; eapply IH; eauto; *)
  (*       try ( *)
  (*           match goal with H: (?gps, _, _, _, _) = (?gps1, _, _, _, _) |- *)
  (*                           (?gps, _, _, _, _) = (?gps1, _, _, _, _) => *)
  (*                           inversion H; reflexivity *)
  (*           end *)
  (*         ). *)
  (*     + (* Is this even provable? *) *)
  (*       inversion Hmerg. *)
  (*       match goal with Hinit: initial_state sem s_init, Hs0 : initial_state sem ?s0 |- _ *)
  (*                       => pose proof sd_initial_determ *)
  (*                               (CS.determinacy_non_inform prog) s_init s0 Hinit Hs0 as *)
  (*                           Hsinit_s0 *)
  (*       end. *)
  (*       subst. *)
  (*       admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + (* Derive a contradiction from the assumption: *)
  (*          CS.event_non_inform_of e = E0 *)
  (*        *) *)
  (*       admit. *)
  (*     + (* Derive a contradiction from the assumption: *)
  (*          CS.event_non_inform_of e = E0 *)
  (*        *) *)
  (*       admit. *)
  (*     + (* Derive a contradiction from the assumption: *)
  (*          CS.event_non_inform_of e = E0 *)
  (*        *) *)
  (*       admit. *)
  (*   - admit. *)
  (*     (* *)
  (*     intros; inversion Hstep''; subst; *)
  (*       try match goal with *)
  (*       | Heq: _ = (_, _, _, _) |- _ => inversion Heq; subst; now eapply IH *)
  (*           end. *)
  (*     + (* Derive a contradiction from the assumption: *)
  (*          CS.event_non_inform_of e = E0 *)
  (*        *) *)
  (*       admit. *)
  (*     + (* Derive a contradiction from the assumption: *)
  (*          CS.event_non_inform_of e = E0 *)
  (*        *) *)
  (*       admit. *)

  (*      *) *)
  (*   - intros gps2 mem2 regs2 pc2 addrs2 gps2'' mem2'' regs2'' pc2'' addrs2'' Heqs2 Heqs2''; subst. *)
  (*     (* Note: do not try to do: *)
  (*        inversion Hstep; inversion Hstep''; try congruence. *)
  (*        as it generates 13*13 = subgoals before discarding the *)
  (*        absurd ones. *) *)
  (*     inversion Hstep; subst; try contradiction; *)
  (*       inversion Hstep''; subst; try contradiction; *)
  (*         try match goal with HE0: E0 = ?x, Hx: ?x <> E0 |- _ => *)
  (*                             rewrite <- HE0 in Hx; contradiction *)
  (*             end; *)
  (*         match goal with Hstp : CS.step _ _ ?e _, *)
  (*                                Hstp' : CS.step _ _ ?e0 _ |- _ => *)
  (*                         inversion Hstp; *)
  (*                           match goal with Hexec: executing ?G ?pc ?i, *)
  (*                                                  Hexec': executing ?G ?pc ?i' |- _ => *)
  (*                                           pose proof *)
  (*                                                executing_deterministic *)
  (*                                                G pc i i' Hexec Hexec' as cntr; *)
  (*                                             try discriminate *)
  (*                           end; *)
  (*                           inversion Hstp'; *)
  (*                           match goal with Hexec: executing ?G ?pc ?i, *)
  (*                                                  Hexec': executing ?G ?pc ?i' |- _ => *)
  (*                                           pose proof *)
  (*                                                executing_deterministic *)
  (*                                                G pc i i' Hexec Hexec' as cntra; *)
  (*                                             try discriminate *)
  (*                           end *)
  (*         end. *)
  (*     + subst. inversion cntr. subst. inversion cntra. subst. *)
  (*       eapply mergeable_stack_cons; eauto. *)
  (*       * inversion cntra. subst. simpl in *.  *)
  (*         match goal with *)
  (*           H: [ECall (Pointer.component pc0) _ _ _ _] = [ECall (Pointer.component pc) _ _ _ _] *)
  (*           |- _ => *)
  (*           inversion H *)
  (*         end. *)
  (*         now do 2 rewrite Pointer.inc_preserves_component. *)
  (*       * (* Shouldn't this somehow follow from  *)
  (*            "Hprog_is_closed" together *)
  (*            with  executing (globalenv (CS.sem_non_inform (program_link p c))) pc (ICall C P)? *)
  (*          *) *)
  (*         assert (Pointer.component pc \in domm ip \/ *)
  (*                 Pointer.component pc \in domm ic) as gl. *)
  (*         { *)
  (*           eapply CS.star_pc_domm; eauto. *)
  (*           - pose proof program_behaves_exists sem as [beh Hbeh]. *)
  (*             pose proof CS.program_behaves_inv_non_inform prog beh Hbeh as [ee [Hee1 Hee2]]. *)
  (*             eexists. *)
  (*           - inversion Hmerg; eauto. *)
  (*             match goal with *)
  (*               Hstar_s0: Star sem ?s0 ?t ?s', *)
  (*               Hinit_s0: initial_state sem ?s0 *)
  (*               |- _ => *)
  (*               pose proof CS.star_sem_non_inform_star_sem_inform *)
  (*                    prog s0 t s' Hstar_s0 *)
  (*                 as [t_inform [gl _gl]]; *)
  (*               pose proof sd_initial_determ *)
  (*                    (CS.determinacy_non_inform prog) s0 *)
  (*                    (CS.initial_machine_state (program_link p c)) *)
  (*                    Hinit_s0 as Hinit_eq *)
  (*             end. *)
  (*             simpl in *. unfold CS.initial_state in *. *)
  (*             unfold prog in *. *)
  (*             match goal with *)
  (*               Hs0: ?s0 = CS.initial_machine_state (program_link p c) *)
  (*               |- _ => *)
  (*               rewrite Hs0 in gl *)
  (*             end. *)
  (*             (* exact gl. *) *)
  (*             admit. *)
  (*         } *)
  (*         destruct gl as [l | r]. *)
  (*         -- right. rewrite Pointer.inc_preserves_component. assumption. *)
  (*         -- left. rewrite Pointer.inc_preserves_component. assumption. *)
  (*       * admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*Admitted.*) (* RB: TODO: Should not be provable. Repair induction principle? *)

  (*
  Lemma mergeable_states_cons_domm
        frame1   gps1   mem1   regs1   pc1
        st1'
        frame1'' gps1'' mem1'' regs1'' pc1''
        t t' t'':
    mergeable_states (frame1   :: gps1  , mem1  , regs1  , pc1  ) st1'
                     (frame1'' :: gps1'', mem1'', regs1'', pc1'')
                     t t' t'' ->
    Pointer.component frame1 = Pointer.component frame1''.
  Proof.
    intros Hmerge.
    pose proof mergeable_states_mergeable_stack Hmerge as H.
    now inversion H.
  Qed.*)

  (* Memory lemmas on mergeable states. *)
  (* RB: NOTE: In the current form, these lemmas are sufficient if unsatisfying
     in that only an imprecise existential intros offered. *)
(*
  Lemma program_store_from_partialized_memory s s'' ptr v mem' :
    mergeable_interfaces ip ic ->
    Pointer.component (CS.state_pc s) \in domm ip ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.store (merge_states_mem ip ic s s'') ptr v = Some mem' ->
  exists mem,
    Memory.store (CS.state_mem s) ptr v = Some mem.
  Proof.
    destruct s as [[[[gps mem] regs] pc] addrs].
    destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs''].
    destruct ptr as [[[P C] b] o].
    unfold Memory.store, merge_states, merge_states_mem, merge_memories.
    intros Hmerge_ifaces Hdomm Hcomp.
    rewrite unionmE Hcomp.
    erewrite to_partial_memory_in; try eassumption.
    erewrite to_partial_memory_notin;
      try eassumption; [| apply mergeable_interfaces_sym; eassumption].
    simpl.
    destruct (P =? Permission.data) eqn:Hcase0;
      last discriminate.
    destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase1;
      last discriminate.
    simpl.
    destruct (ComponentMemory.store memC b o v) as [memC' |] eqn:Hcase2;
      last discriminate.
    now eauto.
  Qed.

  Lemma program_alloc_from_partialized_memory s s'' size mem' ptr' :
    mergeable_interfaces ip ic ->
    Pointer.component (CS.state_pc s) \in domm ip ->
    Memory.alloc (merge_states_mem ip ic s s'') (CS.state_component s) size =  Some (mem', ptr') ->
  exists mem ptr,
    Memory.alloc (CS.state_mem s) (CS.state_component s) size = Some (mem, ptr).
  Proof.
    destruct s as [[[[gps mem] regs] pc] addrs].
    destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs''].
    unfold Memory.alloc, merge_states, merge_states_mem, merge_memories, CS.state_component.
    intros Hmerge_ifaces Hdomm.
    rewrite unionmE.
    erewrite to_partial_memory_in; try eassumption.
    erewrite to_partial_memory_notin;
      try eassumption; [| apply mergeable_interfaces_sym; eassumption].
    simpl.
    destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase1;
      last discriminate.
    simpl.
    destruct (ComponentMemory.alloc memC size) as [memC' b].
    now eauto.
  Qed.

  (* RB: NOTE: Consider changing the naming conventions from "partialized" to
     "recombined" or similar. Exposing the innards of the memory merge operation
     is not pretty; sealing them would require to add the program step from s to
     the lemmas. In this block, mergeable_states may be too strong and could be
     weakened if it were interesting to do so. See comments for pointers to
     existing related lemmas. *)

  Lemma to_partial_memory_merge_memories_left s s'' :
    mergeable_states s s'' ->
    to_partial_memory                       (CS.state_mem s)                     (domm ic) =
    to_partial_memory (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) (domm ic).
  Proof.
    intros Hmerg.
    inversion Hmerg
      as [s0 s0'' t t'' n n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
          Hprog_is_closed Hprog_is_closed' Hini Hini'' Hstar Hstar'' Hrel].
    apply /eq_fmap => Cid.
    pose proof mergeable_interfaces_sym _ _ Hmergeable_ifaces
      as Hmergeable_ifaces_sym.
    assert (Hmem : domm (CS.state_mem s) = domm (unionm ip ic)).
    {
      apply CS.comes_from_initial_state_mem_domm.
      inversion Hprog_is_closed as [_ [main [Hmain _]]].
      pose proof linking_well_formedness Hwfp Hwfc (proj1 Hmergeable_ifaces) as Hwf.
      pose proof CS.star_sem_non_inform_star_sem_inform prog s0 t _ Hstar as
          [t_inform [Hstar_inform _]].
      now exists prog, s0, t_inform.
    }
    assert (Hmem'' : domm (CS.state_mem s'') = domm (unionm ip ic)).
    {
      apply CS.comes_from_initial_state_mem_domm.
      inversion Hprog_is_closed' as [_ [main [Hmain _]]].
      unfold ip, ic in Hmergeable_ifaces_sym. rewrite Hifacec Hifacep in Hmergeable_ifaces_sym.
      pose proof linking_well_formedness Hwfp' Hwfc' (linkable_sym (proj1 Hmergeable_ifaces_sym)) as Hwf.
      apply mergeable_interfaces_sym in Hmergeable_ifaces_sym.
      pose proof CS.star_sem_non_inform_star_sem_inform prog'' s0'' t'' _ Hstar'' as
          [t_inform'' [Hstar_inform'' _]].
      exists prog'', s0'', t_inform''.
      repeat (split; eauto). unfold ip, ic; now rewrite Hifacec Hifacep.
    }
    unfold merge_memories.
    destruct (Cid \in domm ip) eqn:Hdommp;
      destruct (Cid \in domm ic) eqn:Hdommc.
    - exfalso.
      apply domm_partition_notin with (ctx1 := ip) in Hdommc.
      now rewrite Hdommp in Hdommc.
      assumption.
    - erewrite to_partial_memory_in; try eassumption.
      erewrite to_partial_memory_in; try eassumption.
      rewrite unionmE.
      erewrite to_partial_memory_in; try eassumption.
      erewrite to_partial_memory_notin; try eassumption.
      now destruct ((CS.state_mem s) Cid).
    - erewrite to_partial_memory_notin; try eassumption.
      erewrite to_partial_memory_notin; try eassumption.
      reflexivity.
    - erewrite !to_partial_memory_notin_strong; try eassumption;
        try now apply negb_true_iff in Hdommc;
        try now apply negb_true_iff in Hdommp.
      rewrite unionmE.
      erewrite !to_partial_memory_notin_strong; try eassumption;
        try now apply negb_true_iff in Hdommc;
        try now apply negb_true_iff in Hdommp.
      destruct (isSome ((CS.state_mem s) Cid)) eqn:HisSome; try reflexivity.
      (* Might want to use star_mem_well_formed to prove these subgoals. *)
      assert (Hmem_Cid: (CS.state_mem s) Cid = None).
      { apply /dommPn.
        apply negb_true_iff in Hdommp; apply negb_true_iff in Hdommc.
        rewrite Hmem.
        rewrite domm_union. apply /fsetUP.
        intros Hn; destruct Hn as [Hn | Hn].
        now rewrite Hn in Hdommp.
        now rewrite Hn in Hdommc.
      }
      assert (Hmem''_Cid: (CS.state_mem s'') Cid = None).
      { apply /dommPn.
        apply negb_true_iff in Hdommp; apply negb_true_iff in Hdommc.
        rewrite Hmem''.
        rewrite domm_union. apply /fsetUP.
        intros Hn; destruct Hn as [Hn | Hn].
        now rewrite Hn in Hdommp.
        now rewrite Hn in Hdommc.
      }
      now rewrite Hmem_Cid Hmem''_Cid.
  Qed.

  (* Search _ Memory.load filterm. *)
  Lemma program_load_to_partialized_memory s s'' ptr v :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.load (CS.state_mem s) ptr = Some v ->
    Memory.load (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr =
    Some v.
  Proof.
    intros Hpc Hmerge Hptr Hload.
    destruct s as [[[gps mem] regs] pc]. destruct ptr as [[[P C] b] o]. simpl in *. subst.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hdomm.
    pose proof to_partial_memory_merge_memories_left Hmerge as Hmem.
    now erewrite <- (program_load_in_partialized_memory_strong Hmem Hdomm).
  Qed.

  (* RB: NOTE: Consider removing weaker version of lemma above. *)
  Lemma program_load_to_partialized_memory_strong s s'' ptr :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.load (CS.state_mem s) ptr =
    Memory.load (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr.
  Proof.
    destruct (Memory.load (CS.state_mem s) ptr) as [v |] eqn:Hcase1;
      first (symmetry; now apply program_load_to_partialized_memory).
    intros Hpc Hmerge Hptr.
    destruct s as [[[[gps mem] regs] pc] addrs]; destruct ptr as [[[P C] b] o];
      unfold Memory.load, merge_memories in *; simpl in *; subst.
    eapply is_program_component_pc_in_domm in Hpc; last eassumption; try assumption.
    inversion Hmerge as [_ _ _ _ _ _ _ _ _ _ Hmergeable_ifaces _ _ _ _ _ _ _ _ _].
    erewrite unionmE, to_partial_memory_in, to_partial_memory_notin;
      try eassumption;
      [| apply mergeable_interfaces_sym; eassumption].
    now destruct (mem (Pointer.component pc)).
  Qed.

  (* RB: NOTE: Could the following lemmas be moved to memory without relying on
     mergeable_states?

     Indeed, now that we have distilled well-formedness conditions, it is clear
     that in many cases they are overkill -- though they can be convenient.
     Conversely, one could phrase the previous genv_* lemmas in terms of
     mergeable_states as well. *)

  (* Search _ Memory.store filterm. *)
  (* Search _ Memory.store PS.to_partial_memory. *)
  (* Search _ Memory.store PS.merge_memories. *)
  (* RB: TODO: Resolve name clash with theorem in Memory. *)
  Lemma program_store_to_partialized_memory s s'' ptr v mem :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.store (CS.state_mem s) ptr v = Some mem ->
    Memory.store (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr v =
    Some (merge_memories ip ic mem (CS.state_mem s'')).
  Proof.
    intros Hpc Hmerge Hptr Hstore.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin.
    rewrite <- Hptr in Hnotin.
    pose proof partialize_program_store Hnotin Hstore as Hstore'.
    pose proof unpartialize_program_store
         (to_partial_memory (CS.state_mem s'') (domm ip)) Hstore' as Hstore''.
    done.
  Qed.

  (* Search _ Memory.alloc filterm. *)
  (* Search _ Memory.alloc PS.to_partial_memory. *)
  (* Search _ Memory.alloc PS.merge_memories. *)
  Lemma program_alloc_to_partialized_memory s s'' mem ptr size :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    Memory.alloc (CS.state_mem s) (CS.state_component s) size = Some (mem, ptr) ->
    Memory.alloc (merge_memories ip ic (CS.state_mem s) (CS.state_mem s''))
                 (CS.state_component s) size =
    Some (merge_memories ip ic mem (CS.state_mem s''), ptr).
  Proof.
    intros Hpc Hmerge Halloc.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin.
    pose proof partialize_program_alloc Hnotin Halloc as Halloc'.
    pose proof unpartialize_program_alloc
         (to_partial_memory (CS.state_mem s'') (domm ip)) Halloc' as Halloc''.
    done.
  Qed.
*)

  Lemma find_label_in_component_mergeable_internal_states
        s s' s'' t t' t'' l spc pc:
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc = CS.state_pc s' ->
    find_label_in_component (globalenv sem) spc l = Some pc ->
    find_label_in_component (globalenv sem') spc l = Some pc.
  Proof.
    intros Hprog_comp Hmerge Hspc Hfind.
    inversion Hmerge as [Hwf|Hwf]; inversion Hwf.
    - (*rewrite find_label_in_component_program_link_left; auto.
      + erewrite <- find_label_in_component_program_link_left.
        Search _ prepare_global_env global_env.
        unfold sem in Hfind.*)
      admit.
    - (* here, contradiction *)
      admit.
  Admitted.

  
  Lemma find_label_in_procedure_mergeable_internal_states
        s s' s'' t t' t'' l spc pc:
    CS.is_program_component s' ic ->
    mergeable_internal_states s s' s'' t t' t'' ->
    spc = CS.state_pc s' ->
    find_label_in_procedure (globalenv sem) spc l = Some pc ->
    find_label_in_procedure (globalenv sem') spc l = Some pc.
  Proof.
    intros Hprog_comp Hmerge Hspc Hfind.
    inversion Hmerge as [Hwf|Hwf]; inversion Hwf.
    - admit.
    - (* here, contradiction *)
      admit.
  Admitted.
        
    
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


Ltac find_nil_rcons :=
  let Hcontra := fresh "Hcontra" in
  match goal with
  | H: [::] = rcons ?t ?e |- _ =>
    pose proof size_rcons t e as Hcontra;
      by rewrite <- H in Hcontra
  | H: rcons ?t ?e = [::] |- _ =>
    pose proof size_rcons t e as Hcontra;
      by rewrite H in Hcontra
  end.

(* Helpers, epsilon and lockstep versions of three-way simulation. *)
Section ThreewayMultisem1.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.
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

  (* Given a silent star driven by the "program" side p, the "context" side c
     remains unaltered. *)

  (* Ltac t_to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' := *)
  (*   inversion Hmerge1 *)
  (*     as [_ s0'' t01'' _ _ Hwfp' Hwfc' Hmergeable_ifaces *)
  (*         Hifacep Hifacec _ Hprog_is_closed' _ Hini0'' _ Hstar01'']; *)
  (*   pose proof mergeable_states_program_to_program Hmerge1 Hcomp as Hcomp1''; *)
  (*   rewrite Hifacec in Hcomp1''; *)
  (*   assert (Hmergeable_ifaces' := Hmergeable_ifaces); *)
  (*     rewrite Hifacep Hifacec in Hmergeable_ifaces'; *)
  (*   pose proof CS.epsilon_star_preserves_program_component _ _ _ _ Hcomp1'' Hstar12'' as Hcomp2''; *)
  (*   destruct (CS.star_pc_domm _ _ *)
  (*               Hwfp' Hwfc' Hmergeable_ifaces' Hprog_is_closed' Hini0'' *)
  (*               (star_trans Hstar01'' Hstar12'' eq_refl)) as [Hgoal | Hcontra]; *)
  (*   [ now rewrite Hifacep *)
  (*   | CS.simplify_turn; now rewrite Hcontra in Hcomp2'' *)
  (*   ]. *)

  (* [DynShare]

     This lemma is false in the existence of dynamic memory sharing.
     Instead, what remains untouched is *only* the part of the partial memory
     that *remains* private after considering (i.e., set-differencing) the set
     of shared addresses.
   *)
  (* Lemma to_partial_memory_epsilon_star s s1'' s2'' s3'' : *)
  (*   mergeable_states p c p' c' s s1'' -> *)
  (*   CS.is_program_component s ic -> *)
  (*   Star sem'' s1'' E0 s2'' -> *)
  (*   Step sem'' s2'' E0 s3'' -> *)
  (*   to_partial_memory (CS.state_mem s2'') (domm ip) = *)
  (*   to_partial_memory (CS.state_mem s3'') (domm ip). *)
  (* Proof. *)
  (*   intros Hmerge1 Hcomp Hstar12'' Hstep23''. *)
  (*   destruct s2'' as [[[[gps2'' mem2''] regs2''] pc2''] addr2'']. *)
  (*   destruct s3'' as [[[[gps3'' mem3''] regs3''] pc3''] addr3'']. *)
  (*   pose proof CS.step_non_inform_step_inform prog'' *)
  (*        (gps2'', mem2'', regs2'', pc2'', addr2'') _ _ Hstep23'' as *)
  (*       [t_inform [Hstep_inform _]]. *)
  (*   inversion Hstep_inform; subst; *)
  (*     (* Most cases do not touch the memory. *) *)
  (*     try reflexivity. *)
  (*     (* *)
  (*       [DynShare] *)

  (*       The proof below no longer holds. The proof is looking for the assumption *)
  (*       Heq that ensures that the store is not touching any non-pc-owned memory. *)
  (*       However, no such assumption exists anymore for the store instruction. *)
  (*      *) *)
  (* Abort. *)

  (* [DynShare] DEPRECATED ARGUMENT BELOW

      (* Rewrite memory goals, discharge side goals and homogenize shape. *)
      match goal with
      | Hstore : Memory.store _ _ _ = _,
        Heq : Pointer.component _ = Pointer.component _ |- _ =>
        erewrite Memory.program_store_to_partialized_memory; eauto 1; rewrite Heq
      | Halloc : Memory.alloc _ _ _ = _ |- _ =>
        erewrite program_allocation_to_partialized_memory; eauto 1
      end.
      (* Prove the PC is in the program in both cases. *)
      unfold ip;
      t_to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12''.
  Qed.

   *)

  Ltac t_merge_states_silent_star :=
    inversion IHstar''; subst;
    [econstructor]; try eassumption;
    (* In most cases, only one sub-goal is left, always solvable thus: *)
    try (eapply star_right; try eassumption;
         now rewrite E0_right).
    (* In memory-altering cases, a second sub-goal is left to be solved. *)

  (* RB: NOTE: Likely provable: since we are on the program, we would not care
     what changes the "other program" makes to its memory, only what "our
     program" eventually will. *)
  (* AEK: Notice here that the precondition CS.is_program_component looks like *)
  (* it should be accompanied with a "mirrored" version of the same lemma that *)
  (* has the precondition CS.is_context_component instead. However, this mirrored *)
  (* lemma is not really necessary. And the mirroring is instead done at use time. *)
  Lemma merge_states_silent_star s1 s1' s1'' s2'' t t' t'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s2'' t t' t''.
  Proof.
    intros Hmerge1 Hcomp Hstar12''.
    remember E0 as t0.
    apply star_iff_starR in Hstar12''.
    induction Hstar12''
      as [s'' | s1'' t1 s2'' t2 s3'' ? Hstar12'' IHstar'' Hstep23'' Ht12]; subst.
    - assumption.
    - (* Simplify, apply IH and case analyze. *)
      symmetry in Ht12; apply Eapp_E0_inv in Ht12 as [? ?]; subst.
      specialize (IHstar'' Hmerge1 Logic.eq_refl).
      (* rewrite IHstar''. *)
      apply star_iff_starR in Hstar12''.
      destruct s1 as [[[gps1 mem1] regs1] pc1].
      destruct s2'' as [[[gps2'' mem2''] regs2''] pc2''].
      destruct s3'' as [[[gps3'' mem3''] regs3''] pc3''].
      pose proof CS.step_non_inform_step_inform prog''
           (gps2'', mem2'', regs2'', pc2'') _ _ Hstep23'' as
          [t_inform [Hstep_inform _]].
      (* Analyze and recompose mergeability relation in each case. *)
      inversion Hstep_inform; subst.
      + (* INop *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* ILabel *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IConst *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IMov *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBinop *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* ILoad *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IStore *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            find_and_invert_mergeable_states_well_formed;
              eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            (*++ eapply Hgood_prog''.
               (* is_prefix again *)
               unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** by rewrite E0_right.*)
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
          -- (* mem of part not executing *)
            unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal.
            (* Key fact to prove:
               the address that is stored at does NOT satisfy the preconditions
               of this goal.
             *)
            
            match goal with
            | Hstore: Memory.store mem2'' ?PTR _ = _ |- _ =>
              destruct PTR as [[[perm cid_store] bid_store] offset_store]
            end.
            assert (CSInvariants.wf_ptr_wrt_cid_t
                      (Pointer.component (Pointer.inc pc2''))
                      t''
                      (perm, cid_store, bid_store, offset_store)
                   ) as Hwfptr.
            {
              find_and_invert_mergeable_states_well_formed.
          
              eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
              rewrite Pointer.inc_preserves_component.
              eapply CSInvariants.wf_state_wf_reg.
              - eapply CSInvariants.is_prefix_wf_state_t;
                  last (
                      match goal with
                      | H: CSInvariants.is_prefix _ _ t'' |- _ => exact H
                      end
                    ).
                eapply linking_well_formedness; eauto.
                unfold mergeable_interfaces in *.
                  by
                    match goal with
                    | Hp: prog_interface p = _,
                          Hc: prog_interface c = _,
                              Hlink: linkable _ _ /\ _
                      |- _ => rewrite <- Hp, <- Hc; destruct Hlink as [Hgoal _]
                    end.
              - by simpl.
              - by simpl.
              - auto.
            }
            assert (
              cid_store \in domm (prog_interface c') ->
                            addr_shared_so_far (cid_store, bid_store) t''
            ) as Hstore_addr_fact.
            {
              intros Hcid_store.
              inversion Hwfptr as [ | ]; eauto.
              - (* Now show through mergeable_well_formedness 
                     that Hcid_store is false.
                 *)
                subst.
                find_and_invert_mergeable_states_well_formed.
                simpl in *.
                unfold CS.is_program_component, CS.is_context_component,
                turn_of, CS.state_turn, ic, negb in Hcomp.
                match goal with
                |
                H: prog_interface c = prog_interface c',
                   H1: Pointer.component (CS.state_pc s1') = Pointer.component pc1,
                       H2: Pointer.component (CS.state_pc s1') =
                           Pointer.component pc2''
                |- _ => rewrite <- H1, H2, H in Hcomp
                end.
                rewrite (Pointer.inc_preserves_component) in Hcid_store. 
                  by rewrite Hcid_store in Hcomp. 
            }

            split. (* split into 2 subgoals. *)
            ++ intros original_addr Horiginal_addr1 Horiginal_addr2.
               
               (* destruct whether original_addr == address stored-at, and
                  obtain a contradiction (in the true case) to the key fact above.
                  
                  And in the false case, use Memory.load_after_store to reuse
                  the assumption about mem2'' (H5).
                *)
               
               destruct (@pair_eq
                           nat_eqType nat_eqType
                           original_addr
                           (cid_store, bid_store)
                        ) eqn:eq_original_addr.
               ** unfold pair_eq in *. simpl in *.
                  pose proof (andb_prop _ _ eq_original_addr) as [Hcid Hbid].
                  assert (original_addr.1 = cid_store) as Hcid1. by apply/eqP.
                  assert (original_addr.2 = bid_store) as Hbid1. by apply/eqP.
                  subst.
                  rewrite <- surjective_pairing in Hstore_addr_fact.
                    by pose proof (Hstore_addr_fact Horiginal_addr1).
               **  match goal with
                   | H: mem_of_part_not_executing_rel_original_and_recombined_at_internal
                          _ _ _ _ _ _ |- _ =>
                     unfold
                       mem_of_part_not_executing_rel_original_and_recombined_at_internal
                       in H;
                       destruct H as [Hshift_mem2'' _]
                   end.
                   specialize
                     (Hshift_mem2'' original_addr  Horiginal_addr1 Horiginal_addr2).
                   unfold memory_shifts_memory_at_private_addr,
                   memory_renames_memory_at_private_addr in *.
                   split.
                   --- simpl. simpl in Hshift_mem2''. intros.
                   pose proof (Memory.load_after_store
                                 mem2''
                                 (perm, cid_store, bid_store, offset_store)
                                 (Register.get r2 regs3'')
                                 mem3''
                                 (Permission.data,
                                  original_addr.1,
                                  original_addr.2,
                                  offset)
                              ) as Hmem2''_mem3''.
                   (* Notation NOT WORKING *)
                   destruct (@eq_op
                               (prod_eqType
                                  (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                               nat_eqType)
                                  Extra.Z_eqType)
                               (Permission.data,
                                original_addr.1,
                                original_addr.2, offset)
                               (perm, cid_store,
                                bid_store,
                                offset_store)
                            ) eqn:Heq.
                   +++ (* case true; derive a contradiction to eq_original_addr *)
                     do 3 (rewrite <- pair_eqE in Heq;
                           unfold pair_eq in Heq). simpl in Heq.
                     unfold pair_eq in eq_original_addr.
                     pose proof andb_false_iff as [Hifandbfalse _].
                     pose proof (Hifandbfalse eq_original_addr) as [Hf1 | Hf1];
                       by rewrite Hf1 !andb_false_r !andb_false_l in Heq.
                   +++ (* case false; now use Hmem2''_mem3'' *)
                     destruct Hshift_mem2'' as [Hrewr _].
                     erewrite Hrewr; eauto.
                     setoid_rewrite <- Hmem2''_mem3''; eauto.
                   --- simpl. simpl in Hshift_mem2''. intros ? ? Hload.
                   pose proof (Memory.load_after_store
                                 mem2''
                                 (perm, cid_store, bid_store, offset_store)
                                 (Register.get r2 regs3'')
                                 mem3''
                                 (Permission.data,
                                  original_addr.1,
                                  original_addr.2,
                                  offset)
                              ) as Hmem2''_mem3''.
                   (* Notation NOT WORKING *)
                   destruct (@eq_op
                               (prod_eqType
                                  (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                               nat_eqType)
                                  Extra.Z_eqType)
                               (Permission.data,
                                original_addr.1,
                                original_addr.2, offset)
                               (perm, cid_store,
                                bid_store,
                                offset_store)
                            ) eqn:Heq.
                   +++ (* case true; derive a contradiction to eq_original_addr *)
                     do 3 (rewrite <- pair_eqE in Heq;
                           unfold pair_eq in Heq). simpl in Heq.
                     unfold pair_eq in eq_original_addr.
                     pose proof andb_false_iff as [Hifandbfalse _].
                     pose proof (Hifandbfalse eq_original_addr) as [Hf1 | Hf1];
                       by rewrite Hf1 !andb_false_r !andb_false_l in Heq.
                   +++ destruct Hshift_mem2'' as [_ Hrewr].
                       specialize (Hrewr offset v' Hload) as [v_exists Hv_exists].
                       eexists.
                       setoid_rewrite Hmem2''_mem3''; eauto.
            ++ intros cid Hcid. simpl.
               unfold Memory.store in *. simpl in *.
               destruct (perm =? Permission.data); try discriminate.
               destruct (mem2'' cid_store) as [cMem|] eqn:ecMem; try discriminate.
               destruct (ComponentMemory.store cMem bid_store offset_store
                                               (Register.get r2 regs3''))
                 as [cMem'|] eqn:estore;
                 try discriminate.
               match goal with | H: Some _ = Some _ |- _ => inversion H end.
               rewrite setmE.
               destruct (cid == cid_store) eqn:e; rewrite e.
               ** assert (ComponentMemory.next_block cMem =
                          ComponentMemory.next_block cMem') as Hnextblockeq.
                  by eapply ComponentMemory.next_block_store_stable; eauto.
                  unfold
                  mem_of_part_not_executing_rel_original_and_recombined_at_internal
                    in *.
                  unfold omap, obind, oapp in *. rewrite <- Hnextblockeq.
                  assert (cid = cid_store). by apply/eqP. subst.
                  
                  match goal with
                  | H1: _ /\ _
                    |- _ => destruct H1 as [_ G] end.
                  erewrite <- G; auto.
                   by rewrite ecMem.
               ** unfold
                    mem_of_part_not_executing_rel_original_and_recombined_at_internal
                   in *.
                  by intuition.
               
               
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.

      + (* IJal *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eapply find_label_in_component_1; eauto.
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IJump *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eauto.
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBnz *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              assert (Pointer.component pc2'' = Pointer.component pc3'') as Hpc2''.
              {
                eapply find_label_in_procedure_1; eauto. 
              }
              by rewrite <- Hpc2''.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IBnz *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            inversion H; eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.
      + (* IAlloc *)
        inversion IHstar''.
        * eapply mergeable_internal_states_p_executing; try eassumption.
          -- (* well-formedness is left *)
            find_and_invert_mergeable_states_well_formed;
              eapply mergeable_states_well_formed_intro; try eassumption.
            ++ (* is_prefix *)
              unfold CSInvariants.is_prefix in *.
              eapply star_right; try eassumption.
              ** by rewrite E0_right.
            (*++ eapply Hgood_prog''.
               (* is_prefix *)
               unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** by rewrite E0_right.*)
            ++ (* Pointer.component = Pointer.component *)
              simpl in *.
              match goal with
              | H: Pointer.component (CS.state_pc s1') = Pointer.component pc2'' |- _
                => rewrite H
              end.
                by rewrite Pointer.inc_preserves_component.
          -- (* mem of part not executing *)
            unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal
              in *.

            (* key fact to prove is that the address that is allocated *)
            (* does not satisfy the condition \in domm (prog_interface c') *)
            match goal with
            | Halloc: Memory.alloc _ _ _ = _ |- _ =>
              pose proof Memory.component_of_alloc_ptr _ _ _ _ _ Halloc as Hptr_comp
            end.
            
            find_and_invert_mergeable_states_well_formed.
            pose proof CS.is_program_component_pc_notin_domm _ _ Hcomp.
            unfold ic in *. simpl in *.
            
            split.
            ++ intros original_addr.
              (* then, destruct original_addr equals the allocated address *)
              destruct (original_addr == (Pointer.component ptr, Pointer.block ptr))
                       eqn:Heqptr.
              **
                (* in the true case, rely on the key fact above (i.e., Hptr_comp)
                   to prove the goal vacuously. *)
                assert (original_addr = (Pointer.component ptr, Pointer.block ptr))
                  as Heqptr2. by apply/eqP.
                 destruct original_addr. intros Hcontra. inversion Heqptr2. subst.
                 simpl in *.
                 rewrite Hptr_comp in Hcontra.
                 match goal with
                 | H: _ = Pointer.component pc2'',
                      Hiface: prog_interface c = _
                   |- _ => rewrite <- H, <- Hiface in Hcontra
                 end.

                 match goal with
                 | Hnotin: is_true (negb _) (* too hacky *) |- _ =>
                   unfold negb in Hnotin;
                     by rewrite Hcontra in Hnotin
                 end.
              ** 
                (* in the false case, rely on some "load_after_alloc" lemma to
                   use the assumption in H4. *)

                unfold memory_shifts_memory_at_private_addr,
                memory_renames_memory_at_private_addr in *.
                intros Horiginal1 Horiginal2.
                split.
                --- intros offset v.

                match goal with
                | Halloc: Memory.alloc _ _ _ = _ |- _ =>
                  pose proof (Memory.load_after_alloc _ _ _ _ _
                                                      (Permission.data,
                                                       original_addr.1,
                                                       original_addr.2,
                                                       offset)
                                                      Halloc
                             ) as Hload_alloc
                end.
                simpl in *.

                rewrite Hload_alloc.
                +++ match goal with
                    | Hmem_invariant: _ /\ _ (* too hacky *) |- _ =>
                      destruct Hmem_invariant as [Hshift _]; eapply Hshift; eauto
                    end.
                +++ unfold not. intros Heq.
                    rewrite <- surjective_pairing in Heq. subst.
                      by rewrite eqxx in Heqptr.
                --- intros offset v.

                match goal with
                | Halloc: Memory.alloc _ _ _ = _ |- _ =>
                  pose proof (Memory.load_after_alloc _ _ _ _ _
                                                      (Permission.data,
                                                       original_addr.1,
                                                       original_addr.2,
                                                       offset)
                                                      Halloc
                             ) as Hload_alloc
                end.
                simpl in *.

                rewrite Hload_alloc.
                +++ match goal with
                    | Hmem_invariant: _ /\ _ (* too hacky *) |- _ =>
                      destruct Hmem_invariant as [Hshift _]; eapply Hshift; eauto
                    end.
                +++ unfold not. intros Heq.
                    rewrite <- surjective_pairing in Heq. subst.
                      by rewrite eqxx in Heqptr.
            ++ assert (Pointer.component pc2'' \in domm (prog_interface c') = false)
                as Hcontra.
               {
                 rewrite <- Hifc_cc', <- Hpccomp_s'_s'', Hpccomp_s'_s.
                 unfold negb in H5.
                 destruct (Pointer.component pc1 \in domm (prog_interface c)) eqn:e;
                   auto.
                 by rewrite e in H5.
               }

               unfold Memory.alloc in *.
               destruct (mem2'' (Pointer.component pc2'')) as [memC|] eqn:ememc;
                 try discriminate.
               destruct (ComponentMemory.alloc memC (Z.to_nat size))
                 as [memC' b] eqn:ememc'.
               
               match goal with | H: Some _ = Some _ |- _ =>
                                 inversion H as [H'] end.
               intros cid Hcid. rewrite setmE.
               destruct (cid == Pointer.component pc2'') eqn:ecid.
               ** assert (cid = Pointer.component pc2''). by apply/eqP.
                  subst. by rewrite Hcid in Hcontra.
               ** rewrite ecid.
                  by intuition.

        * (* Here, we are in the case of c' executing.
             Obtain a contradiction by relying on Hcomp 
             and on the "CS.is_context_component" assumption. *)
          find_and_invert_mergeable_states_well_formed.
          simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
          simpl in *. unfold ic in *.
          match goal with
          | H: Pointer.component pc1' = Pointer.component pc1 |- _ =>
            rewrite <- H in Hcomp
          end.
          unfold negb in Hcomp.
          match goal with
          | H: is_true (@in_mem _ (Pointer.component pc1') _)  |- _ =>
            rewrite H in Hcomp
          end.
          intuition.

          
      + pose proof CS.silent_step_non_inform_preserves_component _ _ _ Hstep23'' as
            Hpceq.
        simpl in Hpceq. by subst.
      + pose proof CS.silent_step_non_inform_preserves_component _ _ _ Hstep23'' as
            Hpceq.
        simpl in Hpceq. by subst.
  Qed.

   (*[DynShare]

     This lemma should intuitively continue to hold (under some weaker
     definition of mergeable_states).

     The current proof that is commented below relies on "to_partial_memory_epsilon_star",
     the lemma that does not hold any more in the [DynShare] world.

     We should be able to find a weaker version of "to_partial_memory_epsilon_star"
     that will help us complete the proof of this lemma.

    *)

    (*;
        try (pose proof to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' Hstep23'' as Hmem23'';
             simpl in Hmem23''; rewrite Hmem23'');
        reflexivity.
  Qed.
     *)

  (* RB: NOTE: By itself, this lemma no longer says anything interesting, in
     fact it is trivial because [s1'] and [s1''] are not really related. To add
     significance to it, one may consider adding the mergeability relation, but
     then we need to know what [s1] is doing. *)
  Lemma context_epsilon_star_merge_states s1 s1' s1'' s2'' t t' t'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s1 s2' s2'' t t' t''.
  Admitted. (* RB: TODO: Currently not useful, maybe with tweaks later? *)
  (* Proof. *)
  (*   intros Hmerge1 Hcomp1 Hstar12''. *)
  (*   remember E0 as t12'' eqn:Ht12''. *)
  (*   revert s1 s1' Hmerge1 Hcomp1 Ht12''. *)
  (*   induction Hstar12''; intros; subst. *)
  (*   - exists s1'. now apply star_refl. *)
  (*   - (* Fix some names quickly for now... *) *)
  (*     rename s1 into s1''. rename s2 into s2''. rename s3 into s3''. rename s0 into s1. *)
  (*     (* Back to the proof. *) *)
  (*     apply Eapp_E0_inv in Ht12'' as [? ?]; subst. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s1 s1' s2''). *)
  (*     { *)
  (*       eapply merge_states_silent_star; try eassumption. *)
  (*       eapply star_step; [eassumption | eapply star_refl | reflexivity]. *)
  (*     } *)
  (*     exact (IHHstar12'' _ _ Hmerge2 Hcomp1 eq_refl). *)
  (* Qed. *)

  (* RB: NOTE: This lemma no longer holds as currently stated: even if [p]
     steps silently (no calls and returns), it can perform memory-altering
     operations that will not be reflected in [s1']. It can be repaired by
     adding a matching [Step] on [sem']. *)
  Lemma threeway_multisem_mergeable_step_E0 s1 s2 s1' s1'' t t' t'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t t' t'' ->
    Step sem s1 E0 s2 ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s1'' t t' t''.
  Abort. (* RB: TODO: Check repair, uses. Should be provable, but see
            [threeway_multisem_step_E0]. *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12. *)
  (*   inversion Hmerge1 *)
  (*     as [s0 s0' s0'' t t' t'' n n' n'' Hwfp Hwfc Hwfp' Hwfc' *)
  (*         Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed' *)
  (*         Hini Hini' Hini'' Hstar01 Hstar01' Hstar01'' Hrel' Hrel'']. *)
  (*   apply mergeable_states_intro with s0 s0' s0'' t t' t'' n n' n''; *)
  (*     try assumption. *)
  (*   eapply (star_right _ _ Hstar01 Hstep12); try eassumption. now rewrite E0_right. *)
  (* Qed. *)

  (* RB: NOTE: The structure follows closely that of
     threeway_multisem_star_program. *)
  (* RB: NOTE: Expect the proof to hold, but the statement is in all likelihood
     not sufficiently informative, as the sequence of steps taken by [s1'] will
     be hidden by the existential. *)

  (* AEK: This lemma is probably redundant.  *)
  (*Lemma threeway_multisem_mergeable_program
        s1 s1' s1'' t1 t1' t1'' t2 t2'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t2   s2   ->
    Star sem'' s1'' t2'' s2'' ->
    behavior_rel_behavior_all_cids n n'' (FTbc t2) (FTbc t2'') ->
    (*mem_rel2 n n'' (CS.state_mem s1, t2) (CS.state_mem s1'', t2'') p -> *)
  exists s2' t2',
    mergeable_internal_states p c p' c' n n'' s2 s2' s2''
                     (t1 ++ t2) (t1' ++ t2') (t1'' ++ t2'').
  Admitted.*) (* RB: TODO: Wait to see how this will be useful. *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstar12 Hstar12'' Hrel''. *)
  (*   inversion Hmerge1 *)
  (*     as [s0 s0' s0'' t1 t1' t1'' ? n' ? Hwfp Hwfc Hwfp' Hwfc' *)
  (*         Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed Hprog_is_closed' *)
  (*         Hini Hini' Hini'' Hstar01 Hstar01' Hstar01'' Hrel Hrel']. *)
  (*   (* Assume that we can not only execute the star in the recombined context, *)
  (*      but also establish the trace relation, here on partial traces. *) *)
  (*   assert (exists t2' s2', *)
  (*              Star sem' s1' t2' s2' /\ *)
  (*              behavior_rel_behavior_all_cids n n' (FTbc t2) (FTbc t2')) *)
  (*     as [t2' [s2' [Hstar12' Hrel2']]] *)
  (*     by admit. *)
  (*   (* If we do so, we can begin to reconstruct the mergeability relation... *) *)
  (*   exists s2'. *)
  (*   eapply mergeable_states_intro; try assumption. *)
  (*   eassumption. eassumption. eassumption. *)
  (*   (* The various stars compose easily (and in the way the old proof was *)
  (*      written). *) *)
  (*   instantiate (1 := t1 ++ t2). eapply star_trans; try eassumption; reflexivity. *)
  (*   instantiate (1 := t1' ++ t2'). eapply star_trans; try eassumption; reflexivity. *)
  (*   instantiate (1 := t1'' ++ t2''). eapply star_trans; try eassumption; reflexivity. *)
  (*   (* And it should be possible to compose the relations, possibly using some *)
  (*      of the stars. *) *)
  (*   instantiate (1 := n'). instantiate (1 := n). admit. *)
  (*   instantiate (1 := n''). admit. *)
  (* (* Qed. *) *)

  (* Ltac t_threeway_multisem_step_E0 := *)
  (*   CS.step_of_executing; *)
  (*   try eassumption; try reflexivity; *)
  (*   (* Solve side goals for CS step. *) *)
  (*   match goal with *)
  (*   | |- Memory.load _ _ = _ => *)
  (*     eapply program_load_to_partialized_memory; *)
  (*     try eassumption; [now rewrite Pointer.inc_preserves_component] *)
  (*   | |- Memory.store _ _ _ = _ => *)
  (*     eapply program_store_to_partialized_memory; eassumption *)
  (*   | |- find_label_in_component _ _ _ = _ => *)
  (*     eapply find_label_in_component_recombination; eassumption *)
  (*   | |- find_label_in_procedure _ _ _ = _ => *)
  (*     eapply find_label_in_procedure_recombination; eassumption *)
  (*   | |- Memory.alloc _ _ _ = _ => *)
  (*     eapply program_alloc_to_partialized_memory; eassumption *)
  (*   | _ => idtac *)
  (*   end; *)
  (*   (* Apply linking invariance and solve side goals. *) *)
  (*   eapply execution_invariant_to_linking; try eassumption; *)
  (*   [ congruence *)
  (*   | apply linkable_implies_linkable_mains; congruence *)
  (*   | apply linkable_implies_linkable_mains; congruence *)
  (*   | eapply is_program_component_in_domm; eassumption *)
  (*   ]. *)

  (* Ltac solve_executing_threeway_multisem_step_E0 Hlinkable pc1 := *)
  (*   eapply execution_invariant_to_linking with (c1 := c); eauto; *)
  (*   match goal with *)
  (*   | Hcc' : prog_interface c = _ |- _ => *)
  (*     match goal with *)
  (*       Hcomp1 : is_true (CS.is_program_component (?gps2, ?mem2, ?regs2, pc1, ?addrs2) _) *)
  (*       |- _ => *)
  (*       match goal with *)
  (*       | |- linkable _ _ => rewrite Hcc' in Hlinkable; exact Hlinkable *)
  (*       | |- linkable_mains p c => eapply linkable_implies_linkable_mains; eauto *)
  (*       | |- linkable_mains p c' => eapply linkable_implies_linkable_mains; eauto; *)
  (*                                   rewrite Hcc' in Hlinkable; exact Hlinkable *)
  (*       | |- _ => *)
  (*         eapply is_program_component_pc_in_domm *)
  (*           with (s := (gps2, mem2, regs2, pc1, addrs2)) *)
  (*                (c := c); eauto *)
  (*       end *)
  (*     end *)
  (*   end. *)

  (* RB: NOTE: Another trivial lemma that needs to add the mergeability relation
     to make up for the information lost by removing the computable state
     merging functions and hiding the third execution in the relation. *)
  Theorem threeway_multisem_step_E0 s1 s1' s1'' t1 t1' t1'' s2 :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Step sem  s1  E0 s2  ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s1'' t1 t1' t1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstep12.
    (* NOTE: Keep the context light for now, rewrite lemmas are no longer
       directly applicable, as [s2'] is not computed explicitly. *)
    (* inversion Hmerge1 as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hmergeable_ifaces _ _ _ _ _ _ _ _ _ _ _ _]. *)
    (* Derive some useful facts and begin to expose state structure. *)
    (* inversion Hmergeable_ifaces as [Hlinkable _]. *)
    (* rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)
    pose proof CS.silent_step_non_inform_preserves_program_component
         _ _ _ _ Hcomp1 Hstep12 as Hcomp2.
    (* pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12 *)
      (* as Hmerge2. *)
    (* rewrite (mergeable_states_merge_program Hcomp2 Hmerge2). *)
    (* NOTE: As usual, we should proceed by cases on the step. *)
    simpl in Hstep12.
    inversion Hstep12 as [? t ? ? Hstep12' DUMMY Ht DUMMY'];
      subst; rename Hstep12 into Hstep12_.
    inversion Hstep12'; subst; rename Hstep12' into Hstep12'_.

    - (* INop *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; eauto. exact (CS.Nop _ _ _ _ _ Hex'). (* Make more implicit later. *)
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; eauto. by eapply CS.Nop.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.
  
    - (* ILabel *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; eauto. exact (CS.Label _ _ _ _ _ _ Hex'). (* Make more implicit later. *)
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; eauto. eapply CS.Label; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IConst *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Const.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Const; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- inversion Hregsp as [Hregs]. simpl in *. constructor. intros reg.
             unfold Register.set, Register.get in *.
             destruct (Register.to_nat reg == Register.to_nat r) eqn:Hreg;
               rewrite setmE Hreg; specialize (Hregs reg).
             ++ rewrite setmE Hreg.
                assert ((exists i, v = IInt i)
                        \/ (exists perm cid bid off,
                               v = IPtr (perm, cid, bid, off) /\
                               cid \in domm (prog_interface p)
                           )
                       ) as Hv.
                {
                  (* Here, we need to show that the value v can only be a pointer *)
                  (* whose cid \in domm (prog_interface p).                       *)
                  (* This fact should follow from "well_formed_program p".        *)
                
                  admit.
                }
                destruct Hv as [[i Hvi] | [perm [cid [bid [off [Hvptr Hcid]]]]]].
                ** left. by subst.
                ** left. subst. simpl.
                   destruct (perm =? Permission.data) eqn:eperm; auto.
                   unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr. simpl.
                     by rewrite Hcid sigma_shifting_lefttoright_option_n_n_id.
             ++ rewrite setmE Hreg. assumption.
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IMov *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Mov.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Mov; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (* regs_rel_of_executing_part *)
            constructor.
            match goal with
            | H: regs_rel_of_executing_part _ _ _ _ _ _ |- _ => inversion H as [Hreg] end.
            intros reg.
            pose proof (Hreg r1)
              as [Hget_shift | [Hshift_r1_None Heq1]];
              pose proof (Hreg reg)
              as [Hreg_shift | [Hshift_reg_None Heq2]];
              destruct ((Register.to_nat reg == Register.to_nat r2)) eqn:Hreg_r; simpl;
                unfold Register.set, Register.get; rewrite !setmE Hreg_r.
            ++ left. by simpl in *.
            ++ left. eauto.
            ++ left. by simpl in *.
            ++ right. split; eauto.
            ++ right. split.
               ** by simpl in *.
               ** by simpl in *.
            ++ left. eauto.
            ++ right. split; eauto.
            ++ right. split; eauto.

      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBinOp *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
          + unfold CS.is_program_component,
            CS.is_context_component, turn_of, CS.state_turn in *.
            unfold negb in Hcomp1.
            pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
            assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_p.
        {
            by specialize (is_program_component_pc_in_domm Hcomp1 Hmerge1).
        }

        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.BinOp.
          -- exact Hex'.
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
                 by rewrite E0_right.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.BinOp; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (* regs_rel_of_executing_part *)
            constructor.
            match goal with
            | H: regs_rel_of_executing_part _ _ _ _ _ _ |- _ =>
              inversion H as [Hreg] end.
            intros reg. simpl in *.
            destruct ((Register.to_nat reg == Register.to_nat r3)) eqn:Hreg_r; simpl.
            ++ unfold Register.set, Register.get in *. rewrite !setmE Hreg_r.
               unfold result, shift_value_option, rename_value_option,
               rename_value_template_option, sigma_shifting_wrap_bid_in_addr,
               rename_addr_option in *.

               pose proof (Hreg r1) as rel_r1.
               pose proof (Hreg r2) as rel_r2.
               pose proof (Hreg r3) as rel_r3.

               destruct op; simpl.
               **
                 (* Add *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq'
                                               [rel_r1_shr_t1 rel_r1_shr_t1']]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq'
                                              [rel_r2_shr_t1 rel_r2_shr_t1']]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.add;
                    (* 15 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          );
                    (* 9 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          ).

                 (* 8 subgoals *)
                  --- destruct (perm2 =? Permission.data) eqn:eperm2.
                      +++ 
                        destruct (sigma_shifting_lefttoright_option
                                    (n cid2)
                                    (if cid2 \in domm (prog_interface p)
                                     then n cid2 else n'' cid2)
                                    bid2) as [bid2_shift|] eqn:ebid2_shift;
                          rewrite ebid2_shift in Hrel_r2_eq; try discriminate;
                            rewrite ebid2_shift.
                        inversion Hrel_r2_eq; subst. by left.
                      +++ 
                        inversion Hrel_r2_eq; subst. by left.
                  --- destruct (perm2 =? Permission.data) eqn:eperm2;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid2)
                                  (if cid2 \in domm (prog_interface p)
                                   then n cid2 else n'' cid2)
                                  bid2) as [bid2_shift|] eqn:ebid2_shift;
                        rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                      rewrite ebid2_shift.
                      inversion rel_r2_eq'; subst.
                      right. by intuition.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1.
                      +++
                        destruct (sigma_shifting_lefttoright_option
                                    (n cid1)
                                    (if cid1 \in domm (prog_interface p)
                                     then n cid1 else n'' cid1)
                                    bid1) as [bid1_shift|] eqn:ebid1_shift;
                          rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                        rewrite ebid1_shift.
                        inversion Hrel_r1_eq. subst. by left.
                      +++
                        inversion Hrel_r1_eq. subst. by left.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                      rewrite ebid1_shift. inversion rel_r1_eq'. subst.
                      right; by intuition.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                  --- destruct (perm1 =? Permission.data) eqn:eperm1;
                        try discriminate.
                      destruct (sigma_shifting_lefttoright_option
                                  (n cid1)
                                  (if cid1 \in domm (prog_interface p)
                                   then n cid1 else n'' cid1)
                                  bid1) as [bid1_shift|] eqn:ebid1_shift;
                        rewrite ebid1_shift in Hrel_r1_eq; try discriminate.


               **
                 (* Minus *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq'
                                               [rel_r1_shr_t1 rel_r1_shr_t1']]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq'
                                              [rel_r2_shr_t1 rel_r2_shr_t1']]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.sub;
                    (* 31 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 13 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).

                 (* 10 subgoals *)
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.

                 --- destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       rewrite ebid1_shift.
                       inversion Hrel_r1_eq. subst. by left.
                     +++
                       inversion Hrel_r1_eq. subst. by left.
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                           
                 --- destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                     assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2) bid2)
                       as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                     inversion rel_r2_eq'. subst.
                     destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid1)
                                     (if cid1 \in domm (prog_interface p)
                                      then n cid1 else n'' cid1) bid1)
                         as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                         inversion Hrel_r1_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid12.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                         ----
                           assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                         ----
                           simpl in *. rewrite ebid2_shift.
                           destruct (bid1' =? bid2') eqn:ebid1'2'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                               by rewrite G sigma_shifting_lefttoright_option_n_n_id
                               in ebid2_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                               pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r1_eq. subst.
                       rewrite eperm1 !andFb. by left.

                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1)
                                 bid1) as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     rewrite ebid1_shift. inversion rel_r1_eq'. subst.
                     by right; intuition.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                               by rewrite G sigma_shifting_lefttoright_option_n_n_id
                               in ebid1_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       assert (Permission.data = perm2'). by apply beq_nat_true.
                       by subst.

                 --- inversion rel_r1_eq'. subst.
                     inversion rel_r2_eq'. subst.

                     by destruct ((perm1' =? perm2') &&
                                  (cid1' =? cid2') &&
                                  (bid1' =? bid2')); auto.

               **
                 (* Mul *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq'
                                               [rel_r1_shr_t1 rel_r1_shr_t1']]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq'
                                              [rel_r2_shr_t1 rel_r2_shr_t1']]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left).

                 (* 3 subgoals *)
                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.

                 --- destruct (perm1 =? Permission.data) eqn:eperm1;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1)
                                 bid1) as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.

                 --- destruct (perm2 =? Permission.data) eqn:eperm2;
                       try discriminate.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid2_shift|] eqn:ebid2_shift;
                       rewrite ebid2_shift in Hrel_r2_eq; try discriminate.




               **
                 (* Eq *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq'
                                               [rel_r1_shr_t1 rel_r1_shr_t1']]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq'
                                              [rel_r2_shr_t1 rel_r2_shr_t1']]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.eq;
                    (* 27 subgoals *)

                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 11 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).

                 (* 8 subgoals *)
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                   assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                   
                   destruct (sigma_shifting_lefttoright_option
                               (n cid2)
                               (if cid2 \in domm (prog_interface p)
                                then n cid2 else n'' cid2) bid2)
                     as [bid2_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                   inversion rel_r2_eq'. subst.
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                   +++
                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion Hrel_r1_eq. subst.
                     rewrite andTb.
                     destruct (cid1' =? cid2') eqn:ecid12.
                     ***
                       assert (cid1' = cid2'). by apply beq_nat_true. subst.
                       rewrite andTb.
                       destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                       ----
                         assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                       ----
                         simpl in *. rewrite ebid2_shift.
                         destruct (bid1' =? bid2') eqn:ebid1'2'.
                         ****
                           assert (bid1' = bid2'). by apply beq_nat_true. subst.
                           assert (CSInvariants.wf_ptr_wrt_cid_t
                                     (Pointer.component pc)
                                     t1'
                                     (Permission.data, cid2', bid2', off2'))
                             as Hwf.
                           {
                             eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                               last (unfold Register.get;
                                       by erewrite eregs1'r2).
                             eapply CSInvariants.wf_state_wf_reg
                               with (s := (gps1', mem1', regs1', pc)); eauto.
                             eapply CSInvariants.is_prefix_wf_state_t;
                               last exact Hpref_t'.
                             eapply linking_well_formedness; eauto.
                             unfold mergeable_interfaces in *.
                               by rewrite <- Hifc_cc'; intuition.
                           }
                           inversion Hwf as [| ? ? ? ? Hshr]; subst.
                           -----
                             assert (Pointer.component pc \in domm
                                                                (prog_interface p))
                             as G. by eapply mergeable_states_program_component_domm;
                                     eauto.
                             by rewrite G sigma_shifting_lefttoright_option_n_n_id
                             in ebid2_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                             pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                             rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                         ****
                             by left.
                     *** rewrite !andFb. by left.
                   +++
                     inversion Hrel_r1_eq. subst.
                     rewrite eperm1 !andFb. by left.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                               by rewrite G sigma_shifting_lefttoright_option_n_n_id
                               in ebid1_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       
                 ---
                   inversion rel_r1_eq'. inversion rel_r2_eq'. subst. by left. 

                 
               ** 
                 (* Leq *)
                 destruct (regs (Register.to_nat r1)) 
                   as [[i1 | [[[perm1 cid1] bid1] off1] |]|] eqn:eregsr1;
                    destruct (regs1' (Register.to_nat r1))
                    as [[i1' | [[[perm1' cid1'] bid1'] off1'] |]|] eqn:eregs1'r1;
                    destruct rel_r1 as [rel_r1_eq |
                                         [rel_r1_eq
                                            [rel_r1_eq'
                                               [rel_r1_shr_t1 rel_r1_shr_t1']]]];
                    try discriminate;
                    destruct (regs (Register.to_nat r2)) 
                      as [[i2 | [[[perm2 cid2] bid2] off2] |]|] eqn:eregsr2;
                    destruct (regs1' (Register.to_nat r2))
                      as [[i2' | [[[perm2' cid2'] bid2'] off2'] |]|] eqn:eregs1'r2;
                    destruct rel_r2 as [rel_r2_eq |
                                        [rel_r2_eq
                                           [rel_r2_eq'
                                              [rel_r2_shr_t1 rel_r2_shr_t1']]]];
                    try discriminate;
                    try (by left);
                    inversion rel_r1_eq as [Hrel_r1_eq];
                    inversion rel_r2_eq as [Hrel_r2_eq];
                    subst;
                    try (by left);
                    unfold Pointer.leq;
                    (* 27 subgoals *)
                    
                    try by (
                            destruct (perm1 =? Permission.data) eqn:eperm1;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid1)
                                        (if cid1 \in domm (prog_interface p)
                                         then n cid1 else n'' cid1)
                                        bid1) as [bid1_shift|] eqn:ebid1_shift;
                            rewrite ebid1_shift in Hrel_r1_eq; try discriminate
                          );
                    (* 11 subgoals *)

                    try by (
                            destruct (perm2 =? Permission.data) eqn:eperm2;
                            try discriminate;
                            destruct (sigma_shifting_lefttoright_option
                                        (n cid2)
                                        (if cid2 \in domm (prog_interface p)
                                         then n cid2 else n'' cid2)
                                        bid2) as [bid2_shift|] eqn:ebid2_shift;
                            rewrite ebid2_shift in Hrel_r2_eq; try discriminate
                          ).


                 (* 8 subgoals *)
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                     +++
                       destruct (sigma_shifting_lefttoright_option
                                   (n cid1)
                                   (if cid1 \in domm (prog_interface p)
                                    then n cid1 else n'' cid1)
                                   bid1) as [bid1_shift|] eqn:ebid1_shift;
                         rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                       inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2)
                                     bid2) as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         destruct ((perm1' =? perm2') &&
                                   (cid1' =? cid2') &&
                                   (bid1 =? bid2)) eqn:eandb.
                         ----
                           symmetry in eandb.
                           apply andb_true_eq in eandb as [eandb1 eandb2].
                           apply andb_true_eq in eandb1 as [eandb1 eandb3].
                           rewrite <- eandb1, <- eandb3, !andTb.
                           
                           assert (cid1' = cid2'). by apply beq_nat_true. subst.
                           assert (bid1 = bid2). by apply beq_nat_true. subst.
                           
                           rewrite ebid1_shift in ebid2_shift. inversion ebid2_shift.
                           subst.
                           
                           left. by rewrite <- beq_nat_refl.
                         ----
                           left.
                           destruct (perm1' =? perm2') eqn:eperm12.
                           ++++
                             destruct (cid1' =? cid2') eqn:ecid12.
                             ****
                               destruct (bid1 =? bid2) eqn:ebid12; try discriminate.
                               assert (cid1' = cid2'). by apply beq_nat_true. subst.
                               assert (bid1' <> bid2') as Hneq.
                               {
                                 unfold not. intros. subst.
                                 assert (bid1 = bid2).
                                   by eapply
                                        sigma_shifting_lefttoright_option_Some_inj;
                                     eauto.
                                   subst.
                                     by rewrite <- beq_nat_refl in ebid12.
                               }
                               assert (bid1' =? bid2' = false) as G.
                                 by rewrite Nat.eqb_neq.

                                 by rewrite G !andbF.

                             ****
                               by rewrite !andFb.
                           ++++
                               by rewrite !andFb.
                               
                       ***
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm1' = Permission.data). by apply beq_nat_true.
                           subst.
                           apply beq_nat_false in eperm2. unfold not in eperm2.
                           destruct (Permission.data =? perm2') eqn:econtra; auto.
                           assert (Permission.data = perm2'). by apply beq_nat_true.
                           by subst.
                         }
                         left. by rewrite G !andFb.
                     +++
                       left. inversion Hrel_r1_eq. subst.
                       destruct (perm2 =? Permission.data) eqn:eperm2.
                       ***
                         destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                           as [bid2_shift|] eqn:ebid2_shift;
                           rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         assert (perm1' =? perm2' = false) as G.
                         {
                           assert (perm2' = Permission.data). by apply beq_nat_true.
                           subst. assumption.
                         }
                           by rewrite G !andFb.
                       ***
                         inversion Hrel_r2_eq. subst.
                           by destruct ((perm1' =? perm2') &&
                                        (cid1' =? cid2') &&
                                        (bid1' =? bid2')).
                 --- 
                   destruct (perm2 =? Permission.data) eqn:eperm2; try discriminate.

                   assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                   
                   destruct (sigma_shifting_lefttoright_option
                               (n cid2)
                               (if cid2 \in domm (prog_interface p)
                                then n cid2 else n'' cid2) bid2)
                     as [bid2_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                   inversion rel_r2_eq'. subst.
                   destruct (perm1 =? Permission.data) eqn:eperm1.
                   +++
                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion Hrel_r1_eq. subst.
                     rewrite andTb.
                     destruct (cid1' =? cid2') eqn:ecid12.
                     ***
                       assert (cid1' = cid2'). by apply beq_nat_true. subst.
                       rewrite andTb.
                       destruct (bid1 =? bid2') eqn:ebid1_bid2'; auto.
                       ----
                         assert (bid1 = bid2'). by apply beq_nat_true. subst.
                           by rewrite ebid1_shift in ebid2_shift.
                       ----
                         simpl in *. rewrite ebid2_shift.
                         destruct (bid1' =? bid2') eqn:ebid1'2'.
                         ****
                           assert (bid1' = bid2'). by apply beq_nat_true. subst.
                           assert (CSInvariants.wf_ptr_wrt_cid_t
                                     (Pointer.component pc)
                                     t1'
                                     (Permission.data, cid2', bid2', off2'))
                             as Hwf.
                           {
                             eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                               last (unfold Register.get;
                                       by erewrite eregs1'r2).
                             eapply CSInvariants.wf_state_wf_reg
                               with (s := (gps1', mem1', regs1', pc)); eauto.
                             eapply CSInvariants.is_prefix_wf_state_t;
                               last exact Hpref_t'.
                             eapply linking_well_formedness; eauto.
                             unfold mergeable_interfaces in *.
                               by rewrite <- Hifc_cc'; intuition.
                           }
                           inversion Hwf as [| ? ? ? ? Hshr]; subst.
                           -----
                             assert (Pointer.component pc \in domm
                                                                (prog_interface p))
                             as G. by eapply mergeable_states_program_component_domm;
                                     eauto.
                             by rewrite G sigma_shifting_lefttoright_option_n_n_id
                             in ebid2_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r2_shr_t1'.
                             pose proof rel_r2_shr_t1' (cid2', bid2') as Hcontra.
                             rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                         ****
                             by left.
                     *** rewrite !andFb. by left.
                   +++
                     inversion Hrel_r1_eq. subst.
                     rewrite eperm1 !andFb. by left.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 ---
                   destruct (perm2 =? Permission.data) eqn:eperm2;
                     try discriminate;
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid2)
                                 (if cid2 \in domm (prog_interface p)
                                  then n cid2 else n'' cid2)
                                 bid2) as [bid1_shift|] eqn:ebid2_shift;
                     rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                 --- destruct (perm1 =? Permission.data) eqn:eperm1; try discriminate.

                     assert (perm1 = Permission.data). by apply beq_nat_true. subst.
                       
                     destruct (sigma_shifting_lefttoright_option
                                 (n cid1)
                                 (if cid1 \in domm (prog_interface p)
                                  then n cid1 else n'' cid1) bid1)
                       as [bid1_shift|] eqn:ebid1_shift;
                       rewrite ebid1_shift in Hrel_r1_eq; try discriminate.
                     inversion rel_r1_eq'. subst.
                     destruct (perm2 =? Permission.data) eqn:eperm2.
                     +++
                       assert (perm2 = Permission.data). by apply beq_nat_true. subst.
                       destruct (sigma_shifting_lefttoright_option
                                     (n cid2)
                                     (if cid2 \in domm (prog_interface p)
                                      then n cid2 else n'' cid2) bid2)
                         as [bid2_shift|] eqn:ebid2_shift;
                         rewrite ebid2_shift in Hrel_r2_eq; try discriminate.
                         inversion Hrel_r2_eq. subst.
                         rewrite andTb.
                         destruct (cid1' =? cid2') eqn:ecid21.
                       ***
                         assert (cid1' = cid2'). by apply beq_nat_true. subst.
                         rewrite andTb.
                         destruct (bid1' =? bid2) eqn:ebid2_bid1'; auto.
                         ----
                           assert (bid1' = bid2). by apply beq_nat_true. subst.
                           by rewrite ebid2_shift in ebid1_shift.
                         ----
                           simpl in *. rewrite ebid1_shift.
                           destruct (bid1' =? bid2') eqn:ebid2'1'.
                           ****
                             assert (bid1' = bid2'). by apply beq_nat_true. subst.
                             assert (CSInvariants.wf_ptr_wrt_cid_t
                                       (Pointer.component pc)
                                       t1'
                                       (Permission.data, cid2', bid2', off2'))
                                   as Hwf.
                             {
                               eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t;
                                 last (unfold Register.get;
                                         by erewrite eregs1'r2).
                               eapply CSInvariants.wf_state_wf_reg
                                 with (s := (gps1', mem1', regs1', pc)); eauto.
                               eapply CSInvariants.is_prefix_wf_state_t;
                                 last exact Hpref_t'.
                               eapply linking_well_formedness; eauto.
                               unfold mergeable_interfaces in *.
                                 by rewrite <- Hifc_cc'; intuition.
                             }
                             inversion Hwf as [| ? ? ? ? Hshr]; subst.
                             -----
                               assert (Pointer.component pc \in domm
                                                                  (prog_interface p))
                               as G. by eapply mergeable_states_program_component_domm;
                                       eauto.
                               by rewrite G sigma_shifting_lefttoright_option_n_n_id
                               in ebid1_shift.
                             -----
                               setoid_rewrite in_fset1 in rel_r1_shr_t1'.
                               pose proof rel_r1_shr_t1' (cid2', bid2') as Hcontra.
                               rewrite eqxx in Hcontra. unfold not in Hcontra.
                               by intuition.
                           ****
                             by left.
                       *** rewrite !andFb. by left.
                     +++
                       inversion Hrel_r2_eq. subst.
                       destruct (Permission.data =? perm2') eqn:perm2contra; auto.
                       assert (Permission.data = perm2'). by apply beq_nat_true.
                       by subst.

                 ---
                   inversion rel_r1_eq'. inversion rel_r2_eq'. subst. left. 
                     by destruct ((perm1' =? perm2') &&
                                  (cid1' =? cid2') &&
                                  (bid1' =? bid2')).


                     
            ++ unfold Register.set, Register.get in *.
               rewrite !setmE Hreg_r.
               pose proof (Hreg reg)
                 as [Hget_shift_reg | [HNone Heq]].
              ** left. assumption. 
              ** right. split; eauto.

      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
            by rewrite H_c' in Hcomp1.
            
    - (* ILoad *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)

        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_in.
        {
          by eapply mergeable_states_program_component_domm; eauto.
        }
            
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }


        (* ILoad-specific *)

        match goal with
        | H: Memory.load _ _ = Some _ |- _ =>
          specialize (Memory.load_some_permission mem ptr _ H) as Hperml
        end.
        destruct ptr as [[[perml cidl] bidl] offl].
        simpl in Hperml. subst.
        
        assert (CSInvariants.wf_ptr_wrt_cid_t
                  (Pointer.component pc) t1
                  (Permission.data, cidl, bidl, offl)
               ) as cidl_bidl_invariant.
        {
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - reflexivity.
        }

        unfold mem_of_part_executing_rel_original_and_recombined,
        memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
        memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr
         in Hmemp.
        simpl in Hmemp.
        destruct Hmemp as [Hmem_own [Hmem_shared Hmem_next_block]].
        
        assert (
            (cidl, bidl).1 \in domm (prog_interface p) ->
                               (
                                 Memory.load mem1' (Permission.data,
                                                    cidl, bidl, offl) =
                                 match
                                   rename_value_option
                                     (rename_addr_option
                                        (sigma_shifting_wrap_bid_in_addr
                                           (sigma_shifting_lefttoright_addr_bid
                                              n
                                              (fun cid : nat =>
                                                 if cid \in domm (prog_interface p)
                                                 then n cid else n'' cid)))) v
                                 with
                                 | Some v' => Some v'
                                 | None => Some v
                                 end)
          ) as Hmem_own1.
        {
          intros Hcidl.
          specialize (Hmem_own _ Hcidl) as [Hspec _].
          
          match goal with | H: Memory.load _ _ = _ |- _ => 
                              by specialize (Hspec _ _ H)
          end.
        }
        
                
        assert (CSInvariants.is_prefix
                  (gps,
                   mem,
                   Register.set
                     r2
                     v
                     regs,
                   Pointer.inc pc
                  )
                  prog
                    t1
               ) as Hprefix_t1_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }



        inversion Hregsp as [Hregs]. simpl in Hregs.
        specialize (Hregs r1) as Hregsr1.

        assert (exists ptr, Register.get r1 regs1' = Ptr ptr) as Hget_r1_ptr.
        {
          unfold shift_value_option, rename_value_option, rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.

          inversion Hregsr1 as [Hregs1'_r1 | [Hregs1'_r1 [Heq [Hnotshr1 Hnotshr2]]]].
          - match goal with
            | H: Register.get r1 regs = Ptr _ |- _ =>
              rewrite H in Hregs1'_r1
            end.
            simpl in *.
            destruct (sigma_shifting_lefttoright_option
                        (n cidl)
                        (if cidl \in domm (prog_interface p)
                         then n cidl else n'' cidl) bidl) eqn:eshift;
              rewrite eshift in Hregs1'_r1;
              try discriminate.
            inversion Hregs1'_r1.
              by eauto.
          - setoid_rewrite <- Heq.
            by eexists;
              match goal with
              | H: Register.get r1 regs = Ptr _ |- _ =>
                erewrite H
              end.
        }

        destruct Hget_r1_ptr as [ptr Hptr].

        match goal with
        | H: Register.get r1 regs = Ptr _ |- _ =>
          rewrite H in Hregsr1
        end.
        rewrite Hptr in Hregsr1.


        unfold shift_value_option, rename_value_option, rename_value_template_option,
        rename_addr_option, sigma_shifting_wrap_bid_in_addr,
        sigma_shifting_lefttoright_addr_bid in *. simpl in *.
        
        assert (
          exists v',
            Memory.load mem1' ptr = Some v'
          ) as [v' Hloadmem1'].
        {
          destruct (
              sigma_shifting_lefttoright_option
                (n cidl)
                (if cidl \in domm (prog_interface p) then n cidl else n'' cidl) bidl
            ) as [bidl_shift|] eqn:ebidl_shift; rewrite ebidl_shift in Hregsr1. 
          - inversion Hregsr1 as [G | [? _]]; try discriminate.
            inversion G. subst. clear G Hregsr1 Hregs.
            inversion cidl_bidl_invariant as [| ? ? ? ?  Hshr]; subst.
            + rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id in ebidl_shift.
              rewrite Hpc_in in Hmem_own1.
              inversion ebidl_shift. subst.
              setoid_rewrite Hmem_own1; auto.
              destruct v as [|[[[perm cid] bid] ?]|].
              * eexists; eauto.
              * destruct (perm =? Permission.data).
                -- destruct (sigma_shifting_lefttoright_option
                               (n cid)
                               (if cid \in domm (prog_interface p)
                                then n cid else n'' cid) bid) eqn:rewr;
                     rewrite rewr; eexists; eauto.
                -- eexists; eauto.
              * eexists; eauto.
            + specialize (Hmem_shared _ Hshr) as Hmem_shared_cid_bid.
              setoid_rewrite ebidl_shift in Hmem_shared_cid_bid.
              destruct Hmem_shared_cid_bid as [addr' [addr'eq [addr'load _]]].
              inversion addr'eq. subst.
              match goal with
              | Hload: Memory.load mem _ = _ |- _ =>
                specialize (addr'load _ _ Hload) as [v' [G _]]
              end.
              eexists. eassumption.
          - inversion Hregsr1 as [| [_ [ptr_eq [Hnotshrt1 Hnotshrt1']]]];
              try discriminate.
            inversion ptr_eq. subst. simpl in *.
            clear Hregsr1 ptr_eq.
            inversion cidl_bidl_invariant as [| ? ? ? ?  Hshr]; subst.
            + by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id in ebidl_shift.
            + specialize (Hnotshrt1 (cidl, bidl)). rewrite in_fset1 eqxx in Hnotshrt1.
              exfalso. by apply Hnotshrt1.
        }

        
        eexists. split.
        * eapply CS.Step_non_inform; first eapply CS.Load.
          -- exact Hex'.
          -- exact Hptr.
          -- exact Hloadmem1'. 
          -- reflexivity.
          -- by simpl.
        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ unfold CSInvariants.is_prefix in *.
               eapply star_right; try eassumption.
               ** eapply CS.Step_non_inform; first eapply CS.Load; eauto.
               ** by rewrite E0_right.
            ++ by simpl.
            ++ by rewrite Pointer.inc_preserves_component.
          -- by simpl.
          -- (** regs_rel_of_executing_part *)
            simpl. constructor. intros reg.
            unfold Register.get, Register.set. rewrite setmE.
            destruct (Register.to_nat reg == Register.to_nat r2) eqn:ereg;
              rewrite ereg; rewrite setmE ereg.
            ++ unfold shift_value_option, rename_value_option,
               rename_value_template_option,
               rename_addr_option, sigma_shifting_wrap_bid_in_addr,
               sigma_shifting_lefttoright_addr_bid in *. simpl in *.
               destruct (
                   sigma_shifting_lefttoright_option
                     (n cidl)
                     (if cidl \in domm (prog_interface p)
                      then n cidl else n'' cidl) bidl
                 ) as [bidl_shift|] eqn:ebidl_shift;
               rewrite !ebidl_shift in Hregsr1.
               ** inversion Hregsr1 as [G | [? _]]; try discriminate.
                  inversion G. subst. clear G Hregsr1 Hregs.

                  (* Is this the right next step? *)
                  inversion cidl_bidl_invariant as [|? ? ? ? Hshr]; subst.
                  ---
                    rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                      in ebidl_shift.
                    inversion ebidl_shift. subst.
                    rewrite <- Hloadmem1'.
                    rewrite Hmem_own1; auto.
                    left.
                    destruct v as [|[[[perm cid] b] o]|]; simpl; auto.
                    destruct (perm =? Permission.data); auto.
                    destruct (sigma_shifting_lefttoright_option
                                (n cid)
                                (if cid \in domm (prog_interface p)
                                 then n cid else n'' cid) b) eqn:esigma;
                      rewrite esigma; auto.
                    
                    assert (CSInvariants.wf_load_wrt_t_pc
                              (Permission.data, Pointer.component pc, bidl_shift, offl)
                              t1
                              (Pointer.component pc)
                              (perm, cid, b, o)
                           ) as cid_b_invariant.
                    {
                      eapply CSInvariants.wf_mem_wrt_t_pc_wf_load_wrt_t_pc; eauto.
                      eapply CSInvariants.wf_state_wf_mem
                        with (s := (gps, mem, regs, pc)); eauto.
                      eapply CSInvariants.is_prefix_wf_state_t
                        with (p := (program_link p c)); eauto.
                      eapply linking_well_formedness; eauto.
                      by unfold mergeable_interfaces in *; intuition.
                    }

                    inversion cid_b_invariant as [? wfptr|? Hloadatshr wfptr]; subst.
                    +++
                      simpl in *.
                      inversion wfptr as [| ? ? ? ? Hshr]; subst.
                      ***
                        by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                          in esigma.
                      ***
                        (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Hshr)
                          as cidbgood.*)
                        inversion Hgood_t as [? shared_good]. subst.
                        specialize (shared_good _ Hshr) as cidbgood.
                        
                        unfold left_addr_good_for_shifting in *.                        
                        specialize (sigma_lefttoright_good_Some
                                      _
                                      (if cid \in domm (prog_interface p)
                                       then n cid else n'' cid)
                                      _
                                      cidbgood
                                   ) as [? [contra _]].
                          by rewrite contra in esigma.
                    +++
                      (* The same as the parallel case above *)
                      inversion wfptr as [| ? ? ? ? Hshr]; subst.
                      ***
                        by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                          in esigma.
                      ***
                        (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Hshr)
                          as cidbgood.*)
                        inversion Hgood_t as [? shared_good]. subst.
                        specialize (shared_good _ Hshr) as cidbgood.

                        unfold left_addr_good_for_shifting in *.                        
                        specialize (sigma_lefttoright_good_Some
                                      _
                                      (if cid \in domm (prog_interface p)
                                       then n cid else n'' cid)
                                      _
                                      cidbgood
                                   ) as [? [contra _]].
                          by rewrite contra in esigma.
                  ---
                    destruct (Hmem_shared (cidl, bidl) Hshr)
                      as [? [Hcidlbidl [Hmem_shared1 _]]].
                    rewrite ebidl_shift in Hcidlbidl. inversion Hcidlbidl. subst.
                    simpl in *.
                    match goal with
                    | Hload: Memory.load mem _ = _ |- _ =>
                      specialize (Hmem_shared1 _ _ Hload) as [v'exists [v'eq G]]
                    end.
                    rewrite Hloadmem1' in v'eq.
                    inversion v'eq. subst. left. exact G.

               **                    
                 inversion cidl_bidl_invariant as [|? ? ? ? Hshr]; subst.
                 ---
                     by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                     in ebidl_shift.
                 --- (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Hshr)
                       as cidbgood.*)
                   inversion Hgood_t as [? shared_good]. subst.
                   specialize (shared_good _ Hshr) as cidbgood.
                   
                   unfold left_addr_good_for_shifting in *.                        
                   specialize (sigma_lefttoright_good_Some
                                 _
                                 (if cidl \in domm (prog_interface p)
                                  then n cidl else n'' cidl)
                                 _
                                 cidbgood
                              ) as [? [contra _]].
                     by rewrite contra in ebidl_shift.
                     
            ++ by apply Hregs.

          -- (* mem_of_part_executing_rel_original_and_recombined *)
            by unfold mem_of_part_executing_rel_original_and_recombined; intuition.
            
      + simpl in *. subst.
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb, ic in Hcomp1.
          rewrite Hpccomp_s'_s in H_c'.
            by rewrite H_c' in Hcomp1.

    - (* IStore *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)

        assert (Pointer.component pc \in domm (prog_interface p)) as Hpc_in.
        {
          by eapply mergeable_states_program_component_domm; eauto.
        }
            

        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }


        (* IStore-specific *)

        unfold mem_of_part_executing_rel_original_and_recombined,
        memory_shifts_memory_at_private_addr, memory_shifts_memory_at_shared_addr,
        memory_renames_memory_at_private_addr, memory_renames_memory_at_shared_addr
         in Hmemp.
        simpl in Hmemp.
        destruct Hmemp as [Hmem_own [Hmem_shared Hmem_next_block]].
        


        assert (CSInvariants.is_prefix
                  (gps,
                   mem',
                   regs,
                   Pointer.inc pc
                  )
                  prog
                    t1
               ) as Hprefix_t1_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }



        match goal with
        | H: Memory.store _ _ _ = Some _ |- _ =>
          specialize (Memory.store_some_permission mem ptr _ _ H) as Hperm_st
        end.
        destruct ptr as [[[perm_st cid_st] bid_st] off_st].
        simpl in Hperm_st. subst.


        inversion Hregsp as [Hregs]. simpl in Hregs.
        specialize (Hregs r1) as Hregs1'r1.
        match goal with
        | H: Register.get r1 regs = Ptr _ |- _ =>
          rewrite H in Hregs1'r1
        end.
        

        assert (exists ptr, Register.get r1 regs1' = Ptr ptr) as Hget_r1_ptr.
        {
          unfold shift_value_option, rename_value_option, rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.

          inversion Hregs1'r1 as [Hregs1'_r1 | [Hregs1'_r1 [Heq [Hnotshr1 Hnotshr2]]]].
          - simpl in *.
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) eqn:eshift;
              rewrite eshift in Hregs1'_r1;
              try discriminate.
            inversion Hregs1'_r1.
              by eauto.
          - setoid_rewrite <- Heq.
            by eexists.
        }

        destruct Hget_r1_ptr as [ptr Hptr].


        
        
        assert (CSInvariants.wf_ptr_wrt_cid_t
                  (Pointer.component pc) t1
                  (Permission.data, cid_st, bid_st, off_st)
               ) as cidst_bidst_invariant.
        {
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - by apply Pointer.inc_preserves_component.
        }


        assert (forall cidv bidv offv,
                   Register.get r2 regs = Ptr (Permission.data, cidv, bidv, offv) ->
                   CSInvariants.wf_ptr_wrt_cid_t
                     (Pointer.component pc) t1
                     (Permission.data, cidv, bidv, offv)
               ) as get_r2_invariant.
        {
          intros ? ? ? Hget.
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog); eauto.
            eapply linking_well_formedness; auto.
            unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - by apply Pointer.inc_preserves_component.
        }


        assert (forall cidv bidv offv,
                   Register.get r2 regs1' = Ptr (Permission.data, cidv, bidv, offv) ->
                   CSInvariants.wf_ptr_wrt_cid_t
                     (Pointer.component pc) t1'
                     (Permission.data, cidv, bidv, offv)
               ) as get_r2_invariant'.
        {
          intros ? ? ? Hget.
          eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
          eapply CSInvariants.wf_state_wf_reg.
          - eapply CSInvariants.is_prefix_wf_state_t with (p := prog'); eauto.
            eapply linking_well_formedness; auto.
            rewrite <- Hifc_cc'. unfold mergeable_interfaces in *.
              by intuition.
          - by simpl.
          - by simpl.
          - reflexivity.
        }

        
        assert (exists v,
                   Memory.load mem (Permission.data, cid_st, bid_st, off_st) =
                   Some v) as [vload Hload].
        {
          eapply Memory.store_some_load_some.
          eexists. eassumption.
        }

        (*assert (good_memory
                  (left_addr_good_for_shifting n)
                  (CS.state_mem (gps, mem', regs, Pointer.inc pc)))
          as Hgood_after_store.
        {
          eapply Hgood_prog; eassumption.
        }*)

        
        
        assert (
          exists mem2',
            Memory.store mem1' ptr (Register.get r2 regs1') = Some mem2'
          ) as [mem2' Hstoremem1'].
        {
          rewrite <- Memory.store_some_load_some.



          (* Consider refactoring the unfold and the assert out of 
             the enclosing assertion proof *)
          unfold mem_of_part_executing_rel_original_and_recombined,
          shift_value_option, rename_value_option,
          rename_value_template_option,
          rename_addr_option, sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *. simpl in *.
          
          assert (
              (cid_st, bid_st).1 \in domm (prog_interface p) ->
                                     (
                                       Memory.load mem1' (Permission.data,
                                                          cid_st, bid_st, off_st) =
                                       match
                                         rename_value_option
                                           (rename_addr_option
                                              (sigma_shifting_wrap_bid_in_addr
                                                 (sigma_shifting_lefttoright_addr_bid
                                                    n
                                                    (fun cid : nat =>
                                                       if cid \in domm (prog_interface p)
                                                       then n cid else n'' cid)))) vload
                                       with
                                       | Some v' => Some v'
                                       | None => Some vload
                                       end)
            ) as Hmem_own1.
          {
            intros Hcidl.
            specialize (Hmem_own _ Hcidl) as [Hspec _].
            
            match goal with | H: Memory.load _ _ = _ |- _ => 
                                by specialize (Hspec _ _ H)
            end.
          }


          
          destruct (
              sigma_shifting_lefttoright_option
                (n cid_st)
                (if cid_st \in domm (prog_interface p)
                 then n cid_st else n'' cid_st) bid_st
            ) as [bidst_shift|] eqn:ebidst_shift; rewrite ebidst_shift in Hregs1'r1. 
          - inversion Hregs1'r1 as [G | [? _]]; try discriminate.
            rewrite Hptr in G. inversion G. subst. clear G Hregs1'r1 Hregs.
            inversion cidst_bidst_invariant as [| ? ? ? ?  Hshr]; subst.
            + rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id in ebidst_shift.
              inversion ebidst_shift. subst.
              rewrite Hpc_in in Hmem_own1.
              setoid_rewrite Hmem_own1; auto.
              unfold rename_value_option, rename_value_template_option,
              rename_addr_option, sigma_shifting_wrap_bid_in_addr,
              sigma_shifting_lefttoright_addr_bid in *.
              destruct vload as [|[[[perm cid] bid] ?]|].
              * eexists; by simpl.
              * destruct (perm =? Permission.data) eqn:eperm; simpl.
                -- destruct (sigma_shifting_lefttoright_option
                               (n cid)
                               (if cid \in domm (prog_interface p)
                                then n cid else n'' cid) bid) eqn:rewr;
                     eexists; rewrite rewr; eauto.
                -- eexists; eauto.
              * eexists; eauto.
            + specialize (Hmem_shared _ Hshr) as Hmem_shared_cid_bid.
              setoid_rewrite ebidst_shift in Hmem_shared_cid_bid.
              destruct Hmem_shared_cid_bid as [addr' [addr'eq [addr'load _]]].
              inversion addr'eq. subst.
              match goal with
              | Hload: Memory.load mem _ = _ |- _ =>
                specialize (addr'load _ _ Hload) as [v' [G _]]
              end.
              eexists. eassumption.
          - inversion Hregs1'r1 as [| [_ [ptr_eq [Hnotshrt1 Hnotshrt1']]]];
              try discriminate.
            inversion ptr_eq. subst. simpl in *.
            clear Hregs1'r1 ptr_eq.
            inversion cidst_bidst_invariant as [| ? ? ? ?  Hshr]; subst.
            + by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                in ebidst_shift.
            + specialize (Hnotshrt1 (cid_st, bid_st)).
              rewrite in_fset1 eqxx in Hnotshrt1.
              exfalso. by apply Hnotshrt1.
        }

        assert (
          Step (CS.sem_non_inform (program_link p c'))
               (gps1', mem1', regs1', pc) 
               E0
               (gps1', mem2', regs1', Pointer.inc pc)
        ) as Hstep.
        {
          eapply CS.Step_non_inform; first eapply CS.Store.
          -- exact Hex'.
          -- exact Hptr.
          -- exact Hstoremem1'. 
          -- reflexivity.
        }
        
        assert (
          CSInvariants.is_prefix
            (gps1',
             mem2',
             regs1',
             Pointer.inc pc
            )
            (program_link p c')
            t1'
        ) as Hprefix_t1'_E0.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
            by rewrite E0_right.
        }

        (* TODO: Refactor out *)
        Ltac find_if_inside_hyp H :=
          let e := fresh "e" in
          match goal with
          | [ H: context[if ?X then _ else _] |- _ ] => destruct X eqn:e
          end.
        Ltac find_if_inside_goal :=
          let e := fresh "e" in
          match goal with
          | [ |- context[if ?X then _ else _] ] => destruct X eqn:e
          end.

        assert (Pointer.permission ptr = Permission.data) as Hptrperm.
        {
          simpl in *.
          unfold rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          rewrite Hptr in Hregs1'r1.
          inversion Hregs1'r1 as [Hregs1'r1a | Hregs1'r1a]; simpl in *;
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) as [?|] eqn:esigma;
            rewrite esigma in Hregs1'r1a; try discriminate.
          - by inversion Hregs1'r1a.
          - exfalso. by destruct Hregs1'r1a.
          - destruct Hregs1'r1a as [_ [G _]]. by inversion G.
        }

        assert (Pointer.component ptr = cid_st) as Hptrcomp.
        {
          simpl in *.
          unfold rename_addr_option,
          sigma_shifting_wrap_bid_in_addr,
          sigma_shifting_lefttoright_addr_bid in *.
          rewrite Hptr in Hregs1'r1.
          inversion Hregs1'r1 as [Hregs1'r1a | Hregs1'r1a]; simpl in *;
            destruct (sigma_shifting_lefttoright_option
                        (n cid_st)
                        (if cid_st \in domm (prog_interface p)
                         then n cid_st else n'' cid_st) bid_st) as [?|] eqn:esigma;
            rewrite esigma in Hregs1'r1a; try discriminate.
          - by inversion Hregs1'r1a.
          - exfalso. by destruct Hregs1'r1a.
          - destruct Hregs1'r1a as [_ [G _]]. by inversion G.
        }

        rewrite Hptr in Hregs1'r1.

        assert (
            mem_of_part_executing_rel_original_and_recombined
              p
              mem'
              mem2'
              n
              (fun cid : nat_ordType =>
                 if cid \in domm (prog_interface p) then n cid else n'' cid) t1
          ) as Hmem'mem2'.
        {
          split; last split.
          - unfold shift_value_option, memory_shifts_memory_at_private_addr,
            memory_renames_memory_at_private_addr,
            rename_value_option, rename_value_template_option,
            rename_addr_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            simpl in *.
            intros ? Horiginal. split.
            + intros ? ? Hloadmem'.
              erewrite Memory.load_after_store in Hloadmem'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem'.
              * inversion Hloadmem'. subst.
                assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq as [[Hcid Hbid]]. subst.
                  rewrite Hcid in Horiginal.
                  rewrite Horiginal sigma_shifting_lefttoright_option_n_n_id
                    in Hregs1'r1.
                  destruct Hregs1'r1 as [G| [contra _]]; try discriminate.
                  inversion G. subst. rewrite Hcid eqxx.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; try by rewrite G'.
                  destruct (Register.get r2 regs) as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [G'' ?]]; try discriminate.
                  destruct (perm =? Permission.data); try discriminate.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.
                  by rewrite esigma G''.
              * subst.
                find_if_inside_goal.
                --
                  assert (ptr =
                          (Permission.data, original_addr.1, original_addr.2, offset)).
                  by apply/(@eqP (prod_eqType
                                 (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                              nat_eqType)
                                 Extra.Z_eqType)); rewrite eq_sym.
                  subst. simpl in *.
                  rewrite Horiginal sigma_shifting_lefttoright_option_n_n_id
                    in Hregs1'r1.
                  destruct Hregs1'r1 as [G | [contra _]]; try discriminate.
                  inversion G. subst. by rewrite eqxx in e.
                --
                  specialize (Hmem_own _ Horiginal) as [G _].
                    by eapply G; eauto.
            + intros ? ? Hloadmem2'.
              erewrite Memory.load_after_store in Hloadmem2'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem2'.
              * inversion Hloadmem2'. subst.
                assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                        ptr)
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  subst.
                  simpl in *.
                  rewrite Horiginal sigma_shifting_lefttoright_option_n_n_id
                    in Hregs1'r1.
                  destruct (Hregs1'r1) as [Hrewr | [contra _]]; try discriminate.
                  inversion Hrewr. subst. clear Hregs1'r1 Hrewr. rewrite eqxx.
                  eexists; split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; try by right.
                  left. by intuition.
              * subst. find_if_inside_goal.
                --
                  assert ((Permission.data, original_addr.1, original_addr.2, offset) =
                          (Permission.data, Pointer.component ptr, bid_st, off_st))
                    as contra.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion contra as [[Hcid Hbid]]. subst.
                  rewrite Hcid in Horiginal.
                  rewrite Horiginal sigma_shifting_lefttoright_option_n_n_id
                    in Hregs1'r1.
                  destruct Hregs1'r1 as [G | [? _]]; try discriminate.
                  inversion G as [G']. rewrite <- G' in e. by rewrite Hcid eqxx in e.
                --
                  specialize (Hmem_own _ Horiginal) as [_ G].
                    by eapply G; eauto.
          - unfold shift_value_option, memory_shifts_memory_at_shared_addr,
            memory_renames_memory_at_shared_addr,
            rename_value_option, rename_value_template_option,
            rename_addr_option,
            sigma_shifting_wrap_bid_in_addr,
            sigma_shifting_lefttoright_addr_bid in *.
            simpl in *.
            intros ? Horiginal.
            (*specialize (addr_shared_so_far_good_addr _ _ Hgood_t _ Horiginal)
                as Hgood.*)
            inversion Hgood_t as [? shared_good]. subst.
            specialize (shared_good _ Horiginal) as Hgood.


            unfold left_addr_good_for_shifting in *.
            destruct original_addr as [cid_orig bid_orig].
            specialize (sigma_lefttoright_good_Some
                          _
                          (if cid_orig \in domm (prog_interface p)
                           then n cid_orig else n'' cid_orig)
                          _
                          Hgood) as [bid_shift [Hbid_shift bid_shift_good]].
            setoid_rewrite Hbid_shift.
            eexists. split; auto; split; simpl in *; intros ? ?.
            + intros Hloadmem'.
              erewrite Memory.load_after_store in Hloadmem'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem'.
              * inversion Hloadmem'. subst. clear Hloadmem'.
                assert ((Permission.data, cid_orig, bid_orig, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e.
                  rewrite Hbid_shift in Hregs1'r1.
                  destruct Hregs1'r1 as [Heq | [? _]]; try discriminate.
                  inversion Heq. simpl in *. rewrite eqxx. eexists. split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; auto.
                  destruct (Register.get r2 regs) as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [G'' [Hnotshr Hnotshr']]]; try discriminate.
                  destruct (perm =? Permission.data) eqn:eperm; try discriminate.
                  assert (perm = Permission.data). by apply beq_nat_true. subst.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.
                  rewrite esigma.

                  assert (CSInvariants.wf_ptr_wrt_cid_t
                            (Pointer.component pc)
                            t1
                            (Permission.data, cid, b, o)) as Hwf.
                  {
                    eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                    eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps, mem, regs, pc)); eauto.
                    eapply CSInvariants.is_prefix_wf_state_t
                      with (p := (program_link p c)); eauto.
                      by eapply linking_well_formedness;
                        unfold mergeable_interfaces in *; intuition.
                  }

                  inversion Hwf as [| ? ? ? ? Hshr]; subst.
                --
                    by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                    in esigma.
                --
                  by specialize (Hnotshr (cid, b));
                    rewrite in_fset1 eqxx in Hnotshr;
                    unfold not in *;
                    apply Hnotshr in Hshr.
                  
                  (*specialize (Hgood_after_store _ _ off_st cid b o Hgood) as Hcontra.
                  erewrite Memory.load_after_store in Hcontra; eauto.
                  rewrite eqxx in Hcontra.
                  assert (left_block_id_good_for_shifting (n cid) b) as Happ. by auto.
                  specialize (sigma_lefttoright_good_Some
                                _
                                (if cid \in domm (prog_interface p)
                                 then n cid else n'' cid) _ Happ) as [? [G _]].
                  by rewrite G in esigma.*)
              * subst.
                find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, bid_shift, offset) =
                          ptr)
                    as Heq.
                    by apply/(@eqP (prod_eqType
                                      (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                   nat_eqType)
                                      Extra.Z_eqType)).
                    subst.
                    simpl in *.
                    destruct (
                        sigma_shifting_lefttoright_option
                          (n cid_orig)
                          (if cid_orig \in domm (prog_interface p)
                           then n cid_orig else n'' cid_orig)
                          bid_st
                      ) eqn:esigma; rewrite esigma in Hregs1'r1.
                  ++
                    destruct Hregs1'r1 as [contra | [? _]]; try discriminate.
                    inversion contra. subst.
                    assert (bid_orig = bid_st).
                    by eapply sigma_shifting_lefttoright_option_Some_inj; eauto.
                    subst. by rewrite eqxx in e.
                  ++
                    destruct Hregs1'r1 as [contra | [? [Hrewr [? contra]]]];
                      try discriminate.
                    inversion Hrewr. subst. clear Hrewr.
                    specialize (contra (cid_orig, bid_shift)).
                    rewrite in_fset1 eqxx in contra.
                    inversion Hshift_tt' as [? ? Hren]. subst.
                    inversion Hren as [|? ? ? ?  ? ? Hshr_shr _ _ _ _ _ _ ]; subst;
                      try by inversion Horiginal; find_nil_rcons.
                    specialize (Hshr_shr _ Horiginal) as [_ [? [Hsigma Hcontra]]].
                    unfold rename_addr_option,
                    sigma_shifting_wrap_bid_in_addr,
                    sigma_shifting_lefttoright_addr_bid in *.
                    rewrite Hbid_shift in Hsigma. inversion Hsigma. subst.
                    exfalso. by apply contra; first auto; exact Hcontra.
                --
                  specialize (Hmem_shared _ Horiginal) as [? [esigma [G _]]].
                  rewrite Hbid_shift in esigma. inversion esigma. subst.
                  simpl in *. by eapply G; eauto.
            + intros Hloadmem2'.
              erewrite Memory.load_after_store in Hloadmem2'; eauto.
              erewrite Memory.load_after_store; eauto.
              find_if_inside_hyp Hloadmem2'.
              * inversion Hloadmem2'. subst. clear Hloadmem2'.
                assert ((Permission.data, cid_orig, bid_shift, offset) = ptr)
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  subst. simpl in *.
                  find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, bid_orig, offset) =
                          (Permission.data, cid_orig, bid_st, off_st)) as Heq.
                    by apply/(@eqP (prod_eqType
                                      (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                   nat_eqType)
                                      Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e0.
                  eexists; split; eauto.
                  specialize (Hregs r2) as Hgetr2.
                  destruct Hgetr2 as [G'|G']; auto.
                  destruct (Register.get r2 regs)
                    as [|[[[perm cid] b] o]|] eqn:eget;
                    destruct G' as [contra [G'' [Hnotshr Hnotshr']]];
                    try discriminate.
                  destruct (perm =? Permission.data) eqn:eperm; try discriminate.
                  assert (perm = Permission.data). by apply beq_nat_true. subst.
                  destruct (sigma_shifting_lefttoright_option
                              (n cid)
                              (if cid \in domm (prog_interface p)
                               then n cid else n'' cid) b) eqn:esigma;
                    rewrite esigma in contra; try discriminate.

                  assert (CSInvariants.wf_ptr_wrt_cid_t
                            (Pointer.component pc)
                            t1
                            (Permission.data, cid, b, o)) as Hwf.
                  {
                    eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                    eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps, mem, regs, pc)); eauto.
                    eapply CSInvariants.is_prefix_wf_state_t
                      with (p := (program_link p c)); eauto.
                      by eapply linking_well_formedness;
                        unfold mergeable_interfaces in *; intuition.
                  }

                  inversion Hwf as [| ? ? ? ? Hshr]; subst.
                  ++
                    by rewrite Hpc_in sigma_shifting_lefttoright_option_n_n_id
                    in esigma.
                  ++
                      by specialize (Hnotshr (cid, b));
                        rewrite in_fset1 eqxx in Hnotshr;
                        unfold not in *;
                        apply Hnotshr in Hshr.

                  (*
                  specialize (Hgood_after_store _ _ off_st cid b o Hgood) as Hcontra.
                  erewrite Memory.load_after_store in Hcontra; eauto.
                  rewrite eqxx in Hcontra.
                  assert (left_block_id_good_for_shifting (n cid) b) as Happ. by auto.
                  specialize (sigma_lefttoright_good_Some
                                _
                                (if cid \in domm (prog_interface p)
                                 then n cid else n'' cid) _ Happ) as [? [G _]].
                  by rewrite G in esigma.*)
                --
                  destruct (
                      sigma_shifting_lefttoright_option
                        (n cid_orig)
                        (if cid_orig \in domm (prog_interface p)
                         then n cid_orig else n'' cid_orig)
                        bid_st
                    ) eqn:esigma; rewrite esigma in Hregs1'r1.
                  ++
                    destruct Hregs1'r1 as [Hrewr|[? _]]; try discriminate.
                    inversion Hrewr. subst. clear Hrewr.
                    assert (bid_orig = bid_st).
                      by eapply sigma_shifting_lefttoright_option_Some_inj; eauto.
                    subst. by rewrite eqxx in e0.
                  ++
                    destruct Hregs1'r1 as [?|[_ [? [? Hcontra]]]]; try discriminate.
                    specialize (Hcontra (cid_orig, bid_shift)).
                    rewrite in_fset1 eqxx in Hcontra.
                    inversion Hshift_tt' as [? ? Hren]. subst.
                    inversion Hren as [|? ? ? ?  ? ? Hshr_shr _ _ _ _ _ _ ]; subst;
                      try by inversion Horiginal; find_nil_rcons.
                    specialize (Hshr_shr _ Horiginal) as [_ [? [Hsigma contra]]].
                    unfold rename_addr_option,
                    sigma_shifting_wrap_bid_in_addr,
                    sigma_shifting_lefttoright_addr_bid in *.
                    rewrite Hbid_shift in Hsigma. inversion Hsigma. subst.
                    exfalso. by apply Hcontra; first auto; exact contra.
              * find_if_inside_goal.
                --
                  assert ((Permission.data, cid_orig, bid_orig, offset) =
                        (Permission.data, Pointer.component ptr, bid_st, off_st))
                  as Heq.
                  by apply/(@eqP (prod_eqType
                                    (prod_eqType (prod_eqType nat_eqType nat_eqType)
                                                 nat_eqType)
                                    Extra.Z_eqType)).
                  inversion Heq. subst. clear Heq e0.
                  rewrite Hbid_shift in Hregs1'r1.
                  destruct Hregs1'r1 as [Hrewr|[? _]]; try discriminate.
                  inversion Hrewr as [Hsubst]. by rewrite Hsubst eqxx in e.
                --
                  specialize (Hmem_shared _ Horiginal) as [? [esigma [_ G]]].
                  rewrite Hbid_shift in esigma. inversion esigma. subst.
                  simpl in *. by eapply G; eauto.

                    
          - unfold Memory.store in *. simpl in *.
            destruct (mem cid_st) as [memC|] eqn:ememC; try discriminate.
            destruct (ComponentMemory.store memC bid_st off_st (Register.get r2 regs))
              as [memC'|] eqn:ememC'; try discriminate.
            match goal with | H: Some _ = Some _ |- _ => inversion H end. subst.
            find_if_inside_hyp Hstoremem1'; try discriminate.
            destruct (mem1' (Pointer.component ptr)) as [mem1'ptr|] eqn:emem1'ptr;
              try discriminate.
            destruct (ComponentMemory.store
                        mem1'ptr
                        (Pointer.block ptr) 
                        (Pointer.offset ptr)
                        (Register.get r2 regs1')) as [mem1'ptrComp|]
            eqn:compMemStore; try discriminate.
            inversion Hstoremem1'. subst.
            intros cid Hcid. rewrite !setmE.
            destruct (cid == Pointer.component ptr) eqn:ecid; rewrite ecid.
            + specialize (Hmem_next_block cid Hcid).
              unfold omap, obind, oapp in *.
              erewrite <- ComponentMemory.next_block_store_stable; last exact ememC'.
              symmetry.
              erewrite <- ComponentMemory.next_block_store_stable;
                last exact compMemStore.
              symmetry.
              assert (cid = Pointer.component ptr). by apply/eqP. subst.
              by rewrite ememC emem1'ptr in Hmem_next_block.
            + by specialize (Hmem_next_block cid Hcid). 
        }


        assert (
          mem_of_part_not_executing_rel_original_and_recombined_at_internal
            c'
            (CS.state_mem s1'')
            mem2'
            n''
            (fun cid : nat_ordType =>
               if cid \in domm (prog_interface p) then n cid else n'' cid)
            t1''
        ).
        {
          unfold
            mem_of_part_not_executing_rel_original_and_recombined_at_internal,
          memory_shifts_memory_at_private_addr,
          memory_renames_memory_at_private_addr in *.
          destruct Hmemc' as [Hprivrel Halloc].
          split.
          - intros ? Horiginal Hnotshr.

            assert (original_addr.1 \in domm (prog_interface p) -> False)
              as Horiginal_not_p.
            {
              intros contra.
              rewrite <- Hifc_cc' in Horiginal.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Horiginal contra).
            }
            
            split; intros ? ? Hload_c'.
            + erewrite Memory.load_after_store; last exact Hstoremem1'.
              find_if_inside_goal.
              * assert ((Permission.data, original_addr.1,
                         original_addr.2, offset) = ptr).
                by apply/(@eqP (prod_eqType
                                  (prod_eqType
                                     (prod_eqType nat_eqType nat_eqType)
                                     nat_eqType)
                                  Extra.Z_eqType)).
                subst.
                assert (CSInvariants.wf_ptr_wrt_cid_t
                          (Pointer.component pc)
                          t1'
                          (Permission.data,
                           original_addr.1,
                           original_addr.2, offset)) as Hwf.
                {
                  eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                  eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps1', mem1', regs1', pc)); eauto.
                  eapply CSInvariants.is_prefix_wf_state_t
                    with (p := (program_link p c')); eauto.
                  eapply linking_well_formedness; try assumption.
                  rewrite <- Hifc_cc'.
                    by unfold mergeable_interfaces in *;
                      intuition.
                }
                

                inversion Hwf as [| ? ? ? ? Hshr]; subst.
                ++
                  match goal with
                  | Hrewr: Pointer.component pc = _ |- _ =>
                    rewrite Hrewr in Hpc_in
                  end.
                  by intuition. (* contradiction *)
                ++
                  inversion Hshift_t''t' as [? ? t''t'ren]. subst.
                  inversion t''t'ren
                    as [|? ? ? ? ? ? _ Hshr'_shr'' _ _ _ _ _]; subst.
                  ** inversion Hshr; by find_nil_rcons.
                  ** specialize (Hshr'_shr'' _ Hshr)
                      as [_ [[cid bid] [Hren Hcontra]]].
                     unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr
                       in *.
                     simpl in *.
                     destruct (cid \in domm (prog_interface p)) eqn:ecid;
                       rewrite ecid in Hren.
                     ---
                       destruct (sigma_shifting_lefttoright_option
                                   (n'' cid) (n cid) bid); try discriminate.
                       inversion Hren. subst.
                         by rewrite ecid in Horiginal_not_p; exfalso; auto.
                     ---
                       rewrite sigma_shifting_lefttoright_option_n_n_id in Hren.
                       inversion Hren. subst.
                         by destruct original_addr; simpl in *; intuition.
                         (* contradiction Hcontra with Hnotshr *)
                    
              * specialize (Hprivrel _ Horiginal Hnotshr) as [Hprivrel' _].
                  by eapply Hprivrel'.
            + erewrite Memory.load_after_store in Hload_c';
                last exact Hstoremem1'.
              find_if_inside_hyp Hload_c'.
              * assert ((Permission.data, original_addr.1,
                         original_addr.2, offset) = ptr).
                by apply/(@eqP (prod_eqType
                                  (prod_eqType
                                     (prod_eqType nat_eqType nat_eqType)
                                     nat_eqType)
                                  Extra.Z_eqType)).
                subst.
                assert (CSInvariants.wf_ptr_wrt_cid_t
                          (Pointer.component pc)
                          t1'
                          (Permission.data,
                           original_addr.1,
                           original_addr.2, offset)) as Hwf.
                {
                  eapply CSInvariants.wf_reg_wf_ptr_wrt_cid_t; eauto.
                  eapply CSInvariants.wf_state_wf_reg
                      with (s := (gps1', mem1', regs1', pc)); eauto.
                  eapply CSInvariants.is_prefix_wf_state_t
                    with (p := (program_link p c')); eauto.
                  eapply linking_well_formedness; try assumption.
                  rewrite <- Hifc_cc'.
                    by unfold mergeable_interfaces in *;
                      intuition.
                }
                

                inversion Hwf as [| ? ? ? ? Hshr]; subst.
                ++
                  match goal with
                  | Hrewr: Pointer.component pc = _ |- _ =>
                    rewrite Hrewr in Hpc_in
                  end.
                  by intuition. (* contradiction *)
                ++
                  inversion Hshift_t''t' as [? ? t''t'ren]. subst.
                  inversion t''t'ren
                    as [|? ? ? ? ? ? _ Hshr'_shr'' _ _ _ _ _]; subst.
                  ** inversion Hshr; by find_nil_rcons.
                  ** specialize (Hshr'_shr'' _ Hshr)
                      as [_ [[cid bid] [Hren Hcontra]]].
                     unfold rename_addr_option, sigma_shifting_wrap_bid_in_addr
                       in *.
                     simpl in *.
                     destruct (cid \in domm (prog_interface p)) eqn:ecid;
                       rewrite ecid in Hren.
                     ---
                       destruct (sigma_shifting_lefttoright_option
                                   (n'' cid) (n cid) bid); try discriminate.
                       inversion Hren. subst.
                         by rewrite ecid in Horiginal_not_p; exfalso; auto.
                     ---
                       rewrite sigma_shifting_lefttoright_option_n_n_id in Hren.
                       inversion Hren. subst.
                         by destruct original_addr; simpl in *; intuition.
                         (* contradiction Hcontra with Hnotshr *)
                
              * specialize (Hprivrel _ Horiginal Hnotshr) as [_ Hprivrel'].
                  by eapply Hprivrel'.

          - intros ? Hcid.
            assert (cid \in domm (prog_interface p) -> False)
              as Hcid_not_p.
            {
              intros contra.
              rewrite <- Hifc_cc' in Hcid.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Hcid contra).
            }
            
            unfold Memory.store in *. simpl in *.
            destruct (mem cid_st) as [memC|] eqn:ememC; try discriminate.
            destruct (ComponentMemory.store memC bid_st off_st (Register.get r2 regs))
              as [memC'|] eqn:ememC'; try discriminate.
            match goal with | H: Some _ = Some _ |- _ => inversion H end. subst.
            find_if_inside_hyp Hstoremem1'; try discriminate.
            destruct (mem1' (Pointer.component ptr)) as [mem1'ptr|] eqn:emem1'ptr;
              try discriminate.
            destruct (ComponentMemory.store
                        mem1'ptr
                        (Pointer.block ptr) 
                        (Pointer.offset ptr)
                        (Register.get r2 regs1')) as [mem1'ptrComp|]
            eqn:compMemStore; try discriminate.
            inversion Hstoremem1'. subst.
            rewrite !setmE.
            destruct (cid == Pointer.component ptr) eqn:ecid; rewrite ecid.
            + specialize (Halloc cid Hcid).
              unfold omap, obind, oapp in *.
              erewrite <- ComponentMemory.next_block_store_stable;
                last exact compMemStore.
              rewrite Halloc.
              assert (cid = Pointer.component ptr). by apply/eqP. subst.
              by rewrite emem1'ptr.
              
            + by specialize (Halloc cid Hcid).
        }
        
        
        eexists. split.
        * exact Hstep.

        * econstructor; try eassumption.
          -- (* mergeable_states_well_formed *)
            eapply mergeable_states_well_formed_intro; try eassumption.
            ++ by simpl.
            ++ simpl. rewrite <- Hpccomp_s'_s''.
                 by rewrite Pointer.inc_preserves_component.
          -- by simpl.

      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.
          


    -  (* IJal *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1',
                      Register.set R_RA (Ptr (Pointer.inc pc)) regs1',
                      pc'
                     )
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Jal.
          -- exact Hex'.
          -- unfold sem', prog'.
             eapply find_label_in_component_mergeable_internal_states; auto.
             ++ exact H_p.
             ++ exact Hmerge1.
             ++ reflexivity.
             ++ unfold sem, prog in *. assumption.
          -- reflexivity.
          -- reflexivity.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem,
                   Register.set R_RA (Ptr (Pointer.inc pc)) regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1',
                   Register.set R_RA (Ptr (Pointer.inc pc)) regs1',
                   pc'
                  )
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl. symmetry.
             eapply find_label_in_component_1; eassumption.
        * by simpl.
        * simpl. constructor. intros ?.
          inversion Hregsp as [Hregs]. specialize (Hregs reg).
          unfold Register.get, Register.set in *. simpl in Hregs. rewrite !setmE.
          destruct (Register.to_nat reg == Register.to_nat R_RA) eqn:ereg;
            rewrite ereg; try assumption.
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.
          assert (Pointer.permission pc = Permission.code).
          {
            eapply CSInvariants.pc_permission_code.
            - eapply linking_well_formedness.
              + exact Hwfp.
              + exact Hwfc.
              + unfold mergeable_interfaces in *. intuition.
            - exact Hpref_t.
            - reflexivity.
          }
          assert (Pointer.permission (Pointer.inc pc) = Permission.code) as Hcode.
            by rewrite Pointer.inc_preserves_permission.
            
          destruct (Pointer.inc pc) as [[[perm cid] bid] off]. simpl in *. subst.
          simpl. by left.

      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IJump *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Ptr pc') as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            destruct pc' as [[[perm ?] ?] ?];
            simpl in *;
            subst;
            simpl in *;
            by inversion Hshift.
        }

        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', pc')
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Jump.
          -- exact Hex'.
          -- assumption.
          -- assumption.
          -- assumption.
          -- by simpl.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem, regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', pc')
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl. assumption.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBnz, non-zero case *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Int val) as Hregs1'_r.
        {

          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.

        }

        
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', pc')
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.BnzNZ.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
          -- eapply find_label_in_procedure_mergeable_internal_states; auto.
             ++ exact H_p.
             ++ exact Hmerge1.
             ++ reflexivity.
             ++ unfold sem, prog in *. assumption.
          -- by simpl.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem, regs, pc')
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', pc')
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             symmetry.
             eapply find_label_in_procedure_1; eassumption.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IBnz, zero case *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get r regs1' = Int 0) as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs r) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get r regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.
        }

        
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem1', regs1', Pointer.inc pc)
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.BnzZ.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
        }

          assert (CSInvariants.is_prefix
                  (gps, mem, regs, Pointer.inc pc)
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem1', regs1', Pointer.inc pc)
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             by rewrite Pointer.inc_preserves_component.
        * by simpl.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.

    - (* IAlloc *)
      destruct s1' as [[[gps1' mem1'] regs1'] pc1'].
      find_and_invert_mergeable_internal_states;
        find_and_invert_mergeable_states_well_formed.
      + assert (pc1' = pc). by simpl in *.
        subst pc1'. (* PC lockstep. *)
        assert (Pointer.component pc \in domm (prog_interface p)) as
            Hpc_prog_interface_p.
        {
          unfold CS.is_program_component,
          CS.is_context_component, turn_of, CS.state_turn in *.
          unfold negb in Hcomp1.
          pose proof @CS.star_pc_domm_non_inform p c
                 Hwfp Hwfc Hmerge_ipic Hclosed_prog as Hor'.
          assert (Pointer.component pc \in domm (prog_interface p)
                    \/
                    Pointer.component pc \in domm (prog_interface c))
              as [G | Hcontra]; auto.
            {
              unfold CSInvariants.is_prefix in Hpref_t.
              eapply Hor'; eauto.
              - by unfold CS.initial_state.
            }
            by (unfold ic in *; rewrite Hcontra in Hcomp1).
        }
        
        match goal with
        | H : executing (prepare_global_env prog) ?PC ?INSTR |- _ =>
          assert (Hex' : executing (prepare_global_env prog') PC INSTR)
        end.
        {
          eapply execution_invariant_to_linking with (c1 := c); eauto.
          + unfold mergeable_interfaces in *. by intuition.
          + rewrite <- Hifc_cc'. unfold mergeable_interfaces in *. by intuition.
        }

        assert (Register.get rsize regs1' = Int size) as Hregs1'_r.
        {
          inversion Hregsp as [Hregs].
          unfold shift_value_option, rename_value_option,
          rename_value_template_option in *.

          specialize (Hregs rsize) as [Hshift | Hshift];
            simpl in Hshift;
            match goal with
            | Hr: Register.get rsize regs = _ |- _ => rewrite Hr in Hshift
            end;
            simpl in *;
            by inversion Hshift.
        }

        assert (
          exists mem2',
            Memory.alloc mem1' (Pointer.component pc) (Z.to_nat size) =
            Some (mem2', ptr)
        ) as [mem2' Halloc'].
        {
          destruct Hmemp as [_ [_ Hnextb_eq]].
          specialize (Hnextb_eq (Pointer.component pc) Hpc_prog_interface_p).
          simpl in Hnextb_eq.
          unfold omap, obind, oapp in *.
          unfold Memory.alloc in *.
          destruct (mem (Pointer.component pc)) as [cMem|] eqn:ecMem; try discriminate.
          destruct (mem1' (Pointer.component pc)) as [cMem1'|] eqn:ecMem1';
            try discriminate.
          destruct (ComponentMemory.alloc cMem1' (Z.to_nat size))
            as [cMem1'_new b] eqn:ecMem1'_new.
          eexists.
          destruct (ComponentMemory.alloc cMem (Z.to_nat size))
            as [cMem_new also_b] eqn:ecMem_new.
          assert (also_b = b).
          {
            specialize (ComponentMemory.next_block_alloc _ _ _ _ ecMem1'_new) as [eb _].
            specialize (ComponentMemory.next_block_alloc _ _ _ _ ecMem_new) as [eb' _].
            subst.
            by inversion Hnextb_eq.
          }
          subst.
          repeat match goal with | H: Some _ = Some _ |- _ => inversion H; clear H end.
          reflexivity.
        }


        assert (Pointer.component ptr \in domm (prog_interface p)) as Hptr.
        {
          specialize (Memory.component_of_alloc_ptr _ _ _ _ _ Halloc').
          intros H_. by rewrite H_.
        }
          
        assert (mem_of_part_executing_rel_original_and_recombined
                  p
                  mem'
                  mem2'
                  n
                  (fun cid : nat_ordType => if cid \in domm (prog_interface p)
                                            then n cid else n'' cid)
                  t1
               ) as [Hshift [Hinvshift Hnextblock]].
        {
          destruct Hmemp as [Hshift_given [Hinvshift_given Hnextblock_given]].
          split; last split.
          - intros [cid_original bid_original] Horiginal.
            unfold memory_shifts_memory_at_addr, memory_renames_memory_at_addr,
            rename_addr in *.
            intros off. unfold sigma_shifting_addr. simpl.
            specialize (Memory.load_after_alloc
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Hnoteq.
            simpl in Hnoteq.

            specialize (Memory.load_after_alloc_eq
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Heq.
            simpl in Heq.

            match goal with
            | H: Memory.alloc mem _ _ = _ |- _ =>
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, off)
                            H
                         ) as Hnoteq_p;
                simpl in Hnoteq_p;

                specialize (Memory.load_after_alloc_eq
                              _ _ _ _ _
                              (Permission.data, cid_original, bid_original, off)
                              H
                           ) as Heq_p;
                simpl in Heq_p
            end.

            specialize (Hshift_given (cid_original, bid_original) Horiginal off).
            simpl in Hshift_given.


            destruct ((cid_original, bid_original) ==
                      (Pointer.component ptr, Pointer.block ptr)) eqn:Hwhichaddr.
            + assert ((cid_original, bid_original) =
                      (Pointer.component ptr, Pointer.block ptr)) as H_. by apply/eqP.
              inversion H_. subst. clear H_.
              rewrite Hptr sigma_shifting_n_n_id Heq_p; auto. simpl.
              rewrite Heq.
              destruct (Z.ltb off (Z.of_nat (Z.to_nat size)));
                destruct (Z.leb Z0 off); by auto.
              reflexivity.
            + assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.
              unfold option_rename_value, omap, obind, oapp in *.
              rewrite Hnoteq_p; auto.
              destruct (sigma_shifting
                          (n cid_original)
                          (if cid_original \in domm (prog_interface p)
                           then n cid_original else n'' cid_original)
                          (care, bid_original))
                as [care_shift bid_original_shift] eqn:eshift;
                rewrite eshift; rewrite eshift in Hshift_given.
              simpl in *.
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original_shift, off)
                            Halloc'
                         ) as Hnoteq'.
              rewrite Hnoteq'.
              * by rewrite Hshift_given.
              * simpl. unfold not. rewrite pair_equal_spec. intros [? ?]. subst.
                 rewrite Hptr sigma_shifting_n_n_id in eshift.
                 inversion eshift. by subst.

          - intros [cid_recomb bid_recomb] Hrecomb.
            unfold memory_inverse_shifts_memory_at_addr,
            memory_inverse_renames_memory_at_addr,
            inverse_rename_addr in *.
            intros off. unfold inv_sigma_shifting_addr. simpl.
            specialize (Memory.load_after_alloc
                          _ _ _ _ _
                          (Permission.data, cid_recomb, bid_recomb, off)
                          Halloc'
                       ) as Hnoteq.
            simpl in Hnoteq.

            specialize (Memory.load_after_alloc_eq
                          _ _ _ _ _
                          (Permission.data, cid_recomb, bid_recomb, off)
                          Halloc'
                       ) as Heq.
            simpl in Heq.

            match goal with
            | H: Memory.alloc mem _ _ = _ |- _ =>
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_recomb, bid_recomb, off)
                            H
                         ) as Hnoteq_p;
                simpl in Hnoteq_p;

                specialize (Memory.load_after_alloc_eq
                              _ _ _ _ _
                              (Permission.data, cid_recomb, bid_recomb, off)
                              H
                           ) as Heq_p;
                simpl in Heq_p
            end.

            specialize (Hinvshift_given (cid_recomb, bid_recomb) Hrecomb off).
            simpl in Hinvshift_given.

            destruct ((cid_recomb, bid_recomb) ==
                      (Pointer.component ptr, Pointer.block ptr)) eqn:Hwhichaddr.
            + assert ((cid_recomb, bid_recomb) =
                      (Pointer.component ptr, Pointer.block ptr)) as H_. by apply/eqP.
              inversion H_. subst. clear H_.
              rewrite Hptr inv_sigma_shifting_n_n_id Heq_p; auto. simpl.
              rewrite Heq.
              destruct (Z.ltb off (Z.of_nat (Z.to_nat size)));
                destruct (Z.leb Z0 off); by auto.
              reflexivity.
            + assert ((cid_recomb, bid_recomb) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
                  by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.
              unfold option_inverse_rename_value, omap, obind, oapp in *.
              rewrite Hnoteq; auto.
              destruct (inv_sigma_shifting
                          (n cid_recomb)
                          (if cid_recomb \in domm (prog_interface p)
                           then n cid_recomb else n'' cid_recomb)
                          (care, bid_recomb))
                as [care_shift bid_recomb_shift] eqn:eshift;
                rewrite eshift; rewrite eshift in Hinvshift_given.
              simpl in *.
              match goal with
              | Halloc: Memory.alloc mem _ _ = _ |- _ =>
                specialize (Memory.load_after_alloc
                              _ _ _ _ _
                              (Permission.data, cid_recomb, bid_recomb_shift, off)
                              Halloc
                           ) as Hnoteq'
              end.
              rewrite Hnoteq'.
              * by rewrite Hinvshift_given.
              * simpl. unfold not. rewrite pair_equal_spec. intros [? ?]. subst.
                rewrite Hptr inv_sigma_shifting_n_n_id in eshift.
                 inversion eshift. by subst.


          - intros cid Hcid.
            unfold Memory.alloc in *.
            destruct (mem (Pointer.component pc)) as [memComp|] eqn:ememComp;
              try discriminate.
            destruct (mem1' (Pointer.component pc)) as [mem1'Comp|] eqn:emem1'Comp;
              try discriminate.
            destruct (ComponentMemory.alloc memComp (Z.to_nat size))
              as [memComp' b] eqn:ememComp'.
            destruct (ComponentMemory.alloc mem1'Comp (Z.to_nat size))
              as [mem1'Comp' b'] eqn:emem1'Comp'.
            match goal with
            | H: Some _ = Some _, H2: Some _ = Some _ |- _ =>
              inversion H; subst; clear H; inversion H2; subst; clear H2
            end.
            rewrite !setmE.
            destruct (cid == Pointer.component pc) eqn:ecid.
            + unfold omap, obind, oapp in *.
              
              specialize (ComponentMemory.next_block_alloc _ _ _ _ emem1'Comp')
                as [_ G1].
              rewrite G1.
              specialize (ComponentMemory.next_block_alloc _ _ _ _ ememComp')
                as [_ G2].
              rewrite G2.

              specialize (Hnextblock_given (Pointer.component pc) Hptr).
              simpl in Hnextblock_given.
              rewrite ememComp emem1'Comp in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.

            + specialize (Hnextblock_given cid Hcid).
              simpl in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.
                
        }


        assert (mem_of_part_not_executing_rel_original_and_recombined_at_internal
                  c' 
                  (CS.state_mem s1'')
                  mem2'
                  n''
                  (fun cid : nat => if cid \in domm (prog_interface p)
                                    then n cid else n'' cid)
                  t1''
                  t1') as [Hshift_not [Hinvshift_not Hnextblock_not]].
        {
          destruct Hmemc' as [Hshift_given [Hinvshift_given Hnextblock_given]].
          split; last split.
          - intros [cid_original bid_original] Horiginal1 Horiginal2.
            unfold memory_shifts_memory_at_addr, memory_renames_memory_at_addr,
            rename_addr in *.
            intros off. unfold sigma_shifting_addr. simpl.
            specialize (Memory.load_after_alloc
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Hnoteq.
            simpl in Hnoteq.

            specialize (Memory.load_after_alloc_eq
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Heq.
            simpl in Heq.

            specialize (Hshift_given
                          (cid_original, bid_original) Horiginal1 Horiginal2 off).
            simpl in Hshift_given.

            destruct ((cid_original, bid_original) ==
                      (Pointer.component ptr, Pointer.block ptr)) eqn:Hwhichaddr.
            + assert ((cid_original, bid_original) =
                      (Pointer.component ptr, Pointer.block ptr)) as H_. by apply/eqP.
              inversion H_. subst. clear H_.
              simpl in Horiginal1.
              rewrite <- Hifc_cc' in Horiginal1.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hcontra] _].
              by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).
            + assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
              by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.
              unfold option_rename_value, omap, obind, oapp in *.
              destruct (sigma_shifting
                          (n'' cid_original)
                          (if cid_original \in domm (prog_interface p)
                           then n cid_original else n'' cid_original)
                          (care, bid_original))
                as [care_shift bid_original_shift] eqn:eshift;
                rewrite eshift; rewrite eshift in Hshift_given.
              simpl in *.
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original_shift, off)
                            Halloc'
                         ) as Hnoteq'.
              rewrite Hnoteq'.
              * by rewrite Hshift_given.
              * simpl. unfold not. rewrite pair_equal_spec. intros [? ?]. subst.
                rewrite <- Hifc_cc' in Horiginal1.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).

          - intros [cid_original bid_original] Horiginal1 Horiginal2.
            unfold memory_inverse_shifts_memory_at_addr,
            memory_inverse_renames_memory_at_addr,
            inverse_rename_addr in *.
            intros off. unfold sigma_shifting_addr. simpl.
            specialize (Memory.load_after_alloc
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Hnoteq.
            simpl in Hnoteq.

            specialize (Memory.load_after_alloc_eq
                          _ _ _ _ _
                          (Permission.data, cid_original, bid_original, off)
                          Halloc'
                       ) as Heq.
            simpl in Heq.

            specialize (Hinvshift_given
                          (cid_original, bid_original) Horiginal1 Horiginal2 off).
            simpl in Hinvshift_given.

            destruct ((cid_original, bid_original) ==
                      (Pointer.component ptr, Pointer.block ptr)) eqn:Hwhichaddr.
            + assert ((cid_original, bid_original) =
                      (Pointer.component ptr, Pointer.block ptr)) as H_. by apply/eqP.
              inversion H_. subst. clear H_.
              simpl in Horiginal1.
              rewrite <- Hifc_cc' in Horiginal1.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hcontra] _].
              by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).
            + assert ((cid_original, bid_original) <>
                        (Pointer.component ptr, Pointer.block ptr)) as H_.
              by intros H_; inversion H_; subst; rewrite eqxx in Hwhichaddr.
              unfold option_inverse_rename_value, omap, obind, oapp in *.
              destruct (inv_sigma_shifting
                          (n'' cid_original)
                          (if cid_original \in domm (prog_interface p)
                           then n cid_original else n'' cid_original)
                          (care, bid_original))
                as [care_shift bid_original_shift] eqn:eshift;
                rewrite eshift; rewrite eshift in Hinvshift_given.
              simpl in *.
              specialize (Memory.load_after_alloc
                            _ _ _ _ _
                            (Permission.data, cid_original, bid_original, off)
                            Halloc'
                         ) as Hnoteq'.
              rewrite Hnoteq'.
              * by rewrite Hinvshift_given.
              * simpl. unfold not. rewrite pair_equal_spec. intros [? ?]. subst.
                rewrite <- Hifc_cc' in Horiginal1.
                unfold mergeable_interfaces, linkable in *.
                destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth Hcontra Horiginal1 Hptr).

          - intros cid Hcid.
            unfold Memory.alloc in *.
            destruct (mem (Pointer.component pc)) as [memComp|] eqn:ememComp;
              try discriminate.
            destruct (mem1' (Pointer.component pc)) as [mem1'Comp|] eqn:emem1'Comp;
              try discriminate.
            destruct (ComponentMemory.alloc memComp (Z.to_nat size))
              as [memComp' b] eqn:ememComp'.
            destruct (ComponentMemory.alloc mem1'Comp (Z.to_nat size))
              as [mem1'Comp' b'] eqn:emem1'Comp'.
            match goal with
            | H: Some _ = Some _, H2: Some _ = Some _ |- _ =>
              inversion H; subst; clear H; inversion H2; subst; clear H2
            end.
            rewrite !setmE.
            destruct (cid == Pointer.component pc) eqn:ecid.
            + assert (cid = Pointer.component pc). by apply/eqP. subst.
              rewrite <- Hifc_cc' in Hcid.
              unfold mergeable_interfaces, linkable in *.
              destruct Hmerge_ipic as [[_ Hcontra] _].
                by specialize (fdisjoint_partition_notinboth
                                 Hcontra Hcid Hpc_prog_interface_p).

            + specialize (Hnextblock_given cid Hcid).
              simpl in Hnextblock_given.
              inversion Hnextblock_given as [Hrewr].
              by rewrite Hrewr.

        }

        assert (
          regs_rel_of_executing_part
            (Register.set rptr (Ptr ptr) regs)
            (Register.set rptr (Ptr ptr) regs1')
            n
            (fun cid : nat => if cid \in domm (prog_interface p)
                              then n cid else n'' cid)
        ) as Hregs.
        {
          constructor. intros reg. unfold Register.get, Register.set. rewrite !setmE.
          destruct (Register.to_nat reg == Register.to_nat rptr) eqn:ereg;
            rewrite ereg.
          - destruct ptr as [[[perm cid] bid] off].
            unfold shift_value, inverse_shift_value, rename_value, inverse_rename_value,
            rename_addr, inverse_rename_addr. simpl.
            rewrite Hptr sigma_shifting_n_n_id inv_sigma_shifting_n_n_id.
            unfold Memory.alloc in *.
            destruct (mem1' (Pointer.component pc)); try discriminate.
            destruct (ComponentMemory.alloc s (Z.to_nat size)).
            inversion Halloc'. subst. by simpl.
          - inversion Hregsp as [G]. by specialize (G reg).
        }
        
        
        assert (Step sem'
                     (gps1', mem1', regs1', pc)
                     E0
                     (gps1', mem2', Register.set rptr (Ptr ptr) regs1', Pointer.inc pc)
               ) as Hstep12'.
        {
          eapply CS.Step_non_inform; first eapply CS.Alloc.
          -- exact Hex'.
          -- eassumption.
          -- assumption.
          -- eassumption.
          -- reflexivity.
          -- reflexivity.
        }


        assert (CSInvariants.is_prefix
                  (gps, mem', Register.set rptr (Ptr ptr) regs, Pointer.inc pc)
                  (program_link p c) t1)
          as H_prefix_after_step.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }
        

        assert (CSInvariants.is_prefix
                  (gps1', mem2', Register.set rptr (Ptr ptr) regs1', Pointer.inc pc)
                  (program_link p c')
                  t1'
               )
          as H_prefix_after_step'.
        {
          unfold CSInvariants.is_prefix in *.
          eapply star_right; try eassumption.
          ++ by rewrite E0_right.
        }

        assert (good_memory (left_addr_good_for_shifting n) mem') as Hgood_memp_alloc.
        {
          unfold good_memory.
          intros ? ? ? ? ? ? Hlgood Hloadptr.
          match goal with | Halloc: Memory.alloc mem _ _ = _ |- _ =>
                            specialize (Memory.load_after_alloc_eq
                                          _ _ _ _ _
                                          (Permission.data, cid, bid, offset)
                                          Halloc
                                       ) as Heq;
                            specialize (Memory.load_after_alloc
                                          _ _ _ _ _
                                          (Permission.data, cid, bid, offset)
                                          Halloc
                                       ) as Hnoteq  
          end.
          simpl in Heq. simpl in Hnoteq.
          destruct ((cid, bid) == (Pointer.component ptr, Pointer.block ptr))
                   eqn:eptr.
          - assert ((cid, bid) = (Pointer.component ptr, Pointer.block ptr)) as H_.
              by apply/eqP.
            inversion H_. subst. clear H_ eptr.
            rewrite Heq in Hloadptr; auto.
            destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
              destruct (Z.leb Z0 offset); discriminate.
          - assert ((cid, bid) <> (Pointer.component ptr, Pointer.block ptr)) as H_.
            { intros H_. inversion H_. subst. clear H_. by rewrite eqxx in eptr.  }
            rewrite Hnoteq in Hloadptr; auto.
            by eapply Hgood_mem; eauto.
        }

        assert (good_memory
                  (left_addr_good_for_shifting
                     (fun cid : nat => if cid \in domm (prog_interface p)
                                       then n cid else n'' cid))
                  mem2') as Hgood_mem2'.
        {
          unfold good_memory.
          intros ? ? ? ? ? ? Hlgood Hloadptr.
          specialize (Memory.load_after_alloc_eq
                        _ _ _ _ _
                        (Permission.data, cid, bid, offset)
                        Halloc'
                     ) as Heq.
          specialize (Memory.load_after_alloc
                        _ _ _ _ _
                        (Permission.data, cid, bid, offset)
                        Halloc'
                     ) as Hnoteq.
          simpl in Heq. simpl in Hnoteq.
          destruct ((cid, bid) == (Pointer.component ptr, Pointer.block ptr))
                   eqn:eptr.
          - assert ((cid, bid) = (Pointer.component ptr, Pointer.block ptr)) as H_.
              by apply/eqP.
            inversion H_. subst. clear H_ eptr.
            rewrite Heq in Hloadptr; auto.
            destruct (Z.ltb offset (Z.of_nat (Z.to_nat size)));
              destruct (Z.leb Z0 offset); discriminate.
          - assert ((cid, bid) <> (Pointer.component ptr, Pointer.block ptr)) as H_.
            { intros H_. inversion H_. subst. clear H_. by rewrite eqxx in eptr.  }
            rewrite Hnoteq in Hloadptr; auto.
            by eapply Hgood_mem'; eauto.
        }
        
        eexists. split; eauto.
        econstructor; try eassumption.
        * (* mergeable_states_well_formed *)
          eapply mergeable_states_well_formed_intro; try eassumption.
          -- by simpl.
          -- rewrite <- Hpccomp_s'_s''. simpl.
             by rewrite Pointer.inc_preserves_component.
        * by simpl.
        * by unfold mem_of_part_executing_rel_original_and_recombined; intuition.
        * by unfold mem_of_part_not_executing_rel_original_and_recombined_at_internal;
            intuition.
        
      + simpl in *. subst.
        unfold CS.is_program_component,
        CS.is_context_component, turn_of, CS.state_turn in *.
        unfold negb, ic in Hcomp1.
        rewrite Hpccomp_s'_s in H_c'.
          by rewrite H_c' in Hcomp1.


    - discriminate.
    - discriminate.

      
  Admitted.
  

  (* Compose two stars into a merged star. The "program" side drives both stars
     and performs all steps without interruption, the "context" side remains
     unaltered in both stars. *)
  (* NOTE: By itself, the reformulation of this lemma does not say anything
     interesting, because the existential can be discharged trivially by
     reflexivity, but that is not what we want. In fact, even the proof is
     tellingly boring. *)
  Theorem threeway_multisem_star_E0_program s1 s1' s1'' t1 t1' t1'' s2 s2'':
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstar12 Hstar12''.
    inversion Hmerge1.
    - pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'.

      (* inversion H (* as ...*). *)
      find_and_invert_mergeable_states_well_formed.

      rewrite (* Hifacec *) Hifc_cc' in Hcomp1'.
      remember E0 as t eqn:Ht.
      revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''.
      apply star_iff_starR in Hstar12.
      induction Hstar12 as [s | s1 t1E0 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Ht Hmerge1 Hcomp1 Hcomp1'' Hstar12''.
      + exists s1'. split.
        * now apply star_refl.
        * eapply merge_states_silent_star; eassumption.
      + apply Eapp_E0_inv in Ht. destruct Ht; subst.
        specialize (IHstar H H0 H2 H3
                           Hpref_t Hgood_mem Hstack_s_s' Hpccomp_s'_s
                           Logic.eq_refl Hmerge1 Hcomp1 Hcomp1'' Hstar12'')
          as [s2' [Hstar12' Hmerge2]].
        (*specialize (IHstar Hstar eq_refl Hmerge1 Hcomp1 Hcomp1'' Hstar12'')
          as [s2' [Hstar12' Hmerge2]].*)
        pose proof CS.epsilon_star_non_inform_preserves_program_component _ _ _ _
             Hcomp1 ((proj2 (star_iff_starR _ _ _ _ _)) Hstar12) as Hcomp2.
        pose proof threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23
          as [s3' [Hstep23' Hmerge3]].
        exists s3'. split.
        * apply star_trans with (t1 := E0) (s2 := s2') (t2 := E0);
            [assumption | | reflexivity].
          now apply star_one.
        * assumption.
    - (* derive a contradiction to Hcomp1 *) admit.
  Admitted.

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
    traces_shift_each_other n n'' (rcons t1 e) (rcons t1'' e'') ->
    good_trace (left_addr_good_for_shifting n) (rcons t1 e) ->
    good_trace (left_addr_good_for_shifting n'') (rcons t1'' e'') ->
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
    inversion Hstep12. subst.
    inversion Hmerge1; find_and_invert_mergeable_states_well_formed.
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
        inversion Hrel2 as [? ? Hrel2'].
        inversion Hrel2' as [  |
                           tpref1 e1 tpref1'' e1'' Hr1 Hr2 Hr3 Hr4 Harg Harginv Hr5 Hr6].
        * pose proof size_rcons t1'' e'' as Hcontra.
          match goal with
          | H: [::] = rcons _ _ |- _ =>
            rewrite <- H in Hcontra
          end.
            by simpl in *.
        * apply rcons_inj in Hr5. apply rcons_inj in Hr6. inversion Hr5. inversion Hr6.
          subst. clear Hr5 Hr6.
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
          eexists.  (*(ECall cid pid _ (CS.state_mem s1') cid_caller)*)
          eexists ((Pointer.inc s1'pc) :: s1'stk,
                   s1'mem,
                   Register.invalidate s1'reg,
                   _).
          destruct s2'' as [[[s2''stk s2''mem] s2''reg] s2''pc].
          inversion Hstep12'' as [? ? ? ? Hstep'' Hcontra'']. subst.
          inversion Hstep''; subst; simpl in Hcontra''; try discriminate.
          inversion Hcontra''. subst.
          split.
          -- eapply CS.Step_non_inform; eauto.
             ++ eapply (@CS.Call (prepare_global_env prog') _ _ _ _ _ _ _ _);
                  try eassumption.
                ** eapply (execution_invariant_to_linking p c c'); eauto.
                   --- unfold mergeable_interfaces in *. by intuition.
                   --- match goal with
                       | H: _ = prog_interface c' |- _ => rewrite <- H end.
                       unfold mergeable_interfaces in *. by intuition.
                   --- simpl in *.
                       (*Search _ Pointer.component prog_interface.*)
                       (* probably need to apply CS.domm_partition *)
                       admit.
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
                ** (** here, use the register relation **)
                  match goal with
                  | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
                    inversion H as [Hregrel]
                  end.
                  simpl in Hregrel.
                  pose proof Hregrel R_COM. by intuition.
             ++ reflexivity.
          -- apply mergeable_border_states_c'_executing.
             ++ constructor; auto; simpl.
                ** (* is_prefix *) admit.
                ** (* is_prefix *) admit.
                ** (* is_prefix *) admit.
                ** constructor; auto.
                   --- (* argument is good *)
                     simpl in *. intros a Ha.
                     match goal with
                     | Hregs: regs_rel_of_executing_part _ s1'reg _ _ |- _ =>
                       inversion Hregs as [Hreg]
                     end.
                     unfold left_addr_good_for_shifting,
                     left_block_id_good_for_shifting.
                     destruct a as [acid abid].
                     
                     destruct (Hreg R_COM) as [Hshift _].
                     destruct (Register.get R_COM regs) as
                         [ i | [[[perm cid] bid] off] | ];
                       simpl in Hshift; rewrite <- Hshift in Ha; simpl in Ha.
                     +++ by rewrite in_fset0 in Ha.
                     +++ destruct (perm =? Permission.data) eqn:eperm.
                         *** unfold rename_addr in *.
                             destruct (
                                 sigma_shifting_addr n
                                                     (fun cid : nat =>
                                                        if cid \in domm (prog_interface p)
                                                        then n cid else n'' cid)
                                                     (cid, bid)
                               ) as [cidshift bidshift] eqn:eshift.
                             rewrite eshift in Ha.
                             unfold addr_of_value in Ha. rewrite eperm in Ha.
                             rewrite in_fset1 in Ha.
                             rewrite eqE in Ha. simpl in Ha.
                             pose proof
                                  left_addr_good_right_addr_good
                                  n
                                  (fun cid : nat =>
                                     if cid \in domm (prog_interface p)
                                     then n cid else n'' cid)
                                  (cid, bid)
                                  (cidshift, bidshift) as Hleft_right.
                             unfold rename_addr, right_addr_good_for_shifting,
                             right_block_id_good_for_shifting in *.
                             rewrite eshift in Hleft_right.
                             assert (acid == cidshift /\ abid == bidshift) as [h1 h2].
                               by apply/andP.
                               assert (acid = cidshift). by apply/eqP.
                               assert (abid = bidshift). by apply/eqP.
                               subst. clear h1 h2.
                               eapply Hleft_right; auto.
                               (* Remains to prove 
                                  left_addr_good_for_shifting n (cid, bid) *)
                               inversion Hgood2 as [| ? ? ? ? Harg_good Hrcons ].
                             ---- (* nil = rcons *)
                                 by find_nil_rcons.
                             ---- apply rcons_inj in Hrcons.
                                  inversion Hrcons. subst.
                                  eapply Harg_good. simpl.
                                  by rewrite eperm in_fset1.
                         *** unfold addr_of_value in Ha.
                               by rewrite eperm in_fset0 in Ha.
                     +++ by rewrite in_fset0 in Ha.
                ** (* stack of p is related to the stack of recombined *)
                  simpl in *. subst.
                  apply stack_of_program_part_rel_stack_of_recombined_cons; auto.
                    by destruct
                         (Pointer.component (Pointer.inc pc)
                                            \in domm (prog_interface p)).
                ** (* stack of c' is related to the stack of recombined *)
                  simpl in *. subst.
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
                ** (* traces_shift_each_other *)
                  constructor. constructor; auto.
                   --- assert (traces_shift_each_other
                                 n
                                 (fun cid : nat =>
                                    if cid \in domm (prog_interface p)
                                    then n cid
                                    else n'' cid
                                 )
                                 t1 t1'
                              ) as G.
                       {
                         apply traces_shift_each_other_transitive
                           with (n2 := n'') (t2 := t1''); auto.
                         by constructor.
                       }
                         by inversion G.
                   --- intros addr Haddrshare_t1_call.
                       pose proof Hr2 addr Haddrshare_t1_call as
                           [Hren_n_n'' Hshrt1''].
                       apply Hr3 in Hshrt1'' as [Hinvren_n_n'' Hshr_t1_call].
                       simpl in *.
                       split.
                       +++ unfold event_renames_event_at_addr. simpl.
                           (* SearchAbout mem0 s1'mem *)
                           unfold mem_of_part_executing_rel_original_and_recombined
                             in *.
                           (* TODO: Need to strengthen the memory invariant? 
                              The relevant memory invariant seems to be H5.
                              But H5 is too weak. 
                              
                              It only establishes renaming
c
                              for an address whose component is in the domain
                              of prog_interface p.

                              Is there an "event renaming" among the hypotheses
                              that we can use instead?
                            *)
                           admit.
                       +++ admit.
                   --- (* the symmetric/inverse case of renaming *)
                     admit.
                   --- constructor; eauto.
                   --- simpl in *.
                       match goal with
                       | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
                         inversion H as [Hregs]
                       end.
                       unfold shift_value in *.
                       destruct (Hregs R_COM) as [Hregs_ren _].
                       by rewrite <- Hregs_ren.
                   --- simpl in *.
                       match goal with
                       | H: regs_rel_of_executing_part _ _ _ _ |- _ =>
                         inversion H as [Hregs]
                       end.
                       unfold inverse_shift_value in *.
                       destruct (Hregs R_COM) as [_ Hregs_invren].
                       by rewrite <- Hregs_invren.
                ** constructor. constructor; auto.
                   --- match goal with
                       | Hshift: traces_shift_each_other n'' _ t1'' t1' |- _ =>
                           by inversion Hshift
                       end.
                   --- admit.
                   --- admit.
                   --- by intuition.
                   --- simpl.
                       (* They should both be invalidated register files. *)
                       admit.
                   --- simpl.
                       (* They should both be invalidated register files. *)
                       admit.
             ++ simpl. (* SearchAbout b'. *)
                (* Need a lemma about EntryPoint.get before we are able to use
                   the following match.
                 *)
                (*match goal with
                | Hb0: _ = Some b0 |- _ =>
                  rewrite Hb' in Hb0; inversion Hb0
                end.*)
                admit.
             ++ (* SearchAbout C'0. *)
                (* should be available from Pointer.component pc0 <> C'0 *)
                admit.
             ++ simpl.
                (* prove a lemma about Register.invalidate regs_rel_of_executing_part *)
                admit.
             ++ (* memory relation executing part *)
               simpl.
               admit.
             ++ (* memory relation of the non-executing part *)
               simpl.
               admit.
               
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

(* Helpers and symmetric version of three-way simulation. *)
Section ThreewayMultisem2.
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

  (* RB: TODO: Rename, relocate. *)
  (* RB: NOTE: [DynShare] In this series of results, identical traces will need
     to be replaced by related traces. We can expect similar complications as in
     previous sections, especially in the need to produce explicit successor
     states that continue to satisfy the mergeability relation. *)
  Lemma threeway_multisem_mergeable
        s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s1, t) (CS.state_mem s1'', t'') p ->
  exists s2' t',
    mergeable_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  (* Qed. *)
  Admitted. (* RB: TODO: Add stepping of [s1']. Redundant? *)

  (* RB: TODO: Implicit parameters, compact if possible. *)
  (* RB: NOTE: Again, without mergeability, this lemma is trivial and
     uninteresting. *)
  Lemma threeway_multisem_star_E0 s1 s1' s1'' t1 t1' t1'' s2 s2'':
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    (* Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2''). *)
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' t1 t1' t1''.
  Proof.
    intros H H0 H1.
  (*   inversion H as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hprg_component.
    - eapply threeway_multisem_star_E0_program; eassumption.
    - admit.
  (*   - rewrite (merge_states_sym H); try assumption. *)
  (*     rewrite (merge_states_sym (threeway_multisem_mergeable H H0 H1)); try assumption. *)
  (*     assert (Hlinkable : linkable ip ic) by now destruct Hmergeable_ifaces. *)
  (*     unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. *)
  (*     pose proof (program_linkC Hwfp Hwfc' Hlinkable) as Hprg_linkC'. *)
  (*     unfold sem', prog'. *)
  (*     rewrite Hprg_linkC'. *)
  (*     pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''. *)
  (*     unfold sem'', prog'' in H1. *)
  (*     rewrite (Hprg_linkC'' Hlinkable) in H1. *)
  (*     pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC. *)
  (*     unfold sem, prog in H0. *)
  (*     rewrite (Hprg_linkC Hlinkable) in H0. *)
  (*     pose proof (threeway_multisem_star_E0_program) as Hmultisem. *)
  (*     specialize (Hmultisem c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in Hmultisem. *)
  (*     specialize (Hmultisem s1'' s1 s2'' s2). *)
  (*     assert (His_prg_component'' : CS.is_program_component s1'' (prog_interface p)). *)
  (*     { eapply mergeable_states_context_to_program. *)
  (*       apply H. *)
  (*       unfold CS.is_program_component in Hprg_component. apply negbFE in Hprg_component. *)
  (*       assumption. *)
  (*     } *)
  (*     assert (Hmerg_sym : mergeable_states c' p' c p s1'' s1). *)
  (*     { inversion H. *)
  (*       econstructor; *)
  (*         try rewrite <- (Hprg_linkC Hlinkable); try rewrite <- (Hprg_linkC'' Hlinkable); eauto. *)
  (*       apply mergeable_interfaces_sym; congruence. *)
  (*     } *)
  (*     specialize (Hmultisem His_prg_component'' Hmerg_sym H1 H0). *)
  (*     assumption. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Add mergeability. *)

  (* A restricted version of the lockstep simulation on event-producing steps.
     RB: NOTE: Here is where we depart from the multi-semantics and need to
     furnish our own version. We may save effort if, as is the case here, we only
     need to concern ourselves with visible steps. *)
  (* RB: NOTE: Events need to be properly for full generality. Otherwise, this
     is just a symmetry lemma. *)
  Lemma threeway_multisem_event_lockstep s1 s1' s1'' t1 t1' t1'' e e'' s2 s2'' :
    mergeable_internal_states p c p' c' n n''  s1 s1' s1'' t1 t1' t1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    traces_shift_each_other n n'' (rcons t1 e) (rcons t1'' e'') ->
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mergeable_border_states p c p' c' n n'' s2 s2' s2'' (rcons t1 e) 
                            (rcons t1' e') (rcons t1'' e'').
  Proof.
    intros Hmerge1 Hstep12 Hstep12'' Hrel2.
  (*   inversion Hmerge1 as [? ? ? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed _ Hini H1 Hstar H2]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - inversion Hmerge1.
      eapply threeway_multisem_event_lockstep_program; try eassumption.
  (*   - inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof @threeway_multisem_event_lockstep_program c' p' c p as H. *)
  (*     rewrite <- Hifacec, <- Hifacep in H. *)
  (*     specialize (H s1'' s1 e s2'' s2). *)
  (*     assert (Hmerge11 := Hmerge1). *)
  (*     erewrite mergeable_states_sym in Hmerge11; try eassumption. *)
  (*     erewrite mergeable_states_sym; try eassumption. *)
  (*     unfold ip, ic; erewrite merge_states_sym; try eassumption. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s2 s2''). *)
  (*     { inversion Hmerge1. *)
  (*       econstructor; try eassumption. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. } *)
  (*     rewrite (merge_states_sym Hmerge2); try assumption. *)
  (*     unfold sem', prog'; rewrite program_linkC; try congruence. *)
  (*     apply H; try assumption. *)
  (*     + unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn. *)
  (*       pose proof mergeable_states_pc_same_component Hmerge1 as Hpc. *)
  (*       destruct s1 as [[[[? ?] ?] pc1] ?]; destruct s1'' as [[[[? ?] ?] pc1''] ?]. *)
  (*       simpl in Hpc. *)
  (*       rewrite -Hpc. *)
  (*       unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcase. *)
  (*       destruct (CS.star_pc_domm_non_inform _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hdomm | Hdomm]. *)
  (*       apply domm_partition_notin_r with (ctx2 := ic) in Hdomm. *)
  (*       move: Hcase => /idP Hcase. rewrite Hdomm in Hcase. congruence. assumption. *)
  (*       now apply domm_partition_notin with (ctx1 := ip) in Hdomm. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       apply linkable_sym; congruence. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       now apply linkable_sym. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Symmetry lemma. Fix according to program side. *)
  (* JT: TODO: clean this proof. *)

  Theorem threeway_multisem_star_program
          s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    (* mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2',  t' ). *)
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' t'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 ta s2 tb s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' t'' s2'' Hcomp1 Hmerge1 Hstar12'' Hrel3.
    - assert (t'' = E0) by admit; subst t''. (* By the relation. *)
      exists E0, s1'. split.
      + now apply star_refl.
      + eapply merge_states_silent_star; try eassumption.
        (* AEK: 
           The lemma applied above looks suspicious because it seems
           we are now getting the same goal (as before the apply) again.
         *)
        admit.
        (* eapply context_epsilon_star_merge_states. eassumption. *)
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      assert (exists ta'' tb'', t'' = ta'' ** tb'')
        as [ta'' [tb'' ?]] by admit; subst t''. (* By pairwise events.
                                                   More info? *)
      assert (Hstar13''_ := Hstar13''). (* Which variants are needed? *)
      apply (star_app_inv (@CS.singleton_traces_non_inform _)) in Hstar13''_
        as [s2'' [Hstar12'' Hstar23'']].
      assert (Hrel1 : mem_rel2 n n'' (CS.state_mem s2, ta) (CS.state_mem s2'', ta'') p)
        by admit. (* Need to recompose memory relation based on executions. *)

      (*******************************************************************************)
      (*
      specialize (IHstar12' _ _ _ Hcomp1 Hmerge1 Hstar12'' Hrel1)
        as [ta' [s2' [Hstar12' Hmerge2]]].
      destruct tb as [| e2 [| e2' tb]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star.
           eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl]. *)
        assert (tb'' = E0) by admit; subst tb''.
        destruct (threeway_multisem_star_E0
                    Hmerge2 (star_one _ _ _ _ _ Hstep23) Hstar23'')
          as [s3' [Hstar23' Hmerge3]].
        exists ta', s3'. split.
        * eapply star_trans; try eassumption. by rewrite E0_right.
        * by rewrite !E0_right.
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        assert (exists e2'', tb'' = [e2'']) as [e2'' ?]
            by admit; subst tb''. (* By one-to-one event correspondence. More? *)
        change [e2''] with (E0 ** e2'' :: E0) in Hstar23''.
        apply (star_middle1_inv (@CS.singleton_traces_non_inform _)) in Hstar23''
          as [s2''1 [s2''2 [Hstar2'' [Hstep23'' Hstar3'']]]].
        (* Prefix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s2
          as Hstar2.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar2 as Hstar2_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge2 Hstar2_non_inform Hstar2''
          as [s2'1 [Hstar2' Hmerge21]].
        (* Propagate mergeability, step.
           NOTE: This is done early now, just above. *)
        (* assert (Hrel2 : mem_rel2 p α γ (CS.state_mem s2, E0) (CS.state_mem s2'', E0)) *)
          (* by admit. (* Should be easy. *) *)
        (* pose proof threeway_multisem_mergeable Hmerge2 Hstar2_non_inform Hstar2'' Hrel2 *)
          (* as [s2'2 Hmerge21']. *)
        assert (Hrel2 :
                  mem_rel2 n n'' (CS.state_mem s3, [e2]) (CS.state_mem s2''2, [e2'']) p)
          by admit. (* This one should also be obtainable from premises. *)
        pose proof threeway_multisem_event_lockstep Hmerge21 Hstep23 Hstep23'' Hrel2
          as [e' [s2'2 [Hstep23' Hmerge22]]].
        (* Propagate mergeability, suffix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s3
          as Hstar3.
        pose proof CS.star_sem_inform_star_sem_non_inform _ _ _ _ Hstar3 as Hstar3_non_inform.
        pose proof threeway_multisem_star_E0 Hmerge22 Hstar3_non_inform Hstar3''
          as [s3' [Hstar3' Hmerge3]].
        (* Compose. *)
        exists (ta' ++ [e']), s3'. split. (*[| assumption].*)
        * eapply star_trans; first eassumption.
        exact (star_trans
                 (star_right _ _ Hstar2' Hstep23' (eq_refl _))
                 Hstar3' (eq_refl _)).
        rewrite -> E0_right, <- Eapp_assoc, -> E0_right.
        reflexivity.
        * by rewrite <- !Eapp_assoc.
      + (* Contradiction: a step generates at most one event. *)
        pose proof @CS.singleton_traces_non_inform _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  (* Qed. *)
       *)
      (******************************************************************************)
  Admitted. (* RB: TODO: Check admits. *)
End ThreewayMultisem2.

(* Three-way simulation and its inversion. *)
Section ThreewayMultisem3.
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

  Theorem threeway_multisem_star s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n'' (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
    (* Star (CS.sem_non_inform (program_link p  c')) (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
    (* /\ mergeable_states ip ic s2 s2'' *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    intros Hmerge1 Hstar12 Hstar12'' Hrel2.
  (*   inversion Hmerge1 as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    destruct (CS.is_program_component s1 ic) eqn:Hcomp1.
    - eapply threeway_multisem_star_program; eassumption.
  Admitted. (* TODO: Proof of symmetry. Harmonize statements as needed. *)
  (*   - apply negb_false_iff in Hcomp1. *)
  (*     apply (mergeable_states_context_to_program Hmerge1) *)
  (*       in Hcomp1. *)
  (*     assert (Hmerge2: mergeable_states p c p' c' s2 s2'') *)
  (*       by (eapply threeway_multisem_mergeable; eassumption). *)
  (*     rewrite program_linkC in Hstar12; try assumption; *)
  (*       last now destruct Hmergeable_ifaces. *)
  (*     rewrite program_linkC in Hstar12''; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec -Hifacep. *)
  (*     rewrite program_linkC; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec. *)
  (*     unfold ip, ic. *)
  (*     setoid_rewrite merge_states_sym at 1 2; try eassumption. *)
  (*     pose proof threeway_multisem_star_program as H. *)
  (*     specialize (H c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in H. *)
  (*     specialize (H s1'' s1 t s2'' s2). *)
  (*     apply H; try assumption. *)
  (*     apply mergeable_states_sym in Hmerge1; try assumption; *)
  (*       try rewrite -Hifacec; try rewrite -Hifacep; try apply mergeable_interfaces_sym; *)
  (*         now auto. *)
  (* Qed. *)
  (* JT: TODO: improve this proof *)

  (* RB: NOTE: With the added premises, this becomes simply the three-way
     simulation lemma, and one of them ([threeway_multisem_mergeable]) becomes
     redundant.
     TODO: Possibly remove that lemma, and/or merge this with the main three-way
     result. *)
  Corollary star_simulation s1 s1' s1'' t1 t1' t1'' t t'' s2 s2'' :
    mergeable_internal_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 n n''  (CS.state_mem s2, t1 ++ t) (CS.state_mem s2'', t1'' ++ t'') p ->
  exists t' s2',
    Star sem'  s1' t' s2' /\
    mergeable_internal_states p c p' c' n n'' s2 s2' s2'' (t1 ++ t) (t1' ++ t') (t1'' ++ t'').
  Proof.
    now apply threeway_multisem_star.
  Qed.

  (* [DynShare]
     The following tactic applies program_store_from_partialized_memory
     and program_alloc_from_partialized_memory, which will both fail.
   *)
  (* Ltac t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec:= *)
  (*   match goal with *)
  (*   (* Memory operations. *) *)
  (*   | Hstore : Memory.store _ _ _ = _ |- _ => *)
  (*     apply program_store_from_partialized_memory in Hstore as [mem1_ Hstore]; *)
  (*       try eassumption *)
  (*   | Halloc : Memory.alloc _ _ _ = _ |- _ => *)
  (*     apply program_alloc_from_partialized_memory in Halloc as [mem1_ [ptr_ Halloc]]; *)
  (*       try assumption *)
  (*   (* Calls. *) *)
  (*   | Hget : EntryPoint.get _ _ _ = _ |- _ => *)
  (*     apply (genv_entrypoints_interface_some) with (p' := prog) in Hget as [b' Hget]; *)
  (*     last (simpl; congruence); *)
  (*     try assumption *)
  (*   (* Returns. *) *)
  (*   | Hcons : ?PC' :: ?GPS' = ?GPS (* merge_states_stack *) |- _ => *)
  (*     destruct GPS as [| frame1' gps1'] eqn:Hgps; [discriminate |]; *)
  (*     destruct gps1 as [| frame1 gps1]; [now destruct gps1'' |]; *)
  (*     destruct gps1'' as [| frame1'' gps1'']; [easy |]; *)
  (*     inversion Hcons; subst PC' GPS'; *)
  (*     assert (Heq : Pointer.component frame1 = Pointer.component frame1') *)
  (*       by (unfold merge_states_stack in Hgps; *)
  (*           inversion Hgps as [[Hframe Hdummy]]; *)
  (*           unfold merge_frames; *)
  (*           destruct (Pointer.component frame1 \in domm ip) eqn:Hcase; rewrite Hcase; *)
  (*           [ reflexivity *)
  (*           | eapply mergeable_states_cons_domm; last exact Hmerge; eassumption]); *)
  (*     rewrite <- Heq *)
  (*   | _ => idtac *)
  (*   end; *)
  (*   [eexists; *)
  (*   CS.step_of_executing]; *)
  (*     try eassumption; try congruence; try reflexivity; *)
  (*     try (simpl; rewrite Hifacec; eassumption); *)
  (*     match goal with *)
  (*     (* Memory operations. *) *)
  (*     | Hload : Memory.load _ _ = _ |- Memory.load _ _ = _ => *)
  (*       unfold merge_states_mem in Hload; *)
  (*       erewrite <- program_load_to_partialized_memory_strong in Hload; *)
  (*       try exact Hmerge; eassumption *)
  (*     (* Jumps. *) *)
  (*     | Hlabel : find_label_in_component _ _ _ = _ |- find_label_in_component _ _ _ = _ => *)
  (*       rewrite find_label_in_component_program_link_left; *)
  (*       rewrite find_label_in_component_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     | Hlabel : find_label_in_procedure _ _ _ = _ |- find_label_in_procedure _ _ _ = _ => *)
  (*       rewrite find_label_in_procedure_program_link_left; *)
  (*       rewrite find_label_in_procedure_program_link_left in Hlabel; *)
  (*       try eassumption; simpl in *; congruence *)
  (*     (* Calls. *) *)
  (*     | Himp : imported_procedure _ _ _ _ |- imported_procedure _ _ _ _ => *)
  (*       rewrite imported_procedure_unionm_left; [| assumption]; *)
  (*       rewrite Hifacec in Hnotin; now rewrite imported_procedure_unionm_left in Himp *)
  (*     | _ => idtac *)
  (*     end; *)
  (*   [apply execution_invariant_to_linking with (c1 := c')]; *)
  (*   try congruence; *)
  (*   try eassumption. *)
  (*     (* try eassumption; [congruence]. *) *)


  (* AEK: Looks too strong. *)
  Theorem threeway_multisem_step_inv_program s1 s1' s1'' t1 t1' t1'' t' s2' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' n n'' s1 s1' s1'' t1 t1' t1'' ->
    (* Step sem' (merge_states ip ic s1 s1'') t s2' -> *)
    Step sem' s1' t' s2' ->
  exists t s2,
    Step sem  s1  t  s2 /\
    mem_rel2 n n'' (CS.state_mem s1', t') (CS.state_mem s1, t) p.
  Admitted. (* RB: TODO: Tweak relations, prove later IF NEEDED. *)
  (* Proof. *)
  (*   intros Hpc Hmerge Hstep. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct s1 as [[[[gps1 mem1] regs1] pc1] addrs1]. *)
  (*   destruct s1'' as [[[[gps1'' mem1''] regs1''] pc1''] addrs1'']. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm'. *)
  (*   pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin; unfold ic in Hnotin; *)
  (*   assert (Hmains : linkable_mains p c') *)
  (*     by (apply linkable_implies_linkable_mains; congruence). *)
  (*   rewrite (mergeable_states_merge_program _ Hmerge) in Hstep; *)
  (*     try assumption. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc Hlinkable as Hwfprog. *)
  (*   pose proof linking_well_formedness Hwfp' Hwfc' Hlinkable' as Hwfprog'. *)
  (*   assert (Hlinkable'' := Hlinkable); rewrite Hifacec in Hlinkable''. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc' Hlinkable'' as Hwfprog''. *)

  (*   (* [DynShare] *)
  (*      Fails because of the program_store_from_partialized_memory and *)
  (*      program_alloc_from_partialized_memory *)
  (*    *) *)
  (*   (* *)
  (*   inversion Hstep; subst; *)
  (*     t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec. *)
  (* Qed. *)
  (*    *) *)
End ThreewayMultisem3.

(* Theorems on initial states for main simulation. *)
Section ThreewayMultisem4.
  Variables p c p' c' : program.

  (* In this section, we should instantiate n and n'', not parameterize over them. *)
  Variables n n'' : Component.id -> nat.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog''_is_closed : closed_program (program_link p' c').
    

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.


  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_trace_extensional (left_addr_good_for_shifting n) tt.
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_trace_extensional (left_addr_good_for_shifting n'') tt''.


  Lemma merged_program_is_closed: closed_program prog'.
  Proof.
    unfold mergeable_interfaces in *.
    destruct Hmergeable_ifaces.
    eapply interface_preserves_closedness_r; eauto.
    - by eapply linkable_implies_linkable_mains.
    - by eapply interface_implies_matching_mains.
  Qed.

  (* Lemma initial_states_mergeability s s'' : *)
  (*   initial_state sem   s   -> *)
  (*   initial_state sem'' s'' -> *)
  (*   mergeable_states p c p' c' s s''. *)
  (* Proof. *)
  (*   simpl. unfold CS.initial_state. *)
  (*   intros Hini Hini''. *)
  (*   apply mergeable_states_intro with (s0 := s) (s0'' := s'') (t := E0); subst; *)
  (*     try assumption; *)
  (*     reflexivity || now apply star_refl. *)
  (* Qed. *)

  Lemma match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
  exists s',
    initial_state sem'  s'  /\
    mergeable_border_states p c p' c' n n'' s s' s'' E0 E0 E0.
  Proof.
    intros Hini Hini''. simpl in *.
    exists (CS.initial_machine_state prog'). split.
    - unfold initial_state, CS.initial_machine_state; reflexivity.
    - pose proof merged_program_is_closed as Hprog'_is_closed.
      assert (CS.initial_machine_state (program_link p c') =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitpc'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacec.
      }
      assert (CS.initial_machine_state (program_link p c) =
              (
                [],
                unionm (prepare_procedures_memory p) (prepare_procedures_memory c),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c,
                  Z.of_nat 0
                )
              )
             ) as Hinitpc.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          by destruct Hmergeable_ifaces as [? _].
      }
      
      assert (CS.initial_machine_state (program_link p' c') =
              (
                [],
                unionm (prepare_procedures_memory p') (prepare_procedures_memory c'),
                Register.init,
                (
                  Permission.code,
                  Component.main,
                  CS.prog_main_block p' + CS.prog_main_block c',
                  Z.of_nat 0
                )
              )
             ) as Hinitp'c'.
      {
        eapply CS.initial_machine_state_after_linking; eauto.
        - (* remaining goal: linkable *)
          destruct Hmergeable_ifaces as [? _].
          by rewrite <- Hifacep; rewrite <- Hifacec.
      }
      
      rewrite Hinitpc'.
      (* 
         Need to know whether to apply mergeable_border_states_p_executing
         or mergeable_border_states_c'_executing.

         But in any case, we will need mergeable_states_well_formed.
       *)
      assert (mergeable_states_well_formed
                p c p' c' n n'' s
                ([],
                 unionm (prepare_procedures_memory p) (prepare_procedures_memory c'),
                 Register.init,
                 (Permission.code,
                  Component.main,
                  CS.prog_main_block p + CS.prog_main_block c',
                  Z.of_nat 0)
                )
                s'' E0 E0 E0
             ) as Hmergewf.
      {
        eapply mergeable_states_well_formed_intro;
          simpl; eauto; unfold CS.initial_state, CSInvariants.is_prefix in *; subst.
        + apply star_refl.
        + rewrite Hinitpc'. apply star_refl.
        + apply star_refl.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- simpl.
             (* good_memory prepare_procedures_memory *)
             (* Search _ prepare_initial_memory. *)
             (* Search _ alloc_static_buffers. *)
             admit.
          -- by inversion Hmergeable_ifaces.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- simpl.
             (* good_memory prepare_procedures_memory *)
             admit.
          -- rewrite <- Hifacep, <- Hifacec. by inversion Hmergeable_ifaces.
        + (* good_memory prepare_procedures_memory *)
          admit.
        + constructor.
        + constructor.
        + constructor.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- constructor.
          -- by inversion Hmergeable_ifaces.
        + rewrite CS.initial_machine_state_after_linking; eauto.
          -- constructor.
          -- rewrite <- Hifacep, <- Hifacec. by inversion Hmergeable_ifaces.
        + by rewrite Hinitpc.
        + by rewrite Hinitp'c'.
        + constructor. constructor.
        + constructor. constructor.
      } 
      destruct (Component.main \in domm (prog_interface p)) eqn:whereismain.
      + (* Component.main is in p. *)
        eapply mergeable_border_states_p_executing; simpl; eauto.
        * (* Goal: program counters equal *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          assert (CS.prog_main_block c = CS.prog_main_block c') as Hprogmainblk.
          {
            admit.
          }
          by rewrite Hprogmainblk.
        * (* Goal: is_program_component. *)
          admit.
        * (* Goal: registers related *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.
          eapply regs_rel_of_executing_part_intro.
          intros reg.
          unfold Register.get.
          destruct (Register.to_nat reg \in domm Register.init) eqn:regdomm.
          -- assert (Register.init (Register.to_nat reg) = Some Undef)
              as Hreginit_undef.
             {
               by apply Register.reg_in_domm_init_Undef.
             }
             by rewrite Hreginit_undef.
          -- assert (Register.init (Register.to_nat reg) = None) as Hreginit_none.
             {
               rewrite mem_domm in regdomm.
               by destruct (Register.init (Register.to_nat reg)) eqn:e.
             }
             by rewrite Hreginit_none.
        * (* Goal: mem_of_part_executing_rel_original_and_recombined *)
          unfold CS.initial_state in *. subst. rewrite Hinitpc. simpl.

          (* Observe that mem_of_part_executing_rel_original_and_recombined 
             only cares about addresses from the left part of the "unionm"'s.
             And observe that the left part is the same in both "uninonm"'s.
           *)
          admit.
          
          (*Search _ prepare_procedures_memory.*)

          (* This assertion is not needed. *)
          (*assert (prepare_procedures_memory c = prepare_procedures_memory c') as Hmemcc'.
          {
            (* Apparently, this assertion is false. *)
            (* The reason it is false is that the memory resulting from 
               prepare_procedures_memory is code memory, and the code of
               c is different from the code of c'.
             *)
            unfold prepare_procedures_memory.
            rewrite !prepare_procedures_initial_memory_equiv.
            unfold prepare_procedures.
            Search _ prog_procedures.
            
            Search _ prepare_procedures_initial_memory.
            Search _ prepare_initial_memory.
          }*)
          
         
        * (* Goal: mem_of_part_not_executing_rel_original_and_recombined_at_border*)
          unfold CS.initial_state in *. subst. rewrite Hinitp'c'. simpl.
          unfold mem_of_part_not_executing_rel_original_and_recombined_at_border.

          (* Observe that this is very similar to the previous subgoal.
             The only difference is that it's the right part of the "unionm"
             that we want to relate.
           *)
          
          admit.
      + (* Component.main is in c'. Should be analogous to the parallel goal. *)
          
  Admitted. (* RB: TODO: Establish trivial relations, should not be hard. *)

  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof initial_states_mergeability Hini Hini'' as Hmerge. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   simpl in *. unfold CS.initial_state in *. subst. *)
  (*   split; last assumption. *)
  (*   (* Expose structure of initial states. *) *)
  (*   rewrite !CS.initial_machine_state_after_linking; try congruence; *)
  (*     last (apply interface_preserves_closedness_r with (p2 := c); try assumption; *)
  (*           now apply interface_implies_matching_mains). *)
  (*   unfold merge_states, merge_memories, merge_registers, merge_pcs; simpl. *)
  (*   (* Memory simplifictions. *) *)
  (*   rewrite (prepare_procedures_memory_left Hlinkable). *)
  (*   unfold ip. erewrite Hifacep at 1. rewrite Hifacep Hifacec in Hlinkable. *)
  (*   rewrite (prepare_procedures_memory_right Hlinkable). *)
  (*   (* Case analysis on main and related simplifications. *) *)
  (*   destruct (Component.main \in domm ip) eqn:Hcase; *)
  (*     rewrite Hcase. *)
  (*   - pose proof domm_partition_notin_r _ _ Hmergeable_ifaces _ Hcase as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfc Hnotin). *)
  (*     rewrite Hifacec in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfc' Hnotin). *)
  (*   - (* Symmetric case. *) *)
  (*     assert (Hcase' : Component.main \in domm ic). *)
  (*     { pose proof domm_partition_program_link_in_neither Hwfp Hwfc Hprog_is_closed as H. *)
  (*       rewrite Hcase in H. *)
  (*       destruct (Component.main \in domm ic) eqn:Hcase''. *)
  (*       - reflexivity. *)
  (*       - rewrite Hcase'' in H. *)
  (*         exfalso; now apply H. *)
  (*     } *)
  (*     pose proof domm_partition_notin _ _ Hmergeable_ifaces _ Hcase' as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfp Hnotin). *)
  (*     rewrite Hifacep in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfp' Hnotin). *)
  (* Qed. *)
End ThreewayMultisem4.

(* Remaining theorems for main simulation.  *)
Section ThreewayMultisem5.
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

  (* RB: NOTE: Consider execution invariance and similar lemmas on the right as
     well, as symmetry arguments reoccur all the time.
     TODO: Observe the proof of match_nostep is almost identical, and refactor
     accordingly. *)
  Theorem match_final_states s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    final_state sem   s   ->
    final_state sem'' s'' ->
    (* final_state sem'  (merge_states ip ic s s''). *)
    final_state sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   destruct s as [[[[gps mem] regs] pc] addrs]. *)
  (*   destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal''. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c1 := c); try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     rewrite program_linkC; try congruence. *)
  (*     apply linkable_sym in Hlinkable. *)
  (*     apply linkable_mains_sym in Hmain_linkability. *)
  (*     apply linkable_mains_sym in Hmain_linkability'. *)
  (*     apply execution_invariant_to_linking with (c1 := p'); try congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now apply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)

  Theorem match_nofinal s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    (* ~ final_state sem'  (merge_states ip ic s s''). *)
    ~ final_state sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   destruct s as [[[[gps mem] regs] pc] addrs]. *)
  (*   destruct s'' as [[[[gps'' mem''] regs''] pc''] addrs'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal'' Hfinal'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _ ]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c2 := c) in Hfinal'; try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal'; try congruence. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     apply execution_invariant_to_linking with (c2 := p') in Hfinal'; try easy. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_sym; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now eapply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)

  Lemma match_nostep s s' s'' t t' t'' :
    mergeable_states p c p' c' n n'' s s' s'' t t' t'' ->
    Nostep sem   s   ->
    Nostep sem'' s'' ->
    (* Nostep sem'  (merge_states ip ic s s''). *)
    Nostep sem'  s'.
  Admitted. (* RB: TODO: Should still be provable. Do later as needed. Needs relation tweaks? *)
  (* Proof. *)
  (*   rename s into s1. rename s'' into s1''. *)
  (*   intros Hmerge Hstep Hstep'' t s2' Hstep'. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable' _]; rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
  (*   - pose proof threeway_multisem_step_inv_program Hcase Hmerge Hstep' *)
  (*       as [s2 Hcontra]. *)
  (*     specialize (Hstep t s2). contradiction. *)
  (*   - (* Symmetric case. *) *)
  (*     apply negb_false_iff in Hcase. *)
  (*     pose proof mergeable_states_context_to_program Hmerge Hcase as Hcase'. *)
  (*     pose proof proj1 (mergeable_states_sym _ _ _ _ _ _) Hmerge as Hmerge'. *)
  (*     pose proof @threeway_multisem_step_inv_program c' p' c p as H. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H s1'' s1 t s2' Hcase' Hmerge'). *)
  (*     rewrite program_linkC in H; try assumption; [| apply linkable_sym; congruence]. *)
  (*     rewrite Hifacec Hifacep in H. *)
  (*     erewrite merge_states_sym with (p := c') (c := p') (p' := c) (c' := p) in H; *)
  (*       try eassumption; try now symmetry. *)
  (*     rewrite -Hifacec -Hifacep in H. *)
  (*     specialize (H Hstep'). *)
  (*     destruct H as [s2'' Hcontra]. *)
  (*     specialize (Hstep'' t s2''). *)
  (*     unfold sem'', prog'' in Hstep''; rewrite program_linkC in Hstep''; try assumption. *)
  (*     contradiction. *)
  (* Qed. *)
End ThreewayMultisem5.

(* Main simulation theorem. *)
Section Recombination.
  Variables p c p' c' : program.
  Variables n n'' : Component.id -> nat.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Hypothesis Hprog_is_good:
    forall ss tt,
      CSInvariants.is_prefix ss prog tt ->
      good_memory (left_addr_good_for_shifting n) (CS.state_mem ss).
  Hypothesis Hprog''_is_good:
    forall ss'' tt'',
      CSInvariants.is_prefix ss'' prog'' tt'' ->
      good_memory (left_addr_good_for_shifting n'') (CS.state_mem ss'').


  (* RB: NOTE: Possible improvements:
      - Try to refactor case analysis in proof.
      - Try to derive well-formedness, etc., from semantics.
     This result is currently doing the legwork of going from a simulation on
     stars to one on program behaviors without direct mediation from the CompCert
     framework. *)
  (* Theorem recombination_prefix m : *)
  (*   does_prefix sem   m -> *)
  (*   does_prefix sem'' m -> *)
  (*   does_prefix sem'  m. *)
  (* Proof. *)
  (*   unfold does_prefix. *)
  (*   intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']]. *)
  (*   assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh''). *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]]. *)
  (*   apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']]. *)
  (*   destruct m as [tm | tm | tm]. *)
  (*   - destruct b   as [t   | ? | ? | ?]; try contradiction. *)
  (*     destruct b'' as [t'' | ? | ? | ?]; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst. *)
  (*     inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst. *)
  (*     exists (Terminates tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_terminates with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     now apply match_final_states with (p' := p'). *)
  (*   - destruct b   as [? | ? | ? | t  ]; try contradiction. *)
  (*     destruct b'' as [? | ? | ? | t'']; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst. *)
  (*     inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst. *)
  (*     exists (Goes_wrong tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_goes_wrong with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     + eapply match_nostep; eassumption. *)
  (*     + eapply match_nofinal; eassumption. *)
  (*   - (* Here we talk about the stars associated to the behaviors, without *)
  (*        worrying now about connecting them to the existing initial states. *) *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix) *)
  (*       as [s1_ [s2 [Hini1_ Hstar12]]]. *)
  (*     destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'') *)
  (*       as [s1''_ [s2'' [Hini1''_ Hstar12'']]]. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1_ Hini1''_ as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     eapply program_behaves_finpref_exists; *)
  (*       last now apply Hstar12'. *)
  (*     assumption. *)
  (* Qed. *)

  (* RB: NOTE: [DynShare] This definition may be used to expose a simpler
     relation, which would still fit the theorem statement, though one of the
     explicit connections would be lost. *)
  (* Definition prefix_rel m m' := *)
  (*   exists n n', behavior_rel_behavior_all_cids n n' m m'. *)
  Theorem recombination_prefix_rel m m'' :
    does_prefix sem   m ->
    does_prefix sem'' m'' ->
    behavior_rel_behavior n  n'' m  m'' ->
  exists m' n',
    does_prefix sem'  m' /\
    behavior_rel_behavior n' n   m' m.
  Proof.
    (* unfold does_prefix. *)
    intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']] Hrel.
    (* Invert prefix executions to expose their initial states (and full program
       behaviors. *)
    assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh'').
    apply CS.program_behaves_inv_non_inform in Hst_beh   as [s1   [Hini1   Hst_beh  ]].
    apply CS.program_behaves_inv_non_inform in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']].
    (* Suppose we can establish the relation between the initial states of the
       two runs and the initial state of the recombined program. *)
    pose (s1' := CS.initial_machine_state (program_link p c')).

    
    (* AEK: TODO: Get the "t"s from the behaviors. *)
    (*assert (Hmerge1 : mergeable_states p c p' c' n n'' s1 s1' s1'' (* t1 t1' t1''*))
      by admit.*)


    (* In the standard proof, because the two executions produce the same
       prefix, we know that the two runs either terminate, go wrong or are
       unfinished. The third case is probably the most interesting here. *)
    destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix)
      as [s1_ [s2 [Hini1_ Hstar12]]].
    destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'')
      as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
    pose proof match_initial_states (*n n''*) Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
         Hprog_is_closed Hprog_is_closed' Hprog_is_good Hprog''_is_good Hini1_ Hini1''_
      as [s1'_ [Hini1' Hmerge1_]].
    (* By determinacy of initial program states: *)
    assert (Heq1 : s1 = s1_) by admit.
    assert (Heq1' : s1' = s1'_) by admit.
    assert (Heq1'' : s1'' = s1''_) by admit.
    subst s1_ s1'_ s1''_.
    clear Hini1_ Hini1''_ Hmerge1_.


    (* Now we should be able to apply a modified star simulation. *)

    (* AEK: TODO: Uncomment after having defined Hmerge1. See the TODO above. *)
    (************
    pose proof star_simulation Hmerge1 Hstar12 Hstar12''
      as [t' [s2' [Hstar12' Hmerge2]]].
    {
      (* For this, however, we need to be able to establish the memory
         relation between the two, in principle starting from [Hmerge1] and
         [Hrel]. *)
      (* NOTE: The memory relation is designed to hold at the boundaries!
         vs. higher-level memory relation *)
      admit.
    }
`   *************)



    (* AEK: TODO: Uncomment after having defined t'. See the TODO above. *)
    (*************
    (* Actually, we need to ensure that the executed trace corresponds to a
       finite prefix behavior (and that the obtained relation extends to
       it.) *)
    assert (exists m', t' = finpref_trace m') as [m' Heq] by admit; subst.


    (* Now we can instantiate the quantifiers (assume the mapping [n'] can be
       obtained easily). *)
    exists m'. eexists. split.
    - (* In principle, the same lemma that was used for the third case of the
         original proof should work here. *)
      pose proof program_behaves_finpref_exists Hini1' Hstar12'
             as [beh' [Hbeh' Hprefix']].
      exists beh'. admit.
    - (* We would then be left to establish the trace relation. *)
      admit.
     *********)



  Admitted.

End Recombination.

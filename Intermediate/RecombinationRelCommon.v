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
  Lemma mergeable_states_notin_to_in s s' s'' t t' t'' :
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) \notin domm ip ->
    Pointer.component (CS.state_pc s) \in domm ic.
  Proof.
    intros Hmerg Hpc_notin.
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

  Lemma mergeable_states_in_to_notin s s' s'' t t' t'' :
    mergeable_internal_states s s' s'' t t' t'' ->
    Pointer.component (CS.state_pc s) \in domm ic ->
    Pointer.component (CS.state_pc s) \notin domm ip.
  Proof.
    intros Hmerg Hpc_notin.
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


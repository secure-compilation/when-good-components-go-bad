Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Renaming.
Require Import Common.Reachability.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(* State merging functions. *)
Section Merge.
  Variable ip ic : Program.interface.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces ip ic.

  (* Return addresses are the sole responsibility of each side. No
     cross-component interactions are possible. *)
  Definition merge_frames (f f''   : Pointer.t) : Pointer.t :=
    if Pointer.component f \in domm ip then f else f''.

  Fixpoint merge_stacks (s s'' : CS.stack) : CS.stack :=
    match s, s'' with
    | [], [] => []
    | f :: s, f'' :: s'' => merge_frames f f'' :: merge_stacks s s''
    | _, _ => [] (* Should not happen *)
    end.

  (* [DynShare] TODO: define properly 
     (by using ComponentMemory.load_block
     and/or by defining new functions in Common/Memory.v)
   *)
  (*
  Definition transfer_contents_component_memory
             (m m'' : ComponentMemory.t) (a : Component.id * Block.id)
    : ComponentMemory.t := m.
   *)

  (* RB: TODO: Here and above, Program.interface vs. fset. *)
  (* [DynShare]
     1- Expect pc (?) --- similar to merge_registers
     2- Expect set of shared addresses (i.e., shared between ic and ip)

     From this set of shared addresses, partition the memory (either m or m'') into
     three parts:
     (a) part that is shared (obvious)
     (b) part that remains private to ip
     (c) part that remains private to ic

     Result := m.(a) ++ m/m''.(b) ++ m''.(c) if Pointer.component pc \in domm ip
          else m''.(a) ++ m/m''.(b) ++ m.(c)

   *)
  Definition merge_memories (m m'' : Memory.tt) : Memory.tt :=
    unionm (to_partial_memory m   (domm ic))
           (to_partial_memory m'' (domm ip)).

  Definition merge_registers (r r'' : Register.t) (pc : Pointer.t) : Register.t :=
    if Pointer.component pc \in domm ip then r else r''.

  Definition merge_pcs (pc pc'' : Pointer.t) : Pointer.t :=
    if Pointer.component pc \in domm ip then pc else pc''.

  Definition merge_states (state state'' : CS.state) : CS.state :=
    let '(s, m, r, pc) := state in
    let '(s'', m'', r'', pc'') := state'' in
    (merge_stacks s s'', merge_memories m m'', merge_registers r r'' pc, merge_pcs pc pc'').

  Lemma merge_frames_program frame frame'' :
    Pointer.component frame \in domm ip ->
    merge_frames frame frame'' = frame.
  Proof.
    intros Hpc. unfold merge_frames. now rewrite Hpc.
  Qed.

  Lemma merge_stacks_cons_program frame gps frame'' gps'' :
    Pointer.component frame \in domm ip ->
    merge_stacks (frame :: gps) (frame'' :: gps'') = frame :: merge_stacks gps gps''.
  Proof.
    intros Hpc. simpl. now rewrite merge_frames_program.
  Qed.

  Lemma merge_frames_context frame frame'' :
    Pointer.component frame \in domm ic ->
    merge_frames frame frame'' = frame''.
  Proof.
    intros Hpc.
    eapply (domm_partition_notin _ _ Hmergeable_ifaces) in Hpc.
    unfold merge_frames.
    move: Hpc => /negP Hpc.
    now destruct (Pointer.component frame \in domm ip) eqn:Heq.
  Qed.

  Lemma merge_stacks_cons_context frame gps frame'' gps'' :
    Pointer.component frame \in domm ic ->
    merge_stacks (frame :: gps) (frame'' :: gps'') =
    frame'' :: merge_stacks gps gps''.
  Proof.
    intros Hpc. simpl. now rewrite merge_frames_context.
  Qed.

  Definition merge_states_stack s s'' :=
    merge_stacks (CS.state_stack s) (CS.state_stack s'').

  Definition merge_states_mem s s'' :=
    merge_memories (CS.state_mem s) (CS.state_mem s'').

  Definition merge_states_regs s s'' :=
    if Pointer.component (CS.state_pc s) \in domm ip then
      CS.state_regs s
    else
      CS.state_regs s''.

  Definition merge_states_pc s s'' :=
    if Pointer.component (CS.state_pc s) \in domm ip then
      CS.state_pc s
    else
      CS.state_pc s''.

  Lemma merge_states_unfold s s'' :
    merge_states s s'' =
    (merge_states_stack s s'', merge_states_mem s s'', merge_states_regs s s'', merge_states_pc s s'').
  Proof. now CS.unfold_states. Qed.
End Merge.

(* An inductive notion of pairs of states for which merging is well-defined. *)
(* RB: TODO: Harmonize naming conventions. *)
Section Mergeable.
  Variables p c p' c' : program.

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

  Variable sigma : addr_t -> addr_t.
  Variable sigma_inv : addr_t -> addr_t.

  Definition trace_addrs_rel t m m' :=
    forall addrs,
      addr_shared_so_far addrs t ->
      memory_renames_memory_at_addr sigma addrs m m'.

  Definition trace_addrs_rel_inv t m m' :=
    forall addrs,
      addr_shared_so_far addrs t ->
      memory_inverse_renames_memory_at_addr sigma_inv addrs m m'.

  (* An inductive definition to relate a program with the pointers found in its
     buffers and procedures. A computational definition can be given as well.
     NOTE: Unnecessary? *)
  Inductive prog_addrs (p : program) (addrs : addr_t) : Prop :=
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

  Definition prog_addrs_rel p m m' :=
    forall addrs,
      prog_addrs p addrs ->
      (* XXX -> *) (* TODO: Find renaming relation, add parameters to state relation. *)
      memory_renames_memory_at_addr sigma addrs m m'.

  Definition prog_addrs_rel_inv p m m' :=
    forall addrs,
      prog_addrs p addrs ->
      (* ... *)
      memory_inverse_renames_memory_at_addr sigma_inv addrs m m'.

  Definition memtrace : Type := eqtype.Equality.sort Memory.t * trace event.

  Inductive mem_rel2 (mt mt' : memtrace) : Prop :=
  | mem_rel2_intro : forall m t m' t',
      mt  = (m , t ) ->
      mt' = (m', t') ->
      trace_addrs_rel     t  m m' ->
      trace_addrs_rel_inv t' m m' ->
      prog_addrs_rel      p  m m' ->
      prog_addrs_rel_inv  p  m m' ->
      mem_rel2 mt mt'.

  Inductive mem_rel3 (mt mt' mt'' : memtrace) : Prop :=
  | mem_rel3_intro :
      (* Pairwise relations between the original runs and the combined run. *)
      mem_rel2 mt   mt' ->
      mem_rel2 mt'' mt' ->

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
      mem_rel3 mt mt' mt''.

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

  Inductive mergeable_states (s s' s'' : CS.state) : Prop :=
    mergeable_states_intro : forall s0 s0' s0'' t t' t'' n n' n'',
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
      initial_state sem   s0   ->
      initial_state sem'  s0'  ->
      initial_state sem'' s0'' ->
      Star sem   s0   t   s   ->
      Star sem'  s0'  t'  s'  ->
      Star sem'' s0'' t'' s'' ->
      (* Sharing conditions.
         NOTE: Think about possible redundancies. *)
      mem_rel3 (CS.state_mem s, t) (CS.state_mem s', t') (CS.state_mem s'', t'') ->
      behavior_rel_behavior_all_cids n n'  (FTbc t) (FTbc t' ) ->
      behavior_rel_behavior_all_cids n n'' (FTbc t) (FTbc t'') ->
      mergeable_states s s' s''.

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
  (* The following lemmas establish the connection between the mergeability
     relation and the application of the state merging functions. *)
  Lemma merge_mergeable_states_regs_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states_regs ip s s'' = CS.state_regs s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[[stack mem] reg] pc] addrs]; destruct s'' as [[[[stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states_regs. simpl.
    CS.simplify_turn.
    inversion Hmerg as [s0 s0'' t t'' _ _
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
  Lemma mergeable_states_pc_same_component s s' s'' :
    mergeable_states s s' s'' ->
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

  Lemma mergeable_states_program_to_program s s' s'' :
    mergeable_states s s' s'' ->
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

  Lemma mergeable_states_context_to_program s s' s'' :
    mergeable_states s s' s'' ->
    CS.is_context_component s ic ->
    CS.is_program_component s'' ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack1 mem1] reg1] pc1];
      destruct s'' as [[[stack2 mem2] reg2] pc2].
    pose proof mergeable_states_pc_same_component Hmerg as Hpc; simpl in Hpc.
    rewrite <- Hpc; clear Hpc.
    inversion Hmerg
      as [? ? _ _ _ _ _ _ _ _ _ _ _ [[_ Hdisj] _] _ _ _ _ _ _ _ _ _ _ _ _ _].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    now auto.
  Qed.

  Lemma mergeable_states_program_to_context s s' s'' :
    mergeable_states s s' s'' ->
    CS.is_program_component s ic ->
    CS.is_context_component s'' ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack mem] reg] pc];
      destruct s'' as [[[stack'' mem''] reg''] pc''].
    pose proof mergeable_states_pc_same_component Hmerg as Hpc; simpl in Hpc.
    rewrite <- Hpc.
    inversion Hmerg as [s0 _ _ t _ _ _ _ _
                        Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _
                        Hini _ _ Hstar _ _ _ _ _].
    pose proof (CS.star_pc_domm_non_inform
                  _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar).
    intros Hn; destruct H.
    assumption.
    rewrite H in Hn. inversion Hn.
  Qed.

  (* RB: NOTE: Try to phrase everything either as CS.is_XXX_component, or as
     \[not]in. This is the equivalent of the old [PS.domm_partition]. *)
  Lemma mergeable_states_notin_to_in s s' s'' :
    mergeable_states s s' s'' ->
    Pointer.component (CS.state_pc s) \notin domm ip ->
    Pointer.component (CS.state_pc s) \in domm ic.
  Proof.
    intros Hmerg Hpc_notin.
    inversion Hmerg as [[[[? ?] ?] ?] _ ? ? _ ? _ _ _
                        Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _
                        Hini _ _ Hstar _ _ _ _ _].
    CS.unfold_states.
    pose proof (CS.star_pc_domm_non_inform
                  _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as Hpc.
    destruct Hpc as [Hprg | Hctx].
    - now rewrite Hprg in Hpc_notin.
    - now assumption.
  Qed.

  (* RB: NOTE: Consider if the core of the lemma could be moved to CS, as is the
     case of its simpler variant, is_program_component_pc_notin_domm. *)
  Lemma is_program_component_pc_in_domm s s' s'' :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' ->
    Pointer.component (CS.state_pc s) \in domm ip.
  Proof.
    intros Hpc Hmerge.
    assert (Hcc := Hmerge);
      apply mergeable_states_program_to_context in Hcc; try assumption.
    unfold CS.is_context_component, turn_of, CS.state_turn in Hcc.
    rewrite (mergeable_states_pc_same_component Hmerge).
    now destruct s'' as [[[? ?] ?] ?].
  Qed.

  Lemma mergeable_states_program_component_domm mem gps regs pc s' s'' :
    mergeable_states (mem, gps, regs, pc) s' s'' ->
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

  Lemma mergeable_states_mergeable_stack
        gps1   mem1   regs1   pc1
        st1'
        gps1'' mem1'' regs1'' pc1'' :
    mergeable_states (gps1  , mem1  , regs1  , pc1  )
                     st1'
                     (gps1'', mem1'', regs1'', pc1'') ->
    mergeable_stack gps1 gps1''.
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
  Admitted. (* RB: TODO: Should not be provable. Repair induction principle? *)

  Lemma mergeable_states_cons_domm
        frame1   gps1   mem1   regs1   pc1
        st1'
        frame1'' gps1'' mem1'' regs1'' pc1'' :
    mergeable_states (frame1   :: gps1  , mem1  , regs1  , pc1  ) st1'
                     (frame1'' :: gps1'', mem1'', regs1'', pc1'') ->
    Pointer.component frame1 = Pointer.component frame1''.
  Proof.
    intros Hmerge.
    pose proof mergeable_states_mergeable_stack Hmerge as H.
    now inversion H.
  Qed.

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

  (* Search _ find_label_in_component. *)
  Lemma find_label_in_component_recombination s s' s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' ->
    find_label_in_component (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_component (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    inversion Hmerge as [_ _ _ _ _ _ _ _ _ Hwfp Hwfc _ Hwfc' Hmergeable_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _].
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmains.
    pose proof find_label_in_component_1 _ _ _ _ Hlabel as Hpc_.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hdomm; simpl in Hdomm.
    rewrite (find_label_in_component_program_link_left _ _ _ _ Hmains) in Hlabel;
      try assumption.
    unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    unfold ip, ic in Hlinkable.
    rewrite (find_label_in_component_program_link_left Hdomm Hwfp);
      try congruence.
    apply linkable_implies_linkable_mains; congruence.
  Qed.

  (* Search _ find_label_in_procedure. *)
  Lemma find_label_in_procedure_recombination s s' s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' ->
    find_label_in_procedure (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_procedure (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    inversion Hmerge as [_ _ _ _ _ _ _ _ _ Hwfp Hwfc _ Hwfc' Hmergeable_ifaces _ Hifacec _ _ _ _ _ _ _ _ _ _ _].
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmains.
    pose proof find_label_in_procedure_1 _ _ _ _ Hlabel as Hpc_.
    pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hdomm; simpl in Hdomm.
    rewrite (find_label_in_procedure_program_link_left _ _ _ _ Hmains) in Hlabel;
      try assumption.
    unfold find_label_in_procedure in *.
    destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc_))
      as [C_procs |] eqn:Hcase; last discriminate.
    unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc' Hlinkable as Hmains'.
    rewrite (genv_procedures_program_link_left_notin _ _ _ _ Hmains');
      try assumption.
    now rewrite Hcase.
  Qed.

  (* Search _ PS.is_program_component Pointer.component. *)
  Lemma is_program_component_in_domm s s' s'' :
    CS.is_program_component s ic ->
    mergeable_states s s' s'' ->
    CS.state_component s \in domm (prog_interface p).
  Proof.
    intros Hcomp Hmerge.
    unfold CS.is_program_component, CS.is_context_component, CS.state_turn, turn_of in Hcomp.
    destruct s as [[[gps1 mem1] regs1] pc1].
    inversion Hmerge as [s0 _ _ t _ _ _ _ _ Hwfp Hwfc _ _ Hmergeable_ifaces _ _ Hprog_is_closed _ Hini _ _ Hstar _ _ _ _ _].
    destruct (CS.star_pc_domm_non_inform _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hip | Hic].
    - assumption.
    - now rewrite Hic in Hcomp.
  Qed.
End Mergeable.

Section MergeSym.
  Variables p c p' c' : program.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'' := CS.sem_non_inform prog''.

(*
  Lemma merge_stacks_sym gps gps'' :
    mergeable_interfaces ip ic ->
    mergeable_stack p c gps gps'' ->
    merge_stacks ip gps gps'' = merge_stacks ic gps'' gps.
  Proof.
    intros Hmergeable_ifaces Hmerge.
    induction Hmerge as [|frame frame'' gps gps'' Hframe Hdomm Hmerge IH].
    - now simpl.
    - simpl.
      unfold merge_frames.
      rewrite Hframe IH; rewrite Hframe in Hdomm.
      destruct Hdomm as [Hdomm | Hdomm].
      rewrite Hdomm; apply domm_partition_notin with (ctx1 := ip) in Hdomm.
      now rewrite notin_to_in_false.
      assumption.
      rewrite Hdomm; apply domm_partition_notin_r with (ctx2 := ic) in Hdomm.
      now rewrite notin_to_in_false.
      assumption.
  Qed.

  (* The necessary disjointness of the partializations is obtained from the fact
     that the memories belong to a pair of mergeable states (i.e., their domains
     coincide). *)
  Lemma merge_memories_sym mem mem'' :
    mergeable_interfaces ip ic ->
    domm mem   = domm (unionm ip ic) ->
    domm mem'' = domm (unionm ip ic) ->
    merge_memories ip ic mem mem'' = merge_memories ic ip mem'' mem.
  Proof.
    (* Reduces to a problem on disjointness. *)
    intros Hmergeable_ifaces Hmem Hmem''.
    unfold merge_memories.
    rewrite unionmC;
      first reflexivity.
    apply /fdisjointP => Cid Hin.
    unfold to_partial_memory in *.
    (* Expose some basic facts and their symmetries. *)
    inversion Hmergeable_ifaces as [[_ Hdisjoint] _].
    assert (HdisjointC := Hdisjoint); rewrite fdisjointC in HdisjointC.
    assert (HmemC := Hmem); assert (HmemC'' := Hmem'');
      rewrite unionmC in HmemC, HmemC''; try assumption.
    (* Specialized simplifications from a more general result. *)
    erewrite domm_filterm_partial_memory with (i2 := ic) (m0 := mem'') (m2 := mem'');
      erewrite domm_filterm_partial_memory with (i2 := ip) (m0 := mem) (m2 := mem) in Hin;
      try reflexivity || assumption.
    eapply domm_partition_notin_r; eassumption.
  Qed.

  Lemma merge_registers_sym reg reg'' pc pc'' :
    mergeable_interfaces ip ic ->
    Pointer.component pc \in (domm (prog_interface prog)) ->
    Pointer.component pc = Pointer.component pc'' ->
    merge_registers ip reg reg'' pc = merge_registers ic reg'' reg pc''.
  Proof.
    intros Hmergeable_ifaces Hdomm Heq.
    unfold merge_registers.
    rewrite -Heq.
    simpl in Hdomm.
    rewrite domm_union in Hdomm.
    move: Hdomm => /fsetUP [Hip | Hic].
    - rewrite Hip; apply domm_partition_notin_r with (ctx2 := ic) in Hip.
      now rewrite notin_to_in_false.
      assumption.
    - rewrite Hic; apply domm_partition_notin with (ctx1 := ip) in Hic.
      now rewrite notin_to_in_false.
      assumption.
  Qed.

  Lemma merge_pc_sym pc pc'' :
    mergeable_interfaces ip ic ->
    Pointer.component pc \in (domm (prog_interface prog)) ->
    Pointer.component pc = Pointer.component pc'' ->
    merge_pcs ip pc pc'' = merge_pcs ic pc'' pc.
  Proof.
    intros Hmergeable_ifaces Hdomm Heq.
    unfold merge_pcs.
    rewrite -Heq.
    simpl in Hdomm.
    rewrite domm_union in Hdomm.
    move: Hdomm => /fsetUP [Hip | Hic].
    - rewrite Hip; apply domm_partition_notin_r with (ctx2 := ic) in Hip.
      now rewrite notin_to_in_false.
      assumption.
    - rewrite Hic; apply domm_partition_notin with (ctx1 := ip) in Hic.
      now rewrite notin_to_in_false.
      assumption.
  Qed.

  Lemma merge_addrs_sym addrs addrs'' :
    mergeable_interfaces ip ic ->
    merge_addrs addrs addrs'' = merge_addrs addrs'' addrs.
  Admitted.

  (* JT: TODO: Clean this proof (RB: agreed). *)
  Theorem merge_states_sym s s'' :
    mergeable_states p c p' c' s s'' ->
    merge_states ip ic s s'' = merge_states ic ip s'' s.
  Proof.
    intros Hmerg.
    inversion Hmerg
      as [s0 s0'' t t'' n n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
          Hprog_is_closed Hprog_is_closed' Hini Hini'' Hstar Hstar'' Hrel].
    (* RB: NOTE: As elsewhere, clean CS.comes_from_initial state. This is done up
       front for syntactic economy. Simplify if possible. *)
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
      unfold ip, ic. rewrite Hifacep Hifacec.
      apply CS.comes_from_initial_state_mem_domm.
      inversion Hprog_is_closed' as [_ [main [Hmain _]]].
      assert (Hmergeable_ifacesC := Hmergeable_ifaces);
        rewrite Hifacep Hifacec in Hmergeable_ifacesC.
      pose proof linking_well_formedness Hwfp' Hwfc' (proj1 Hmergeable_ifacesC) as Hwf''.
      pose proof CS.star_sem_non_inform_star_sem_inform prog'' s0'' t'' _ Hstar'' as
          [t_inform'' [Hstar_inform'' _]].
      now exists prog'', s0'', t_inform''.
    }
    destruct s as [[[[stack mem] reg] pc] addrs]; destruct s'' as [[[[stack'' mem''] reg''] pc''] addrs''].
    unfold merge_states.
    rewrite (merge_stacks_sym Hmergeable_ifaces).
    rewrite (merge_memories_sym Hmergeable_ifaces Hmem Hmem'').
    erewrite (merge_registers_sym _ _ Hmergeable_ifaces).
    rewrite (merge_pc_sym Hmergeable_ifaces).
    rewrite (merge_addrs_sym _ _ Hmergeable_ifaces).
    reflexivity.
    simpl.
    pose proof CS.star_pc_domm_non_inform
         _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar as Hdomm.
    rewrite domm_union. now apply /fsetUP.
    replace pc with (CS.state_pc (stack, mem, reg, pc, addrs)); try reflexivity.
    replace pc'' with (CS.state_pc (stack'', mem'', reg'', pc'', addrs'')); try reflexivity.
    eapply mergeable_states_pc_same_component; eassumption.
    simpl.
    pose proof CS.star_pc_domm_non_inform
         _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar as Hdomm.
    rewrite domm_union. now apply /fsetUP.
    replace pc with (CS.state_pc (stack, mem, reg, pc, addrs)); try reflexivity.
    replace pc'' with (CS.state_pc (stack'', mem'', reg'', pc'', addrs'')); try reflexivity.
    eapply mergeable_states_pc_same_component; eassumption.
    eapply mergeable_states_mergeable_stack with (p' := p') (c' := c'); eassumption.
  Qed.
*)

  (* RB: NOTE: Now the two sub-goals look even more similar than before. *)
  (* Lemma mergeable_states_sym s1 s1'' : *)
  (*   mergeable_states p c p' c' s1 s1'' <-> mergeable_states c' p' c p s1'' s1. *)
  (* Proof. *)
  (*   split. *)
  (*   - intros Hmerg. *)
  (*     inversion Hmerg *)
  (*       as [s0 s0'' t t'' n n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*           Hprog_is_closed Hprog_is_closed' Hini Hini'' Hstar Hstar'' Hrel]. *)
  (*     inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof (program_linkC Hwfc Hwfp (linkable_sym Hlinkable)) as Hcp. *)
  (*     rewrite Hifacec Hifacep in Hlinkable. *)
  (*     pose proof (program_linkC Hwfc' Hwfp' (linkable_sym Hlinkable)) as Hc'p'. *)
  (*     apply mergeable_states_intro with s0'' s0 t'' t n'' n; *)
  (*       try congruence; *)
  (*       [ apply mergeable_interfaces_sym; congruence *)
  (*       | now rewrite Hc'p' *)
  (*       | now rewrite Hcp *)
  (*       | admit (* RB: TODO: Symmetry of trace relation. *) *)
  (*       ]. *)
  (*   - intros Hmerg. *)
  (*     inversion Hmerg *)
  (*       as [s0 s0'' t t'' n n'' Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*              Hprog_is_closed Hprog_is_closed' Hini Hini'' Hstar Hstar'' Hrel]. *)
  (*     inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof (program_linkC Hwfc Hwfp (linkable_sym Hlinkable)) as Hcp. *)
  (*     rewrite Hifacec Hifacep in Hlinkable. *)
  (*     pose proof (program_linkC Hwfc' Hwfp' (linkable_sym Hlinkable)) as Hc'p'. *)
  (*     apply mergeable_states_intro with s0'' s0 t'' t n'' n; *)
  (*       try congruence. *)
  (*     + apply mergeable_interfaces_sym; congruence. *)
  (*     + rewrite program_linkC; try congruence. *)
  (*       now apply linkable_sym. *)
  (*     + rewrite program_linkC; try congruence. *)
  (*       apply linkable_sym; congruence. *)
  (*     + admit. (* RB: TODO: Symmetry of trace relation. *)
  (*                           Also write both splits similarly. *) *)
  (* (* Qed. *) *)
  (* Admitted. *)
End MergeSym.

(* Helpers, epsilon and lockstep versions of three-way simulation. *)
Section ThreewayMultisem1.
  Variables p c p' c' : program.

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

  Variables α γ : addr_t -> addr_t.

  (* RB: NOTE: Likely provable: since we are on the program, we would not care
     what changes the "other program" makes to its memory, only what "our
     program" eventually will. *)
  Lemma merge_states_silent_star s1 s1' s1'' s2'' :
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
    mergeable_states p c p' c' α γ s1 s1' s2''.
  Proof.
    intros Hmerge1 Hcomp Hstar12''.
    remember E0 as t.
    apply star_iff_starR in Hstar12''.
    induction Hstar12''
      as [s'' | s1'' t1 s2'' t2 s3'' ? Hstar12'' IHstar'' Hstep23'' Ht12]; subst.
    - assumption.
    - (* Simplify, apply IH and case analyze. *)
      symmetry in Ht12; apply Eapp_E0_inv in Ht12 as [? ?]; subst.
      specialize (IHstar'' Hmerge1 eq_refl).
      (* rewrite IHstar''. *)
      apply star_iff_starR in Hstar12''.
      destruct s1 as [[[gps mem] regs] pc].
      destruct s2'' as [[[gps2'' mem2''] regs2''] pc2''].
      destruct s3'' as [[[gps3'' mem3''] regs3''] pc3''].
      pose proof CS.step_non_inform_step_inform prog''
           (gps2'', mem2'', regs2'', pc2'') _ _ Hstep23'' as
          [t_inform [Hstep_inform _]].
      inversion Hstep_inform; subst.
      (* For each sub-goal, we need to recompose the mergeability relation. *)
      + inversion IHstar''; subst.
        econstructor; try eassumption.
        eapply star_right; try eassumption.
        now rewrite E0_right.
      (* The same proof works for all cases, except those that change the
         memory. *)
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + (* Store *)
        inversion IHstar''; subst.
        econstructor; try eassumption.
        eapply star_right; try eassumption.
        now rewrite E0_right.
        (* Not like this! This should hold trivially by our informal definition
           of the memory relation conditions. *)
        inversion H17; subst.
        constructor; try assumption.
        inversion H21; subst.
        econstructor; try eassumption.
        simpl. simpl in H22. rewrite <- H22.
        admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + (* Alloc *)
        inversion IHstar''; subst.
        econstructor; try eassumption.
        eapply star_right; try eassumption.
        now rewrite E0_right.
        (* Same as above, this should hold trivially. *)
        admit.
      + admit.
      + admit.
  Admitted. (* RB: TODO: Should not be too hard, may require tinkering with memrel. *)

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
  Lemma context_epsilon_star_merge_states s1 s1' s1'' s2'' :
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    CS.is_program_component s1 ic ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem' s1' E0 s2'.
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
  Lemma threeway_multisem_mergeable_step_E0 s1 s2 s1' s1'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Step sem s1 E0 s2 ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_states p c p' c' α γ s2 s2' s1''.
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
  Lemma threeway_multisem_mergeable_program s1 s1' s1'' t2 t2'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   t2   s2   ->
    Star sem'' s1'' t2'' s2'' ->
    (* behavior_rel_behavior_all_cids n n'' (FTbc t2) (FTbc t2'') -> *)
    mem_rel2 p α γ (CS.state_mem s1, t2) (CS.state_mem s1'', t2'') ->
  exists s2',
    mergeable_states p c p' c' α γ s2 s2' s2''.
  Admitted. (* RB: TODO: Wait to see how this will be useful. *)
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
  Theorem threeway_multisem_step_E0 s1 s1' s1'' s2 :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Step sem  s1  E0 s2  ->
  exists s2',
    Step sem' s1' E0 s2' /\
    mergeable_states p c p' c' α γ s2 s2' s1''.
  Admitted. (* RB: TODO: With the new conjunct, probably strong enough. *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12. *)
  (*   (* NOTE: Keep the context light for now, rewrite lemmas are no longer *)
  (*      directly applicable, as [s2'] is not computed explicitly. *) *)
  (*   (* inversion Hmerge1 as [????????????? Hmergeable_ifaces ????????????]. *) *)
  (*   (* Derive some useful facts and begin to expose state structure. *) *)
  (*   (* inversion Hmergeable_ifaces as [Hlinkable _]. *) *)
  (*   (* rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *) *)
  (*   pose proof CS.silent_step_non_inform_preserves_program_component *)
  (*        _ _ _ _ Hcomp1 Hstep12 as Hcomp2. *)
  (*   pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12 *)
  (*     as Hmerge2. *)
  (*   (* rewrite (mergeable_states_merge_program Hcomp2 Hmerge2). *) *)
  (*   (* NOTE: As usual, we should proceed by cases on the step. *) *)
  (*   inversion Hstep12; subst; rename Hstep12 into _Hstep12. *)

  (*   - (* INop *) *)
  (*     (* NOTE: Underneath the non-informative step there is an informative step *)
  (*        that we need to synchronize with the outer step. At present this is a *)
  (*        little tedious. *) *)
  (*     inversion H0; subst; rename H0 into _H0. *)
  (*     + simpl. destruct s1' as [[[[gps1' mem1'] regs1'] pc1'] addrs1']. *)
  (*       (* NOTE: We execute the corresponding instructions in the goal. *) *)
  (*       eexists. eapply CS.Nop_non_inform. *)
  (*       * (* NOTE: Now we need to prove that the instructions are indeed *)
  (*            synchronized. We should be able to learn this from *)
  (*            [mergeable_states], and in particular from the trace relation *)
  (*            contained therein. *) *)
  (*         inversion Hmerge1. *)
  (*         admit. *)
  (*       * eapply CS.Nop. *)
  (*         (* NOTE: This should also be learnable from [mergeable_states]. *) *)
  (*         admit. *)
  (*     + (* All other subgoals are nonsensical by determinism of the [executing] *)
  (*          instruction. *) *)
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
  (*     + admit. *)

  (*   - (* ILabel *) *)
  (*     (* NOTE: Simple instructions proceed similarly. *) *)
  (*     inversion H0; subst; rename H0 into _H0. *)
  (*     + admit. *)
  (*     + simpl. destruct s1' as [[[[gps1' mem1'] regs1'] pc1'] addrs1']. *)
  (*       eexists. eapply CS.Label_non_inform. *)
  (*       * admit. *)
  (*       * eapply CS.Label. *)
  (*         admit. *)
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
  (*     + admit. *)

  (*   - admit. *)
  (*   - admit. *)
  (*   - admit. *)

  (*   - (* ILoad *) *)
  (*     (* NOTE: The case of the load instruction will be more interesting. The *)
  (*        basic structure remains the same... *) *)
  (*     inversion H0; subst; rename H0 into _H0. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + simpl. destruct s1' as [[[[gps1' mem1'] regs1'] pc1'] addrs1']. *)
  (*       eexists. eapply CS.Load_non_inform. *)
  (*       * admit. *)
  (*       * eapply CS.Load. *)
  (*         -- admit. *)
  (*         (* NOTE: ... but now we have additional goals. Again, to relate the *)
  (*            two executions, we will need to resort to [mergeable_states]. *)
  (*            Among its constituents, only the trace relation is potentially *)
  (*            informative enough to contain the necessary information. *) *)
  (*         -- admit. *)
  (*         -- admit. *)
  (*         -- admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + admit. *)

    (* NOTE: ... And the cases go on. *)

    (* destruct s1 as [[[[gps1 mem1] regs1] pc1] addrs1]. *)
    (* destruct s2 as [[[[gps2 mem2] regs2] pc2] addrs2]. *)
    (* destruct s1'' as [[[[gps1'' mem1''] regs1''] pc1''] addrs1'']. *)
    (* (* Case analysis on step. *) *)
    (* pose proof CS.step_non_inform_step_inform *)
    (*      _ (gps1, mem1, regs1, pc1, addrs1) _ _ Hstep12 as [t_inform [Hstep12_inform Hrelt's]]. *)
    (* simpl. *)
    (*[DynShare]

      t_threeway_multisem_step_E0 uses CS.step_of_executing.
      Need to figure out how to use CS.step_of_executing_non_inform or similar.

     *)
    (* assert (CS.step (prepare_global_env prog') *)
    (*                 ( *)
    (*                   merge_states_stack (prog_interface p) (gps1, mem1, regs1, pc1, addrs1) *)
    (*                                      (gps1'', mem1'', regs1'', pc1'', addrs1''), *)
    (*                   merge_states_mem (prog_interface p) (prog_interface c) *)
    (*                                    (gps1, mem1, regs1, pc1, addrs1) *)
    (*                                    (gps1'', mem1'', regs1'', pc1'', addrs1''), *)
    (*                   regs1, pc1, addrs1 *)
    (*                 ) *)
    (*                 t_inform *)
    (*                 ( *)
    (*                   merge_states_stack (prog_interface p) *)
    (*                                      (gps2, mem2, regs2, pc2, addrs2) *)
    (*                                      (gps1'', mem1'', regs1'', pc1'', addrs1''), *)
    (*                   merge_states_mem (prog_interface p) (prog_interface c) *)
    (*                                    (gps2, mem2, regs2, pc2, addrs2) *)
    (*                                    (gps1'', mem1'', regs1'', pc1'', addrs1''), *)
    (*                   regs2, pc2, addrs2 *)
    (*                 ) *)
    (*        ) *)
    (*   as Hstep_inform. *)
    (* { *)
    (*   inversion Hstep12_inform; subst. *)
    (*   - eapply CS.Nop. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.Label. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.Const; try reflexivity. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.Mov; try reflexivity. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.BinOp; try reflexivity. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.Load; try reflexivity; try eassumption. *)
    (*     + solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*     + admit. *)
    (*       (* [DynShare] *)
    (*          Need to apply program_load_to_partialized_memory. *)
    (*          Currently, its preconditions are too strong. *)
    (*        *) *)
    (*   - eapply CS.Store; try reflexivity; try eassumption. *)
    (*     + solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*     + admit. *)
    (*       (* [DynShare] *)
    (*          Need to apply program_store_to_partialized_memory. *)
    (*          Currently, its preconditions are too strong. *)
    (*        *) *)
    (*   - eapply CS.Jal; try reflexivity; try eassumption. *)
    (*     + solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*     + assert ( *)
    (*           find_label_in_component (globalenv *)
    (*                                      (CS.sem_non_inform (program_link p c')) *)
    (*                                   ) *)
    (*                                   (CS.state_pc (gps2, mem2, regs1, pc1, addrs2)) *)
    (*                                   l *)
    (*           = Some pc2 *)
    (*         ) as gl. *)
    (*       { *)
    (*         eapply find_label_in_component_recombination; eauto. *)
    (*       } *)
    (*       exact gl. *)
    (*   - eapply CS.Jump; try reflexivity; try eassumption. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.BnzNZ; try reflexivity; try eassumption. *)
    (*     + solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*     + assert ( *)
    (*           find_label_in_procedure (globalenv *)
    (*                                      (CS.sem_non_inform (program_link p c')) *)
    (*                                   ) *)
    (*                                   (CS.state_pc (gps2, mem2, regs2, pc1, addrs2)) *)
    (*                                   l *)
    (*           = Some pc2 *)
    (*         ) as gl. *)
    (*       { *)
    (*         eapply find_label_in_procedure_recombination; eauto. *)
    (*       } *)
    (*       exact gl. *)
    (*   - eapply CS.BnzZ; try reflexivity; try eassumption. *)
    (*     solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*   - eapply CS.Alloc; try reflexivity; try eassumption. *)
    (*     + solve_executing_threeway_multisem_step_E0 Hlinkable pc1. *)
    (*     + admit. *)
    (*       (* Will we able to use program_alloc_from_partialized_memory? *) *)
    (*       (*pose proof (@program_alloc_from_partialized_memory *)
    (*                     p c (gps2, mem1, regs1, pc1, addrs2) *)
    (*                     (gps2, mem2, Register.set rptr (Ptr ptr) regs1, Pointer.inc pc1, addrs2) *)
    (*                     (Z.to_nat size) mem2 ptr Hmergeable_ifaces) as Halloc. *)
    (*       simpl in Halloc. *)
    (*        *) *)
    (*   - discriminate. *)
    (*   - discriminate. *)
    (* } *)
    (* pose proof (CS.step_inform_step_non_inform _ _ _ _ Hstep_inform) as gl. *)
    (* rewrite Hrelt's in gl. *)
    (* exact gl. *)
  (* Admitted. *)

  (* Compose two stars into a merged star. The "program" side drives both stars
     and performs all steps without interruption, the "context" side remains
     unaltered in both stars. *)
  (* NOTE: By itself, the reformulation of this lemma does not say anything
     interesting, because the existential can be discharged trivially by
     reflexivity, but that is not what we want. In fact, even the proof is
     tellingly boring. *)
  Theorem threeway_multisem_star_E0_program s1 s1' s1'' s2 s2'':
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_states p c p' c' α γ s2 s2' s2''.
  (*   Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2''). *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstar12 Hstar12''. *)
  (*   inversion Hmerge1 as [?? t0 ???? Hmergeable_ifaces ? Hifacec ???? Hstar ?]. *)
  (*   pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'. *)
  (*   rewrite Hifacec in Hcomp1'. *)
  (*   remember E0 as t eqn:Ht. *)
  (*   revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''. *)
  (*   apply star_iff_starR in Hstar12. *)
  (*   induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst; *)
  (*     intros Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'. *)
  (*   - rewrite -Hifacec in Hcomp1'. *)
  (*     unfold ip, ic; erewrite merge_states_silent_star; try eassumption. *)
  (*     now apply star_refl. *)
  (*   - apply Eapp_E0_inv in Ht. destruct Ht; subst. *)
  (*     specialize (IHstar Hstar eq_refl Hmerge1 Hcomp1 Hcomp1' Hstar12'). *)
  (*     apply star_trans with (t1 := E0) (s2 := merge_states ip ic s2 s2'') (t2 := E0); *)
  (*       [assumption | | reflexivity]. *)
  (*     apply star_step with (t1 := E0) (s2 := merge_states ip ic s3 s2'') (t2 := E0). *)
  (*     + apply star_iff_starR in Hstar12. *)
  (*       pose proof threeway_multisem_mergeable_program Hcomp1 Hmerge1 Hstar12 Hstar12' *)
  (*         as Hmerge2. *)
  (*       pose proof CS.epsilon_star_non_inform_preserves_program_component *)
  (*            _ _ _ _ Hcomp1 Hstar12 *)
  (*         as Hcomp2. *)
  (*       exact (threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23). *)
  (*     + now constructor. *)
  (*     + reflexivity. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Likely doable now. *)

  (* RB: NOTE: Observe similarity with threeway_multisem_mergeable_program, use
     to replace this if possible. *)
  (* RB: TODO: [DynShare] Events will need to be related instead of identical,
     in addition to the usual existential trick we are using now. *)
  Lemma threeway_multisem_event_lockstep_program_mergeable s1 s1' s1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, [e]) (CS.state_mem s2'', [e'']) ->
  exists s2',
    mergeable_states p c p' c' α γ s2 s2' s2''.
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12 Hstep12''. inversion Hmerge1. *)
  (*   apply mergeable_states_intro with (s0 := s0) (s0'' := s0'') (t := t ** [e]); *)
  (*     try assumption. *)
  (*   - eapply star_right; try eassumption; reflexivity. *)
  (*   - eapply star_right; try eassumption; reflexivity. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Fix statement as needed, prove later. *)

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

  (* RB: TODO: Does it make sense to compact calls and returns into a unified
     solve tactic? *)
  Theorem threeway_multisem_event_lockstep_program_step s1 s1' s1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, [e]) (CS.state_mem s2'', [e'']) ->
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mem_rel2 p α γ (CS.state_mem s2, [e]) (CS.state_mem s2'', [e' ]).
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2''). *)
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12 Hstep12''. *)
  (*   (* Derive some useful facts and begin to expose state structure. *) *)
  (*   inversion Hmerge1 as [??? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec ??????]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)
  (*   pose proof threeway_multisem_event_lockstep_program_mergeable *)
  (*        Hcomp1 Hmerge1 Hstep12 Hstep12'' as Hmerge2. *)
  (*   set s1copy := s1. destruct s1 as [[[[gps1 mem1] regs1] pc1] addrs1]. *)
  (*   set s2copy := s2. destruct s2 as [[[[gps2 mem2] regs2] pc2] addrs2]. *)
  (*   destruct s1'' as [[[[gps1'' mem1''] regs1''] pc1''] addrs1'']. *)
  (*   destruct s2'' as [[[[gps2'' mem2''] regs2''] pc2''] addrs2'']. *)
  (*   (* Case analysis on step. *) *)
  (*   inversion Hstep12; subst; *)
  (*     inversion Hstep12''; subst. *)
  (*   (* [DynShare] Instead of 2 subgoals, we now have 4: [ICall, IReturn] x [ICall, IReturn] *)
       
  (*      That is a bit confusing. I do not understand why we used to have *)
  (*      only two subgoals. *)
  (*    *) *)
  (*   - admit. *)
      
  (*   - (* Here, ICall, IReturn. Derive a contradiction through [e] *) *)
  (*     admit. *)
      
  (*   - (* Here, IReturn, ICall. Derive a contradiction through [e] *) *)
  (*     admit. *)
      
  (*   - admit. *)
  Admitted. (* RB: TODO: Fix statement and prove later, combine with lemma above. *)

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
  Corollary threeway_multisem_event_lockstep_program s1 s1' s1'' e e'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, [e]) (CS.state_mem s2'', [e'']) ->
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\ mergeable_states p c p' c' α γ s2 s2' s2''.
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  (* Proof. *)
  (*   split. *)
  (*   - now apply threeway_multisem_event_lockstep_program_step. *)
  (*   - eapply threeway_multisem_event_lockstep_program_mergeable; eassumption. *)
  (* Qed. *)
  Admitted. (* RB: TODO: Fix statement, redundant w.r.t. the above lemmas. *)
End ThreewayMultisem1.

(* Helpers and symmetric version of three-way simulation. *)
Section ThreewayMultisem2.
  Variables p c p' c' : program.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Variables α γ : addr_t -> addr_t.

  (* RB: TODO: Rename, relocate. *)
  (* RB: NOTE: [DynShare] In this series of results, identical traces will need
     to be replaced by related traces. We can expect similar complications as in
     previous sections, especially in the need to produce explicit successor
     states that continue to satisfy the mergeability relation. *)
  Lemma threeway_multisem_mergeable s1 s1' s1'' t t'' s2 s2'' :
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 p α γ (CS.state_mem s1, t) (CS.state_mem s1'', t'') ->
  exists s2',
    mergeable_states p c p' c' α γ s2 s2' s2''.
  (* Qed. *)
  Admitted. (* RB: TODO: Add stepping of [s1']. Redundant? *)

  (* RB: TODO: Implicit parameters, compact if possible. *)
  (* RB: NOTE: Again, without mergeability, this lemma is trivial and
     uninteresting. *)
  Lemma threeway_multisem_star_E0 s1 s1' s1'' s2 s2'':
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    (* Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2''). *)
  exists s2',
    Star sem'  s1'  E0 s2' /\
    mergeable_states p c p' c' α γ s2 s2' s2''.
  Admitted. (* RB: TODO: Add mergeability. *)
  (* Proof. *)
  (*   intros H H0 H1. *)
  (*   inversion H as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hprg_component. *)
  (*   - now apply threeway_multisem_star_E0_program. *)
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

  (* A restricted version of the lockstep simulation on event-producing steps.
     RB: NOTE: Here is where we depart from the multi-semantics and need to
     furnish our own version. We may save effort if, as is the case here, we only
     need to concern ourselves with visible steps. *)
  (* RB: NOTE: Events need to be properly for full generality. Otherwise, this
     is just a symmetry lemma. *)
  Lemma threeway_multisem_event_lockstep s1 s1' s1'' e e'' s2 s2'' :
    mergeable_states p c p' c' α γ  s1 s1' s1'' ->
    Step sem   s1   [e  ] s2   ->
    Step sem'' s1'' [e''] s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, [e]) (CS.state_mem s2'', [e'']) ->
    (* Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\ *)
    (* mergeable_states p c p' c' s2 s2''. *)
  exists e' s2',
    Step sem'  s1'  [e' ] s2' /\
    mergeable_states p c p' c' α γ  s2 s2' s2''.
  Admitted. (* RB: TODO: Symmetry lemma. Fix according to program side. *)
  (* Proof. *)
  (*   intros Hmerge1 Hstep12 Hstep12''. *)
  (*   inversion Hmerge1 as [? ? ? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed _ Hini H1 Hstar H2]. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
  (*   - now apply threeway_multisem_event_lockstep_program. *)
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
  (* JT: TODO: clean this proof. *)

  Theorem threeway_multisem_star_program s1 s1' s1'' t t'' s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2'', t'') ->
    (* Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    (* mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2',  t' ). *)
    mergeable_states p c p' c' α γ s2 s2' s2''.
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' t'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' t'' s2'' Hcomp1 Hmerge1 Hstar12'' Hrel3.
    - assert (t'' = E0) by admit; subst t''. (* By the relation. *)
      exists E0, s1'. split.
      + now apply star_refl.
      + eapply merge_states_silent_star; eassumption.
      (* eapply context_epsilon_star_merge_states. eassumption. *)
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      assert (exists t1'' t2'', t'' = t1'' ** t2'')
        as [t1'' [t2'' ?]] by admit; subst t''. (* By pairwise events.
                                                   More info? *)
      assert (Hstar13''_ := Hstar13''). (* Which variants are needed? *)
      apply (star_app_inv (@CS.singleton_traces_non_inform _)) in Hstar13''_
        as [s2'' [Hstar12'' Hstar23'']].
      assert (Hrel1 : mem_rel2 p α γ (CS.state_mem s2, t1) (CS.state_mem s2'', t1''))
        by admit. (* Need to recompose memory relation based on executions. *)
      specialize (IHstar12' _ _ _ Hcomp1 Hmerge1 Hstar12'' Hrel1)
        as [t1' [s2' [Hstar12' Hmerge2]]].
      destruct t2 as [| e2 [| e2' t2]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star.
           eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl]. *)
        assert (t2'' = E0) by admit; subst t2''.
        destruct (threeway_multisem_star_E0
                    Hmerge2 (star_one _ _ _ _ _ Hstep23) Hstar23'')
          as [s3' [Hstar23' Hmerge3]].
        exists t1', s3'. split; [| assumption].
        eapply star_trans; try eassumption.
        now rewrite E0_right.
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        assert (exists e2'', t2'' = [e2'']) as [e2'' ?]
            by admit; subst t2''. (* By one-to-one event correspondence. More? *)
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
        assert (Hrel2 : mem_rel2 p α γ (CS.state_mem s3, [e2]) (CS.state_mem s2''2, [e2'']))
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
        exists (t1' ++ [e']), s3'. split; [| assumption].
        eapply star_trans; first eassumption.
        exact (star_trans
                 (star_right _ _ Hstar2' Hstep23' (eq_refl _))
                 Hstar3' (eq_refl _)).
        rewrite -> E0_right, <- Eapp_assoc, -> E0_right.
        reflexivity.
      + (* Contradiction: a step generates at most one event. *)
        pose proof @CS.singleton_traces_non_inform _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  (* Qed. *)
  Admitted. (* RB: TODO: Check admits. *)
End ThreewayMultisem2.

(* Three-way simulation and its inversion. *)
Section ThreewayMultisem3.
  Variables p c p' c' : program.

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Variables α γ : addr_t -> addr_t.

  Theorem threeway_multisem_star s1 s1' s1'' t t'' s2 s2'' :
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 p α γ (CS.state_mem s2, t) (CS.state_mem s2'', t'') ->
    (* Star (CS.sem_non_inform (program_link p  c')) (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2''). *)
    (* /\ mergeable_states ip ic s2 s2'' *)
  exists t' s2',
    Star sem'  s1'  t'  s2' /\
    mergeable_states p c p' c' α γ s2 s2' s2''.
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
  Corollary star_simulation s1 s1' s1'' t t'' s2 s2'' :
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    Star sem   s1   t   s2   ->
    Star sem'' s1'' t'' s2'' ->
    mem_rel2 p α γ  (CS.state_mem s2, t) (CS.state_mem s2'', t'') ->
  exists t' s2',
    Star sem'  s1' t' s2' /\
    mergeable_states p c p' c' α γ s2 s2' s2''.
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

  Theorem threeway_multisem_step_inv_program s1 s1' s1'' t' s2' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' α γ s1 s1' s1'' ->
    (* Step sem' (merge_states ip ic s1 s1'') t s2' -> *)
    Step sem' s1' t' s2' ->
  exists t s2,
    Step sem  s1  t  s2 /\
    mem_rel2 p α γ (CS.state_mem s1', t') (CS.state_mem s1, t).
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

  Variables α γ : addr_t -> addr_t.

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

  Variables sigma sigma_inv : addr_t -> addr_t.

  Lemma match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
  exists s',
    initial_state sem'  s'  /\
    mergeable_states p c p' c' sigma sigma_inv s s' s''.
  Proof.
    intros Hini Hini''.
    exists (CS.initial_machine_state prog'). split.
    - unfold initial_state, CS.initial_machine_state. reflexivity.
    - eapply mergeable_states_intro
        with (s0 := s) (s0'' := s'') (t := E0) (t' := E0) (t'' := E0);
        try eassumption;
        try now constructor.
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

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem_non_inform prog.
  Let sem'  := CS.sem_non_inform prog'.
  Let sem'' := CS.sem_non_inform prog''.

  Variables α γ : addr_t -> addr_t.

  (* RB: NOTE: Consider execution invariance and similar lemmas on the right as
     well, as symmetry arguments reoccur all the time.
     TODO: Observe the proof of match_nostep is almost identical, and refactor
     accordingly. *)
  Theorem match_final_states s s' s'' :
    mergeable_states p c p' c' α γ s s' s'' ->
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

  Theorem match_nofinal s s' s'' :
    mergeable_states p c p' c' α γ s s' s'' ->
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

  Lemma match_nostep s s' s'' :
    mergeable_states p c p' c' α γ s s' s'' ->
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

  Variables α γ : addr_t -> addr_t.

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
  Theorem recombination_prefix_rel m m'' n n'' :
    does_prefix sem   m ->
    does_prefix sem'' m'' ->
    behavior_rel_behavior_all_cids n  n'' m  m'' ->
  exists m' n',
    does_prefix sem'  m' /\
    behavior_rel_behavior_all_cids n' n   m' m.
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
    assert (Hmerge1 : mergeable_states p c p' c' α γ s1 s1' s1'')
      by admit.
    (* In the standard proof, because the two executions produce the same
       prefix, we know that the two runs either terminate, go wrong or are
       unfinished. The third case is probably the most interesting here. *)
    destruct (CS.behavior_prefix_star_non_inform Hbeh Hprefix)
      as [s1_ [s2 [Hini1_ Hstar12]]].
    destruct (CS.behavior_prefix_star_non_inform Hbeh'' Hprefix'')
      as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
    pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec
         Hprog_is_closed Hprog_is_closed' α γ α γ Hini1_ Hini1''_
      as [s1'_ [Hini1' Hmerge1_]].
    (* By determinacy of initial program states: *)
    assert (Heq1 : s1 = s1_) by admit.
    assert (Heq1' : s1' = s1'_) by admit.
    assert (Heq1'' : s1'' = s1''_) by admit.
    subst s1_ s1'_ s1''_.
    clear Hini1_ Hini1''_ Hmerge1_.
    (* Now we should be able to apply a modified star simulation. *)
    pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [t' [s2' [Hstar12' Hmerge2]]].
    {
      (* For this, however, we need to be able to establish the memory
         relation between the two, in principle starting from [Hmerge1] and
         [Hrel]. *)
      (* NOTE: The memory relation is designed to hold at the boundaries!
         vs. higher-level memory relation *)
      admit.
    }
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
  Admitted.

End Recombination.

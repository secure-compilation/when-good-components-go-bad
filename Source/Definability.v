Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.RenamingOption.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Lia.
Require Intermediate.CS.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section Definability.
  Local Open Scope fset_scope.

  Variable intf: Program.interface.
  Variable closed_intf: closed_interface intf.
  Variable has_main: intf Component.main.

  Variable prog_buffers : NMap (nat + list value).
  Hypothesis domm_buffers : domm intf = domm prog_buffers.
  (* Essentially a copy of the intermediate [wfprog_well_formed_buffers]. *)
  Hypothesis wf_buffers :
    forall C buf,
      prog_buffers C = Some buf ->
      Buffer.well_formed_buffer buf.

  (** The definability proof takes an execution trace as its input and builds a
      source program that can produce that trace.  Roughly speaking, it does so
      by keeping one counter for each component, and using that counter to track
      how many calls or returns have been executed by that component.

      To see how this works, suppose that we have an interface with two
      procedures P1 and P2, which live in components C1 and C2.  Given the trace
      *)


  (**   ECall mainC P1    0 C1
        ECall C1    P2    1 C2
        ERet  C2          2 C1
        ECall C1    P2    3 C2
        ECall C2    mainP 4 mainC *)

  (** we would produce the program *)

  (**   C1 {
          P1() {
            if (local[0] == 0) {
              local[0]++;
              C2.P2(1);
              C1.P1(0);
            } else if (local[0] == 1) {
              local[0]++;
              C2.P2(3);
              C1.P1(0);
            } else {
              exit();
            }
          }
        }

        C2 {
          P2() {
            if (local[0] == 0) {
              local[0]++;
              return 2;
            } else if (local[0] == 1) {
              local[0]++;
              mainC.mainP(4);
              C2.P2(0);
            } else {
              exit();
            }
          }
        } *)

  (** TODO: [DynShare] Complete, relocate.

      In the memory sharing case, back-translation will offset whole blocks to
      make room for a certain amount of metadata, as appropriate. The choice of
      shifting whole blocks somewhat complicates the trace relation (and the
      notion of shared address in particular), but it is less disruptive than
      performing shifting inside a block to reserve some space for
      back-translation metadata. The issue is that metadata must never be
      shared, but the block where it is contained may.

      In general, whenever there is dynamic memory sharing, shared addresses
      need to be unobservable. In this setting, the presence of metadata imposes
      a need to hide said metadata.

      In particular, if the granularity of address sharing is offset-based (not
      block-based), it will be difficult to know if the behavior of the receiver
      is influenced by those data.

      However, we do know whether a given component was or not the result of
      back-translation, so we could reserve a given block (say, block 0) for
      metadata, and therefore make it private by construction. In this model,
      the complexity of the back-translated code increases only moderately. The
      idea is that a component may share its local buffer, but never its
      metadata buffer, so the two need to be separate. One way to achieve this
      is as follows:

      When a component is called, it checks whether it is the first time that it
      has been called. If this is the case, it allocates a new local buffer for
      its private metadata, distinct from the "program-local" buffer. This is
      combined with a simple constant shifting scheme in the trace relation.

      A program back-translation is parametric on the interface as well as the
      static buffers of the program being back-translated, given that their
      contents can affect execution in ways unaccounted for in the program
      trace, in particular in the event of sharing of a component's local
      buffer. A back-translated component must therefore initialize its
      "program-local" buffer with the same contents in the original component
      for their behaviors to match.

      TODO Extend/adapt example *)

  (** If a component has multiple procedures, they can share the same
      code. Notice that each branch that performs call performs a recursive call
      at the end.  This is needed to trigger multiple events from a single
      function.

      The first ingredient needed to perform this translation is a switch
      statement that runs code based on the value of the first local variable.

   *)

  (* If the local counter (first position of the local buffer) contains the
     value [n], increment it and execute [e_then], otherwise execute
     [e_else]. *)
  Definition switch_clause (n : Z) (e_then e_else : expr) : expr :=
    let one := E_val (Int 1%Z) in
    E_if (E_binop Eq (E_deref E_local) (E_val (Int n)))
         (E_seq (E_assign E_local (E_binop Add (E_deref E_local) one)) e_then)
         e_else.

  Ltac take_step :=
    match goal with
    | |- @star _ _ _ _ _ _ ?t _ =>
      eapply (@star_step _ _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
    end.

  Ltac take_steps := (take_step; [take_steps]) || take_step.

  Lemma switch_clause_spec p' P C stk mem n n' e_then e_else arg :
    Memory.load mem (P, C, Block.local, 0%Z) = Some (Int n) ->
    if (n =? n') % Z then
      exists mem',
        Memory.store mem (P, C, Block.local, 0%Z) (Int (Z.succ n)) = Some mem' /\
        Star (CS.sem p')
             [CState C, stk, mem , Kstop, switch_clause n' e_then e_else, arg] E0
             [CState C, stk, mem', Kstop, e_then, arg]
    else
      Star (CS.sem p')
           [CState C, stk, mem, Kstop, switch_clause n' e_then e_else, arg] E0
           [CState C, stk, mem, Kstop, e_else, arg].
  Proof.
    intros Hload.
    destruct (Z.eqb_spec n n') as [n_n'|n_n'].
    - subst n'.
      assert (Hload' := Hload).
      unfold Memory.load in Hload'.
      unfold Memory.store.
      simpl in *.
      destruct (Permission.eqb P Permission.data) eqn:EpermData; try discriminate.
      destruct (getm mem C) as [memC|] eqn:EmemC; try discriminate.
      destruct (ComponentMemory.store_after_load _ _ _ _ (Int (Z.succ n)) Hload')
        as [memC' EmemC'].
      rewrite EmemC'.
      eexists; split; eauto.
      repeat take_step; trivial; try eassumption.
      + unfold Memory.load. simpl. rewrite EmemC. eauto.
      + repeat take_step; trivial; try eassumption.
        rewrite Z.eqb_refl -[_ != _]/(true) /=.
        repeat take_step; trivial; try eassumption.
        * unfold Memory.load. simpl. rewrite EmemC. eauto.
        * unfold Memory.store. simpl. rewrite EmemC. simpl. now rewrite Z.add_1_r EmemC'.
        * apply star_refl.
    - unfold switch_clause.
      repeat take_step; trivial; try eassumption.
      + unfold Memory.load in Hload. simpl in Hload.
        destruct (Permission.eqb P Permission.data); try discriminate.
        unfold Memory.load. simpl. eauto.
      + eapply (@star_step _ _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
        { rewrite <- Z.eqb_neq in n_n'. rewrite n_n'. simpl.
          eapply CS.KS_If2. }
        apply star_refl.
  Qed.

  (* Given an indexed switch statement [res], add a new expression [e] at the
     top. If the first available index for [res] is [n], this number is used
     to check the execution of [e], and the first available index of the result
     is [n - 1]. *)
  Definition switch_add_expr (e : expr) (res : nat * expr) : (nat * expr) :=
    (Nat.pred (fst res), switch_clause (Z.of_nat (Nat.pred (fst res))) e (snd res)).

  (* Create a base switch out of the list expressions [es ++ [e_else]]. *)
  Definition switch (es: list expr) (e_else: expr) : expr :=
    snd (fold_right switch_add_expr (length es, e_else) es).

  Lemma fst_switch n (e_else: expr) (es : list expr) :
    fst (fold_right switch_add_expr (n, e_else) es) = (n - length es)%nat.
  Proof.
    induction es as [|e' es IH]; try now rewrite Nat.sub_0_r.
    simpl. now rewrite IH Nat.sub_succ_r.
  Qed.

  Lemma switch_spec_else p' P C stk mem n es e_else arg :
    Memory.load mem (P, C, Block.local, 0%Z) = Some (Int (Z.of_nat n)) ->
    (length es <= n)%nat ->
    Star (CS.sem p')
         [CState C, stk, mem, Kstop, switch es e_else, arg] E0
         [CState C, stk, mem, Kstop, e_else, arg].
  Proof.
    intros C_local es_n. unfold switch.
    enough (forall m,
               m <= n -> length es <= m ->
               Star (CS.sem p')
                    [CState C, stk, mem, Kstop, snd (fold_right switch_add_expr (m, e_else) es), arg]
                    E0
                    [CState C, stk, mem, Kstop, e_else, arg])%nat.
    { apply (H (length es)); trivial. }
    clear es_n. intros m m_le_n es_le_n.
    induction es as [|e es IH]; try apply star_refl.
    unfold switch. simpl. simpl in es_le_n. rewrite fst_switch -Nat.sub_succ_r. simpl.
    do 5 take_step; [eauto|].
    - unfold Memory.load in C_local. simpl in C_local.
      destruct (Permission.eqb P Permission.data); try discriminate.
      unfold Memory.load. simpl. eauto.
    - do 2 take_step.
      eapply (@star_step _ _ _ _ _ _ E0); try now (simpl; reflexivity).
      { apply CS.eval_kstep_sound. simpl.
        destruct (Z.eqb_spec (Z.of_nat n) (Z.of_nat (m - S (length es)))) as [n_eq_0|?]; simpl.
        - zify. lia.
        - reflexivity. }
      apply IH. lia.
  Qed.

  Lemma switch_spec p' P C stk mem es e es' e_else arg :
    Memory.load mem (P, C, Block.local, 0%Z) = Some (Int (Z.of_nat (length es))) ->
    exists mem',
      Memory.store mem (P, C, Block.local, 0%Z) (Int (Z.of_nat (S (length es)))) = Some mem' /\
      Star (CS.sem p')
           [CState C, stk, mem , Kstop, switch (es ++ e :: es') e_else, arg] E0
           [CState C, stk, mem', Kstop, e, arg].
  Proof.
    intros Hload.
    assert (Eswitch :
              exists e_else',
                switch (es ++ e :: es') e_else =
                switch es (switch_clause (Z.of_nat (length es)) e e_else')).
    { unfold switch. rewrite fold_right_app app_length. simpl.
      exists (snd (fold_right switch_add_expr ((length es + S (length es'))%nat, e_else) es')).
      repeat f_equal. rewrite -> surjective_pairing at 1. simpl.
      rewrite fst_switch Nat.add_succ_r.
      assert (H : (S (length es + length es') - length es' = S (length es))%nat) by lia.
      rewrite H. reflexivity. }
    destruct Eswitch as [e_else' ->]. clear e_else. rename e_else' into e_else.
    assert (Hcont := switch_clause_spec p' stk (Z.of_nat (length es)) e e_else arg Hload).
    rewrite Z.eqb_refl in Hcont.
    destruct Hcont as (mem' & Hstore & Hstar2).
    exists mem'. rewrite Nat2Z.inj_succ. split; trivial.
    apply (fun H => @star_trans _ _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial.
    apply (switch_spec_else p' stk _ arg Hload).
    reflexivity.
  Qed.

  (* RB: NOTE: Should we try to avoid writing [Source] qualifiers all over the
     place? We are working on the source after all. *)

  (* A simple scheme that maps registers to constant memory locations
     immediately after the back-translation counter in position 0.
     RB: TODO: Phrase in terms of [Register.to_nat]. *)
  Definition reg_offset (reg : Eregister) : Z :=
    (* 4 + *)
    match reg with
    | E_R_ONE  => 4
    | E_R_COM  => 5
    | E_R_AUX1 => 6
    | E_R_AUX2 => 7
    | E_R_RA   => 8
    | E_R_SP   => 9
    | E_R_ARG  => 10
    end.

  Lemma reg_offset_inj :
    forall reg1 reg2,
      reg_offset reg1 = reg_offset reg2 ->
      reg1 = reg2.
  Proof.
    intros [] [] Heq;
      try inversion Heq;
      reflexivity.
  Qed.

  Definition loc_of_reg (reg : Eregister) : expr :=
    E_binop Add E_local (E_val (Int (reg_offset reg))).

  Lemma values_are_integers_loc_of_reg:
    forall r, Source.values_are_integers (loc_of_reg r).
  Proof.
    now destruct r.
  Qed.

  Lemma called_procedures_loc_of_reg:
    forall r, called_procedures (loc_of_reg r) = fset0.
  Proof.
    destruct r;
      (simpl; unfold fsetU, val; simpl; rewrite fset0E; reflexivity).
  Qed.

  (* Straightforward correspondence between "event" operators and
     regular operators. *)
  Definition binop_of_Ebinop (op : Ebinop) : binop :=
    match op with
    | E_Add   => Add
    | E_Minus => Minus
    | E_Mul   => Mul
    | E_Eq    => Eq
    | E_Leq   => Leq
    end.

  Definition nop_expr: expr := E_val (Int 0%Z).
  Definition error_expr : expr := E_binop Mul (E_val (Int 0)) E_local.

  Definition INITFLAG_offset := 2%Z.
  Definition LOCALBUF_offset := 3%Z.
  Definition LOCALBUF_blockid : Block.id := 1.

  Hint Unfold INITFLAG_offset : definabilitydb.
  Hint Unfold LOCALBUF_offset : definabilitydb.
  Hint Unfold LOCALBUF_blockid : definabilitydb.
 

  Definition INITFLAG := E_binop Add E_local (E_val (Int INITFLAG_offset)).
  Definition LOCALBUF := E_binop Add E_local (E_val (Int LOCALBUF_offset)).

  (* Translation of constant values to expressions, with special attention
     given to pointers. *)
  Definition expr_of_const_val (v : value) : expr :=
    match v with
    (* Integer values are simple. *)
    | Int n            => E_val (Int n)
    (* Pointer values need to take into account some amount of shifting, here
       corresponding to the counter and space reserved to locate register
       values.  *)
    (* FIXME: Offset vs. block-based shifting *)
    | Ptr (perm, cid, bid, o) =>
      if Permission.eqb perm Permission.data then
        (* We make the implicit assumption that all such values refer to
           the local buffer, which should follow from well-formedness. *)
        E_binop Add (E_deref LOCALBUF) (E_val (Int o))
        (* Ptr (perm, cid, S bid, o) *)
        (* E_binop Add E_local (E_val (Int (8 + o))) *)
      else
        (* An implicit assumption is that perm =? Permission.code. *)
        (* TODO: change the type of the permission field so that it is not int, and
           instead just an inductive type. *)
        (* An implicit assumption is that the component id of the code pointer *)
        (* is the same as the component id of the pc. *)
        (* An implicit assumption is that the block id corresponds exactly to *)
        (* the function id. Note that this assumption is satisfied by the memory *)
        (* initialization functions. *)
        E_binop Add (E_funptr bid) (E_val (Int o))
    (* Undefined values are mapped to a well-formed but ill-typed expression
       (instead of some arbitrary but well-typed value, so as to preserve
       bad behavior). This choice might demand more work in some proofs,
       while possibly making other goals distinctly provable. *)
    | Undef            => error_expr
    end.

  Lemma values_are_integers_expr_of_const_val:
    forall v, Source.values_are_integers (expr_of_const_val v).
  Proof.
    intros [n | [[[p C] b ] o] |]; try reflexivity.
    destruct (Permission.eqb p Permission.data) eqn:e; unfold expr_of_const_val; rewrite e; auto.
  Qed.

  Lemma called_procedures_expr_of_const_val:
    forall v, called_procedures (expr_of_const_val v) = fset0.
  Proof.
    intros [n | [[[p C] b ] o] |].
    - reflexivity.
    - simpl. unfold fsetU, val. simpl. rewrite fset0E.
      destruct (Permission.eqb p Permission.data) eqn:Heq;
        simpl; rewrite !fset0U fset0E; reflexivity.
    - simpl. unfold fsetU, val. simpl. rewrite fset0E. reflexivity.
  Qed.

  (** We use [switch] to define the following function [expr_of_trace], which
      converts a sequence of events to an expression that produces that sequence
      of events when run from the appropriate component.  We assume that all
      events were produced from the same component.  The [C] and [P] arguments
      are only needed to generate the recursive calls depicted above. *)

  Notation "x ;; y" := (E_seq x y) (right associativity, at level 90).

  Definition EXTCALL_offset := 1%Z.
  Hint Unfold EXTCALL_offset : definabilitydb.
  Hint Unfold Block.local : definabilitydb.
  
  Definition EXTCALL := E_binop Add E_local (E_val (Int EXTCALL_offset)).
  Definition invalidate_metadata :=
    E_assign (loc_of_reg E_R_ONE) error_expr;;
    E_assign (loc_of_reg E_R_AUX1) error_expr;;
    E_assign (loc_of_reg E_R_AUX2) error_expr;;
    E_assign (loc_of_reg E_R_RA) error_expr;;
    E_assign (loc_of_reg E_R_SP) error_expr;;
    E_assign (loc_of_reg E_R_ARG) error_expr.
  (* Lemma invalidate_metadata_spec (p: Source.program): forall cp st mem k arg, *)
  (*     exists mem', *)
  (*       Star (CS.sem p) (CS.State cp st mem k invalidate_metadata arg) [] *)
  (*            (CS.State cp st mem' k (E_val Undef) arg) /\ *)
  (*       True. *)
  (* Proof. *)
  (*   intros cp st mem k arg. *)
  (* Abort. *)

  (* We call this function when in component C executing P. *)
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (e: event_inform) : expr :=
    match e with
    | ECallInform _ P' arg _ _ C' =>
      E_assign EXTCALL (E_val (Int 1%Z));;
      E_call C' P' (E_deref (loc_of_reg E_R_COM));;
      invalidate_metadata;;
      E_assign EXTCALL (E_val (Int 0%Z));;
      E_call C P (E_val (Int 0%Z)) (* This is really (C, P) calling itself *)
    | ERetInform  _ ret_val _ _ _ =>
      E_assign EXTCALL (E_val (Int 1%Z));;
      E_deref (loc_of_reg E_R_COM)
    (* Other events generate corresponding expressions, even though these do not
       generate any events in the source semantics. Like calls (but unlike
       returns), those "informative-only" events are followed by a recursive
       call to the current procedure. *)
    | EConst _ val reg _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (loc_of_reg reg) (expr_of_const_val val);;
      E_call C P (E_val (Int 0))
    | EMov _ rsrc rdest _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (loc_of_reg rdest) (E_deref (loc_of_reg rsrc));;
      E_call C P (E_val (Int 0))
    | EBinop _ op r1 r2 r3 _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (loc_of_reg r3) (E_binop (binop_of_Ebinop op)
                                        (E_deref (loc_of_reg r1))
                                        (E_deref (loc_of_reg r2)));;
      E_call C P (E_val (Int 0))
    | ELoad _ r_src r_dest _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (loc_of_reg r_dest) (E_deref (E_deref (loc_of_reg r_src)));;
      E_call C P (E_val (Int 0))
    | EStore _ r_dest r_src _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (E_deref (loc_of_reg r_dest)) (E_deref (loc_of_reg r_src));;
      E_call C P (E_val (Int 0))
    | EAlloc _ r_dest r_size _ _ =>
      (* E_assign EXTCALL (E_val (Int 0%Z));; *)
      E_assign (loc_of_reg r_dest) (E_alloc (E_deref (loc_of_reg r_size)));;
      E_call C P (E_val (Int 0))
    end.

  (* RB: TODO: Avoid possible duplication in [Language] and [Machine]. *)
  Definition unfold_buffer (b : (nat + list value)%type) : list value :=
    match b with
    | inl n  => nseq n Undef
    | inr vs => vs
    end.

  (* The local buffer of back-translated programs is dedicated to private
     metadata:
      - The trace step counter at position 0;
      - The external call flag at position 1;
      - The buffer initialization flag at position 2;
      - The pointer to the simulated static buffer at position 3.
     These are followed by locations for the simulated machine registers.
     NOTE: Register indexes must match [loc_of_reg] and would ideally be defined
     in terms of [Register.to_nat], and their initial values in terms of
     [Register.init]. *)
  Definition meta_buffer : list value :=
    [Int 0; Int 1; Int 0; Undef] ++ [Undef; Undef; Undef; Undef; Undef; Undef; Undef].

  (* Compute component buffer side, assuming argument [C] is in the domain of
     [intf]. *)
  Definition buffer_size (C : Component.id) : nat :=
    match prog_buffers C with
    | Some buf => size (unfold_buffer buf)
    | None => 0 (* Should not happen *)
    end.

  (* Allocate a new buffer to serve as the local buffer of the back-translation.
     By convention this will be created immediately after program initialization
     and therefore its block identifier should be 1.

     NOTE: We are relying on knowledge of the implementation and behavior of the
     allocator. If these conditions are not satisfied, the offset shifting
     necessary for the trace relation will be incorrect.

     Note that buffers coming from well-formed program components must have size
     strictly greater than zero, so the behavior of alloc() is defined. *)
  Definition alloc_local_buffer_expr (C : Component.id) : expr :=
    E_alloc (E_val (Int (Z.of_nat (buffer_size C)))).

  (* Copy the [i]-th component of the original program buffer of [C] from its
     temporary location in the local buffer of [C]'s back-translation (following
     its private metadata) into the [i]-th component of the replacement local
     buffer.

     Initially, the back-translated component memory looks like this:
       0: [M, M, M, M, M, M, M, M, D1, D2, ..., Di, ...]
     where the first few positions of the local buffer are taken up by
     (M)etadata, followed by the original component's (D)ata. During this
     process, the local, unshareable data is transferred to the de facto,
     shareable local buffer:
       L: [D1, D2, ..., Di, ...]

     Generated instruction:
       ( *(local[0]) )[i] = *( local[i + META_SIZE] )

     NOTE: Because the local buffers contain no pointers, we could write
     hardcoded initialization code instead of having a copy of the original
     local buffer in the metadata buffer.
   *)
  (* Definition buffer_nth (C : Component.id) (b : Block.id) (i : nat) : expr := *)
  (*   match prog_buffers C with *)
  (*   | Some bufs => *)
  (*     match bufs b with *)
  (*     | Some buf => *)
  (*       match nth_error (unfold_buffer buf) i with *)
  (*       | Some v => E_val v *)
  (*       | None => error_expr (* should not happen *) *)
  (*       end *)
  (*     | None => error_expr (* should not happen *) *)
  (*     end *)
  (*   | None => error_expr (* should not happen *) *)
  (*   end. *)

  (* Definition copy_local_datum_expr (C : Component.id) (b : Block.id) (i : nat) : expr := *)
  (*   E_assign *)
  (*     (E_binop Add (E_deref E_local) *)
  (*                  (E_val (Int (Z.of_nat i)))) *)
  (*     (buffer_nth C b i). *)

  (* To initialize the acting local buffer from its temporary location in the
     private local buffer, allocate a new block of adequate size in memory,
     temporarily keeping its address in local[0]; use this convention to
     initialize the public local buffer; and restore the temporary variable
     to its proper value.

     NOTE: This is not so nice as we are not using the definition of
     [meta_buffer] to restore the initial value. In addition to this, using
     the first position, which holds the program counter, while noting that
     this instruction will be executed at the first value of the counter (and
     prior to its increment), is rather ugly and brittle. *)
  (* Definition init_local_buffer_expr (C : Component.id) : expr := *)
  (*   (* [E_assign E_local (alloc_local_buffer_expr C)] ++ *) *)
  (*   (* map (copy_local_datum_expr C) (iota 0 (buffer_size C)) ++ *) *)
  (*   (* [E_assign E_local (E_val (Int 0))] *) *)
  (*   foldr (fun e acc => E_seq e acc) *)
  (*         (E_assign E_local (E_val (Int 0))) (* last instruction *) *)
  (*         ([E_assign E_local (alloc_local_buffer_expr C b)] ++ *)
  (*          map (copy_local_datum_expr C b) (iota 0 (buffer_size C b))). *)

  Definition comp_call (C : Component.id) (e : event_inform) : bool :=
    match e with
    | ECallInform _ _ _ _ _ C' => C' == C
    | _ => false
    end.

  (* RB: TODO: Treatment for [Component.main]. *)
  (* TODO: Easier to add the prologue to all procedures and control its
     execution through additional counter conditions. *)
  Definition first_proc_in_comp (C : Component.id) (P : Procedure.id)
                                (t : trace event_inform) : bool :=
    match ohead (filter (comp_call C) t) with
    | Some (ECallInform _ P' _ _ _ _) => P' == P
    | _ => false
    end.

  (* RB: TODO: Later in [definability_gen] there are explicit instances of
     this function, which annoyingly will need an additional boolean
     argument. Ideally this parameter would not appear explicitly, but at the
     moment this is passed the [comp_subtrace] of the original trace, and so
     the necessary events for the initialization check are not available. *)
  Definition expr_of_trace
             (C: Component.id) (P: Procedure.id) (t: trace event_inform)
             (* (init: bool) *)
    : expr :=
    (* let init_expr := if init then [init_local_buffer_expr C] else [] in *)
    switch (map (expr_of_event C P) t) E_exit.

  (** To compile a complete trace mixing events from different components, we
      split it into individual traces for each component and apply
      [expr_of_trace] to each one of them.  We also initialize the memory of
      each component to hold 0 at the first local variable. *)

  Definition comp_subtrace (C: Component.id) (t: trace event_inform) :=
    filter (fun e => C == cur_comp_of_event e) t.

  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace event_inform) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply: filter_cat. Qed.

  Definition buffer_nth (C : Component.id) (i : nat) : expr :=
    match prog_buffers C with
    | Some buf =>
      match nth_error (unfold_buffer buf) i with
      | Some v => E_val v
      | None => error_expr (* should not happen *)
      end
    | None => error_expr (* should not happen *)
    end.

  Definition copy_local_datum_expr (C : Component.id) (i : nat) : expr :=
    E_assign
      (E_binop Add (E_deref LOCALBUF)
                   (E_val (Int (Z.of_nat i))))
      (buffer_nth C i).

  Definition init_local_buffer_expr (C : Component.id) : expr :=
    (* [E_assign E_local (alloc_local_buffer_expr C)] ++ *)
    (* map (copy_local_datum_expr C) (iota 0 (buffer_size C)) ++ *)
    (* [E_assign E_local (E_val (Int 0))] *)
    foldr (fun e acc => E_seq e acc)
          (E_assign INITFLAG (E_val (Int 1))) (* last instruction *)
          (map (copy_local_datum_expr C) (iota 0 (buffer_size C))).

  Definition init_check (C : Component.id): expr :=
    E_if (E_binop Eq (E_deref INITFLAG) (E_val (Int 0%Z)))
         ((E_assign LOCALBUF (E_alloc (E_val (Int (Z.of_nat (buffer_size C))))));;
          init_local_buffer_expr C)
         nop_expr.

  Definition extcall_check: expr :=
    E_if (E_binop Eq (E_deref EXTCALL) (E_val (Int 1%Z)))
         (invalidate_metadata;;
          E_assign EXTCALL (E_val (Int 0%Z)))
         nop_expr.

  Definition procedure_of_trace
             (C : Component.id) (P : Procedure.id) (t : trace event_inform)
    : expr :=
    init_check C;;
    extcall_check;;
    expr_of_trace C P (comp_subtrace C t). (* RB: TODO: Substitute check. *)

  Fixpoint procedure_ids_of_subtrace
             (t: trace event_inform) :=
    match t with
    | nil => fset0
    | e :: t' =>
      let procs_of_e :=
          match e with
          | EConst _ (Ptr (perm, cid, bid, off)) _ _ _ =>
            (* What we are collecting right now is a superset of the bids that
               really correspond to a procedure id. *)
            (* If we want to make this superset tighter, then we should check *)
            (* that perm =? Permission.code and that cid =? C *)
            fset1 bid
          | _ => fset0
          end
      in
      procs_of_e :|: procedure_ids_of_subtrace t'
    end.

  Definition procedure_ids_of_trace (C: Component.id) (t: trace event_inform) :=
    procedure_ids_of_subtrace (comp_subtrace C t).

  Definition procedures_of_trace (t: trace event_inform) : NMap (NMap expr) :=
    mapim (fun C Ciface =>
             let procs_no_main :=
                 (procedure_ids_of_trace C t) :|: (Component.export Ciface) in
             let procs :=
                 if C == Component.main then
                   Procedure.main |: procs_no_main
                 else procs_no_main in
               mkfmapf (fun P => procedure_of_trace C P t) procs)
          intf.

  Definition valid_procedure C P :=
    C = Component.main /\ P = Procedure.main
    \/ exported_procedure intf C P.

  Lemma find_procedures_of_trace_exp (t: trace event_inform) C P :
    exported_procedure intf C P ->
    Source.find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    intros [CI [C_CI CI_P]].
    unfold Source.find_procedure, procedures_of_trace.
    rewrite mapimE C_CI /= mkfmapfE.
    case: eqP=> _.
    - by rewrite in_fsetU1 in_fsetU CI_P !orbT.
    - by rewrite in_fsetU CI_P !orbT.
  Qed.

  Lemma find_procedures_of_trace_main (t: trace event_inform) :
    Source.find_procedure (procedures_of_trace t) Component.main Procedure.main
    = Some (procedure_of_trace Component.main Procedure.main t).
  Proof.
    rewrite /Source.find_procedure /procedures_of_trace.
    rewrite mapimE eqxx.
    case: (intf Component.main) (has_main)=> [Cint|] //= _.
    by rewrite mkfmapfE in_fsetU1 eqxx.
  Qed.

  Lemma find_procedures_of_trace (t: trace event_inform) C P :
    valid_procedure C P ->
    Source.find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    by move=> [[-> ->]|?];
    [apply: find_procedures_of_trace_main|apply: find_procedures_of_trace_exp].
  Qed.

  Definition program_of_trace (t: trace event_inform) : Source.program :=
    {| Source.prog_interface  := intf;
       Source.prog_procedures := procedures_of_trace t;
       Source.prog_buffers    :=
         mapm (fun _ => inr meta_buffer) intf |}.
         (* mapm (fun b => inr (meta_buffer ++ (unfold_buffer b))) prog_buffers |}. *)

  (** To prove that [program_of_trace] is correct, we need to describe how the
      state of the program evolves as it emits events from the translated trace.
      One of the difficulties is the stack.  If a call to a component [C]
      performs [n] calls to other components before returning, the code
      generated by [expr_of_trace] will perform [n] *internal* calls in [C].
      Thus, the final return to the calling component must be preceded by [n]
      returns from those recursive calls.  We describe this pattern with the
      following properties.  *)

  Fixpoint well_formed_callers (callers: list Component.id) (stk: CS.stack) : Prop :=
    match callers with
    | [] => True
    | C :: callers' =>
      exists v P top bot,
      stk = CS.Frame C v (Kseq (E_call C P (E_val (Int 0))) Kstop) :: top ++ bot /\
      valid_procedure C P /\
      All (fun '(CS.Frame C' _ k) => C' = C /\ k = Kstop) top /\
      well_formed_callers callers' bot
    end.

  Definition well_formed_stack (s: stack_state) (stk: CS.stack) : Prop :=
    exists top bot,
      stk = top ++ bot /\
      All (fun '(CS.Frame C' _ k) => C' = cur_comp s /\ k = Kstop) top /\
      well_formed_callers (callers s) bot.

  (** The read and write events will also need to rely on the paths. Should the
      (read and write?) events include the paths so as to make back-translation
      easier?

      Would this be the path from the local buffer? *)

  (* ... *)

  (** Main proof of back-translation *)

  Lemma well_formed_events_well_formed_program procs t :
    all (well_formed_event intf procs) t ->
    Source.well_formed_program (program_of_trace t).
  Proof.
    Local Opaque loc_of_reg binop_of_Ebinop expr_of_const_val.
    move=> Ht; split=> //=.
    - exact: closed_interface_is_sound.
    - by rewrite /procedures_of_trace domm_mapi.
    - move=> C P.
      rewrite /exported_procedure /Program.has_component /Component.is_exporting.
      case=> CI [C_CI P_CI].
      by rewrite find_procedures_of_trace_exp //; exists CI; split; eauto.
    - move=> C P Pexpr.
      rewrite /Source.find_procedure /procedures_of_trace mapimE.
      case intf_C: (intf C)=> [CI|] //=.
      rewrite mkfmapfE; case: ifP=> //= P_CI [<-] {Pexpr}; split; last first.
      + split.
        * rewrite /procedure_of_trace /expr_of_trace /switch.
          simpl. repeat (rewrite <- andbA; simpl).
          rewrite !values_are_integers_loc_of_reg; simpl.
          apply /andP. split.
          { admit. }
          elim: {t Ht P_CI} (comp_subtrace C t) (length _) => [|e t IH] n //=.
          by case: e=> /=; intros;
                         try rewrite values_are_integers_expr_of_const_val;
                         apply IH.

        *
          (*clear.
          rewrite /procedure_of_trace /expr_of_trace /switch
                  /program_of_trace.
          remember (length [seq expr_of_event C P i | i <- comp_subtrace C t]) as n.
          generalize dependent n.
          induction t as [|e t' IH]; auto.
          intros ? ?.
          simpl in *.
          destruct (C ==
                      match e with
                      | ECallInform C _ _ _ _ _ | ERetInform C _ _ _ _ |
                        EConst C _ _ _ _ | EMov C _ _ _ _ | EBinop C _ _ _ _ _ _ |
                        ELoad C _ _ _ _ | EStore C _ _ _ _ | EAlloc C _ _ _ _ => C end)
                   eqn:eC; rewrite eC in Heqn.
          -- admit.
          -- rewrite eC. simpl.
          (* specialize (IH n Heqn). *)
          destruct e; auto; simpl.
          case: e=> /=; simpl. intros.
          apply IH.
          try apply IH; simpl.
          *)
          rewrite /procedure_of_trace /expr_of_trace /switch
                  /program_of_trace.
          (*induction t; auto.
          simpl; unfold Source.well_formed_E_funptr; destruct a; simpl.*)
          admit. (* Similar as above. *)
          (* elim: {t Ht P_CI} (comp_subtrace C t) (procedures_of_trace t) (length _) *)
          (* => [|e t IH] p n //=. *)
          (* case: e=> /=; simpl; intros; try apply IH. *)
          (* Local Transparent loc_of_reg expr_of_const_val. *)
          (* destruct e; destruct v; simpl; try apply IH; *)
          (*   match goal with *)
          (*   | ptr : Pointer.t |- _ => *)
          (*     destruct ptr as [[[perm ?] bid] ?]; destruct (Permission.eqb perm Permission.data); *)
          (*       simpl; try apply IH *)
          (*   end; admit. *)

      + pose call_of_event e := if e is ECall _ P _ _ C then Some (C, P) else None.
        have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (project_non_inform (comp_subtrace C t)))).
      {
        rewrite /procedure_of_trace /expr_of_trace /switch.
        admit. (* See above. *)
        (* elim: {t Ht P_CI} (comp_subtrace C t) (length _)=> [|e t IH] n //=. *)
        (* rewrite !fsetU0; exact: fsub0set. *)
        (* move/(_ n) in IH; rewrite !fset0U. *)

        (* case: e=> [C' P' v mem regs C''| | | | | | | ] *)
        (*             //=; *)
        (*             try by move=> C' e e0; rewrite !called_procedures_loc_of_reg !fset0U IH. *)
        (* all:admit. *)
        (* FIXME
        * rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=.
          by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT.
        (* RB: TODO: Refactor cases. *)
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     called_procedures_expr_of_const_val.
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        (* NOTE: Standard cases, not covered by [try by] above. *)
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     !fset0U !fsetU0 !fsubUset !fsub1set !in_fsetU1 !eqxx /= IH.
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     !fset0U !fsetU0 !fsubUset !fsub1set !in_fsetU1 !eqxx /= IH.
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     !fset0U !fsetU0 !fsubUset !fsub1set !in_fsetU1 !eqxx /= IH.
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     !fset0U !fsetU0 !fsubUset !fsub1set !in_fsetU1 !eqxx /= IH.
        * move=> C' v r. intros.
          by rewrite !called_procedures_loc_of_reg
                     !fset0U !fsetU0 !fsubUset !fsub1set !in_fsetU1 !eqxx /= IH.
        FIXME *)
      }
      move=> C' P' /sub/fsetU1P [[-> ->]|] {sub}.
        * rewrite eqxx find_procedures_of_trace;
            first reflexivity.
          move: P_CI; case: eqP intf_C=> [->|_] intf_C.
            rewrite /valid_procedure.
            case/fsetU1P=> [->|P_CI]; eauto.
            move:P_CI => /fsetUP => [[P_CI|P_CI]]. (* New case analysis *)
            { admit. } (* New case *)
            by right; exists CI; split.
          move => /fsetUP => [[|]]. (* New case analysis *)
          { admit. } (* New case *)
          by move=> P_CI; right; exists CI; split.
        * rewrite in_fset /= => C'_P'.
          suffices ? : imported_procedure intf C C' P'.
            by case: eqP => [<-|] //; rewrite find_procedures_of_trace_exp; eauto.
          elim: {P P_CI} t Ht P' C'_P' => [|e t IH] //= /andP [He Ht] P.
          case: (C =P _) => [HC|]; last by eauto.
          case: e HC He=> [_ P' v C'' r C_ <- /= | | | | | | | ]; try by eauto.
          rewrite inE; case/andP=> [C_C'' /imported_procedure_iff imp_C''_P'].
          by case/orP=> [/eqP [-> ->] //|]; eauto.
    - by rewrite domm_map.
    - move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      split.
      + rewrite /Source.has_required_local_buffers. eexists.
        * rewrite mapmE C_CI. reflexivity.
        * simpl. lia.
      + by rewrite /Buffer.well_formed_buffer_opt mapmE C_CI.
    - rewrite /Source.prog_main find_procedures_of_trace //=.
      + split; first reflexivity.
        intros _.
        destruct (intf Component.main) as [mainP |] eqn:Hcase.
        * apply /dommP. exists mainP. assumption.
        * discriminate.
      + by left.
  (* Qed. *)
  Admitted.

  Lemma closed_program_of_trace t :
    Source.closed_program (program_of_trace t).
  Proof.
    split=> //=; by rewrite /Source.prog_main find_procedures_of_trace_main.
  Qed.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace. (* RB: NOTE: Renaming *)

    Variable t : trace event_inform.
    (* NOTE: need assumption of goodness of the trace *)

    (* Let t    :=  *)
    (* [DynShare]: This should be the projection of t_inform.
       This projection function may be defined in the Intermedicate/CS.v *)
    Let p    := program_of_trace t.
    Let init := Source.prepare_buffers p.

    Local Definition component_buffer C := C \in domm intf.

    (* [DynShare] Probably here we should write a spec for expr_of_const_val *)
    (*Lemma expr_of_const_val_well_formed :
    forall v, (* assumption about v being an integer or a "well_formed" pointer*)
      rename_value v = .. (expr_of_const_val v)
     *)

    Lemma valid_procedure_has_block C P :
      valid_procedure C P ->
      component_buffer C.
    Proof.
      case=> [[-> _ {C P}]|[CI]]; rewrite /component_buffer /=.
        by rewrite mem_domm.
      rewrite /Program.has_component /Component.is_exporting /=.
      by rewrite mem_domm; case=> ->.
    Qed.

    Local Definition counter_value C prefix :=
      Z.of_nat (length (comp_subtrace C prefix)).

    (* TODO: Relocate to Memory *)
    Definition next_block (mem: Memory.t) (C : Component.id) : option Block.id :=
      match mem C with
      | Some Cmem => Some (ComponentMemory.next_block Cmem)
      | None => None
      end.

    Lemma next_block_store_stable mem ptr v mem' C:
      Memory.store mem ptr v = Some mem' ->
      next_block mem' C = next_block mem C.
    Admitted.

    (* RB: NOTE: We could make this stronger by noting which component is being
       executed, as this is the only one that can change its own metadata. *)
    Definition well_formed_memory_snapshot_steadystate_shift
               (mem_snapshot mem : Memory.t) (C: Component.id) : Prop :=
      forall b,
        b <> Block.local ->
        memory_shifts_memory_at_shared_addr
          (uniform_shift 1) all_zeros_shift (C, b) mem mem_snapshot.

    Definition well_formed_memory_snapshot_steadystate_block
               (mem_snapshot mem : Memory.t) (C: Component.id) : Prop :=
      forall next,
        next_block mem_snapshot C = Some next ->
        next_block mem C = Some (S next).

    Record well_formed_memory_snapshot_steadystate
           (mem_snapshot mem : Memory.t) (C: Component.id) : Prop := {
      steadysnap_shift :
        well_formed_memory_snapshot_steadystate_shift mem_snapshot mem C;
      steadysnap_block :
        well_formed_memory_snapshot_steadystate_block mem_snapshot mem C
    }.
      (* forall ptr, *)
      (*   Pointer.block ptr <> Block.local -> *)
      (*   Memory.load mem_snapshot ptr = Memory.load mem ptr. *)

      (***************************************************
      forall Cb,
        addr_shared_so_far Cb (project_non_inform prefix) ->
        (* Precondition on Cb:*)
        (*rename_addr_option
          (sigma_shifting_wrap_bid_in_addr
             (sigma_shifting_lefttoright_addr_bid (uniform_shift 1) all_zeros_shift)) Cb
        = Some Cb' ->*)
        memory_shifts_memory_at_shared_addr
          all_zeros_shift (uniform_shift 1) Cb mem_snapshot mem.
       *********************************************)

    Definition well_formed_memory_snapshot_uninitialized
               (mem_snapshot mem : Memory.t) (C: Component.id) : Prop :=
      
      (exists compMem buf,
        mem_snapshot C = Some compMem /\
        prog_buffers C = Some buf /\
        ComponentMemory.next_block compMem = 1 /\
        compMem = ComponentMemory.prealloc (mkfmap [(Block.local, buf)])
      )
      /\
      (exists src_compMem,
          mem C = Some src_compMem /\
          ComponentMemory.next_block src_compMem = LOCALBUF_blockid
      ).
    

    (* JT: NOTE: The reason this lemma should hold is that the store is to the
       local block [Block.local], which should always be *private memory* (from
       the goodness of the trace) and as a result isn't recorded on the memory
       snapshot. *)
    Lemma metadata_store_preserves_snapshot_shift mem_snapshot mem Pm C Csteady o v mem' :
      well_formed_memory_snapshot_steadystate_shift mem_snapshot mem Csteady ->
      Memory.store mem (Pm, C, Block.local, o) v = Some mem' ->
      well_formed_memory_snapshot_steadystate_shift mem_snapshot mem' Csteady.
    Proof.
      move=> WFMS STORE b Hnot.
      case: (WFMS b); auto.
      rewrite /memory_shifts_memory_at_shared_addr
              /memory_renames_memory_at_shared_addr
      => Cbren [eCbren [WFMS1 WFMS2]].
      unfold sigma_shifting_wrap_bid_in_addr, sigma_shifting_lefttoright_addr_bid
        in *.
      destruct (sigma_shifting_lefttoright_option
                  (uniform_shift 1 Csteady)
                  (all_zeros_shift Csteady) b) as [b'|] eqn:eb'; last discriminate.
      exists (Csteady, b'). split; first reflexivity.
      inversion eCbren; subst; clear eCbren.
      split; intros ? ? Hload; simpl in *.
      - assert (Pointer.eq (Pm, C, Block.local, o)
                           (Permission.data, Csteady, b, offset) = false
               ) as Hneq.
        {
          simpl. destruct (Pm); first by auto. simpl.
          destruct (b =? Block.local) eqn:e; first by apply beq_nat_true in e.
          destruct b; first by auto.
            by rewrite !andbF !andFb.
        }
        move : Hneq => /Pointer.eqP => Hneq.
        specialize (Memory.load_after_store_neq _ _ _ _ _ Hneq STORE) as rewr.
        rewrite rewr in Hload.
        by specialize (WFMS1 _ _ Hload).
      - specialize (WFMS2 _ _ Hload) as [v'' [Hv''1 Hv''2]].
        exists v''. split; last assumption.
        assert (Pointer.eq (Pm, C, Block.local, o)
                           (Permission.data, Csteady, b, offset) = false
               ) as Hneq.
        {
          simpl. destruct (Pm); first by auto. simpl.
          destruct (b =? Block.local) eqn:e; first by apply beq_nat_true in e.
          destruct b; first by auto.
            by rewrite !andbF !andFb.
        }
        move : Hneq => /Pointer.eqP => Hneq.
        specialize (Memory.load_after_store_neq _ _ _ _ _ Hneq STORE) as rewr.
          by rewrite rewr.
    Qed.

    Lemma metadata_store_preserves_snapshot_block mem_snapshot mem Pm C Csteady o v mem' :
      well_formed_memory_snapshot_steadystate_block mem_snapshot mem Csteady ->
      Memory.store mem (Pm, C, Block.local, o) v = Some mem' ->
      well_formed_memory_snapshot_steadystate_block mem_snapshot mem' Csteady.
    Proof.
      move=> WFNB STORE b NEXT.
      specialize (WFNB b NEXT).
      unfold next_block in *.
      rewrite -WFNB.
Local Transparent Memory.store.
      unfold Memory.store in STORE.
Local Opaque Memory.store.
      destruct (Permission.eqb (Pointer.permission (Pm, C, Block.local, o))
                               Permission.data) eqn:PERM;
        last discriminate.
      simpl in STORE.
      destruct (mem C) as [memC |] eqn:MEMC; last discriminate.
      destruct (mem Csteady) as [memCsteady |] eqn:MEMCST; last discriminate.
      injection WFNB as WFNB.
      destruct (mem_snapshot Csteady) as [memsCsteady |] eqn:MEMSCST; last discriminate.
      destruct (ComponentMemory.store memC Block.local o v) eqn:CSTORE;
        last discriminate.
      injection NEXT as ?; subst b.
      apply ComponentMemory.next_block_store_stable in CSTORE.
      injection STORE as ?; subst mem'.
      rewrite setmE.
      destruct (Nat.eqb_spec Csteady C) as [|NEQ].
      - subst Csteady. rewrite eqxx. congruence.
      - move:NEQ => /eqP. rewrite /negb => NEQ.
        destruct (Csteady == C) eqn:NEQ'; first discriminate.
        by rewrite NEQ' MEMCST //.
    Qed.

    Lemma metadata_store_preserves_snapshot mem_snapshot mem Pm C Csteady o v mem' :
      well_formed_memory_snapshot_steadystate mem_snapshot mem Csteady ->
      Memory.store mem (Pm, C, Block.local, o) v = Some mem' ->
      well_formed_memory_snapshot_steadystate mem_snapshot mem' Csteady.
    Proof.
      move=> [WFMS WFNB] STORE. split.
      - eapply metadata_store_preserves_snapshot_shift; eassumption.
      - eapply metadata_store_preserves_snapshot_block; eassumption.
    Qed.

    Definition postcondition_event_snapshot_steadystate
               (e: event_inform) (mem: Memory.t) (C: Component.id) : Prop :=
      let mem_snapshot := mem_of_event_inform e in
      well_formed_memory_snapshot_steadystate mem_snapshot mem C.

    Definition postcondition_event_snapshot_uninitialized
               (e: event_inform) (mem: Memory.t) (C: Component.id) : Prop :=
      let mem_snapshot := mem_of_event_inform e in
      well_formed_memory_snapshot_uninitialized mem_snapshot mem C.

    (* NOTE: Seems to talk about the memory /before/ executing the event. Prerequisite
     to do the event *)
    Definition precondition_event_intermediate (e: event_inform) (mem: Memory.t): Prop :=
      match e with
      | ECallInform Csrc _ arg _ _ _ =>
        Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM)
        = Some arg
      | ERetInform Csrc ret _ _ _ =>
        Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM)
        = Some ret
      | EAlloc C _ rsize _ _ =>
        exists size,
          (size > 0)%Z /\
          Memory.load mem (Permission.data, C, Block.local, (reg_offset rsize)) =
          Some (Int size)
      (* TODO: May have to add new well-formedness conditions for other events *)
      | _ => True
      end.

    (* AEK: TODO: This definition should be moved to Common/TracesInform.v, right? *)
    (* The reason I think it should be moved is that we will need a lemma that     *)
    (* tells us that an Intermediate trace satisfies this definition.              *)

    (* Notice that the "from" state (consisting of a Register.t and a Memory.t)    *)
    (* is implicitly given by the first parameter, which is an event_inform.       *)
    (* The second and the third parameters represent the "to" state.               *)
    Inductive event_step_from_regfile_mem : Machine.Intermediate.Register.t ->
                                            Memory.t ->
                                            (* Register file and memory BEFORE
                                               event-producing step *)
                                            event_inform ->
                                            Prop :=
    | step_ECallInform:
        forall C P call_arg mem regs regs' C',
          C <> C' ->
          imported_procedure intf C C' P ->
          Machine.Intermediate.Register.get
            Machine.R_COM
            regs = call_arg ->
          regs' = Machine.Intermediate.Register.invalidate regs ->
          event_step_from_regfile_mem regs mem (ECallInform C P call_arg mem regs' C')
    | step_ERetInform:
        forall mem regs regs' C C' ret_arg,
          C <> C' ->
          Machine.Intermediate.Register.get
            Machine.R_COM
            regs = ret_arg ->
          regs' = Machine.Intermediate.Register.invalidate regs ->
          event_step_from_regfile_mem regs mem (ERetInform C ret_arg mem regs' C')
    | step_EConst:
        forall mem regs regs' C er v,
          regs' = Machine.Intermediate.Register.set
                    (Ereg_to_reg er)
                    v
                    regs ->
          event_step_from_regfile_mem regs mem (EConst C v er mem regs')
    | step_EMov:
        forall mem regs regs' C ersrc erdest,
          regs' = Machine.Intermediate.Register.set (Ereg_to_reg erdest)
                                                    (Machine.Intermediate.Register.get
                                                       (Ereg_to_reg ersrc) regs)
                                                    regs ->
          event_step_from_regfile_mem regs mem (EMov C ersrc erdest mem regs')
    | step_EBinop:
        forall result eop mem regs regs' C er1 er2 er3,
          result = eval_binop
                     (Ebinop_to_binop eop)
                     (Machine.Intermediate.Register.get (Ereg_to_reg er1) regs)
                     (Machine.Intermediate.Register.get (Ereg_to_reg er2) regs) ->
          regs' = Machine.Intermediate.Register.set (Ereg_to_reg er3)
                                                    result
                                                    regs ->
          event_step_from_regfile_mem regs mem (EBinop C eop er1 er2 er3 mem regs')
    | step_ELoad:
        forall mem regs regs' C er1 er2 ptr v,
          Machine.Intermediate.Register.get
            (Ereg_to_reg er1)
            regs = Ptr ptr ->
          Memory.load mem ptr = Some v ->
          Machine.Intermediate.Register.set
            (Ereg_to_reg er2)
            v regs = regs' ->
          event_step_from_regfile_mem regs mem (ELoad C er1 er2 mem regs')
    | step_EStore:
        forall mem mem' regs C ptr er1 er2,
          Machine.Intermediate.Register.get
            (Ereg_to_reg er1)
            regs = Ptr ptr ->
          Memory.store
            mem
            ptr
            (
              Machine.Intermediate.Register.get
                (Ereg_to_reg er2)
                regs
            )
          = Some mem' ->
          event_step_from_regfile_mem regs mem (EStore C er1 er2 mem' regs)
    | step_EAlloc:
        forall mem mem' regs regs' C ersize erptr size ptr,
          Machine.Intermediate.Register.get
            (Ereg_to_reg ersize)
            regs = Int size ->
          (size > 0) % Z ->
          Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
          regs' =
          Machine.Intermediate.Register.set
            (Ereg_to_reg erptr)
            (Ptr ptr)
            regs ->
          event_step_from_regfile_mem regs mem (EAlloc C erptr ersize mem' regs').
    (* | step_EInvalidateRA: *)
    (*     forall mem regs regs' C, *)
    (*       Machine.Intermediate.Register.set *)
    (*         Machine.R_RA *)
    (*         Undef (* We could have chosen any value here.     *) *)
    (*               (* When relating event_step_from_regfile_mem  *) *)
    (*               (* to Intermediate.CS.step, we should be    *) *)
    (*               (* careful to exclude R_RA from the register*) *)
    (*               (* equality relation.                       *) *)
    (*         regs = regs' -> *)
    (*       event_step_from_regfile_mem (EInvalidateRA C mem regs) regs' mem. *)

    Inductive prefix_star_event_steps : (* Machine.Intermediate.Register.t -> *)
                                        (* Memory.t -> *)
                                        trace event_inform -> Prop :=
    | nil_star_event_steps:
        prefix_star_event_steps E0
          (* Machine.Intermediate.Register.init *)
          (* (Source.prepare_buffers p) *)
          (* E0 *)
    (* AEK: Will prepare_buffers match the Intermediate prepare buffer function? *)
    | singleton_star_event_steps:
        forall e,
          event_step_from_regfile_mem
            Machine.Intermediate.Register.init
            (Source.prepare_buffers p)
            e ->
          prefix_star_event_steps [:: e]
    | rcons_star_event_steps:
        forall prefix e e',
          prefix_star_event_steps (rcons prefix e) ->
          event_step_from_regfile_mem (register_file_of_event_inform e) (mem_of_event_inform e) e' ->
          prefix_star_event_steps (rcons (rcons prefix e) e').

    (* TO BE CONTINUED *)

    Definition well_formed_intermediate_prefix (pref: trace event_inform) : Prop :=
      prefix_star_event_steps pref.

    Lemma well_formed_intermediate_prefix_inv:
      forall prefix suffix,
        well_formed_intermediate_prefix (prefix ++ suffix) ->
        well_formed_intermediate_prefix prefix.
    Proof.
      move=> prefix suffix.
      elim: suffix prefix => [prefix | a l IH].
      - by rewrite cats0.
      - move=> prefix.
        rewrite -cat_rcons => /IH IH'.
        inversion IH'.
        + now destruct prefix.
        + have: (e = a /\ prefix = nil).
          { destruct prefix. inversion H; split; congruence.
            inversion H. now destruct prefix. }
          move=> [] ? ?; subst. constructor.
        + eapply rcons_inj in H. inversion H; subst; clear H.
          inversion IH'; subst; clear IH'.
          * now destruct prefix0.
          * now destruct prefix0.
          * eauto.
    Qed.

    (* AEK: Now not sure whether this definition should be called a postcondition.   *)
    (* The reason I am not sure is that the r that we are projecting out of an event *)
    (* e is NOT the register file *after* executing e. It is the register file       *)
    (* *before* executing e.                                                         *)
    Definition postcondition_event_registers (e: event_inform) (mem: Memory.t): Prop :=
        let regs := register_file_of_event_inform e in
        forall reg n,
          reg_offset (CS.CS.reg_to_Ereg reg) = n ->
          exists v v',
            Memory.load mem (Permission.data, next_comp_of_event e, Block.local, n) = Some v  /\
            shift_value_option (uniform_shift 1) all_zeros_shift v = Some v' /\
            Machine.Intermediate.Register.get reg regs = v'.

(*
    Definition postcondition_event_memory_steadystate
               (e: event_inform) (mem': Memory.t) (C: Component.id) :=
      postcondition_event_snapshot_steadystate e mem' C /\
      postcondition_event_registers e mem'.

    Definition postcondition_event_memory_uninitialized
               (e: event_inform) (mem': Memory.t) (C: Component.id) :=
      postcondition_event_snapshot_uninitialized e mem' C /\
      postcondition_event_registers e mem'.
*)  

    Definition postcondition_event_registers_ini (C: Component.id) (mem: Memory.t): Prop :=
        forall (R: Machine.register) (n: Z),
          reg_offset (Intermediate.CS.CS.reg_to_Ereg R) = n ->
          Memory.load mem (Permission.data, C, Block.local, n) = Some Undef.

    Definition postcondition_steady_state
               (e: event_inform) (mem: Memory.t) (C: Component.id) :=
      Memory.load mem (Permission.data, C, Block.local, INITFLAG_offset) =
      Some (Int 1%Z)
      /\
      Memory.load mem (Permission.data, C, Block.local, LOCALBUF_offset) =
      Some (Ptr (Permission.data, C, LOCALBUF_blockid, 0%Z))
      /\
      postcondition_event_snapshot_steadystate e mem C.

    Definition postcondition_uninitialized
               (e: event_inform) (mem: Memory.t) (C: Component.id) :=
      Memory.load mem (Permission.data, C, Block.local, INITFLAG_offset) =
      Some (Int 0%Z)
      /\
      Memory.load mem (Permission.data, C, Block.local, LOCALBUF_offset) = Some Undef
      /\
      postcondition_event_snapshot_uninitialized e mem C.

    Record well_formed_memory (prefix: trace event_inform) (mem: Memory.t) : Prop :=
      {
        wfmem_counter:
          forall C,
            component_buffer C ->
            Memory.load mem (Permission.data, C, Block.local, 0%Z) =
            Some (Int (counter_value C prefix));
        wfmem_extcall_ini:
          prefix = [] ->
          (forall C,
              component_buffer C ->
              C = Component.main ->
              Memory.load mem (Permission.data, C, Block.local, EXTCALL_offset) =
              Some (Int 0%Z)) /\
          (forall C,
              component_buffer C ->
              C <> Component.main ->
              Memory.load mem (Permission.data, C, Block.local, EXTCALL_offset) =
              Some (Int 1%Z));
        wfmem_extcall:
          forall prefix' e,
            prefix = prefix' ++ [:: e] ->
            (forall C,
                component_buffer C ->
                C = next_comp_of_event e ->
                Memory.load mem (Permission.data, C, Block.local, EXTCALL_offset) =
                Some (Int 0%Z)) /\
            (forall C,
                component_buffer C ->
                C <> next_comp_of_event e ->
                Memory.load mem (Permission.data, C, Block.local, EXTCALL_offset) =
                Some (Int 1%Z));
        (* NOTE: Might be redundant? *)
        wfmem_meta:
          forall C r,
            component_buffer C ->
          exists v,
            Memory.load mem (Permission.data, C, Block.local, reg_offset r) = Some v;
        (* NOTE: Reuse memory relation (renaming). *)
        (* Precondition: the memory must be in a state ready to execute the event [e] *)
        (* wfmem: forall prefix' e, *)
        (*     prefix = prefix' ++ [:: e] -> *)
        (*     precondition_event_memory e mem; *)
        (* NOTE: no, this is wrong. We need a post-condition: in what shape is the memory
         after having executed the event [e] *)
        wfmem_ini: forall C,
            prefix = [] ->
            postcondition_event_registers_ini C mem
            /\
            Memory.load mem (Permission.data, C, Block.local, INITFLAG_offset) =
            Some (Int 0%Z)
            /\
            Memory.load mem (Permission.data, C, Block.local, LOCALBUF_offset) =
            Some Undef
            /\
            (exists src_compMem : ComponentMemory.t,
                mem C = Some src_compMem /\
                ComponentMemory.next_block src_compMem = LOCALBUF_blockid)
        ;
        wfmem: forall prefix' e,
            prefix = prefix' ++ [:: e] ->
            postcondition_event_registers e mem
            /\
            (forall C,
                component_buffer C ->
                C = next_comp_of_event e ->
                postcondition_steady_state e mem C) /\
            (forall C,
                component_buffer C ->
                C <> next_comp_of_event e ->
                (
                  postcondition_steady_state e mem C
                  \/
                  postcondition_uninitialized e mem C
                )
            )
      }.

    (* NOTE: it doesn't preserve [well_formed_memory].*)

    (***********************************************
    Lemma well_formed_memory_star_postcondition:
      forall p cs prefix e mem,
        mem = CS.s_memory cs ->
        well_formed_memory (prefix ++ [:: e]) mem ->
        exists cs',
          Star (CS.sem p) cs (project_non_inform [:: e]) cs' /\
          postcondition_event_memory e (CS.s_memory cs').
    Admitted.
    *****************************************************)

    Lemma counter_value_snoc prefix C e :
      counter_value C (prefix ++ [e])
      = (counter_value C prefix
        + if C == cur_comp_of_event e then 1 else 0) % Z.
    Proof.
      unfold counter_value, comp_subtrace.
      rewrite filter_cat app_length. simpl.
      rewrite Nat2Z.inj_add.
      now destruct (_ == _).
    Qed.

    (* RB: TODO: Relocate, replace existing but less general
       [rcons_trace_event_eq_inversion] with second lemma. *)
    Lemma size_inj :
      forall {A} (l1 l2 : list A), l1 = l2 -> size l1 = size l2.
    Proof.
      intros A l1 l2 Heq; subst l2. reflexivity.
    Qed.

    Lemma rcons_inv :
      forall {A} (l1 l2 : list A) e1 e2,
        l1 ++ [e1] = l2 ++ [e2] ->
        l1 = l2 /\ e1 = e2.
    Proof.
      intros A l1.
      induction l1 as [| e l1' IHl1'];
        simpl;
        intros l2 e1 e2 Heq.
      - destruct l2 as [| e' l2'].
        + injection Heq as Heq; subst e2.
          split; reflexivity.
        + inversion Heq as [[Heq1 Heq2]]; subst.
          apply size_inj in Heq2.
          rewrite cats1 size_rcons in Heq2.
          discriminate.
      - destruct l2 as [| e' l2'].
        + inversion Heq as [[Heq1 Heq2]]; subst e2.
          apply size_inj in Heq2.
          rewrite cats1 size_rcons in Heq2.
          discriminate.
        + injection Heq as ? Heq; subst e'.
          specialize (IHl1' l2' e1 e2 Heq) as [? ?]; subst e2 l2'.
          split; reflexivity.
    Qed.

    (* FIXME *)
    (* Lemma well_formed_memory_store_counter prefix mem C e : *)
    (*   component_buffer C -> *)
    (*   well_formed_memory prefix mem -> *)
    (*   C = cur_comp_of_event e -> *)
    (*   well_formed_memory_event e mem -> *)
    (*   exists mem', *)
    (*     Memory.store mem (Permission.data, C, Block.local, 0%Z) *)
    (*                  (Int (counter_value C (prefix ++ [e]))) = Some mem' /\ *)
    (*     well_formed_memory (prefix ++ [e]) mem'. *)
    (* Proof. *)
    (*   move=> C_b (*wf_mem*) HC He. *)
    (*   have C_local := (wfmem_counter (*wf_mem*)) _ C_b. *)
    (*   specialize (C_local _ _ HC). *)
    (*   have [mem' Hmem'] := Memory.store_after_load *)
    (*                          _ _ _ (Int (counter_value C (prefix ++ [e]))) *)
    (*                          C_local. *)
    (*   exists mem'. split; [now trivial |]. constructor. *)
    (*   - move=> C' C'_b. *)
    (*     (* exists mem'. split; trivial=> C' C'_b. *) *)
    (*     have C'_local := wfmem_counter _ C'_b. *)
    (*     specialize (C'_local _ _ HC). *)
    (*     rewrite <- Hmem'. *)
    (*     rewrite -> counter_value_snoc, <- HC, Nat.eqb_refl in *. *)
    (*     case: (altP (C' =P C)) => [?|C_neq_C']. *)
    (*     + subst C'. *)
    (*       by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem'). *)
    (*     + have neq : (Permission.data, C, Block.local, 0%Z) <> *)
    (*                  (Permission.data, C', Block.local, 0%Z) *)
    (*         by move/eqP in C_neq_C'; congruence. *)
    (*       rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem'). *)
    (*       now rewrite Z.add_0_r. *)
    (*   - move=> C' r C'_b. *)
    (*     destruct ((wfmem_meta wf_mem) C' r C'_b) as [v Hload]. *)
    (*     exists v. *)
    (*     erewrite Memory.load_after_store_neq; try eassumption. *)
    (*     intros Hcontra. injection Hcontra as Hcomp Hoffset. *)
    (*     now destruct r. *)
    (*   - move=> prefix' Csrc P arg mem'' regs Cdst Hprefix C'_b. *)
    (*     apply rcons_inv in Hprefix as [? ?]; subst prefix' e. *)
    (*     inversion He as [Hsnap Harg]. *)
    (*     split. *)
    (*     + eapply metadata_store_preserves_snapshot; eassumption. *)
    (*     + erewrite Memory.load_after_store_neq; try eassumption. *)
    (*       now injection. *)
    (*   - move=> prefix' Csrc ret mem'' regs Cdst Hprefix C'_b. *)
    (*     apply rcons_inv in Hprefix as [? ?]; subst prefix' e. *)
    (*     inversion He as [Hsnap Hret]. *)
    (*     split. *)
    (*     + eapply metadata_store_preserves_snapshot; eassumption. *)
    (*     + erewrite Memory.load_after_store_neq; try eassumption. *)
    (*       now injection. *)
    (*   - move=> prefix' C' rptr rsize mem'' regs Hprefix C'_b. *)
    (*     apply rcons_inv in Hprefix as [? ?]; subst prefix' e. *)
    (*     inversion He as [size [Hsize Hload]]. *)
    (*     exists size. split. *)
    (*     + eassumption. *)
    (*     + erewrite Memory.load_after_store_neq; try eassumption. *)
    (*       injection as _ Hoffset. now destruct rsize. *)
    (* Qed. *)

    Lemma well_formed_memory_store_reg_offset prefix mem C r v :
      component_buffer C ->
      well_formed_memory prefix mem ->
    exists mem',
      Memory.store mem (Permission.data, C, Block.local, reg_offset r) v = Some mem'.
    Proof.
      intros C_b wf_mem.
      specialize ((wfmem_meta wf_mem) _ r C_b) as [v' Hload].
      eapply Memory.store_after_load.
      exact Hload.
    Qed.

    Variant well_formed_state (stk_st: stack_state)
            (prefix suffix: trace event_inform) : CS.state -> Prop :=
    | WellFormedState C procs stk mem k exp arg P
      of C = cur_comp stk_st
      &  k = Kstop
      &  exp = procedure_of_trace C P t
      &  well_bracketed_trace stk_st suffix
      &  all (well_formed_event intf procs) suffix
      &  well_formed_stack stk_st stk
      &  well_formed_memory prefix mem
      &  valid_procedure C P
      :  well_formed_state stk_st prefix suffix [CState C, stk, mem, k, exp, arg].

  (* [DynShare] Rephrase state well-formedness invariants in terms of reverse
     executions. This version still preserves the intermediate stack state.
     TODO: This part needs to be trimmed down, and naming conventions
     homogenized. *)
  Variant well_formed_state_r (stk_st: stack_state)
          (prefix suffix: trace event_inform) : CS.state -> Prop :=
  | WellFormedStateR C procs stk mem k exp arg P
    of C = cur_comp stk_st
    &  k = Kstop
    (* &  exp = procedure_of_trace C P t *)
    &  exp = expr_of_trace C P (comp_subtrace C t)
    &  well_bracketed_trace stk_st suffix
    &  all (well_formed_event intf procs) suffix
    &  well_formed_stack stk_st stk
    &  well_formed_memory prefix mem
    &  valid_procedure C P
    :  well_formed_state_r stk_st prefix suffix [CState C, stk, mem, k, exp, arg].

  (* [DynShare] This second version of the right-to-left invariant does away
     with the stack state and effects further simplifications. Some bits,
     especially those that describe the memory, need to be fixed and restored.
     Note that, while this is still phrased in terms of a [suffix], this is
     actually meant to represent a whole trace, e.g., [t]. (However, this could
     make it tricky to compose partial invariants.) *)
  Variant well_formed_state_right (* stk_st: stack_state *)
          (suffix: trace event_inform) : CS.state -> Prop :=
  | WellFormedStateRight C procs stk mem k exp arg P
  of
  (* C = cur_comp stk_s & *)
     k = Kstop
  &  exp = procedure_of_trace C P t
  &  TracesInform.well_bracketed_trace_r suffix
  &  all (well_formed_event intf procs) suffix
  (* &  well_formed_stack stk_st stk *)
  (* &  well_formed_memory prefix mem *) (* FIXME *)
  &  valid_procedure C P
  :  well_formed_state_right (* stk_st *) suffix [CState C, stk, mem, k, exp, arg].

  (* NOTE: Do we need/want to split off memory invariants, etc., so that they
     hold at every step? *)

    (* [DynShare] We will probably need a variant of well formedness that is defined
     on non-informative traces as well. *)

    Variable metadata_size_lhs: Component.id -> nat.

    (* NOTE: Could we dispense with complex well-formed states by looking only
       at well-formedness of traces?

    Definition well_formed_prefix_suffix
               (prefix suffix : trace event_inform) : Prop.
    Admitted.

    Definition well_formed_trace (t : trace event_inform) : Prop :=
      forall prefix suffix,
        t = prefix ++ suffix ->
        well_formed_prefix_suffix prefix suffix.

    Lemma definability_gen_rel t_inform cs :
      well_formed_trace t_inform ->
      CS.initial_state p cs ->
    exists cs' t_noninform const_map,
      Star (CS.sem p) cs t_noninform cs' /\
      traces_shift_each_other metadata_size_lhs const_map (project_non_inform t_inform) t_noninform /\
      CS.final_state cs'.

       The point is that this is essentially the final definability lemma. The
       predictable challenges would reappear in its proof:
         - Would need to state a similar lemma without depending on an initial
           state (unless inducting "on the right"?).
         - Well-bracketedness would fail in the inductive case.

       The possible solutions involve some kind of decomposition of the trace
       into prefix and suffix, or directly relying on AAA's method.

       In any case, well-bracketedness is important for the proof *)

    (* TODO: Relocate *)
    Lemma Eregister_eq_dec :
      forall r1 r2 : Eregister, Decidable.decidable (r1 = r2).
    Proof.
      intros [] [];
        try (left; reflexivity);
        right; intro Hcontra; now inversion Hcontra.
    Qed.

    (* TODO: Relocate *)
    Remark Ereg_to_reg_to_Ereg r : Ereg_to_reg (CS.CS.reg_to_Ereg r) = r.
    Proof.
      now destruct r.
    Qed.

    (* TODO: Relocate *)
    Remark reg_to_Ereg_to_reg r : CS.CS.reg_to_Ereg (Ereg_to_reg r) = r.
    Proof.
      now destruct r.
    Qed.

    (* TODO: Relocate *)
    Remark cats2 {A} s (e1 e2 : A) :
      (s ++ [:: e1]) ++ [:: e2] = rcons (rcons s e1) e2.
    Proof.
      do 2 rewrite cats1. reflexivity.
    Qed.

    (* TODO: Relocate *)
    Remark cats2_inv {A} s s' (e1 e1' e2 e2' : A) :
      (s ++ [:: e1]) ++ [:: e2] = rcons (rcons s' e1') e2' ->
      s = s' /\ e1 = e1' /\ e2 = e2'.
    Proof.
      intro H.
      rewrite cats2 in H.
      apply rcons_inj in H.
      injection H as H ?.
      apply rcons_inj in H.
      injection H as H ?.
      auto.
    Qed.

    (* TODO: Relocate *)
    Remark reg_offset0 r : reg_offset r <> 0%Z.
    Proof.
      destruct r; discriminate.
    Qed.

    Remark pointer_reg_offset0
           (P : Permission.id) (C : Component.id) (b : Block.id) r :
      (P, C, b, reg_offset r) <> (P, C, b, 0%Z).
    Proof.
      injection. apply reg_offset0.
    Qed.

    (* TODO: Move to Memory, add more informative lemma on alloc pointers. *)
    Lemma permission_of_alloc_offset mem cid sz mem' ptr':
      Memory.alloc mem cid sz = Some (mem', ptr') ->
      Pointer.offset ptr' = 0%Z.
    Admitted.

    (* ... Like this one. *)
    Lemma pointer_of_alloc mem cid sz mem' ptr' nb:
      Memory.alloc mem cid sz = Some (mem', ptr') ->
      next_block mem cid = Some nb ->
      ptr' = (Permission.data, cid, nb, 0%Z).
    Admitted.

    (* (This is just here to easy things, maybe temporarily...) *)
    Lemma alloc_next_block mem cid sz mem' ptr':
      Memory.alloc mem cid sz = Some (mem', ptr') ->
    exists nb,
      next_block mem cid = Some nb.
    Admitted.

    (* TODO: Lift to Memory. *)
    Lemma next_block_alloc m C n m' b:
      Memory.alloc m C n = Some (m', b) ->
      next_block m C = Some (Pointer.block b) /\
      next_block m' C = Some (ssrnat.addn (Pointer.block b) 1).
    Admitted.

    (* TODO: Lift to Memory. *)
    Lemma next_block_alloc_neq m C n m' b C' :
      Memory.alloc m C n = Some (m', b) ->
      C' <> C ->
      next_block m' C' = next_block m C'.
    Admitted.

    Lemma shift_S_Some C b :
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid (uniform_shift 1) all_zeros_shift)
        (C, S b) = Some (C, b).
    Proof.
      rewrite /sigma_shifting_wrap_bid_in_addr
              /sigma_shifting_lefttoright_addr_bid
              /sigma_shifting_lefttoright_option
              /all_zeros_shift /uniform_shift
              /ssrnat.leq
              /ssrnat.addn /ssrnat.addn_rec
              /ssrnat.subn /ssrnat.subn_rec
              /=
              Nat.add_0_r Nat.sub_0_r.
      reflexivity.
    Qed.

    (* NOTE: Should live in Memory *)
    Lemma component_memory_after_store_neq mem ptr v mem' C :
      Memory.store mem ptr v = Some mem' ->
      Pointer.component ptr <> C ->
      mem C = mem' C.
    Admitted.

    (* NOTE: Should live in Memory *)
    Lemma component_memory_after_alloc_neq mem C sz mem' ptr C' :
      Memory.alloc mem C sz = Some (mem', ptr) ->
      C' <> C ->
      mem C' = mem' C'.
    Admitted.

    (* TODO: [DynShare] Trace relation should appear here too!

       Well-bracketedness, etc., probably need to be rewritten to operate "in
       reverse", i.e., adding events at the end of the trace to match the
       definition of the trace relation.

       NOTE: Propositional and not boolean conjunction in the conclusion at the
       moment. *)

    Lemma wfmem_postcondition_initial_preserved
          eprev ecur curC (mem' mem0 mem'': Memory.t):
      mem' = mem_of_event_inform eprev ->
      mem' = mem_of_event_inform ecur ->
      next_comp_of_event eprev = curC ->
      cur_comp_of_event ecur = curC ->
      next_comp_of_event ecur = curC ->
      (forall C : nat_ordType,
          component_buffer C ->
          C <> next_comp_of_event eprev ->
          postcondition_steady_state eprev mem0 C \/
          postcondition_uninitialized eprev mem0 C
      ) ->
      (forall C : Component.id, C <> curC -> mem0 C = mem'' C)
      ->
      forall C : nat_ordType,
        component_buffer C ->
        C <> next_comp_of_event ecur ->
        postcondition_steady_state ecur mem'' C \/
        postcondition_uninitialized ecur mem'' C.
    Proof.
      intros Hmem' Hmem'2 Hcomp1 Hcomp2 Hcomp3 Hinitial mem0_mem''_asmp.

      assert (mem0_mem'': forall C b o,
                 C <> curC ->
                 Memory.load mem0  (Permission.data, C, b, o) =
                 Memory.load mem'' (Permission.data, C, b, o)
             ).
      {
        intros ? ? ? HC.
        unfold Memory.load; simpl.
        rewrite mem0_mem''_asmp; by auto.
      }

      intros C' Hcomp Hnext. subst.
      rewrite Hcomp3 in Hnext.
      specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
      * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
        left. split; [| split].
        -- rewrite -mem0_mem''; by auto.
        -- rewrite -mem0_mem''; by auto.
        -- unfold postcondition_event_snapshot_steadystate
            in *.
           destruct Hsteady' as [Hsteady' Hnextblock].
           split.
           ++ intros b Hlocal.
              specialize (Hsteady' b Hlocal)
                as [Cb [Hshift' [Hrename Hrename']]].
              exists Cb. split; [| split].
              ** exact Hshift'.
              ** intros off v' Hload. simpl in *.
                 rewrite <- mem0_mem'' in Hload; last by auto.
                 specialize (Hrename off v' Hload)
                   as [v'' [Hload'' Hrename]].
                 exists v''. split; congruence.
              ** intros off v' Hload. rewrite -Hmem'2 in Hload.
                 specialize (Hrename' off v' Hload)
                   as [v'' [Hload'' Hrename']].
                 exists v''. split; simpl.
                 --- rewrite <- mem0_mem''; by auto.
                 --- assumption.
           ++ intros b Hnextb.
              unfold next_block.
              rewrite -(mem0_mem''_asmp _ Hnext).
              apply Hnextblock.
              rewrite Hmem'2.
              assumption.
      * destruct Hinitial
          as [Hinitflag [Hlocalbuf [
                             [compMem [buf [He1 Hbuf]]]
                               Hintial2
                           ]
             ]].
        right. split; [| split].
        -- rewrite -mem0_mem''; by auto.
        -- rewrite -mem0_mem''; by auto. 
        -- unfold postcondition_event_snapshot_uninitialized
            in *.
           split;
             last by rewrite -mem0_mem''_asmp.
           simpl. exists compMem, buf. by rewrite -Hmem'2.
    Qed.

    (* k = (Kseq (extcall_check;; expr_of_trace C P (comp_subtrace C t)) Kstop) *)
    (* stk_st = {| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: stk *)
    (* mem = mem4 *)
    Lemma exec_init_local_buffer_expr C stk_st mem k bnew :
      exists mem',
        star CS.kstep (prepare_global_env p)
             [CState C, stk_st, mem,  Kseq (init_local_buffer_expr C) k, E_val (Ptr (Permission.data, C, bnew, 0%Z)), Int 0]
             E0
             [CState C, stk_st, mem',                                 k, E_val (Int 1),                               Int 0] /\
        Memory.store mem (Permission.data, C, Block.local, INITFLAG_offset%Z) (Int 1) = Some mem'.
    Admitted.

    Ltac ucongruence := autounfold with definabilitydb; congruence.

    Ltac simplify_memory :=
      repeat (
          match goal with
          | H: Memory.store _ ?ptr ?v' = Some ?mem |-
            Memory.load ?mem ?ptr = Some ?v =>
            rewrite (Memory.load_after_store_eq _ _ _ _ H);
            try (simpl; ucongruence);
            eauto
          | H: Memory.store _ ?ptr _ = Some ?mem |-
            Memory.load ?mem ?ptr' = Some _ =>
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H);
            try (simpl; ucongruence);
            eauto
          | H: Memory.alloc _ _ _ = Some (?mem, _) |-
            Memory.load ?mem _ = Some _ =>
            erewrite Memory.load_after_alloc;
            eauto;
            try (simpl; ucongruence)
          end).

    (* A proof of relational definability on the right. Existential
      quantification is extended to [cs] and [s], and induction performed on
      the prefix, executing from the initial state. Separately, execution to a
      final state needs to be established. *)
    Lemma definability_gen_rel_right prefix suffix :
      well_bracketed_trace {| cur_comp := Component.main; callers := [::] |} t ->
      well_formed_intermediate_prefix t ->
      t = prefix ++ suffix ->
    exists cs s prefix_inform prefix' const_map,
      Star (CS.sem p) (CS.initial_machine_state p) prefix' cs /\
      project_non_inform prefix_inform = prefix' /\
      traces_shift_each_other_option metadata_size_lhs const_map (project_non_inform prefix) prefix' /\
      well_formed_state_r s prefix suffix cs.
    Proof.
      (*
      Ltac solve_load_from_Halloc :=
        erewrite Memory.load_after_alloc; eauto; by autounfold with definabilitydb.

      Ltac solve_neq :=
        simpl; by autounfold with definabilitydb.
      *)
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = Source.prog_procedures p
        by [].
      (* Proof by induction on the prefix. Prior to inducting, generalize on
         the suffix. *)
      move=> wb_trace wf_int_pref.
      elim/rev_ind: prefix suffix => [|e prefix IH] /= suffix.
      - (* Base case. *)
        move=> <-.

        assert (Hmain_buffers_p: Component.main \in domm (Source.prog_buffers p)).
        {
          unfold p, program_of_trace. simpl.
          apply/dommP. rewrite mapmE.
          destruct (intf Component.main); last discriminate. simpl. eauto.
        }

        assert (ini_mem_regs: forall reg,
                   Memory.load (Source.prepare_buffers p)
                               (Permission.data, Component.main,
                                Block.local, reg_offset reg) = Some Undef).
        {
          (** Follows from the definition of meta_buffer. *)
          intros. unfold p, program_of_trace, Source.prepare_buffers, Memory.load.
          simpl. rewrite !mapmE.
          destruct (intf Component.main); last discriminate; auto.
          simpl. by destruct reg; rewrite ComponentMemory.load_prealloc setmE.
        }

        assert (init_mem_EXTCALL_offet:
                  Memory.load
                    (Source.prepare_buffers p)
                    (Permission.data, Component.main, Block.local, EXTCALL_offset) =
                  Some (Int 1)
               ).
        {
          (** Follows from the definition of meta_buffer. *)
          unfold p, program_of_trace, Source.prepare_buffers, Memory.load.
          simpl. rewrite !mapmE.
          destruct (intf Component.main); last discriminate; auto.
          simpl. by rewrite ComponentMemory.load_prealloc setmE.
        }

        assert (exists compMem, (Source.prepare_buffers p) Component.main =
                                  Some compMem) as [compMem HcompMem].
        {
          unfold Source.prepare_buffers.
          apply/dommP. by rewrite domm_map.
        }
        destruct (ComponentMemory.alloc
                    compMem
                    (Z.to_nat (Z.of_nat (buffer_size Component.main))))
          as [compMem' bfresh] eqn:eAllocCompMem.

        assert (Halloc: Memory.alloc
                          (Source.prepare_buffers p)
                          Component.main
                          (Z.to_nat (Z.of_nat (buffer_size Component.main))) =
                        Some
                          (setm (Source.prepare_buffers p) Component.main compMem',
                           (Permission.data, Component.main, bfresh, 0%Z))
               ).
        {
          unfold Memory.alloc; rewrite HcompMem eAllocCompMem; reflexivity.
        }

        assert (bfresh = 1).
        {
          unfold Source.prepare_buffers, p in HcompMem.
          move : Hmain_buffers_p => /dommP => G.
          destruct G as [buf Hbuf]. unfold p in Hbuf.
          rewrite mapmE Hbuf in HcompMem. simpl in HcompMem.
          inversion HcompMem. subst compMem. clear HcompMem.
          specialize (ComponentMemory.nextblock_prealloc (setm emptym 0 buf)) as G.
          specialize (ComponentMemory.next_block_alloc _ _ _ _ eAllocCompMem)
            as [G' _].
          rewrite G domm_set domm0 fsetU0 in G'. by simpl in G'.
        }
        subst bfresh.

        assert (exists buf_main, prog_buffers Component.main = Some buf_main)
          as [buf_main Hbuf_main].
          by (apply/dommP; rewrite <- domm_buffers; apply/dommP;
              destruct (intf Component.main); last discriminate; eauto).

        assert (Hbufsize: (Z.of_nat (buffer_size Component.main) > 0)%Z).
        {
          specialize (wf_buffers Hbuf_main).
          unfold buffer_size. rewrite Hbuf_main.
          destruct buf_main; simpl in *.
          - rewrite size_nseq -Nat2Z.inj_0.
            apply inj_gt. by apply Nat.ltb_lt in wf_buffers.
          - rewrite -Nat2Z.inj_0. apply inj_gt.
            move: wf_buffers => /andP. intros [G _]. by apply Nat.ltb_lt in G.
        }

        assert (exists mem_localbufptr,
                   Memory.store
                     (setm (Source.prepare_buffers p) Component.main compMem')
                     (Permission.data, Component.main,
                      Block.local, (0 + LOCALBUF_offset)%Z)
                     (Ptr (Permission.data, Component.main, 1, 0%Z)) =
                   Some mem_localbufptr) as [mem_localbufptr Hstoreptr].
        {
          eapply Memory.store_after_load.
          erewrite Memory.load_after_alloc; eauto; simpl.
          - unfold Source.prepare_buffers, p.
            move : Hmain_buffers_p => /dommP => G.
            destruct G as [buf Hbuf]. unfold p in Hbuf.
            unfold Memory.load. simpl.
            rewrite mapmE Hbuf. simpl.
            rewrite ComponentMemory.load_prealloc setmE. simpl.
            rewrite mapmE in Hbuf.
            destruct (intf Component.main); last discriminate; auto.
            simpl in Hbuf. inversion Hbuf. by simpl.
          - unfold Block.local. discriminate.
        }

        destruct (Memory.store_after_load
                    mem_localbufptr
                    (Permission.data, Component.main, Block.local, reg_offset E_R_ONE)
                    Undef Undef) as [mem1 Hmem1]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem1
                    (Permission.data, Component.main, Block.local, reg_offset E_R_AUX1)
                    Undef Undef) as [mem2 Hmem2]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem2
                    (Permission.data, Component.main,
                     Block.local, reg_offset E_R_AUX2)
                    Undef Undef) as [mem3 Hmem3]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem3
                    (Permission.data, Component.main,
                     Block.local, reg_offset E_R_RA)
                    Undef Undef) as [mem4 Hmem4]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem4
                    (Permission.data, Component.main,
                     Block.local, reg_offset E_R_SP)
                    Undef Undef) as [mem5 Hmem5]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem5
                    (Permission.data, Component.main,
                     Block.local, reg_offset E_R_ARG)
                    Undef Undef) as [mem6 Hmem6]; eauto; simplify_memory.

        destruct (Memory.store_after_load
                    mem6
                    (Permission.data, Component.main,
                     Block.local, EXTCALL_offset)
                    (Int 1%Z) (Int 0%Z)) as [mem7 Hmem7]; simplify_memory.

        exists (CS.State (Component.main)
                    [:: ]
                    mem7
                    Kstop
                    (expr_of_trace Component.main Procedure.main
                                   (comp_subtrace Component.main t))
                    (Int 0%Z)).
        exists (StackState Component.main []), E0, E0, (uniform_shift 1).
        split; [| split; [| split]].
        + rewrite /CS.initial_machine_state /Source.prog_main
                  find_procedures_of_trace_main.
          take_steps; simpl; auto; simplify_memory.

          {
            instantiate (1 := Int 0%Z).
            (** Follows from the definition of meta_buffer. *)
            unfold p, program_of_trace, Source.prepare_buffers, Memory.load.
            simpl. rewrite !mapmE.
            destruct (intf Component.main); last discriminate; auto.
            simpl. by rewrite ComponentMemory.load_prealloc setmE.
          }

          take_steps; simpl.
          {
            exact Hbufsize.
          }
          {
            exact Halloc.
          }

          take_steps; auto; simplify_memory.
          {
            exact Hstoreptr.
          }

          take_steps.
          (** About to execute "init_local_buffer_expr Component.main" *)
          (*****************************************
          unfold init_local_buffer_expr, copy_local_datum_expr.

          rewrite bigop.foldrE.
          Search _ bigop.BigOp.bigop.
          (* induction ??  using bigop.big_ind[|2|3]. *)
          remember (buffer_size Component.main) as bufsize.
          generalize dependent bufsize.
          intros ? ?.
          induction bufsize.
          {
            (** base case; contra to Hbufsize *)
            by auto.
          }
          {
            Search _ foldr.
          }
          Search _ foldr.
          
          rewrite foldr_map.
          take_steps.
          ******************************************************)
          admit.
        + reflexivity.
        + now do 2 constructor.
        + econstructor; eauto.
          (* unfold CS.initial_machine_state, Source.prog_main. *)
          (* rewrite find_procedures_of_trace_main. *)
          (* econstructor; eauto. *)
          * admit. (* Easy: should be an assumption about t. *)
          * now exists [], [].
          * constructor.
            -- move=> C H.
               simplify_memory.
               move: H.
               rewrite /component_buffer /Memory.load //= mapmE // mapmE mem_domm.
               case HCint: (intf C) => [Cint|] //=.
               by rewrite ComponentMemory.load_prealloc.
            -- simpl in *.
               move=> _. split.
               ++ move=> ? ? ?; subst.
                  simplify_memory.
               ++ move=> ? ? ?; subst.
                  simplify_memory.
                  (** Follows from the definition of meta_buffer. *)
                  admit.
            -- by move=> [].
            (* -- admit. *)
            -- move=> C r H.
               destruct (C == Component.main) eqn:Heq.
               ++ move: Heq => /eqP Heq; subst C.
                  destruct r; simpl in *; eexists; simplify_memory.
                  (** Follows from the definition of meta_buffer. *)
                  admit.
               ++ move: Heq => /eqP Heq.
                  destruct r; simpl in *; eexists; simplify_memory.
                  (** All follow from the definition of meta_buffer. *)
                  all: admit.
            -- move=> C _.
               split; [| split; [| split]].
               ++ move=> R n ?; subst n.
                  destruct (C == Component.main) eqn:Heq.
                  ** move: Heq => /eqP Heq; subst C.
                     destruct R; simpl in *; simplify_memory.
                     admit.
                  ** move: Heq => /eqP Heq.
                     destruct R; simpl in *; simplify_memory.
                     all: admit.
               ++ admit.
               ++ admit.
               ++ admit.
            -- by move=> [].
          * unfold valid_procedure. now auto.
    - (* Inductive step. *)
      rewrite -catA => Et.
      assert (wf_int_pref' : well_formed_intermediate_prefix (prefix ++ [:: e])).
      { rewrite Et in wf_int_pref.
        eapply well_formed_intermediate_prefix_inv.
        rewrite -catA. eauto. }
      assert (wf_int_pref'' : well_formed_intermediate_prefix prefix).
      { eapply well_formed_intermediate_prefix_inv. eauto. }
      specialize (IH (e :: suffix) Et) as
          [cs [s [prefix_inform [prefix' [const_map [Star0 [Hproj [Hshift Hwf_cs]]]]]]]].

      move: Hwf_cs Star0.
(* FIXME *)
      (* case: cs / => /= _ procs stk mem _ _ arg P -> -> -> [] wb /andP [wf_e wf_suffix] wf_stk wf_mem P_exp. *)
      case: cs / => /= _ procs stk mem _ _ arg P -> -> -> [] /andP [[]] /eqP wf_C_orig wb /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.

      move=> Star0.

      have C_b := valid_procedure_has_block P_exp.
      have C_local := wfmem_counter _ C_b.
      specialize (C_local _ _ wf_mem).
      (* have wf_C: cur_comp s = cur_comp_of_event e *)
      (*   by move: wb => /andP => [[]] => /eqP ->. *)

      have wf_C: cur_comp s = cur_comp_of_event e
        by (rewrite wf_C_orig; reflexivity).

      (* Requires reasoning about the memories *)
      (* have wf_mem_e: well_formed_memory_event e mem by admit. *)
      (* destruct (well_formed_memory_store_counter C_b wf_mem wf_C wf_mem_e) as *)
      (*     [mem' [Hmem' wf_mem']]. *)

      set C := cur_comp s.
      (* FIXME: The event may modify the memory, the store needs to take place
         in that memory, after the event has been "executed". *)
      (* assert (exists mem', *)
      (*            Memory.store mem (Permission.data, C, Block.local, 0%Z) (Int (counter_value C (prefix ++ [:: e]))) = Some mem' /\ *)
      (*            well_formed_memory (prefix ++ [:: e]) mem') *)
      (*   as [mem' [Hmem' wf_mem']] *)
      (*   by admit. *)
      assert (exists mem',
                 Memory.store mem (Permission.data, C, Block.local, 0%Z) (Int (counter_value C (prefix ++ [:: e]))) = Some mem')
        as [mem' Hmem'].
      { eapply Memory.store_after_load. eauto. }

      (* We can simulate the event-producing step as the concatenation
         of three successive stars:

          1. By the IH, an initial star that produces the prefix.

          2. A silent star preceding the event.

          3. A star that contains a step that produces the event
             (which at the source level may now be silent).

           The second star, running up to the point where we are ready
           to execute the proper expression associated with the event
           of interest, is fairly simple to establish. *)

      (* NOTE: The base case was simple, but complications arise in the
         recursive case. The first star can be proved as before, but is it
         exactly what we need? *)

      assert (Star1 : Star (CS.sem p)
                           [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                           [CState C, stk, mem', Kstop, expr_of_event C P e, arg]).
      { unfold expr_of_trace. rewrite Et 2!comp_subtrace_app. (*simpl.*)
        do 2 setoid_rewrite map_app.
        (* rewrite <- wf_C, Nat.eqb_refl, map_app. simpl. *)
        (* Check Nat.eqb_refl. unfold C. Check map_app. *)
        assert (H := @switch_spec p Permission.data C  stk mem
                                  (map (expr_of_event C P) (comp_subtrace C prefix))
                                  (expr_of_event C P e)
                                  (map (expr_of_event C P) (comp_subtrace C suffix))
                                  E_exit arg).
        (* specialize (C_local prefix mem wf_mem). *)
        rewrite map_length in H. specialize (H C_local).
        destruct H as [mem'' [Hmem'' Hstar]].
        assert (Heq : List.map (expr_of_event C P) (comp_subtrace C [:: e]) =
                      [:: expr_of_event C P e]).
        {
          rewrite /C wf_C /=. now setoid_rewrite Nat.eqb_refl.
        }
        rewrite Heq.
        enough (H : mem'' = mem') by (subst mem''; easy).
        rewrite -> counter_value_snoc in Hmem'.
        unfold cur_comp_of_event in Hmem'.
        simpl in Hmem'.
        unfold C in Hmem'.
        rewrite -> wf_C in Hmem'.
        (* rewrite <- wf_C in Hmem'. *)
        rewrite eq_refl in Hmem'.
        rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
        unfold counter_value in *.

        rewrite <- wf_C in Hmem'. unfold C in Hmem''.
        rewrite Hmem' in Hmem''.
        congruence. }

      (* TODO: Probably split into a separate lemma (after it is in better
         shape). *)
      assert (Star2 : exists e' s' cs',
                 Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] (event_non_inform_of [:: e']) cs' /\
                 well_formed_state_r s' (prefix ++ [e]) suffix cs' (* TODO: [e']? *)
             (* /\ e ~ e' *)
             (* NOTE: Here, too, we may need additional conjuncts... *)
             ).
      {

        clear Star1 (*wf_mem*) C_local (*Hmem'*). revert mem' (*wf_mem'*) Hmem'. rename mem into mem0. intros mem (*wf_mem'*) Hmem.
        (* Case analysis on observable events, which in this rich setting
           extend to calls and returns and various memory accesses and related
           manipulations, of which only calls and returns are observable at
           both levels. *)
        destruct e as [C_ P' new_arg mem' regs C'|C_ ret_val mem' regs C' |C_ ptr v |C_ src dst|C_ |C_ |C_ |C_];
          simpl in wf_C, wf_e(*, wb_suffix*); subst C_.

        - (* ECall *)
          case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
          (* destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg]. *)
          simpl.
          pose proof (wfmem_extcall wf_mem) as [v Hv].

          pose proof (wfmem_meta wf_mem E_R_ONE C_b) as [v1 Hv1].
          pose proof (wfmem_meta wf_mem E_R_AUX1 C_b) as [v2 Hv2].
          pose proof (wfmem_meta wf_mem E_R_AUX2 C_b) as [v3 Hv3].
          pose proof (wfmem_meta wf_mem E_R_RA C_b) as [v4 Hv4].
          pose proof (wfmem_meta wf_mem E_R_SP C_b) as [v5 Hv5].
          pose proof (wfmem_meta wf_mem E_R_ARG C_b) as [v6 Hv6].
          pose proof (wfmem_meta wf_mem E_R_COM C_b) as [vcom Hvcom].

(* FIXME: Call event proof breaks here.
          exists (ECallInform C P' new_arg mem6 regs C'). (* TODO: new_arg? *)
          exists (StackState C' (C :: callers s)).
          have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).

          exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem6,
                  Kstop, procedure_of_trace C' P' t, new_arg].
          split.
          + (* Process memory invariant. *)
            (* destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg]. *)
            (* subst mem'. *)
            take_step.
Local Transparent loc_of_reg.
            unfold loc_of_reg.
            (* JT: TODO: I couldn't find how to prove this. I think we need an invariant
               that relates the current metadata in memory and the current registers - but
               I don't think it's defined yet *)
            do 84 (take_step; eauto).
Local Opaque loc_of_reg.
            take_step. eauto.

            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem6); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem5); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem4); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem3); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem2); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem1); try (simpl; congruence); eauto.
            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem); try (simpl; congruence); eauto.

            (* RB: TODO: At this precise moment the call is executed, so the
               two memories should be identical. And nothing has changed [mem]
               in the execution of the previous steps. *)
            apply star_one. simpl.
            apply CS.eval_kstep_sound. simpl.
            rewrite (negbTE C_ne_C').
            rewrite -> imported_procedure_iff in Himport. rewrite Himport.
            rewrite <- imported_procedure_iff in Himport.
            rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
            (* JT: instantiate [new_arg] with another value, which is related to [vcom]. *)
            (* We should be able to use the invariants to establish a relation between *)
            (* the content of R_COM and the argument *)
            admit.
            (* FIXME: Similar steps will break after this point. *)
          + econstructor; trivial.
            {
              exact wf_suffix. (* New subgoal. *)
            }
            { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
              eexists []; eexists; simpl; split; eauto.
              split; trivial.
              eexists arg, P, top, bot.
              by do 3 (split; trivial). }
            {
              (* clear -wf_mem Hmem. *)
              destruct wf_mem as [wfmem_counter wfmem_meta wfmem].
              constructor.
              - intros C_ Hcomp.
                (* TODO: Use [case]/reflection lemma. *)
                destruct (C == C_) eqn:Heq;
                  move: Heq => /eqP => Heq.
                + subst C_.
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem6); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem5); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem4); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem3); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem2); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem1); try (simpl; congruence).
                  now rewrite (Memory.load_after_store_eq _ _ _ _ Hmem); eauto.
                + rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem6); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem5); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem4); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem3); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem2); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem1); try (simpl; congruence).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem); try (simpl; congruence).
                  assert (ctr_eq: counter_value C_ (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C']) =
                         counter_value C_ prefix).
                  { unfold counter_value, comp_subtrace.
                    rewrite filter_cat. simpl.
                    suff: ((C_ == cur_comp s) = false) => [-> //=|]. rewrite cats0 //=.
                    apply /eqP.
                    unfold C in Heq. congruence. }
                  rewrite ctr_eq. now eapply wfmem_counter.
              - intros C_ r Hcomp.
                specialize (wfmem_meta _ r Hcomp) as [v Hload].
                admit. (* long case analysis on the register *)
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
                  as [Hprefix | [prefix_ [e_ Hprefix]]]
                  by admit;
                  subst prefix.
                + assert (prefix' = [::]) by admit; subst prefix'.
                  (* Missing invariant (or lemma on initial states?)... *)
                  admit.
                + specialize (wfmem _ _ Logic.eq_refl) as [Hsnapshot Hregs].
                  split.
                  * intros [cid bid] Hshared.
                    specialize (Hsnapshot (cid, bid) Hshared).
                    unfold memory_shifts_memory_at_shared_addr,
                    memory_renames_memory_at_shared_addr,
                    sigma_shifting_wrap_bid_in_addr,
                    sigma_shifting_lefttoright_addr_bid
                      in *.
                    destruct Hsnapshot as [[cid' bid'] [Hinj [Hrename Hrename']]].
                    injection Hinj as ? ?; subst cid' bid'.
                    assert (Hneq : ssrnat.addn (ssrnat.subn bid (all_zeros_shift cid)) (uniform_shift 1 cid) <> Block.local). {
                      rewrite ssrnat.addn1. discriminate.
                    }
                    have Hgood: left_block_id_good_for_shifting (all_zeros_shift cid) bid. {
                      unfold
                      left_block_id_good_for_shifting,
                      all_zeros_shift.
                      auto.
                    }
                    eapply sigma_lefttoright_Some_spec in Hgood as [rbid Hgood].
                    erewrite Hgood.
                    eexists. split; [| split].
                    -- reflexivity.
                    -- intros offset v Hload.
                       (* [e_]'s memory is that of the call event. *)
                       (* Extended trace well-formedness: *)
                       (* Is t a good trace? *)
                       simpl in *.
                       (* Calls do not modify the (shared) memory, therefore
                          these two should be identical. *)
                       assert (Hmem' : mem' = mem_of_event_inform e_) by admit.
                       subst mem'.
                       specialize (Hrename _ _ Hload) as [v' [Hload' Hrename]].
                       exists v'. split.
                       ++ (* NOTE: Lemmas on all_zeros_shift? *)
                          unfold all_zeros_shift, uniform_shift,
                                 sigma_shifting_lefttoright_option
                           in Hgood.
                          injection Hgood as ?; subst rbid.
                          admit.
                          (* erewrite Memory.load_after_store_neq; eauto. *)
                          (* rewrite ssrnat.addn1. discriminate. *)
                       ++ assumption.
                    -- (* "Symmetric" case
                          TODO: refactor *)
                       intros offset v Hload.
                       simpl in *.
                       assert (Hmem' : mem' = mem_of_event_inform e_).
                       { clear -wf_int_pref'.
                         move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
                         inversion wf_int_pref.
                         - now destruct prefix_.
                         - destruct prefix_. inversion H. simpl in H. now destruct prefix_.
                         - apply rcons_inj in H. inversion H; subst; clear H.
                           apply rcons_inj in H3. inversion H3; subst; clear H3.
                           inversion H1; subst; clear H1.
                           reflexivity.
                       }
                       subst mem'.
                       erewrite Memory.load_after_store in Hload; eauto.
                       unfold all_zeros_shift, uniform_shift,
                              sigma_shifting_lefttoright_option
                         in *.
                       injection Hgood as ?; subst rbid.
                       rewrite ssrnat.addn1 in Hload.
                       rewrite ssrnat.addn1 in Hrename'.
                       (* NOTE: [move: Hload. case: /ifP]? *)
                       move: Hload. case: ifP.
                       ++ move /eqP. discriminate.
                       ++ move => Heq Hload.
                          admit.
                          (* specialize (Hrename' _ _ Hload) as [v' [Hload' Hrename']]. *)
                          (* exists v'. split; assumption. *)
                  (* * intros reg off v Hoffset Hload. *)
                  * assert (Hmem' : mem' = mem_of_event_inform e_).
                    { clear -wf_int_pref'.
                      move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
                      inversion wf_int_pref.
                      - now destruct prefix_.
                      - destruct prefix_. inversion H. simpl in H. now destruct prefix_.
                      - apply rcons_inj in H. inversion H; subst; clear H.
                        apply rcons_inj in H3. inversion H3; subst; clear H3.
                        inversion H1; subst; clear H1.
                        reflexivity.
                    }
                    subst mem'.
                    simpl in *.
                    intros n v Hoffset Hload. subst.
                    unfold postcondition_event_registers in Hregs.
                    erewrite Memory.load_after_store_neq in Hload; eauto; try congruence.

                    inversion wf_int_pref'.
                    -- now destruct prefix_.
                    -- destruct prefix_. inversion H. now destruct prefix_.
                    -- rewrite cats1 in H. apply rcons_inj in H. inversion H; subst; clear H.
                       rewrite cats1 in H3. apply rcons_inj in H3; inversion H3; subst; clear H3.
                       inversion H1; subst; clear H1.

                       unfold Machine.Intermediate.Register.invalidate.
                       simpl.
                       eexists; split; eauto.
                       unfold all_zeros_shift, uniform_shift.
                       unfold Machine.Intermediate.Register.get; simpl.
                       destruct e_.
                       ++ specialize (Hregs 2%Z v Logic.eq_refl).
                          admit.
                       ++ specialize (Hregs Machine.R_COM 2%Z v Logic.eq_refl). simpl in Hregs.
                          unfold Machine.Intermediate.Register.get.
                          rewrite !setmE. simpl.
                          rewrite -setmE.
                         spec

                       (* Dead end: we need to prove that the memory was invalidated. *)

                       admit.
            }
            right. by apply: (closed_intf Himport).
            (* NOTE: These snippets continue to work, though they may incur
               modifications later on. *)
*)
          admit. admit.

        - (* EReturn *)
          admit.

        (* NOTE: ... And there is a series of new events to consider. *)

        - (* EConst *)
          (* Gather a few recurrent assumptions at the top. *)
          exists (EConst C ptr v s0 t0).

          (* destruct (well_formed_memory_store_reg_offset v ptr C_b wf_mem) *)
          (*   as [mem' Hstore]. *)
          (* assert (Hoffsetneq: (Permission.data, C, Block.local, 0%Z) <> *)
          (*                     (Permission.data, C, Block.local, reg_offset v)) *)
          (*   by (now destruct v). (* Lemma? *) *)
          (* assert (Hload : exists v', *)
          (*            Memory.load *)
          (*              mem0 (Permission.data, C, Block.local, reg_offset v) = Some v') *)
          (*   by (eapply Memory.store_some_load_some; eauto). *)
          (* setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) *)
          (*   in Hload. *)

          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]].
          {
            destruct prefix; first by auto.
            right. rewrite lastI -cats1. by eauto.
          }
          { (* Treat empty case separately. *)
            subst prefix. simpl in *.
            assert (Hmain : C = Component.main) by admit.

            destruct (wfmem_ini wf_mem C Logic.eq_refl)
              as [Hregs0 [Hload0init [Hload0local _]]].
            assert (Hload0v := Hregs0 (Ereg_to_reg v) _ Logic.eq_refl).
            rewrite reg_to_Ereg_to_reg in Hload0v.
            assert (Hload1v := Hload0v).
            erewrite <- Memory.load_after_store_neq in Hload1v;
              last exact Hmem;
              last (injection; now destruct v).
            destruct (proj1 (Memory.store_some_load_some _ _ ptr) (ex_intro _ _ Hload1v))
              as [mem2 Hstore2].
(*             assert (Hload1init := Hload0init). *)
(*             erewrite <- Memory.load_after_store_neq in Hload1init; *)
(*               last exact Hmem; *)
(*               last (injection; discriminate). *)
            destruct (Memory.alloc_after_load
                        _ _ _ _ _ _ (buffer_size C)
                        (Memory.load_after_store_eq _ _ _ _ Hstore2))
              as [mem3 [bnew [Hnewblock Halloc3]]].
            assert (Hload3local := Hload0local).
            erewrite <- Memory.load_after_store_neq in Hload3local;
              last exact Hmem;
              last (injection; discriminate).
            erewrite <- Memory.load_after_store_neq in Hload3local;
              last exact Hstore2;
              last (injection; now destruct v).
            erewrite <- Memory.load_after_alloc in Hload3local;
              [ | exact Halloc3 | injection; congruence].
            destruct (proj1 (Memory.store_some_load_some _ _ (Ptr (Permission.data, C, bnew, 0%Z))) (ex_intro _ _ Hload3local))
              as [mem4 Hstore4].
            destruct (exec_init_local_buffer_expr
                        C
                        ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: stk)
                        mem4
                        (Kseq (extcall_check;; expr_of_trace C P (comp_subtrace C t)) Kstop)
                        bnew) as [mem5 [Hstar_init Hstore5]].
            (* NOTE: Separate lemma? The execution only makes sense if C is main. *)
            (* assert (exists n, Memory.load mem0 (Permission.data, C, Block.local, EXTCALL_offset) = Some (Int n)) as [extcal Hload0extcall]. { *)
            (*   destruct (wfmem_extcall_ini wf_mem Logic.eq_refl) as [Hextmain Hector]. *)
            (*   destruct (Nat.eqb_spec C Component.main); *)
            (*     eauto. *)
            (* } *)
            assert (Hload0extcall := proj1 (wfmem_extcall_ini wf_mem Logic.eq_refl) _ C_b Hmain).

            destruct ptr as [n | ptr |];
              exists (StackState C (callers s));
              eexists. (* evar (CS : state (CS.sem p)). exists CS. *)

            + (* EConst-Int *)
              split.
              { (** star steps *)
Local Transparent expr_of_const_val loc_of_reg.
                take_steps.
                -- exact Hstore2.
                -- (* Do recursive call. *)
                   take_steps.
                   ++ reflexivity.
                   ++ now apply find_procedures_of_trace.
                   ++ (* Now we are done with the event.
                         We still need to process the external call check. *)
                      take_steps.
                      ** (* TODO: Needs a new invariant that talks about the init
                            check. Assume for now that it exists, and
                            initialization has already taken place --
                            initial events?. *)
                         erewrite Memory.load_after_store_neq;
                           last exact Hstore2;
                           last (injection; now destruct v).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct v).
                         exact Hload0init.
                      ** take_steps.
                         --- (* Easy, from wf_buffers *)
                             admit.
                         --- rewrite Nat2Z.id. exact Halloc3.
                         --- take_steps.
                             +++ exact Hstore4.
                             +++ eapply star_trans with (t2 := E0);
                                   first exact Hstar_init;
                                   last reflexivity.
                                 take_steps.
                                 *** instantiate (1 := Int 0).
                                     (* Check Hload0extcall. *)
                                     admit.
                                 *** take_steps.
                                     apply star_refl.
              }
              { (** well-formed state *)
                econstructor; eauto.
                { destruct s. exact wb. }
                constructor.
                {
                  - intros C_ Hcomp.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    + subst C_.
                      pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                      assert (Hoffsetneq' :
                                (Permission.data, C, Block.local, reg_offset v) <>
                                (Permission.data, C, Block.local, 0%Z))
                        by (now destruct v).
                      (****************************
                      erewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                      assumption.
                       **********************************)
                      admit.
                    + erewrite Memory.load_after_store_neq;
                        last eassumption;
                        last (injection; contradiction).
                      assert (Hload0 := wfmem_counter wf_mem Hcomp).
                      assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                        by (now injection). (* Easy contradiction. *)
                      rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                      (************************************
                      rewrite counter_value_snoc. simpl.
                      move: Hneq => /eqP.
                      case: ifP;
                        last now rewrite Z.add_0_r.
                      move => /eqP => Hcontra => /eqP => Hneq.
                      symmetry in Hcontra. contradiction.
                      **********************************)
                      admit.
                }
                {
                  admit.
                }
                {
                  admit.
                }
                {
                  admit.
                }
                {
                  admit.
                }
                {
                  admit.
                }
              }
            + (* EConst-Ptr *)
              admit.
            + (* EConst-Undef *)
              admit.
          }
          (* Const does not modify the (shared) memory, therefore these two
             should be identical. *)
          assert (Hmem' : s0 = mem_of_event_inform e1). {
            subst prefix.
            clear -wf_int_pref'.
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              reflexivity. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations! [ptr] seems to have no effect in the proofs. *)
          (* Case analysis on concrete constant expression; all cases are
             similar.
             TODO: Refactoring. *)
          destruct ptr as [n | ptr |];
            exists (StackState C (callers s)). (* Must move the second eexists below, after the memories needed for star_refl are in scope *)
            (* eexists. (* evar (CS : state (CS.sem p)). exists CS. *) *)

          + (* EConst-Int *)
            (* Before processing the goal, introduce existential witnesses. *)
            (* match goal with *)
            (* | H : Memory.store _ ?PTR _ = Some ?MEM |- *)
            (*   Memory.store ?MEM ?PTR' _ = _ *)
            (*   => *)
            (*   assert (Hneq : PTR <> PTR') by admit *)
            (* end. *)
            pose proof proj1 (Memory.store_some_load_some _ _ (Int n)) Hload as [mem'' Hstore'].
            eexists. (* NOTE: Moved from above! *)
            (* Continue. *)
            split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              take_steps.
              -- exact Hstore'.
              -- (* Do recursive call. *)
                  take_steps.
                  ++ reflexivity.
                  ++ now apply find_procedures_of_trace.
                  ++ (* Now we are done with the event.
                        We still need to process the external call check. *)
                     take_steps.
                     ** (* TODO: Needs a new invariant that talks about the init
                           check. Assume for now that it exists, and
                           initialization has already taken place --
                           initial events?. *)
                        instantiate (1 := Int 1).
                        simpl.
                        destruct wf_mem. subst prefix. unfold C in *.
                        rewrite <- Hcomp1. rewrite <- Hcomp1 in C_b.
                        specialize (wfmem0 prefix0 e1 Logic.eq_refl)
                          as [_ [Hpostcond_steady _]].
                        specialize (Hpostcond_steady _ C_b Logic.eq_refl) as [G _].
                        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                          last by destruct v.
                        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                          easy.
                     ** take_steps.
                        --- assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                              last (now destruct v). (* Trivial property of register offsets. *)
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                              last easy.
                            exact Hload0.
                        --- unfold invalidate_metadata.
                            take_steps.
                            apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              { destruct s. exact wb. }
              { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
                eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
                exists bot. split; [| split]; easy. }
              (* Reestablish memory well-formedness.
                 TODO: Refactor, automate. *)
              { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
                (* instantiate (1 := mem). (* FIXME *) *)
                constructor.
                - intros C_ Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                    assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset v) <> (Permission.data, C, Block.local, 0%Z))
                      by (now destruct v).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                    assumption.
                  + erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (injection; contradiction).
                    assert (Hload0 := wfmem_counter wf_mem Hcomp).
                    assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                      by (now injection). (* Easy contradiction. *)
                    rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                    rewrite counter_value_snoc. simpl.
                    move: Hneq => /eqP.
                    case: ifP;
                      last now rewrite Z.add_0_r.
                    move => /eqP => Hcontra => /eqP => Hneq.
                    symmetry in Hcontra. contradiction.
                - intros Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  split.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_.
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      now rewrite Hcomp1.
                    * symmetry in Hnext. contradiction.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_. contradiction.
                    * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      intro; subst C_.
                      contradiction.
                - intros C_ reg Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    destruct (EregisterP reg v).
                    * subst v.
                      exists (Int n).
                      erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                    * erewrite Memory.load_after_store_neq;
                        last eassumption;
                        last (destruct reg; destruct v; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (now destruct reg).
                      eapply wfmem_meta; now eauto.
                  + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                    exists v'.
                    erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (now injection).
                    erewrite Memory.load_after_store_neq;
                      try eassumption.
                    now destruct reg.
                - intro Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  destruct (wfmem wf_mem Hprefix01) as [Hpostreg [Hsteady Hinitial]].
                  rename n into n0. rename v into v0. rename Hload into Hload0. rename mem' into mem'0. rename s0 into mem'. (* Trying to preserve proof script... *)
                  split; last split.
                  + (** postcondition_event_registers *)
                    {
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hpostreg.
                      destruct (Z.eqb_spec (reg_offset v0) off) as [Heq | Hneq].
                      * subst off.
                        assert (v0 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst v0.
                        (* assert (v = Int n0). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)
                        specialize (Hpostreg n _ Logic.eq_refl) as [v0 [v0' [Hloadv0 [Hshiftv0 Hgetv0']]]].
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_eq;
                             last exact Hstore'.
                           reflexivity.
                        -- now constructor.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [|]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                              reflexivity.
                      * setoid_rewrite Hcomp1 in Hpostreg.
                        destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                          as [v' Hload'].
                        rewrite Hoffset in Hload'.
                        (* assert (v = v'). { *)
                        (*   assert (Hneq0 : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     subst off. now destruct (CS.CS.reg_to_Ereg n). *)
                        (*   } *)
                        (*   setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneq0 Hmem) in Hload'. *)
                        (*   assert (Hneqv0 : (Permission.data, C, Block.local, reg_offset v0) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     injection as ?. contradiction. *)
                        (*   } *)
                        (*   rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneqv0 Hstore') in Hload'. *)
                        (*   rewrite Hload' in Hload. now injection Hload. *)
                        (* } *)
                        (* subst v'. *)
                        (* destruct (Hpostreg _ _ _ Hoffset Hload') as [v' [Hshift' Hget']]. *)
                        (* exists v'. *)
                        destruct (Hpostreg n _ Logic.eq_refl)
                          as [v [v'' [Hloadv [Hshiftv Hgetv'']]]].
                        assert (v = v'). {
                          subst off. rewrite Hload' in Hloadv. congruence.
                        }
                        subst v'.
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; contradiction).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (subst off; injection; now destruct n).
                           eassumption.
                        -- eassumption.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Machine.Intermediate.Register.gso;
                                first exact Hgetv''.
                              destruct n; destruct v0; try discriminate; contradiction.
                    }
                  + intros C' _ ?; subst C'. simpl.
                    specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                      as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                    split; [|split; [| split]].
                    (* The first two sub-goals are near-identical arguments on
                       memory operations. *)
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hinitflag.
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hlocalbuf.
                    (* ... *)
                    * intros b Hb. simpl.
                      specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                      destruct b as [| b']; first discriminate.
                      rewrite shift_S_Some in Hshift'.
                      injection Hshift' as ? ?; subst cid bid.
                      exists (C, b'). split; [| split].
                      -- rewrite shift_S_Some. reflexivity.
                      -- simpl. intros off v' Hload'.
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hstore';
                           last (injection; congruence).
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hmem;
                           last (injection; congruence).
                         simpl in Hrename.
                         specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ++ subst mem'. exact Hload''.
                         ++ exact Hrename''.
                      -- simpl. intros off v' Hload'.
                         simpl in Hrename'. subst mem'.
                         specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ++ erewrite Memory.load_after_store_neq;
                              last exact Hstore';
                              last (injection; congruence).
                            erewrite Memory.load_after_store_neq;
                              last exact Hmem;
                              last (injection; congruence).
                            exact Hload''.
                         ++ exact Hrename''.
                    * intros next Hnext.
                      rewrite Hmem' in Hnext.
                      specialize (Hnextblock next Hnext).
                      erewrite next_block_store_stable;
                        last exact Hstore'.
                      erewrite next_block_store_stable;
                        last exact Hmem.
                      exact Hnextblock.
                  + assert (mem0_mem''_asmp: forall C,
                               C <> cur_comp s ->
                               mem0 C = mem'' C
                           ).
                    {
Local Transparent Memory.store.
                      unfold Memory.store in *.
Local Opaque Memory.store.
                      simpl in *.
                      destruct (mem C) eqn:eC; last discriminate.
                      destruct (mem0 C) eqn:eC2; last discriminate.
                      destruct (ComponentMemory.store
                                  s1
                                  Block.local
                                  0%Z
                                  (Int (counter_value
                                          C
                                          (prefix ++ [:: EConst
                                                         (cur_comp s)
                                                         (Int n0) v0 mem' t0]))))
                               eqn:ecompMem;
                        last discriminate.
                      destruct (ComponentMemory.store
                                  s0 Block.local (reg_offset v0) (Int n0))
                               eqn:ecompMem2;
                        last discriminate.
                      inversion Hstore'. inversion Hmem. subst mem mem''.
                      intros ? Hneq.
                      rewrite !setmE. unfold C.
                      assert (C0 == cur_comp s = false) as rewr. by apply /eqP.
                      by rewrite rewr.
                    }
                    eapply wfmem_postcondition_initial_preserved; eauto.
              }

          + (* EConst-Ptr *)
            (* Before processing the goal, introduce existential witnesses. *)
            (* assert (Hoffsetneq: (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C, Block.local, reg_offset v)) *)
            (*   by (now destruct v). (* Lemma? *) *)
            (* assert (Hload : exists v', Memory.load mem0 (Permission.data, C, Block.local, reg_offset v) = Some v') *)
            (*   by (eapply Memory.store_some_load_some; eauto). *)
            (* setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) in Hload. *)
            destruct ptr as [[[ptrp ptrC] ptrb] ptro].
            assert (ptrp = Permission.data) by admit; subst ptrp.
            set (saved := (eval_binop Add (Ptr (Permission.data, C, LOCALBUF_blockid, 0%Z)) (Int ptro))).
            pose proof proj1 (Memory.store_some_load_some _ _ (*Ptr ptr*) saved) Hload as [mem'' Hstore'].
            (* Continue. *)
            (* exists (StackState C (callers s)). *)
            eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
            split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              take_steps.
              -- destruct (wfmem wf_mem Hprefix01) as [_ [Hsteady _]].
                 specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1)) as [_ [Hlocalbuf _]].
                 (* erewrite Memory.load_after_store_neq; *)
                 (*   last exact  Hstore'; *)
                 (*   last (injection; now destruct reg2). *)
                 erewrite Memory.load_after_store_neq;
                   last exact Hmem;
                   last (injection; discriminate).
                 exact Hlocalbuf.
              -- take_steps.
                 ++ exact Hstore'.
                 ++ take_steps.
                    ** reflexivity.
                    ** now apply find_procedures_of_trace.
                    ** (* Now we are done with the event.
                          We still need to process the external call check. *)
                       take_steps.
                       --- instantiate (1 := (Int 1)).
                           simpl.
                           destruct wf_mem. subst prefix. unfold C in *.
                           rewrite <- Hcomp1. rewrite <- Hcomp1 in C_b.
                           specialize (wfmem0 prefix0 e1 Logic.eq_refl)
                             as [_ [Hpostcond_steady _]].
                           specialize (Hpostcond_steady _ C_b Logic.eq_refl) as [G _].
                           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                             last by destruct v.
                           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                             easy.
                       --- take_steps.
                           +++ assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                                 last (now destruct v). (* Trivial property of register offsets. *)
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                                 last easy.
                               exact Hload0.
                           +++ unfold invalidate_metadata.
                               take_steps.
                               apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              { destruct s. exact wb. }
              { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
                eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
                exists bot. split; [| split]; easy. }
              (* Reestablish memory well-formedness.
                 TODO: Refactor, automate. *)
              { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
                (* instantiate (1 := mem). (* FIXME *) *)
                constructor.
                - intros C_ Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                    assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset v) <> (Permission.data, C, Block.local, 0%Z))
                      by (now destruct v).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                    assumption.
                  + erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (injection; contradiction).
                    assert (Hload0 := wfmem_counter wf_mem Hcomp).
                    assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                      by (now injection). (* Easy contradiction. *)
                    rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                    rewrite counter_value_snoc. simpl.
                    move: Hneq => /eqP.
                    case: ifP;
                      last now rewrite Z.add_0_r.
                    move => /eqP => Hcontra => /eqP => Hneq.
                    symmetry in Hcontra. contradiction.
                - intros Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  split.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_.
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      now rewrite Hcomp1.
                    * symmetry in Hnext. contradiction.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_. contradiction.
                    * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      intro; subst C_.
                      contradiction.
                - intros C_ reg Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    destruct (EregisterP reg v).
                    * subst v.
                      exists saved.
                      erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                    * erewrite Memory.load_after_store_neq;
                        last eassumption;
                        last (destruct reg; destruct v; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (now destruct reg).
                      eapply wfmem_meta; now eauto.
                  + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                    exists v'.
                    erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (now injection).
                    erewrite Memory.load_after_store_neq;
                      try eassumption.
                    now destruct reg.
                - intro Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  destruct (wfmem wf_mem Hprefix01) as [Hpostreg [Hsteady Hinitial]].
                  (* rename n into n0. *) rename v into v0. rename Hload into Hload0. rename mem' into mem'0. rename s0 into mem'. (* Trying to preserve proof script... *)
                  split; last split.
                  + (** postcondition_event_registers *)
                    {
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      (* unfold postcondition_event_registers in Hpostreg. *)
                      destruct (Z.eqb_spec (reg_offset v0) off) as [Heq | Hneq].
                      * subst off.
                        assert (v0 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst v0.
                        (* assert (v = saved). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)
                      eexists. eexists.
                      split; [| split].
                        -- erewrite Memory.load_after_store_eq;
                             last exact Hstore'.
                           reflexivity.
                      -- unfold shift_value_option,
                         rename_value_option, rename_value_template_option,
                         saved.
                         simpl.
                         unfold ssrnat.addn, ssrnat.subn,
                         LOCALBUF_blockid,
                         all_zeros_shift, uniform_shift.
                         simpl.
                         reflexivity.
                      -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                         ++ destruct prefix; discriminate. (* contra *)
                         ++ subst prefix. destruct prefix0 as [| ? [|]]; discriminate. (* contra *)
                         ++ rewrite Hprefix01 in Ht.
                            symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                            inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                              subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                            subst t0.
                            rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                            move: wf_e => /andP => [[]] => /eqP => Heq1 => /eqP => Heq2.
                            subst ptrC ptrb.
                            reflexivity.

                      * (* setoid_rewrite Hcomp1 in Hpostreg. *)
                        destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                          as [v' Hload'].
                        rewrite Hoffset in Hload'.
                        (* assert (v = v'). { *)
                        (*   assert (Hneq0 : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     subst off. now destruct (CS.CS.reg_to_Ereg n). *)
                        (*   } *)
                        (*   setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneq0 Hmem) in Hload'. *)
                        (*   assert (Hneqv0 : (Permission.data, C, Block.local, reg_offset v0) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     injection as ?. contradiction. *)
                        (*   } *)
                        (*   rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneqv0 Hstore') in Hload'. *)
                        (*   rewrite Hload' in Hload. now injection Hload. *)
                        (* } *)
                        (* subst v'. *)
                        (* destruct (Hpostreg _ _ _ Hoffset Hload') as [v' [Hshift' Hget']]. *)
                        specialize (Hpostreg n _ Logic.eq_refl)
                          as [v [v'' [Hloadv [Hshiftv Hgetv'']]]].
                        assert (v  = v'). {
                          subst off. rewrite -Hcomp1 Hloadv in Hload'. congruence.
                        }
                        subst v'.
                        (* exists v'. *)
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; contradiction).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (subst off; injection; now destruct n).
                           eassumption.
                        -- eassumption.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Machine.Intermediate.Register.gso;
                                first exact Hgetv''.
                              destruct n; destruct v0; try discriminate; contradiction.
                    }
                  + intros C' _ ?; subst C'. simpl.
                    specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                      as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                    split; [| split; [| split]].
                    (* The first two sub-goals are near-identical arguments on
                       memory operations. *)
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hinitflag.
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hlocalbuf.
                    (* ... *)
                    * intros b Hb. simpl.
                      specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                      destruct b as [| b']; first discriminate.
                      rewrite shift_S_Some in Hshift'.
                      injection Hshift' as ? ?; subst cid bid.
                      exists (C, b'). split; [| split].
                      -- rewrite shift_S_Some. reflexivity.
                      -- simpl. intros off v' Hload'.
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hstore';
                           last (injection; congruence).
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hmem;
                           last (injection; congruence).
                         simpl in Hrename.
                         specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ** subst mem'. exact Hload''.
                         ** exact Hrename''.
                      -- simpl. intros off v' Hload'.
                         simpl in Hrename'. subst mem'.
                         specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ++ erewrite Memory.load_after_store_neq;
                              last exact Hstore';
                              last (injection; congruence).
                            erewrite Memory.load_after_store_neq;
                              last exact Hmem;
                              last (injection; congruence).
                            exact Hload''.
                         ++ exact Hrename''.
                    * intros next Hnext.
                      rewrite Hmem' in Hnext.
                      specialize (Hnextblock next Hnext).
                      erewrite next_block_store_stable;
                        last exact Hstore'.
                      erewrite next_block_store_stable;
                        last exact Hmem.
                      exact Hnextblock.
                  + assert (mem0_mem''_asmp: forall C,
                               C <> cur_comp s ->
                               mem0 C = mem'' C
                           ).
                    {
Local Transparent Memory.store.
                      unfold Memory.store in *.
Local Opaque Memory.store.
                      simpl in *.
                      destruct (mem C) eqn:eC; last discriminate.
                      destruct (mem0 C) eqn:eC2; last discriminate.
                      destruct (ComponentMemory.store
                                  s1
                                  Block.local
                                  0%Z
                                  (Int
                                     (counter_value
                                        C
                                        (prefix ++
                                                [:: EConst
                                                    (cur_comp s)
                                                    (Ptr
                                                       (Permission.data,
                                                        ptrC, ptrb, ptro))
                                                    v0 mem' t0]))))
                               eqn:ecompMem;
                        last discriminate.
                      destruct (ComponentMemory.store
                                  s0 Block.local (reg_offset v0) saved)
                               eqn:ecompMem2;
                        last discriminate.
                      inversion Hstore'. inversion Hmem. subst mem mem''.
                      intros ? Hneq.
                      rewrite !setmE. unfold C.
                      assert (C0 == cur_comp s = false) as rewr. by apply /eqP.
                      by rewrite rewr.
                    }
                    eapply wfmem_postcondition_initial_preserved; eauto.
              }

          + (* EConst-Undef *)
            (* assert (Hoffsetneq: (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C, Block.local, reg_offset v)) *)
            (*   by (now destruct v). (* Lemma? *) *)
            (* assert (Hload : exists v', Memory.load mem0 (Permission.data, C, Block.local, reg_offset v) = Some v') *)
            (*   by (eapply Memory.store_some_load_some; eauto). *)
            (* setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) in Hload. *)
            pose proof proj1 (Memory.store_some_load_some _ _ Undef) Hload as [mem'' Hstore'].
            (* Continue. *)
            (* exists (StackState C (callers s)). *)
            eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
            split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              take_steps.
              -- exact Hstore'.
              -- (* Do recursive call. *)
                  take_steps.
                  ++ reflexivity.
                  ++ now apply find_procedures_of_trace.
                  ++ (* Now we are done with the event.
                        We still need to process the external call check. *)
                     take_steps.
                     ** (* TODO: Needs a new invariant that talks about the init
                           check. Assume for now that it exists, and
                           initialization has already taken place --
                           initial events?. *)
                        instantiate (1 := Int 1).
                        simpl.
                        destruct wf_mem. subst prefix. unfold C in *.
                        rewrite <- Hcomp1. rewrite <- Hcomp1 in C_b.
                        specialize (wfmem0 prefix0 e1 Logic.eq_refl)
                          as [_ [Hpostcond_steady _]].
                        specialize (Hpostcond_steady _ C_b Logic.eq_refl) as [G _].
                        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                          last by destruct v.
                        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                          easy.
                     ** take_steps.
                        --- assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                              last (now destruct v). (* Trivial property of register offsets. *)
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                              last easy.
                            exact Hload0.
                        --- unfold invalidate_metadata.
                            take_steps.
                            apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              { destruct s. exact wb. }
              { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
                eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
                exists bot. split; [| split]; easy. }
              (* Reestablish memory well-formedness.
                 TODO: Refactor, automate. *)
              { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
                (* instantiate (1 := mem). (* FIXME *) *)
                constructor.
                - intros C_ Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                    assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset v) <> (Permission.data, C, Block.local, 0%Z))
                      by (now destruct v).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                    assumption.
                  + erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (injection; contradiction).
                    assert (Hload0 := wfmem_counter wf_mem Hcomp).
                    assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                      by (now injection). (* Easy contradiction. *)
                    rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                    rewrite counter_value_snoc. simpl.
                    move: Hneq => /eqP.
                    case: ifP;
                      last now rewrite Z.add_0_r.
                    move => /eqP => Hcontra => /eqP => Hneq.
                    symmetry in Hcontra. contradiction.
                - intros Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  split.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_.
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      now rewrite Hcomp1.
                    * symmetry in Hnext. contradiction.
                  + intros C_ Hcomp Hnext.
                    destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                    * subst C_. contradiction.
                    * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                        last (injection; destruct v; discriminate).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (injection; discriminate).
                      apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                      intro; subst C_.
                      contradiction.
                - intros C_ reg Hcomp.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  + subst C_.
                    destruct (EregisterP reg v).
                    * subst v.
                      exists Undef.
                      erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                    * erewrite Memory.load_after_store_neq;
                        last eassumption;
                        last (destruct reg; destruct v; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                        last (now destruct reg).
                      eapply wfmem_meta; now eauto.
                  + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                    exists v'.
                    erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (now injection).
                    erewrite Memory.load_after_store_neq;
                      try eassumption.
                    now destruct reg.
                - intro Hcontra. now destruct prefix.
                - intros pref ev Hprefix.
                  apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                  destruct (wfmem wf_mem Hprefix01) as [Hpostreg [Hsteady Hinitial]].
                  (* rename n into n0. *) rename v into v0. rename Hload into Hload0.
                  rename mem' into mem'0. rename s0 into mem'.
                  (* Trying to preserve proof script... *)
                  split; last split.
                  + (** postcondition_event_registers *)
                    {
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hpostreg.
                      destruct (Z.eqb_spec (reg_offset v0) off) as [Heq | Hneq].
                      * subst off.
                        assert (v0 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst v0.
                        (* assert (v = Undef). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)
                        (* exists Undef. *)
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_eq;
                             last exact Hstore'.
                           reflexivity.
                        -- now constructor.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [|]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                              reflexivity.
                      * setoid_rewrite Hcomp1 in Hpostreg.
                        destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                          as [v' Hload'].
                        rewrite Hoffset in Hload'.
                        (* assert (v = v'). { *)
                        (*   assert (Hneq0 : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     subst off. now destruct (CS.CS.reg_to_Ereg n). *)
                        (*   } *)
                        (*   setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneq0 Hmem) in Hload'. *)
                        (*   assert (Hneqv0 : (Permission.data, C, Block.local, reg_offset v0) <> (Permission.data, cur_comp s, Block.local, off)). { *)
                        (*     injection as ?. contradiction. *)
                        (*   } *)
                        (*   rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hneqv0 Hstore') in Hload'. *)
                        (*   rewrite Hload' in Hload. now injection Hload. *)
                        (* } *)
                        (* subst v'. *)
                        (* exists v'. *)
                        destruct (Hpostreg n _ Hoffset)
                          as [v [v'' [Hloadv [Hshiftv Hgetv'']]]].
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; contradiction).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (subst off; injection; now destruct n).
                           eassumption.
                        -- eassumption.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Machine.Intermediate.Register.gso;
                                first exact Hgetv''.
                              destruct n; destruct v0; try discriminate; contradiction.
                    }
                  + intros C' _ ?; subst C'. simpl.
                    specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                      as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                    split; [| split; [| split]].
                    (* The first two sub-goals are near-identical arguments on
                       memory operations. *)
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hinitflag.
                    * erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; now destruct v0).
                      erewrite Memory.load_after_store_neq;
                        last exact Hmem;
                        last (injection; now destruct v0).
                      exact Hlocalbuf.
                    (* ... *)
                    * intros b Hb. simpl.
                      specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                      destruct b as [| b']; first discriminate.
                      rewrite shift_S_Some in Hshift'.
                      injection Hshift' as ? ?; subst cid bid.
                      exists (C, b'). split; [| split].
                      -- rewrite shift_S_Some. reflexivity.
                      -- simpl. intros off v' Hload'.
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hstore';
                           last (injection; congruence).
                         erewrite Memory.load_after_store_neq in Hload';
                           last exact Hmem;
                           last (injection; congruence).
                         simpl in Hrename.
                         specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ++ subst mem'. exact Hload''.
                         ++ exact Hrename''.
                      -- simpl. intros off v' Hload'.
                         simpl in Hrename'. subst mem'.
                         specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                         exists v''. split.
                         ++ erewrite Memory.load_after_store_neq;
                              last exact Hstore';
                              last (injection; congruence).
                            erewrite Memory.load_after_store_neq;
                              last exact Hmem;
                              last (injection; congruence).
                            exact Hload''.
                         ++ exact Hrename''.
                    * intros next Hnext.
                      rewrite Hmem' in Hnext.
                      specialize (Hnextblock next Hnext).
                      erewrite next_block_store_stable;
                        last exact Hstore'.
                      erewrite next_block_store_stable;
                        last exact Hmem.
                      exact Hnextblock.
                  + assert (mem0_mem''_asmp: forall C,
                               C <> cur_comp s ->
                               mem0 C = mem'' C
                           ).
                    {
Local Transparent Memory.store.
                      unfold Memory.store in *.
Local Opaque Memory.store.
                      simpl in *.
                      destruct (mem C) eqn:eC; last discriminate.
                      destruct (mem0 C) eqn:eC2; last discriminate.
                      destruct (ComponentMemory.store
                                  s1
                                  Block.local
                                  0%Z
                                  (Int (counter_value
                                          C
                                          (prefix ++ [:: EConst
                                                         (cur_comp s)
                                                         Undef v0 mem' t0]))))
                               eqn:ecompMem;
                        last discriminate.
                      destruct (ComponentMemory.store
                                  s0 Block.local (reg_offset v0) Undef)
                               eqn:ecompMem2;
                        last discriminate.
                      inversion Hstore'. inversion Hmem. subst mem mem''.
                      intros ? Hneq.
                      rewrite !setmE. unfold C.
                      assert (C0 == cur_comp s = false) as rewr. by apply /eqP.
                        by rewrite rewr.
                    }
                    eapply wfmem_postcondition_initial_preserved; eauto.
              }

        - (* EMov *)
          (* Gather a few recurrent assumptions at the top. *)
          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]]
            by admit;
            first admit. (* TODO: Treat empty case separately. *)
          (*destruct (well_formed_memory_store_reg_offset v (Int 42) C_b wf_mem) as [mem' Hstore].*) (* Mostly pollution? *)
          (* Const does not modify the (shared) memory, therefore these two
             should be identical. *)
          assert (Hmem' : s0 = mem_of_event_inform e1). {
            subst prefix.
            clear -wf_int_pref'.
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              reflexivity. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations! [ptr] seems to have no effect in the proofs. *)
          exists (EMov C src dst s0 t0).
          (* NOTE: Can we make this initial part more like the other cases? *)
          assert (Hoffsetneq: (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C, Block.local, reg_offset dst))
            by (now destruct dst). (* Lemma? *)
          assert (Hoffsetneq2: (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C, Block.local, reg_offset src))
            by (now destruct src).
          (* assert (Hload : exists v', Memory.load mem0 (Permission.data, C, Block.local, reg_offset ptr) = Some v') *)
            (* by (eapply Memory.store_some_load_some; eauto). *)
          assert (Hload := wfmem_meta wf_mem dst C_b). fold C in Hload.
          setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) in Hload.
          (* setoid_rewrite -> (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) in Hloadptr. *)

          assert (exists v', Memory.load
                               mem0
                               (Permission.data, C, Block.local, (0 + reg_offset src)%Z)
                             = Some v')
            as [vsrc Hloadmem0_vsrc].
          {
            destruct wf_mem.
            specialize (wfmem_meta0 C src) as [vloadmem0 Hloadmem0]; by eauto.
          }
          assert (Memory.load
                               mem
                               (Permission.data, C, Block.local, (0 + reg_offset src)%Z)
                             = Some vsrc)
            as Hloadmem_vsrc.
          {
            by rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq2 Hmem).
          }
          set saved := vsrc.
          pose proof proj1 (Memory.store_some_load_some _ _ saved) Hload as [mem'' Hstore'].
          (* Continue. *)
          exists (StackState C (callers s)).
          eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
          split.
          + (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
            take_steps.
            * exact Hloadmem_vsrc.
            * take_steps; first exact Hstore'.
                (* Do recursive call. *)
                take_steps.
              -- reflexivity.
              -- now apply find_procedures_of_trace.
              -- (* Now we are done with the event.
                    We still need to process the external call check. *)
                 take_steps.
                 ++ (* TODO: Needs a new invariant that talks about the init
                       check. Assume for now that it exists, and
                       initialization has already taken place --
                       initial events?. *)
                    instantiate (1 := Int 1).
                    simpl.
                    destruct wf_mem. subst prefix. unfold C in *.
                    rewrite <- Hcomp1. rewrite <- Hcomp1 in C_b.
                    specialize (wfmem0 prefix0 e1 Logic.eq_refl)
                      as [_ [Hpostcond_steady _]].
                    specialize (Hpostcond_steady _ C_b Logic.eq_refl) as [G _].
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last by destruct dst.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      easy.
                 ++ take_steps.
                    ** assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                       rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                         last (now destruct dst). (* Trivial property of register offsets. *)
                       rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                         last easy.
                       exact Hload0.
                    ** unfold invalidate_metadata.
                       take_steps.
                       apply star_refl.
          + (* Reestablish invariant. *)
            econstructor; try reflexivity; try eassumption.
            { destruct s. exact wb. }
            { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy. }
            (* Reestablish memory well-formedness.
               TODO: Refactor, automate. *)
            { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
              constructor.
              - intros C_ Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                  assert (Hoffsetneq' := not_eq_sym Hoffsetneq).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                  assumption.
                + erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (injection; contradiction).
                    assert (Hload0 := wfmem_counter wf_mem Hcomp).
                    assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                      by (now injection). (* Easy contradiction. *)
                    rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                    rewrite counter_value_snoc. simpl.
                    move: Hneq => /eqP.
                    case: ifP;
                      last now rewrite Z.add_0_r.
                    move => /eqP => Hcontra => /eqP => Hneq.
                    symmetry in Hcontra. contradiction.
              - intros Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                split.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct dst; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    now rewrite Hcomp1.
                  * symmetry in Hnext. contradiction.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_. contradiction.
                  * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct dst; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    intro; subst C_.
                    contradiction.
              - intros C_ reg Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  destruct (EregisterP reg dst). (* mem -[ptr]-> mem'' *)
                  * subst reg.
                    exists saved. (* exists (Int n). *)
                    erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                  * erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (destruct reg; destruct dst; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (now destruct reg).
                    eapply wfmem_meta; now eauto.
                + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                  exists v'.
                  erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (now injection).
                  erewrite Memory.load_after_store_neq;
                    try eassumption.
                  now destruct reg.
              - intro Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                destruct (wfmem wf_mem Hprefix01) as [Hpostreg [Hsteady Hinitial]].
                (* rename n into n0. *) (* rename v into v0.*)
                rename Hload into Hload0. (*rename mem' into mem'0.*)
                rename s0 into mem'. (* Trying to preserve proof script... *)
                split; [| split].
                + {
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hpostreg.
                      destruct (Z.eqb_spec (reg_offset dst) off) as [Heq | Hneq].
                      * subst off.
                        assert (dst = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst dst.
                        destruct (Hpostreg (Ereg_to_reg src) _ Logic.eq_refl)
                          as [v [v'' [Hloadv [Hshiftv Hgetv'']]]].
                        rewrite reg_to_Ereg_to_reg in Hloadv.
                        setoid_rewrite Hcomp1 in Hloadv.
                        rewrite Hloadmem0_vsrc in Hloadv.
                        injection Hloadv as ?; subst v.
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_eq;
                             last exact Hstore'.
                           reflexivity.
                        -- exact Hshiftv.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [|]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                              exact Hgetv''.
                      * setoid_rewrite Hcomp1 in Hpostreg.
                        destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                          as [v' Hload'].
                        rewrite Hoffset in Hload'.
                        destruct (Hpostreg n _ Hoffset)
                          as [v [v'' [Hloadv [Hshiftv Hgetv'']]]].
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; contradiction).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (subst off; injection; now destruct n).
                           eassumption.
                        -- eassumption.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst t0.
                              rewrite Machine.Intermediate.Register.gso;
                                first exact Hgetv''.
                              destruct n; destruct dst; try discriminate; contradiction.
                  }
                + intros C' _ ?; subst C'. simpl.
                  specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                  split; [| split; [| split]].
                  (* The first two sub-goals are near-identical arguments on
                     memory operations. *)
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct dst).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct dst).
                    exact Hinitflag.
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct dst).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct dst).
                    exact Hlocalbuf.
                  (* ... *)
                  * intros b Hb. simpl.
                    specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                    destruct b as [| b']; first contradiction.
                    rewrite shift_S_Some in Hshift'.
                    injection Hshift' as ? ?; subst cid bid.
                    exists (C, b'). split; [| split].
                    -- rewrite shift_S_Some. reflexivity.
                    -- simpl. intros off v' Hload'.
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hstore';
                         last (injection; congruence).
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hmem;
                         last (injection; congruence).
                       simpl in Hrename.
                       specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ** subst mem'. exact Hload''.
                       ** exact Hrename''.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename'. subst mem'.
                       specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ++ erewrite Memory.load_after_store_neq;
                            last exact Hstore';
                            last (injection; congruence).
                          erewrite Memory.load_after_store_neq;
                            last exact Hmem;
                            last (injection; congruence).
                          exact Hload''.
                       ++ exact Hrename''.
                    * intros next Hnext.
                      rewrite Hmem' in Hnext.
                      specialize (Hnextblock next Hnext).
                      erewrite next_block_store_stable;
                        last exact Hstore'.
                      erewrite next_block_store_stable;
                        last exact Hmem.
                      exact Hnextblock.
                  + intros C' Hcomp Hnext.
                    rewrite <- Hcomp1 in Hnext.
                    specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
                    * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                      left. split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct dst).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct dst).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct dst).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct dst).
                         exact Hlocalbuf.
                      -- destruct Hsteady' as [Hsnapshot Hnextblock].
                         split.
                         ++ intros b Hlocal.
                            specialize (Hsnapshot b Hlocal) as [Cb [Hshift' [Hrename Hrename']]].
                            exists Cb. split; [| split].
                            ** exact Hshift'.
                            ** intros off v' Hload.
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hstore';
                                 last (injection; congruence).
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hmem;
                                 last (injection; congruence).
                               specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                               exists v''. split.
                               --- subst mem'. assumption.
                               --- congruence.
                            ** intros off v' Hload. subst mem'.
                               specialize (Hrename' off v' Hload) as [v'' [Hload'' Hrename']].
                               exists v''. split.
                               --- erewrite Memory.load_after_store_neq;
                                     last exact Hstore';
                                     last (injection; congruence).
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hmem;
                                     last (injection; congruence).
                                   assumption.
                               --- congruence.
                         ++ (* Same sub-proof on next block as above! *)
                            intros next Hnext'.
                            rewrite Hmem' in Hnext'.
                            specialize (Hnextblock next Hnext').
                            erewrite next_block_store_stable;
                              last exact Hstore'.
                            erewrite next_block_store_stable;
                              last exact Hmem.
                            exact Hnextblock.
                    * right.
                      destruct Hinitial as [Hinitflag [Hlocalbuf Hinitial]].
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct dst).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct dst).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hlocalbuf.
                      -- destruct Hinitial as [Hprealloc Hnextblock].
                         split.
                         ** destruct Hprealloc
                             as [Cmem [buf [HCmem [Hbuf [Hnextblock' Hprealloc]]]]].
                            exists Cmem, buf.
                            split; [| split; [| split]]; try assumption.
                            rewrite -HCmem.
                            subst mem'. reflexivity.
                         ** destruct Hnextblock as [Cmem [HCmem Hnextblock]].
                            exists Cmem. split; last assumption.
                            rewrite -HCmem. symmetry.
                            transitivity (mem C').
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
            }

        - (* EBinop *)
          (* Gather a few recurrent assumptions at the top. *)
          rename e into op. rename e0 into reg0. rename e1 into reg1. rename e2 into reg2.
          (* rename s0 into emem. *)
          rename t0 into eregs.
          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]]
            by admit;
            first admit. (* TODO: Treat empty case separately. *)
          (* destruct (well_formed_memory_store_reg_offset v ptr C_b wf_mem) as [mem' Hstore]. (* TODO: Consider actual utility of this. *) *)
          (* Const does not modify the (shared) memory, therefore these two
             should be identical. *)
          assert (Hmem' : s0 = mem_of_event_inform e1). {
            subst prefix.
            clear -wf_int_pref'.
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              reflexivity. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations! [ptr] seems to have no effect in the proofs. *)
          exists (EBinop C op reg0 reg1 reg2 s0 eregs).
          (* Case analysis on concrete constant expression; all cases are
             similar.
             TODO: Refactoring. *)
          destruct (wfmem_meta wf_mem reg0 C_b) as [v0 Hreg0mem0].
          assert (Hreg0mem := Hreg0mem0).
          erewrite <- Memory.load_after_store_neq in Hreg0mem;
            last exact Hmem;
            last (injection; now destruct reg0).
          destruct (wfmem_meta wf_mem reg1 C_b) as [v1 Hreg1mem0].
          assert (Hreg1mem := Hreg1mem0).
          erewrite <- Memory.load_after_store_neq in Hreg1mem;
            last exact Hmem;
            last (injection; now destruct reg1).
          set (saved := eval_binop (binop_of_Ebinop op) v0 v1).
          (* NOTE: In previous cases, we got to the store by a different route. *)
          destruct (wfmem_meta wf_mem reg2 C_b) as [v2 Hreg2mem0].
          assert (Hreg2mem := Hreg2mem0).
          erewrite <- Memory.load_after_store_neq in Hreg2mem;
            last exact Hmem;
            last (injection; now destruct reg2).
          destruct (Memory.store_after_load _ _ _ saved Hreg2mem) as [mem'' Hstore']. (* "Standard" names here... *)
          (* assert (Hoffsetneq: (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C, Block.local, reg_offset regs1)) *)
          (*   by (now destruct v). (* Lemma? *) *)
          (* assert (Hload : exists v', Memory.load mem0 (Permission.data, C, Block.local, reg_offset v) = Some v') *)
          (*   by (eapply Memory.store_some_load_some; eauto). *)
          (* setoid_rewrite <- (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq Hmem) in Hload. *)
          (* pose proof proj1 (Memory.store_some_load_some _ _ (Int n)) Hload as [mem'' Hstore']. *)
          (* Continue. *)
          exists (StackState C (callers s)).
          eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
          split.
          + (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
            take_steps.
            * exact Hreg0mem.
            * take_steps.
              -- exact Hreg1mem.
              -- take_steps.
                 ++ exact Hstore'.
                 ++ (* Do recursive call. *)
                    take_steps.
                    ** reflexivity.
                    ** now apply find_procedures_of_trace.
                    ** (* Now we are done with the event.
                          We still need to process the external call check. *)
                       take_steps.
                       --- destruct (wfmem wf_mem Hprefix01) as [_ [Hsteady _]].
                           specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1)) as [Hoffset _].
                           erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; now destruct reg2).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (injection; now destruct reg2).
                           exact Hoffset.
                       --- take_steps.
                           +++ assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                                 last (now destruct reg2). (* Trivial property of register offsets. *)
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                                 last easy.
                               exact Hload0.
                           +++ unfold invalidate_metadata.
                               take_steps.
                               apply star_refl.
          + (* Reestablish invariant. *)
            econstructor; try reflexivity; try eassumption.
            { destruct s. exact wb. }
            { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy. }
            (* Reestablish memory well-formedness.
               TODO: Refactor, automate. *)
            { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
              (* instantiate (1 := mem). (* FIXME *) *)
              constructor.
              - intros C_ Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                  assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset reg2) <> (Permission.data, C, Block.local, 0%Z))
                    by (now destruct reg2).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                  assumption.
                + erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (injection; contradiction).
                  assert (Hload0 := wfmem_counter wf_mem Hcomp).
                  assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                    by (now injection). (* Easy contradiction. *)
                  rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                  rewrite counter_value_snoc. simpl.
                  move: Hneq => /eqP.
                  case: ifP;
                    last now rewrite Z.add_0_r.
                  move => /eqP => Hcontra => /eqP => Hneq.
                  symmetry in Hcontra. contradiction.
              - intros Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                split.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg2; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    now rewrite Hcomp1.
                  * symmetry in Hnext. contradiction.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_. contradiction.
                  * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg2; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    intro; subst C_.
                    contradiction.
              - intros C_ reg Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  destruct (EregisterP reg reg2).
                  * subst reg2.
                    (* exists (Int n). *)
                    exists saved.
                    erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                  * erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (destruct reg; destruct reg2; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (now destruct reg).
                    eapply wfmem_meta; now eauto.
                + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                  exists v'.
                  erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (now injection).
                  erewrite Memory.load_after_store_neq;
                    try eassumption.
                  now destruct reg.
              - intro Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                destruct (wfmem wf_mem Hprefix01) as [Hregs [Hsteady Hinitial]].
                (* rename n into n0. rename v into v0. rename Hload into Hload0. rename mem' into mem'0. *) rename s0 into mem'. (* Trying to preserve proof script... *)
                split; [| split].
                + {
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hregs.
                      destruct (Z.eqb_spec (reg_offset reg2) off) as [Heq | Hneq].
                      * subst off.
                        assert (reg2 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst reg2.
                        (* assert (v = saved). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)

Ltac t_postcondition_event_registers_get
prefix prefix0 Hprefix01 eregs :=
  inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht];
  [ destruct prefix; discriminate (* contra *)
  | subst prefix; destruct prefix0 as [| ? [|]]; discriminate (* contra *)
  | rewrite Hprefix01 in Ht;
    symmetry in Ht; apply cats2_inv in Ht as [? [? ?]]; subst prefint eint1 eint2;
    inversion Hstep as [| | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | |];
    subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6;
    subst eregs;
    [rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss]].
    (* reflexivity]. *)

                        rewrite <- Hcomp1 in Hreg0mem0.
                        destruct (Hregs (Ereg_to_reg reg0) _ (f_equal _ (reg_to_Ereg_to_reg _)))
                          as [vs0 [vs0' [Hload0 [Hshift0 Hget0]]]].
                        rewrite <- Hcomp1 in Hreg1mem0.
                        destruct (Hregs (Ereg_to_reg reg1) _ (f_equal _ (reg_to_Ereg_to_reg _)))
                          as [vs1 [vs1' [Hload1 [Hshift1 Hget1]]]].
                        rewrite Hreg0mem0 in Hload0. injection Hload0 as ?; subst vs0.
                        rewrite Hreg1mem0 in Hload1. injection Hload1 as ?; subst vs1.

Local Transparent binop_of_Ebinop. (* TODO: This was made locally opaque earlier but not reversed! *)

Ltac t_postcondition_event_registers_binop_case
     mem prefix prefix0 Hprefix01 eregs Hstore' Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' :=
  repeat match goal with
  | Hload : Memory.load mem _ = Some (Ptr (?PERM, _, ?B, _)) |- _ =>
    assert (PERM = Permission.data) by admit;
    subst PERM;
    destruct B as [| ?];
    [discriminate |]
  end;
  [eexists; eexists];
  split; [| split];
  [ erewrite Memory.load_after_store_eq; [reflexivity | exact Hstore']
  | reflexivity
  |];
  t_postcondition_event_registers_get prefix prefix0 Hprefix01 eregs;
  rewrite Hget0 Hget1;
  injection Hshift0 as ?; subst vs0';
  injection Hshift1 as ?; subst vs1';
  reflexivity.

Ltac t_postcondition_event_registers_data_pointers mem :=
  repeat match goal with
  | Hload : Memory.load mem _ = Some (Ptr (?PERM, _, ?B, _)) |- _ =>
    assert (PERM = Permission.data) by admit;
    subst PERM;
    destruct B as [| ?];
    [discriminate |]
  end.

Ltac t_postcondition_event_registers_pointer_Cb
     Hstore' HeqC Heqb prefix prefix0 Hprefix01 eregs Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' HeqC Heqb :=
  eexists; eexists;
    [split; [| split]];
  [ erewrite Memory.load_after_store_eq; [reflexivity | exact Hstore']
  | rewrite /= HeqC Heqb //
  |];
  simpl;
  t_postcondition_event_registers_get prefix prefix0 Hprefix01 eregs;
  rewrite Hget0 Hget1;
  injection Hshift0 as ?; subst vs0';
  injection Hshift1 as ?; subst vs1';
  unfold ssrnat.addn, ssrnat.subn, ssrnat.addn_rec, ssrnat.subn_rec,
  all_zeros_shift, uniform_shift;
  simpl;
  rewrite !Nat.add_0_r !Nat.sub_0_r HeqC Heqb;
  reflexivity.

Ltac t_postcondition_event_registers_pointer_Cbo
     Hstore' prefix prefix0 Hprefix01 eregs Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' HeqC Heqb Heqo :=
  eexists; eexists;
  [split; [| split]];
  [ erewrite Memory.load_after_store_eq; [reflexivity | exact Hstore']
  | rewrite /= HeqC Heqb Heqo //=
  |];
  t_postcondition_event_registers_get prefix prefix0 Hprefix01 eregs;
  rewrite Hget0 Hget1;
  injection Hshift0 as ?; subst vs0';
  injection Hshift1 as ?; subst vs1';
  unfold ssrnat.addn, ssrnat.subn, ssrnat.addn_rec, ssrnat.subn_rec,
  all_zeros_shift, uniform_shift;
  simpl;
  rewrite !Nat.add_0_r !Nat.sub_0_r HeqC Heqb Heqo;
  reflexivity.

                        (* General case analysis on values and operations. Most
                           cases can be solved from this information alone. *)
                        unfold shift_value_option,
                        rename_value_option,
                        rename_value_template_option,
                        rename_addr_option,
                        sigma_shifting_wrap_bid_in_addr,
                        sigma_shifting_lefttoright_addr_bid,
                        sigma_shifting_lefttoright_option in *.
                        unfold ssrnat.leq, ssrnat.addn, ssrnat.subn,
                        all_zeros_shift, uniform_shift in *.
                        unfold saved in *.
                        simpl.
                        destruct v0 as [n0 | [[[p0 C0] b0] o0] |];
                          destruct v1 as [n1 | [[[p1 C1] b1] o1] |];
                          destruct op;
                          simpl;
                          (* t_postcondition_event_registers_shift_pointers. *)
                          try t_postcondition_event_registers_binop_case
                              mem prefix prefix0 Hprefix01 eregs Hstore' Hget0 Hget1 Hshift0 Hshift1 vs0' vs1'.

                        (* In a few cases, more interesting pointer operations
                           are required. Note that this amount of case analysis
                           is overkill in the sense that one false check
                           suffices to short-circuit evaluation (and similar
                           optimizations may be possible above). *)

                        -- t_postcondition_event_registers_data_pointers mem;
                             simpl;
                             destruct (C0 =? C1) eqn:HeqC;
                             destruct (b0 =? b1) eqn:Heqb;
                             t_postcondition_event_registers_pointer_Cb
                               Hstore' HeqC Heqb prefix prefix0 Hprefix01 eregs Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' HeqC Heqb.

                        -- t_postcondition_event_registers_data_pointers mem;
                             simpl;
                             destruct (C0 =? C1) eqn:HeqC;
                             destruct (b0 =? b1) eqn:Heqb;
                             t_postcondition_event_registers_pointer_Cb
                               Hstore' HeqC Heqb prefix prefix0 Hprefix01 eregs Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' HeqC Heqb.

                        -- t_postcondition_event_registers_data_pointers mem;
                             simpl;
                             destruct (C0 =? C1) eqn:HeqC;
                             destruct (b0 =? b1) eqn:Heqb;
                             destruct (o0 <=? o1)%Z eqn:Heqo;
                             t_postcondition_event_registers_pointer_Cbo
                               Hstore' prefix prefix0 Hprefix01 eregs Hget0 Hget1 Hshift0 Hshift1 vs0' vs1' HeqC Heqb Heqo.

                      * setoid_rewrite Hcomp1 in Hregs.
                        destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                          as [v' Hload'].
                        rewrite Hoffset in Hload'.
                        destruct (Hregs n _ Logic.eq_refl) as [v [v'' [Hload [Hshift' Hget']]]].
                        assert (v = v'). {
                          subst off. rewrite Hload' in Hload. now injection Hload.
                        }
                        subst v'.
                        eexists. eexists.
                        split; [| split].
                        -- erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (subst off; injection; now destruct n).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (subst off; injection; now destruct n).
                           exact Hload'.
                        -- eassumption.
                        -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                           ++ destruct prefix; discriminate. (* contra *)
                           ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                           ++ rewrite Hprefix01 in Ht.
                              symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                              inversion Hstep as [| | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | | |];
                              subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                              subst eregs.
                              rewrite Machine.Intermediate.Register.gso;
                                first exact Hget'.
                              destruct n; destruct reg2; try discriminate; contradiction.
                    }
                + intros C' _ ?; subst C'. simpl.
                  specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                  split; [| split; [| split]].
                  (* The first two sub-goals are near-identical arguments on
                     memory operations. *)
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg2).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg2).
                    exact Hinitflag.
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg2).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg2).
                    exact Hlocalbuf.
                  (* ... *)
                  * intros b Hb. simpl.
                    specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                    destruct b as [| b']; first discriminate.
                    rewrite shift_S_Some in Hshift'.
                    injection Hshift' as ? ?; subst cid bid.
                    exists (C, b'). split; [| split].
                    -- rewrite shift_S_Some. reflexivity.
                    -- simpl. intros off v' Hload'.
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hstore';
                         last (injection; congruence).
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hmem;
                         last (injection; congruence).
                       simpl in Hrename.
                       specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ++ subst mem'. exact Hload''.
                       ++ exact Hrename''.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename'. subst mem'.
                       specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ++ erewrite Memory.load_after_store_neq;
                            last exact Hstore';
                            last (injection; congruence).
                          erewrite Memory.load_after_store_neq;
                            last exact Hmem;
                            last (injection; congruence).
                          exact Hload''.
                       ++ exact Hrename''.
                    * intros next Hnext.
                      rewrite Hmem' in Hnext.
                      specialize (Hnextblock next Hnext).
                      erewrite next_block_store_stable;
                        last exact Hstore'.
                      erewrite next_block_store_stable;
                        last exact Hmem.
                      exact Hnextblock.
                + intros C' Hcomp Hnext.
                  rewrite <- Hcomp1 in Hnext.
                  specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
                  * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                    left. split; [| split].
                    -- erewrite Memory.load_after_store_neq;
                         last exact Hstore';
                         last (injection; now destruct reg2).
                       erewrite Memory.load_after_store_neq;
                         last exact Hmem;
                         last (injection; now destruct reg2).
                       exact Hinitflag.
                    -- erewrite Memory.load_after_store_neq;
                         last exact Hstore';
                         last (injection; now destruct reg2).
                       erewrite Memory.load_after_store_neq;
                         last exact Hmem;
                         last (injection; now destruct reg2).
                       exact Hlocalbuf.
                    -- destruct Hsteady' as [Hsnapshot Hnextblock].
                       split.
                       ++ intros b Hlocal.
                          specialize (Hsnapshot b Hlocal) as [Cb [Hshift' [Hrename Hrename']]].
                          exists Cb. split; [| split].
                          ** exact Hshift'.
                          ** intros off v' Hload.
                             erewrite Memory.load_after_store_neq in Hload;
                               last exact Hstore';
                               last (injection; congruence).
                             erewrite Memory.load_after_store_neq in Hload;
                               last exact Hmem;
                               last (injection; congruence).
                             specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                             exists v''. split.
                             --- subst mem'. assumption.
                             --- congruence.
                          ** intros off v' Hload. subst mem'.
                             specialize (Hrename' off v' Hload) as [v'' [Hload'' Hrename']].                               exists v''. split.
                             --- erewrite Memory.load_after_store_neq;
                                   last exact Hstore';
                                   last (injection; congruence).
                                 erewrite Memory.load_after_store_neq;
                                   last exact Hmem;
                                   last (injection; congruence).
                                 assumption.
                             --- congruence.
                       ++ (* Same sub-proof on next block as above! *)
                         intros next Hnext'.
                         rewrite Hmem' in Hnext'.
                         specialize (Hnextblock next Hnext').
                         erewrite next_block_store_stable;
                           last exact Hstore'.
                         erewrite next_block_store_stable;
                           last exact Hmem.
                         exact Hnextblock.
                  * right.
                    destruct Hinitial as [Hinitflag [Hlocalbuf Hinitial]].
                    split; [| split].
                    -- erewrite Memory.load_after_store_neq;
                         last exact Hstore';
                         last (injection; now destruct reg2).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg2).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hlocalbuf.
                      -- destruct Hinitial as [Hprealloc Hnextblock].
                         split.
                         ** destruct Hprealloc
                             as [Cmem [buf [HCmem [Hbuf [Hnextblock' Hprealloc]]]]].
                            exists Cmem, buf.
                            split; [| split; [| split]]; try assumption.
                            rewrite -HCmem.
                            subst mem'. reflexivity.
                         ** destruct Hnextblock as [Cmem [HCmem Hnextblock]].
                            exists Cmem. split; last assumption.
                            rewrite -HCmem. symmetry.
                            transitivity (mem C').
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
              }

        - (* ELoad *)
          (* Gather a few recurrent assumptions at the top. *)
          rename e into reg0. rename e0 into reg1. rename t0 into eregs.
          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]]
            by admit;
            first admit. (* TODO: Treat empty case separately. *)
          (* destruct (well_formed_memory_store_reg_offset v ptr C_b wf_mem) as [mem' Hstore]. (* TODO: Consider actual utility of this. *) *)
          (* Const does not modify the (shared) memory, therefore these two
             should be identical. *)
          assert (Hmem' : s0 = mem_of_event_inform e1). {
            subst prefix.
            clear -wf_int_pref'.
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              reflexivity. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations! [ptr] seems to have no effect in the proofs. *)
          exists (ELoad C reg0 reg1 s0 eregs).
          destruct (wfmem_meta wf_mem reg0 C_b) as [v0 Hreg0mem0].
          destruct v0 as [n0 | ptr0 | ]; [admit | | admit].
          assert (Hreg0mem := Hreg0mem0).
          erewrite <- Memory.load_after_store_neq in Hreg0mem;
            last exact Hmem;
            last (injection; now destruct reg0).
          destruct (wfmem_meta wf_mem reg1 C_b) as [v1 Hreg1mem0].
          assert (Hreg1mem := Hreg1mem0).
          erewrite <- Memory.load_after_store_neq in Hreg1mem;
            last exact Hmem;
            last (injection; now destruct reg1).
          (* set (saved := v1). *)
          (* NOTE: In previous cases, we got to the store by a different route. *)
          assert (exists v, Memory.load mem ptr0 = Some v) as [vptr0 Hptr0mem] by admit.
          destruct (Memory.store_after_load _ _ _ vptr0 Hreg1mem) as [mem'' Hstore']. (* "Standard" names here... *)
          destruct ptr0 as [[[p0 C0] b0] o0].
          assert (p0 = Permission.data) by admit; subst p0.
          destruct b0 as [| b0']; first admit.
          (* Continue. *)
          exists (StackState C (callers s)).
          eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
          split.
          + (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
            take_steps.
            * exact Hreg0mem.
            * (* NOTE: Is it possible to do case analysis on [v0] here? *)
              take_steps.
              -- exact Hptr0mem.
              -- take_steps.
                 ++ exact Hstore'.
                 ++ (* Do recursive call. *)
                    take_steps.
                    ** reflexivity.
                    ** now apply find_procedures_of_trace.
                    ** (* Now we are done with the event.
                          We still need to process the external call check. *)
                       take_steps.
                       --- destruct (wfmem wf_mem Hprefix01) as [_ [Hsteady _]].
                           specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1)) as [Hoffset _].
                           erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; now destruct reg1).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (injection; now destruct reg1).
                           exact Hoffset.
                       --- take_steps.
                           +++ assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                                 last (now destruct reg1). (* Trivial property of register offsets. *)
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                                 last easy.
                               exact Hload0.
                           +++ unfold invalidate_metadata.
                               take_steps.
                               apply star_refl.
          + (* Reestablish invariant. *)
            econstructor; try reflexivity; try eassumption.
            { destruct s. exact wb. }
            { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy. }
            (* Reestablish memory well-formedness.
               TODO: Refactor, automate. *)
            { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
              constructor.
              - intros C_ Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                  assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset reg1) <> (Permission.data, C, Block.local, 0%Z))
                    by (now destruct reg1).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                  assumption.
                + erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (injection; contradiction).
                  assert (Hload0 := wfmem_counter wf_mem Hcomp).
                  assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                    by (now injection). (* Easy contradiction. *)
                  rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                  rewrite counter_value_snoc. simpl.
                  move: Hneq => /eqP.
                  case: ifP;
                    last now rewrite Z.add_0_r.
                  move => /eqP => Hcontra => /eqP => Hneq.
                  symmetry in Hcontra. contradiction.
              - intros Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                split.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg1; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    now rewrite Hcomp1.
                  * symmetry in Hnext. contradiction.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_. contradiction.
                  * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg1; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    intro; subst C_.
                    contradiction.
              - intros C_ reg Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  destruct (EregisterP reg reg1).
                  * subst reg1.
                    exists vptr0.
                    erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                  * erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (destruct reg; destruct reg1; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (now destruct reg).
                    eapply wfmem_meta; now eauto.
                + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                  exists v'.
                  erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (now injection).
                  erewrite Memory.load_after_store_neq;
                    try eassumption.
                  now destruct reg.
              - intro Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                destruct (wfmem wf_mem Hprefix01) as [Hregs [Hsteady Hinitial]].
                (* rename n into n0. rename v into v0. rename Hload into Hload0. rename mem' into mem'0. *) rename s0 into mem'. (* Trying to preserve proof script... *)
                split; [| split].
                + {
                    (* NOTE: We need to have the snapshot at hand, which is not
                       the case with the rearranged invariants. This can be
                       improved; compare also with [Hsnapshot0] later in this
                       same proof. *)
                    specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [_ [_ [Hsnapshot _]]].
                    (* Standard proof *)
                      subst mem'.
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hregs.
                      destruct (Z.eqb_spec (reg_offset reg1) off) as [Heq | Hneq].
                      - subst off.
                        assert (reg1 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst reg1.
                        (* assert (v = vptr0). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)
                        destruct (Nat.eqb_spec C C0) as [| HC0neq].
                        + subst C0.
                          specialize (Hsnapshot _ (Nat.neq_succ_0 b0'))
                            as [[cid bid] [Hshift' [Hrename Hrename']]].
                          injection Hshift' as Hcid Hbid.
                          rewrite /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                  /all_zeros_shift /uniform_shift /= Nat.add_0_r Nat.sub_0_r
                            in Hbid.
                          subst cid bid.
                          simpl in *.
                          assert (Hptr0mem0 := Hptr0mem).
                          erewrite Memory.load_after_store_neq in Hptr0mem0;
                            last exact Hmem;
                            last (injection; discriminate).
                          destruct (Hrename _ _ Hptr0mem0) as [v' [Hload' Hshift']].
                          eexists. eexists. split; [| split].
                          * erewrite Memory.load_after_store_eq;
                              [reflexivity | exact Hstore'].
                          * exact Hshift'.
                          * inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht];
                              [ destruct prefix; discriminate (* contra *)
                              | subst prefix; destruct prefix0 as [| ? [|]]; discriminate (* contra *)
                              | rewrite Hprefix01 in Ht;
                                symmetry in Ht; apply cats2_inv in Ht as [? [? ?]]; subst prefint eint1 eint2;
                                inversion Hstep as [| | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | |];
                                subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6;
                                subst eregs].
                            rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                            rewrite <- Hcomp1 in Hreg0mem0.
                            destruct (Hregs (Ereg_to_reg reg0) _ (f_equal _ (reg_to_Ereg_to_reg _)))
                              as [vtmp [v'' [Hload'' [Hshift'' Hget'']]]].
                            simpl in *.
                            rewrite Hreg0mem0 in Hload''. injection Hload'' as ?; subst vtmp.
                            rewrite /= /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                    /= Nat.add_0_r Nat.sub_0_r
                              in Hshift''.
                          injection Hshift'' as ?; subst v''.
                          rewrite <- H1 in H.
                          injection H as ?; subst ptr.
                          rewrite H0 in Hload'.
                          now injection Hload'.
                        + assert (C0_b : component_buffer C0) by admit.
                          unfold C in HC0neq.
                          rewrite <- Hcomp1 in HC0neq.
                          specialize (Hinitial _ C0_b (nesym HC0neq))
                            as [Hsteady | Hinitial].
                          * (* This is identical to the C = C0 case above. *)
                            destruct Hsteady
                              as [Hinitflag0 [Hlocalbuf0 [Hsnapshot0 Hnextblock0]]].
                            specialize (Hsnapshot0 _ (Nat.neq_succ_0 b0'))
                              as [[cid bid] [Hshift' [Hrename Hrename']]].
                            injection Hshift' as Hcid Hbid.
                            rewrite /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                    /all_zeros_shift /uniform_shift /= Nat.add_0_r Nat.sub_0_r
                              in Hbid.
                            subst cid bid.
                            simpl in *.
                            assert (Hptr0mem0 := Hptr0mem).
                            erewrite Memory.load_after_store_neq in Hptr0mem0;
                              last exact Hmem;
                              last (injection; discriminate).
                            destruct (Hrename _ _ Hptr0mem0) as [v' [Hload' Hshift']].
                            eexists. eexists. split; [| split].
                            -- erewrite Memory.load_after_store_eq;
                                 [reflexivity | exact Hstore'].
                            -- exact Hshift'.
                            -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht];
                                 [ destruct prefix; discriminate (* contra *)
                                 | subst prefix; destruct prefix0 as [| ? [|]]; discriminate (* contra *)
                                 | rewrite Hprefix01 in Ht;
                                   symmetry in Ht; apply cats2_inv in Ht as [? [? ?]]; subst prefint eint1 eint2;
                                   inversion Hstep as [| | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | |];
                                   subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6;
                                   subst eregs].
                               rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                               rewrite <- Hcomp1 in Hreg0mem0.
                               destruct (Hregs (Ereg_to_reg reg0) _ (f_equal _ (reg_to_Ereg_to_reg _)))
                                 as [vtmp [v'' [Hload'' [Hshift'' Hget'']]]].
                               simpl in *.
                               rewrite Hreg0mem0 in Hload''. injection Hload'' as ?; subst vtmp.
                               rewrite /= /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                       /= Nat.add_0_r Nat.sub_0_r
                                 in Hshift''.
                               injection Hshift'' as ?; subst v''.
                               rewrite <- H1 in H.
                               injection H as ?; subst ptr.
                               rewrite H0 in Hload'.
                               now injection Hload'.
                          * (* Contradiction on uninitialized C0, from which
                               nothing could have been shared. *)
                            destruct Hinitial
                              as [Hinitflag0 [Hlocalbuf0 Hsnapshot0]].
                            destruct Hsnapshot0
                              as [[Cmem0 [buf0 [HCmem0 [Hbuf0 [Hnext0 Hprealloc0]]]]]
                                  [Cmem0' [HCmem0' Hblock0']]].
                            subst Cmem0.
                            assert (Hptr0mem0 := Hptr0mem).
                            erewrite Memory.load_after_store_neq in Hptr0mem0;
                              last exact Hmem;
                              last (injection; discriminate).
Local Transparent Memory.load.
                            unfold Memory.load in Hptr0mem0.
Local Opaque Memory.load.
                            rewrite HCmem0' /= in Hptr0mem0.
                            apply ComponentMemory.load_next_block in Hptr0mem0.
                            rewrite Hblock0' in Hptr0mem0.
                            discriminate.
                    - setoid_rewrite Hcomp1 in Hregs.
                      destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                        as [v' Hload'].
                      rewrite Hoffset in Hload'.
                      destruct (Hregs n _ Logic.eq_refl) as [v [v'' [Hload [Hshift' Hget']]]].
                      assert (v = v'). {
                        subst off. rewrite Hload' in Hload. now injection Hload.
                      }
                      subst v'.
                      eexists. eexists.
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (subst off; injection; now destruct n).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (subst off; injection; now destruct n).
                         exact Hload'.
                      -- eassumption.
                      -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                         ++ destruct prefix; discriminate. (* contra *)
                         ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                         ++ rewrite Hprefix01 in Ht.
                            symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                            inversion Hstep as [| | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 | |];
                              subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                            subst eregs.
                            rewrite Machine.Intermediate.Register.gso;
                              first exact Hget'.
                            destruct n; destruct reg1; try discriminate; contradiction.
                    }
                + intros C' _ ?; subst C'. simpl.
                  specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                  split; [| split; [| split]].
                  (* The first two sub-goals are near-identical arguments on
                     memory operations. *)
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg1).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg1).
                    exact Hinitflag.
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg1).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg1).
                    exact Hlocalbuf.
                  (* ... *)
                  * intros b Hb. simpl.
                    specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                    destruct b as [| b']; first contradiction.
                    rewrite shift_S_Some in Hshift'.
                    injection Hshift' as ? ?; subst cid bid.
                    exists (C, b'). split; [| split].
                    -- rewrite shift_S_Some. reflexivity.
                    -- simpl. intros off v' Hload'.
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hstore';
                         last (injection; congruence).
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hmem;
                         last (injection; congruence).
                       simpl in Hrename.
                       specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ++ subst mem'. exact Hload''.
                       ++ exact Hrename''.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename'. subst mem'.
                       specialize (Hrename' off v' Hload') as [v'' [Hload'' Hrename'']].
                       exists v''. split.
                       ++ erewrite Memory.load_after_store_neq;
                            last exact Hstore';
                            last (injection; congruence).
                          erewrite Memory.load_after_store_neq;
                            last exact Hmem;
                            last (injection; congruence).
                          exact Hload''.
                       ++ exact Hrename''.
                  * intros next Hnext.
                    rewrite Hmem' in Hnext.
                    specialize (Hnextblock next Hnext).
                    erewrite next_block_store_stable;
                      last exact Hstore'.
                    erewrite next_block_store_stable;
                      last exact Hmem.
                    exact Hnextblock.
                  + intros C' Hcomp Hnext.
                    rewrite <- Hcomp1 in Hnext.
                    specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
                    * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                      left. split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg1).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg1).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg1).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg1).
                         exact Hlocalbuf.
                      -- destruct Hsteady' as [Hsnapshot Hnextblock].
                         split.
                         ++ intros b Hlocal.
                            specialize (Hsnapshot b Hlocal) as [Cb [Hshift' [Hrename Hrename']]].
                            exists Cb. split; [| split].
                            ** exact Hshift'.
                            ** intros off v' Hload.
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hstore';
                                 last (injection; congruence).
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hmem;
                                 last (injection; congruence).
                               specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                               exists v''. split.
                               --- subst mem'. assumption.
                               --- congruence.
                            ** intros off v' Hload. subst mem'.
                               specialize (Hrename' off v' Hload) as [v'' [Hload'' Hrename']].
                               exists v''. split.
                               --- erewrite Memory.load_after_store_neq;
                                     last exact Hstore';
                                     last (injection; congruence).
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hmem;
                                     last (injection; congruence).
                                   assumption.
                               --- congruence.
                         ++ (* Same sub-proof on next block as above! *)
                            intros next Hnext'.
                            rewrite Hmem' in Hnext'.
                            specialize (Hnextblock next Hnext').
                            erewrite next_block_store_stable;
                              last exact Hstore'.
                            erewrite next_block_store_stable;
                              last exact Hmem.
                            exact Hnextblock.
                    * right.
                      destruct Hinitial as [Hinitflag [Hlocalbuf Hinitial]].
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg1).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg1).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hlocalbuf.
                      -- destruct Hinitial as [Hprealloc Hnextblock].
                         split.
                         ** destruct Hprealloc
                             as [Cmem [buf [HCmem [Hbuf [Hnextblock' Hprealloc]]]]].
                            exists Cmem, buf.
                            split; [| split; [| split]]; try assumption.
                            rewrite -HCmem.
                            subst mem'. reflexivity.
                         ** destruct Hnextblock as [Cmem [HCmem Hnextblock]].
                            exists Cmem. split; last assumption.
                            rewrite -HCmem. symmetry.
                            transitivity (mem C').
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
              }

        - (* EStore *)
          rename e into reg0. rename e0 into reg1.
          (* rename s0 into emem. *)
          rename t0 into eregs.
          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]]
            by admit;
            first admit. (* TODO: Treat empty case separately. *)
          (* Relate memories before and after store. *)
          assert (exists ptr,
                     Machine.Intermediate.Register.get (Ereg_to_reg reg0) (register_file_of_event_inform e1) = Ptr ptr /\
                     Memory.store (mem_of_event_inform e1) ptr (Machine.Intermediate.Register.get (Ereg_to_reg reg1) (register_file_of_event_inform e1)) = Some s0)
            as [ptr [Hgetptr Hstore]]. {
            subst prefix.
            clear -wf_int_pref'.
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              now eauto. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations are irrelevant! *)
          exists (EStore C reg0 reg1 s0 eregs).
          destruct (wfmem_meta wf_mem reg0 C_b) as [v0 Hreg0mem0].
          assert (Hreg0mem := Hreg0mem0).
          erewrite <- Memory.load_after_store_neq in Hreg0mem;
            last exact Hmem;
            last (injection; now destruct reg0).
          destruct (wfmem_meta wf_mem reg1 C_b) as [v1 Hreg1mem0].
          assert (Hreg1mem := Hreg1mem0).
          erewrite <- Memory.load_after_store_neq in Hreg1mem;
            last exact Hmem;
            last (injection; now destruct reg1).
          destruct (wfmem wf_mem Hprefix01) as [Hregs1 [Hsteady1 Hinitial1]].
          specialize (Hsteady1 _ C_b (Logic.eq_sym Hcomp1))
            as [Hoffset1 [Hblockid1 Hsteady1]].

          (* ... *)
          (* unfold postcondition_event_registers in Hregs1. *)
          destruct (Hregs1 (Ereg_to_reg reg0) _ (f_equal _ (reg_to_Ereg_to_reg _)))
            as [v0'' [v0' [Hreg0mem0' [Hshiftv0 Hgetv0']]]].
          rewrite Hcomp1 Hreg0mem0 in Hreg0mem0'.
          injection Hreg0mem0' as ?; subst v0''.
          rewrite Hgetptr in Hgetv0'. subst v0'.
          (* unfold well_formed_memory_snapshot_steadystate_shift in Hsnapshot1. *)

          destruct v0 as [n0 | [[[p0 C0] b0] o0] |]; try discriminate Hshiftv0.
          assert (p0 = Permission.data) by admit; subst p0.
          rewrite /= /rename_addr_option
                  /sigma_shifting_wrap_bid_in_addr
                  /sigma_shifting_lefttoright_addr_bid
                  /sigma_shifting_lefttoright_option
                  /all_zeros_shift /uniform_shift
                  /ssrnat.leq
                  /ssrnat.addn /ssrnat.addn_rec
                  /ssrnat.subn /ssrnat.subn_rec
                  (* /= *)
                  Nat.add_0_r
                  (* Nat.add_0_r /= Nat.sub_0_r. *)
            in Hshiftv0.
          destruct b0 as [| b0']; first discriminate.
          rewrite /= Nat.sub_0_r
            in Hshiftv0.
          injection Hshiftv0 as ?; subst ptr.

          (* destruct (Memory.store_after_load _ _ _ v1 Hreg0mem) as [mem'' Hstore']. *)
          assert (exists vptr, Memory.load mem (Permission.data, C0, S b0', o0) = Some vptr)
            as [vptr Hvptrmem]
            by admit. (* TODO: Missing invariant (should start with mem0)! *)
          destruct (Memory.store_after_load _ _ _ v1 Hvptrmem) as [mem'' Hstore'].

          (* Is this useful? *)
          destruct (Hregs1 (Ereg_to_reg reg1) _ (f_equal _ (reg_to_Ereg_to_reg _)))
            as [v1'' [v1' [Hreg1mem0' [Hshiftv1 Hgetv1']]]].
          subst v1'.
          rewrite Hcomp1 Hreg1mem0 in Hreg1mem0'.
          injection Hreg1mem0' as ?; subst v1''.

          exists (StackState C (callers s)).
          eexists.
          split.
          + (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
            take_steps.
            * exact Hreg1mem.
            * take_steps.
              -- exact Hreg0mem.
              -- take_steps.
                 ++ exact Hstore'.
                 ++ (* Do recursive call. *)
                    take_steps.
                    ** reflexivity.
                    ** now apply find_procedures_of_trace.
                    ** (* Now we are done with the event.
                          We still need to process the external call check. *)
                       take_steps.
                       --- destruct (wfmem wf_mem Hprefix01) as [_ [Hsteady _]].
                           specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1)) as [Hoffset _].
                           erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; discriminate).
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (injection; discriminate).
                           exact Hoffset.
                       --- take_steps.
                           +++ assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                                 last (now destruct reg0). (* Trivial property of register offsets. *)
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                                 last easy.
                               exact Hload0.
                           +++ unfold invalidate_metadata.
                               take_steps.
                               apply star_refl.
          + (* Reestablish invariant. *)
            econstructor; try reflexivity; try eassumption.
            { destruct s. exact wb. }
            { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy. }
            (* Reestablish memory well-formedness.
               TODO: Refactor, automate. *)
            { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
              (* instantiate (1 := mem). (* FIXME *) *)
              constructor.
              - intros C_ Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                  (* assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset reg0) <> (Permission.data, C, Block.local, 0%Z)) *)
                  (*   by (now destruct reg0). *)
                  erewrite Memory.load_after_store_neq;
                    last exact Hstore';
                    last (injection; discriminate).
                  assumption.
                + erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (injection; discriminate).
                  assert (Hload0 := wfmem_counter wf_mem Hcomp).
                  assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                    by (now injection). (* Easy contradiction. *)
                  rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                  rewrite counter_value_snoc. simpl.
                  move: Hneq => /eqP.
                  case: ifP;
                    last now rewrite Z.add_0_r.
                  move => /eqP => Hcontra => /eqP => Hneq.
                  symmetry in Hcontra. contradiction.
              - intros Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                split.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg0; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    now rewrite Hcomp1.
                  * symmetry in Hnext. contradiction.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_. contradiction.
                  * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg0; discriminate).
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    intro; subst C_.
                    contradiction.
              - intros C_ reg Hcomp.
                (* This sub-proof becomes simpler. *)
                erewrite Memory.load_after_store_neq;
                  last exact Hstore';
                  last (injection; discriminate).
                erewrite Memory.load_after_store_neq;
                  last exact Hmem;
                  last (destruct reg; discriminate).
                eapply wfmem_meta; now eauto.
              - intro Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                destruct (wfmem wf_mem Hprefix01) as [Hpostregs [Hsteady Hinitial]]. (* NOTE: Repeated assumptions above! *)
                (* rename n into n0. rename v into v0. rename Hload into Hload0. rename mem' into mem'0. *) rename s0 into mem'. (* Trying to preserve proof script... *)
                split; [| split].
                + { (* No register changes, thus simpler proof. *)
                      (* subst mem'. *)
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hpostregs.
                      destruct (Hpostregs _ _ Hoffset)
                        as [vtmp [v'' [Hload'' [Hshift'' Hget'']]]].
                      eexists. eexists. split; [| split].
                      - erewrite Memory.load_after_store_neq;
                        last exact Hstore';
                        last (injection; discriminate).
                        erewrite Memory.load_after_store_neq;
                          last exact Hmem;
                          last (subst off; injection; by destruct n).
                        rewrite -Hcomp1.
                        exact Hload''.
                      - exact Hshift''.
                      - inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht];
                          [ destruct prefix; discriminate (* contra *)
                          | subst prefix; destruct prefix0 as [| ? [|]]; discriminate (* contra *)
                          | rewrite Hprefix01 in Ht;
                            symmetry in Ht; apply cats2_inv in Ht as [? [? ?]]; subst prefint eint1 eint2;
                            inversion Hstep as [| | | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 |];
                            subst tmp1 tmp2 tmp3 tmp4 tmp6 tmp7;
                            subst eregs].
                        exact Hget''.
                    }
                + intros C' _ ?; subst C'. simpl.
                  specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                  split; [| split; [| split]].
                  (* The first two sub-goals are near-identical arguments on
                     memory operations. *)
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; discriminate).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; discriminate).
                    exact Hinitflag.
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; discriminate).
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; discriminate).
                    exact Hlocalbuf.
                  (* ... *)
                  * intros b Hb. simpl.
                    (* Instead of specialize... (?) *)
                    destruct (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                    destruct b as [| b'];
                      first discriminate.
                    rewrite shift_S_Some in Hshift'.
                    injection Hshift' as ? ?; subst cid bid.
                    exists (C, b'). split; [| split].
                    (* eexists. split; [| split]. *)
                    -- rewrite shift_S_Some.
                       reflexivity.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename.
                       (* ... *)
                       destruct (Pointer.eqP
                                   (Permission.data, C, b', off)
                                   (Permission.data, C0, b0', o0)) as [Heq | Hneq].
                       ++ injection Heq as ? ? ?; subst C0 b0' o0.
                          erewrite Memory.load_after_store_eq in Hload';
                            last exact Hstore'.
                          injection Hload' as ?; subst v'.
                          eexists. split.
                          ** erewrite Memory.load_after_store_eq;
                               last exact Hstore.
                             reflexivity.
                          ** rewrite -Hshiftv1.
                             reflexivity.
                       ++ erewrite Memory.load_after_store_neq in Hload';
                            last exact Hstore';
                            last (injection as ? ? ?; subst C0 b0' o0; contradiction).
                          erewrite Memory.load_after_store_neq in Hload';
                            last exact Hmem;
                            last (injection; discriminate).
                          (* Instead of specialize... (?) *)
                          destruct (Hrename _ _ Hload') as [v'' [Hload'' Hrename'']].
                          eexists. split.
                          ** erewrite Memory.load_after_store_neq;
                               last exact Hstore;
                               last by intuition. (* Better than case analysis! *)
                             exact Hload''.
                          ** exact Hrename''.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename'.
                       (* ... *)
                       destruct (Pointer.eqP
                                   (Permission.data, C, b', off)
                                   (Permission.data, C0, b0', o0)) as [Heq | Hneq].
                       ++ injection Heq as ? ? ?; subst C0 b0' o0.
                          erewrite Memory.load_after_store_eq in Hload';
                            last exact Hstore.
                          injection Hload' as ?; subst v'.
                          eexists. split.
                          ** erewrite Memory.load_after_store_eq;
                               last exact Hstore'.
                             reflexivity.
                          ** rewrite -Hshiftv1.
                             reflexivity.
                       ++ erewrite Memory.load_after_store_neq in Hload';
                            last exact Hstore;
                            last by intuition.
                          destruct (Hrename' _ _ Hload') as [v'' [Hload'' Hrename'']].
                          eexists. split.
                          ** erewrite Memory.load_after_store_neq;
                               last exact Hstore';
                               last (injection as ? ? ?; subst C0 b0' o0; contradiction).
                             erewrite Memory.load_after_store_neq;
                               last exact Hmem;
                               last (injection; discriminate).
                             exact Hload''.
                          ** exact Hrename''.
                  * intros next Hnext.
                    erewrite next_block_store_stable in Hnext;
                      last exact Hstore.
                    (* rewrite Hmem' in Hnext. *)
                    specialize (Hnextblock next Hnext).
                    erewrite next_block_store_stable;
                      last exact Hstore'.
                    erewrite next_block_store_stable;
                      last exact Hmem.
                    exact Hnextblock.
                + intros C' Hcomp Hnext.
                  destruct (Nat.eqb_spec C0 C') as [| Hneq].
                  { (* Store-specific sub-proof *)
                    subst C0.
                    rewrite <- Hcomp1 in Hnext.
                    (* specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial]. *)
                    assert (Hsteady' : postcondition_steady_state e1 mem0 C')
                      by admit. (* TODO: rule out uninitialized state *)
                    (* left. (* There is only one way to go. *) *)
                    destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                    left. split; [| split].
                    -- erewrite Memory.load_after_store_neq;
                         last exact Hstore';
                         last (injection; discriminate).
                       erewrite Memory.load_after_store_neq;
                         last exact Hmem;
                         last (injection; discriminate).
                       exact Hinitflag.
                    -- erewrite Memory.load_after_store_neq;
                         last exact Hstore';
                         last (injection; discriminate).
                       erewrite Memory.load_after_store_neq;
                         last exact Hmem;
                         last (injection; discriminate).
                       exact Hlocalbuf.
                    -- destruct Hsteady' as [Hsnapshot Hnextblock].
                       split.
                       ++ intros b Hlocal.
                          specialize (Hsnapshot b Hlocal) as [Cb [Hshift' [Hrename Hrename']]].
                          exists Cb. split; [| split].
                          ** exact Hshift'. (* Goes away, trivial property though *)
                          ** intros off v' Hload. simpl.
                             destruct b as [| b']; first discriminate.
                             rewrite shift_S_Some in Hshift'.
                             injection Hshift' as ?; subst Cb. (* Should be done upfront *)
                             (* Where should we do case analysis on pointer equality? *)
                             destruct (Pointer.eqP
                                         (Permission.data, C', b', off)
                                         (Permission.data, C', b0', o0))
                               as [Heq | Hneq].
                             --- injection Heq as ? ?; subst b0' o0.
                                 erewrite Memory.load_after_store_eq in Hload;
                                   last exact Hstore'.
                                 injection Hload as ?; subst v'.
                                 eexists. split.
                                 +++ erewrite Memory.load_after_store_eq;
                                       last exact Hstore.
                                     reflexivity.
                                 +++ exact Hshiftv1.
                             --- erewrite Memory.load_after_store_neq in Hload;
                                   last exact Hstore';
                                   last (injection; congruence).
                                 erewrite Memory.load_after_store_neq in Hload;
                                   last exact Hmem;
                                   last (injection; discriminate).
                                 specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                                 exists v''. split.
                                 +++ erewrite Memory.load_after_store_neq;
                                       last exact Hstore;
                                       last (injection; congruence).
                                     exact Hload''.
                                 +++ congruence.
                          ** intros off v' Hload.
                             destruct b as [| b']; first discriminate.
                             rewrite shift_S_Some in Hshift'.
                             injection Hshift' as ?; subst Cb. (* Should be done upfront *)
                             simpl in Hload.
                             (* Where should we do case analysis on pointer equality? *)
                             destruct (Pointer.eqP
                                         (Permission.data, C', b', off)
                                         (Permission.data, C', b0', o0))
                               as [Heq | Hneq].
                             --- injection Heq as ? ?; subst b0' o0.
                                 erewrite Memory.load_after_store_eq in Hload;
                                   last exact Hstore.
                                 injection Hload as ?; subst v'.
                                 eexists. split.
                                 +++ erewrite Memory.load_after_store_eq;
                                       last exact Hstore'.
                                     reflexivity.
                                 +++ exact Hshiftv1.
                             --- erewrite Memory.load_after_store_neq in Hload;
                                   last exact Hstore;
                                   last (injection; congruence).
                                 specialize (Hrename' off v' Hload) as [v'' [Hload'' Hrename']].
                                 exists v''. split.
                                 +++ erewrite Memory.load_after_store_neq;
                                     last exact Hstore';
                                     last (injection; congruence).
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hmem;
                                     last (injection; congruence).
                                   assumption.
                                 +++ congruence.
                         ++ (* Same sub-proof on next block as above! *)
                             intros next Hnext'.
                             erewrite next_block_store_stable in Hnext';
                               last exact Hstore.
                             specialize (Hnextblock next Hnext').
                             erewrite next_block_store_stable;
                               last exact Hstore'.
                             erewrite next_block_store_stable;
                               last exact Hmem.
                             exact Hnextblock.
                  }
                  { (* The standard proof works in this case *)
                    rewrite <- Hcomp1 in Hnext.
                    specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
                    * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                      left. split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; discriminate).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; discriminate).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hlocalbuf.
                      -- destruct Hsteady' as [Hsnapshot Hnextblock].
                         split.
                         ++ intros b Hlocal.
                            specialize (Hsnapshot b Hlocal) as [Cb [Hshift' [Hrename Hrename']]].
                            exists Cb. split; [| split].
                            ** exact Hshift'. (* Goes away, trivial property though *)
                            ** intros off v' Hload.
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hstore';
                                 last (injection as ? ? ?; contradiction).
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hmem;
                                 last (injection as ? ? ?; subst C' b off; contradiction).
                               specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                               exists v''. split.
                               --- (* Cf. Hstore, Hshift' (should be treated upfront) *)
                                   destruct b as [| b']; first discriminate.
                                   rewrite shift_S_Some in Hshift'.
                                   injection Hshift' as ?; subst Cb.
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hstore;
                                     last (injection; contradiction).
                                   exact Hload''.
                               --- congruence.
                            ** intros off v' Hload.
                               destruct b as [| b']; first discriminate.
                               rewrite shift_S_Some in Hshift'.
                               injection Hshift' as ?; subst Cb. (* Should be done upfront *)
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hstore;
                                 last (injection; congruence).
                               specialize (Hrename' off v' Hload) as [v'' [Hload'' Hrename']].
                               exists v''. split.
                               --- erewrite Memory.load_after_store_neq;
                                     last exact Hstore';
                                     last (injection; contradiction).
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hmem;
                                     last (injection; discriminate).
                                   assumption.
                               --- congruence.
                         ++ (* Same sub-proof on next block as above! *)
                             intros next Hnext'.
                             erewrite next_block_store_stable in Hnext';
                               last exact Hstore.
                             specialize (Hnextblock next Hnext').
                             erewrite next_block_store_stable;
                               last exact Hstore'.
                             erewrite next_block_store_stable;
                               last exact Hmem.
                             exact Hnextblock.
                    * right.
                      destruct Hinitial as [Hinitflag [Hlocalbuf Hinitial]].
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; discriminate).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; discriminate).
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; discriminate).
                         exact Hlocalbuf.
                      -- destruct Hinitial as [Hprealloc Hnextblock].
                         split.
                         ** destruct Hprealloc
                             as [Cmem [buf [HCmem [Hbuf [Hnextblock' Hprealloc]]]]].
                            exists Cmem, buf.
                            split; [| split; [| split]]; try assumption.
                            rewrite -HCmem. symmetry.
                            by eapply component_memory_after_store_neq; eauto.
                         ** destruct Hnextblock as [Cmem [HCmem Hnextblock]].
                            exists Cmem. split; last assumption.
                            rewrite -HCmem. symmetry.
                            transitivity (mem C').
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
                            --- by eapply component_memory_after_store_neq; eauto.
                  }
              }

        - (* EAlloc *)
          (* Gather a few recurrent assumptions at the top. *)
          rename e into reg0. rename e0 into reg1.
          (* rename s0 into emem. *)
          rename t0 into eregs.
          assert (prefix = [::] \/ exists prefix' e', prefix = prefix' ++ [:: e'])
            as [Hprefix | [prefix0 [e1 Hprefix01]]]
            by admit;
            first admit. (* TODO: Treat empty case separately. *)
          (* Extract known memory facts. *)
          assert (exists size ptr,
                     Machine.Intermediate.Register.get (Ereg_to_reg reg1) (register_file_of_event_inform e1) = Int size /\
                     (size > 0)%Z /\
                     Memory.alloc (mem_of_event_inform e1) (cur_comp s) (Z.to_nat size) = Some (s0, ptr))
            as [size [ptr [Hregse1 [Hsize' Halloc']]]]. {
            subst prefix.
            clear -wf_int_pref'.
            (* Maybe keep shift? *)
            move: wf_int_pref'; rewrite !cats1 => wf_int_pref.
            inversion wf_int_pref.
            - now destruct prefix0.
            - destruct prefix0. inversion H. simpl in H. now destruct prefix0.
            - apply rcons_inj in H. inversion H; subst; clear H.
              apply rcons_inj in H3. inversion H3; subst; clear H3.
              inversion H1; subst; clear H1.
              now eauto. }
          assert (Hcomp1 : next_comp_of_event e1 = cur_comp s) by admit.
          (* NOTE: Instantiations! [ptr] seems to have no effect in the proofs. *)
          exists (EAlloc C reg0 reg1 s0 eregs).
          (* TODO: Clean assumptions, refactor. *)
          destruct (wfmem_meta wf_mem reg0 C_b) as [v0 Hreg0mem0].
          assert (Hreg0mem := Hreg0mem0).
          erewrite <- Memory.load_after_store_neq in Hreg0mem;
            last exact Hmem;
            last (injection; now destruct reg0).
          destruct (wfmem_meta wf_mem reg1 C_b) as [v1 Hreg1mem0].
          assert (Hreg1mem := Hreg1mem0).
          erewrite <- Memory.load_after_store_neq in Hreg1mem;
            last exact Hmem;
            last (injection; now destruct reg1).
          destruct (wfmem wf_mem Hprefix01) as [Hregs1 [Hsteady1 Hinitial1]].
          specialize (Hsteady1 _ C_b (Logic.eq_sym Hcomp1)) as [Hoffset1 [Hblockid1 [Hsnapshot1 Hblock1]]].
          (* Some alloc-specific reasoning... *)
          (* NOTE: This should come from well-formedness of events. *)
          destruct v1 as [n1 | ptr1 |]; [| admit | admit].
          assert (Hsize : (n1 > 0)%Z) by admit.
          destruct (next_block_alloc Halloc') as [Hnexte1 Hnexts0].
          destruct ptr as [[[pptr Cptr] bptr] optr].
          injection (pointer_of_alloc Halloc' Hnexte1) as ? ? ?; subst pptr Cptr optr.
          (* NOTE: In previous cases, we got to the store by a different route. *)
          destruct (Memory.alloc_after_load _ _ _ _ _ _ (Z.to_nat n1) Hreg0mem)
            as [mem' [bnew [Hb' Halloc]]].
          (* Some more work on this second alloc... *)
          destruct (next_block_alloc Halloc) as [Hnextmem Hnextmem'].
          simpl in Hnextmem, Hnextmem'.
          specialize (Hblock1 _ Hnexte1).
          rewrite <- (next_block_store_stable _ Hmem) in Hblock1.
          rewrite Hblock1 in Hnextmem.
          injection Hnextmem as ?; subst bnew.
          unfold postcondition_event_registers in Hregs1.
          destruct (Hregs1 (Ereg_to_reg reg1) _ Logic.eq_refl)
            as [v1 [v1' [Hloadv1 [Hshiftv1 Hgetv1']]]].
          rewrite Hregse1 in Hgetv1'; subst v1'.
          rewrite reg_to_Ereg_to_reg Hcomp1 Hreg1mem0 in Hloadv1.
          injection Hloadv1 as ?; subst v1.
          injection Hshiftv1 as ?; subst size.
          (* ... *)
          set (saved := Ptr (Permission.data, cur_comp s, S bptr, 0%Z)).
          assert (Hreg0mem' := Hreg0mem).
          erewrite <- Memory.load_after_alloc in Hreg0mem';
            [| exact Halloc | injection; congruence].
          destruct (Memory.store_after_load _ _ _ saved Hreg0mem') as [mem'' Hstore']. (* "Standard" names here... *)
          (* Continue. *)
          exists (StackState C (callers s)).
          eexists. (* evar (CS : state (CS.sem p)). exists CS. *)
          split.
          + (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
            take_steps.
            * exact Hreg1mem.
            * take_steps.
              -- exact Hsize.
              -- exact Halloc.
              -- take_steps.
                 ++ exact Hstore'.
                 ++ (* Do recursive call. *)
                    take_steps.
                    ** reflexivity.
                    ** now apply find_procedures_of_trace.
                    ** (* Now we are done with the event.
                          We still need to process the external call check. *)
                       take_steps.
                       --- destruct (wfmem wf_mem Hprefix01) as [_ [Hsteady _]].
                           specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1)) as [Hoffset _].
                           erewrite Memory.load_after_store_neq;
                             last exact Hstore';
                             last (injection; now destruct reg0).
                           erewrite Memory.load_after_alloc;
                             [| exact Halloc | injection; discriminate].
                           erewrite Memory.load_after_store_neq;
                             last exact Hmem;
                             last (injection; now destruct reg0).
                           exact Hoffset.
                       --- take_steps.
                           +++ assert (Hload0 := proj1 (wfmem_extcall wf_mem Hprefix01) _ C_b (Logic.eq_sym Hcomp1)).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                                 last (now destruct reg0). (* Trivial property of register offsets. *)
                               (* Alloc-specific *)
                               erewrite Memory.load_after_alloc;
                                 [| exact Halloc | injection; congruence].
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                                 last easy.
                               exact Hload0.
                           +++ unfold invalidate_metadata.
                               take_steps.
                               apply star_refl.
          + (* Reestablish invariant. *)
            econstructor; try reflexivity; try eassumption.
            { destruct s. exact wb. }
            { destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy. }
            (* Reestablish memory well-formedness.
               TODO: Refactor, automate. *)
            { (* destruct wf_mem as [wfmem_counter wfmem_meta wfmem]. *)
              (* instantiate (1 := mem). (* FIXME *) *)
              constructor.
              - intros C_ Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  pose proof Memory.load_after_store_eq _ _ _ _ Hmem as Hmem0.
                  assert (Hoffsetneq' : (Permission.data, C, Block.local, reg_offset reg0) <> (Permission.data, C, Block.local, 0%Z))
                    by (now destruct reg0).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ Hoffsetneq' Hstore').
                  erewrite Memory.load_after_alloc;
                    [| exact Halloc | injection; congruence].
                  assumption.
                + erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (injection; contradiction).
                  assert (Hload0 := wfmem_counter wf_mem Hcomp).
                  assert (HCneq : (Permission.data, C, Block.local, 0%Z) <> (Permission.data, C_, Block.local, 0%Z))
                    by (now injection). (* Easy contradiction. *)
                  rewrite <- (Memory.load_after_store_neq _ _ _ _ _ HCneq Hmem) in Hload0.
                  erewrite <- Memory.load_after_alloc in Hload0;
                    [| exact Halloc | injection; congruence].
                  rewrite counter_value_snoc. simpl.
                  move: Hneq => /eqP.
                  case: ifP;
                    last now rewrite Z.add_0_r.
                  move => /eqP => Hcontra => /eqP => Hneq.
                  symmetry in Hcontra. contradiction.
              - intros Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                split.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_.
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg0; discriminate).
                    erewrite Memory.load_after_alloc;
                      [| exact Halloc | injection; congruence].
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj1 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    now rewrite Hcomp1.
                  * symmetry in Hnext. contradiction.
                + intros C_ Hcomp Hnext.
                  destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                  * subst C_. contradiction.
                  * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hstore');
                      last (injection; destruct reg0; discriminate).
                    erewrite Memory.load_after_alloc;
                      [| exact Halloc | injection; congruence].
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (injection; discriminate).
                    apply (proj2 (wfmem_extcall wf_mem Hprefix01) _ Hcomp).
                    intro; subst C_.
                    contradiction.
              - intros C_ reg Hcomp.
                destruct (Nat.eqb_spec C C_) as [Heq | Hneq].
                + subst C_.
                  destruct (EregisterP reg reg0).
                  * subst reg0.
                    (* exists (Int n). *)
                    exists saved.
                    erewrite Memory.load_after_store_eq; try reflexivity; eassumption.
                  * erewrite Memory.load_after_store_neq;
                      last eassumption;
                      last (destruct reg; destruct reg0; try discriminate; contradiction). (* This kind of reasoning on register offsets can be made into a lemma as well. *)
                    erewrite Memory.load_after_alloc;
                      [| exact Halloc | injection; congruence].
                    rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hmem);
                      last (now destruct reg).
                    eapply wfmem_meta; now eauto.
                + destruct (wfmem_meta wf_mem reg Hcomp) as [v' Hload'].
                  exists v'.
                  erewrite Memory.load_after_store_neq;
                    last eassumption;
                    last (now injection).
                  erewrite Memory.load_after_alloc;
                    [| exact Halloc | injection; congruence].
                  erewrite Memory.load_after_store_neq;
                    try eassumption.
                  now destruct reg.
              - intro Hcontra. now destruct prefix.
              - intros pref ev Hprefix.
                apply rcons_inv in Hprefix as [? ?]; subst pref ev.
                destruct (wfmem wf_mem Hprefix01) as [Hpostregs [Hsteady Hinitial]].
                (* rename n into n0. rename v into v0. rename Hload into Hload0. rename mem' into mem'0. *) (* rename s0 into mem'. *) (* Trying to preserve proof script... *)
                split; [| split].
                + {
                    (* NOTE: For simplicity, replacing some hypotheses with their available *1's *)
                      (* subst mem'. *)
                      intros n off Hoffset.
                      simpl in *.
                      (* subst v prefix. *)
                      unfold postcondition_event_registers in Hpostregs.
                      destruct (Z.eqb_spec (reg_offset reg0) off) as [Heq | Hneq].
                      - subst off.
                        assert (reg0 = CS.CS.reg_to_Ereg n)
                          by (now apply reg_offset_inj in Heq).
                        subst reg0.
                        (* assert (v = vptr0). { *)
                        (*   rewrite (Memory.load_after_store_eq _ _ _ _ Hstore') in Hload. *)
                        (*   now injection Hload as ?. } *)
                        (* subst v. *)
                        specialize (Hsnapshot1 _ Hb')
                          as [[cid bid] [Hshift' [Hrename Hrename']]].
                        (* destruct bnew as [| bnew']; *)
                        (*   first admit. (* contra *) *)
                        injection Hshift' as Hcid Hbid.
                        rewrite /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                /all_zeros_shift /uniform_shift /= Nat.add_0_r Nat.sub_0_r
                          in Hbid.
                        subst cid bid.
                        simpl in *.

                        eexists. eexists. split; [| split].
                        * erewrite Memory.load_after_store_eq;
                            [reflexivity | exact Hstore'].
                        * rewrite /= /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec
                                  /= Nat.add_0_r Nat.sub_0_r.
                          reflexivity.
                        * inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht];
                            [ destruct prefix; discriminate (* contra *)
                            | subst prefix; destruct prefix0 as [| ? [|]]; discriminate (* contra *)
                            | rewrite Hprefix01 in Ht;
                              symmetry in Ht; apply cats2_inv in Ht as [? [? ?]]; subst prefint eint1 eint2;
                              inversion Hstep as [| | | | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6];
                              subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6;
                              subst eregs].
                          rewrite Ereg_to_reg_to_Ereg Machine.Intermediate.Register.gss.
                          rewrite <- Hcomp1 in Hreg1mem0.
                          destruct (Hregs1 (Ereg_to_reg reg1) _ (f_equal _ (reg_to_Ereg_to_reg _)))
                            as [vtmp [v'' [Hload'' [Hshift'' Hget'']]]].

                          rewrite Hreg1mem0 in Hload''. injection Hload'' as ?; subst vtmp.
                          (* rewrite /= /ssrnat.addn /ssrnat.addn_rec /ssrnat.subn /ssrnat.subn_rec *)
                          (*         /= Nat.add_0_r Nat.sub_0_r *)
                          (*   in Hshift''. *)
                          injection Hshift'' as ?; subst v''.

                          rewrite Hget'' in H. injection H as ?; subst size.
                          rewrite Halloc' in H1. injection H1 as ?; subst ptr.
                          reflexivity.

                    - setoid_rewrite Hcomp1 in Hregs1.
                      destruct (wfmem_meta wf_mem (CS.CS.reg_to_Ereg n) C_b)
                        as [v' Hload'].
                      rewrite Hoffset in Hload'.
                      destruct (Hregs1 n _ Logic.eq_refl) as [v [v'' [Hload [Hshift' Hget']]]].
                      assert (v = v'). {
                        subst off. rewrite Hload' in Hload. now injection Hload.
                      }
                      subst v'.
                      eexists. eexists.
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (subst off; injection; now destruct n).
                         erewrite Memory.load_after_alloc;
                           [| exact Halloc | injection; congruence].
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (subst off; injection; now destruct n).
                         exact Hload'.
                      -- eassumption.
                      -- inversion wf_int_pref' as [| | prefint eint1 eint2 Hsteps Hstep Ht].
                         ++ destruct prefix; discriminate. (* contra *)
                         ++ subst prefix. destruct prefix0 as [| ? [ | ]]; discriminate. (* contra *)
                         ++ rewrite Hprefix01 in Ht.
                            symmetry in Ht. apply cats2_inv in Ht as [? [? ?]]. subst prefint eint1 eint2.
                            inversion Hstep as [| | | | | | | tmp1 tmp2 tmp3 tmp4 tmp5 tmp6];
                              subst tmp1 tmp2 tmp3 tmp4 tmp5 tmp6.
                            subst eregs.
                            rewrite Machine.Intermediate.Register.gso;
                              first exact Hget'.
                            destruct n; destruct reg0; try discriminate; contradiction.
                    }
                + intros C' _ ?; subst C'. simpl.
                  specialize (Hsteady _ C_b (Logic.eq_sym Hcomp1))
                    as [Hinitflag [Hlocalbuf [Hsnapshot Hnextblock]]].
                  split; [| split; [| split]].
                  (* The first two sub-goals are near-identical arguments on
                     memory operations. *)
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg0).
                    erewrite Memory.load_after_alloc;
                      [| exact Halloc | injection; discriminate].
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg0).
                    exact Hinitflag.
                  * erewrite Memory.load_after_store_neq;
                      last exact Hstore';
                      last (injection; now destruct reg0).
                    erewrite Memory.load_after_alloc;
                      [| exact Halloc | injection; discriminate].
                    erewrite Memory.load_after_store_neq;
                      last exact Hmem;
                      last (injection; now destruct reg0).
                    exact Hlocalbuf.
                  (* ... *)
                  * intros b Hb. simpl.
                    specialize (Hsnapshot b Hb) as [[cid bid] [Hshift' [Hrename Hrename']]].
                    destruct b as [| b']; first discriminate.
                    rewrite shift_S_Some in Hshift'.
                    injection Hshift' as ? ?; subst cid bid.
                    exists (C, b'). split; [| split].
                    -- rewrite shift_S_Some.
                       reflexivity.
                    -- simpl. intros off v' Hload'.
                       erewrite Memory.load_after_store_neq in Hload';
                         last exact Hstore';
                         last (injection; congruence).
                       destruct (Nat.eqb_spec (S b') (S bptr)) as [Heq | Hneq].
                       ++ injection Heq as ?; subst b'.
                          erewrite Memory.load_after_alloc_eq in Hload';
                            [| exact Halloc | reflexivity].
                          simpl in Hload'.
                          destruct (off <? Z.of_nat (Z.to_nat n1))%Z eqn:Hoff1;
                            last discriminate.
                          destruct (0 <=? off)%Z eqn:Hoff2;
                            last discriminate.
                          injection Hload' as ?; subst v'.
                          eexists. split; last reflexivity.
                          by rewrite (Memory.load_after_alloc_eq _ _ _ _ _ (_, _, _, off) Halloc' Logic.eq_refl) /= Hoff1 Hoff2 //.
                       ++ erewrite Memory.load_after_alloc in Hload';
                            [| exact Halloc | injection; congruence].
                          erewrite Memory.load_after_store_neq in Hload';
                            last exact Hmem;
                            last (injection; congruence).
                          simpl in Hrename.
                          specialize (Hrename off v' Hload') as [v'' [Hload'' Hrename'']].
                          exists v''. split; last congruence.
                          erewrite Memory.load_after_alloc;
                            [| exact Halloc' | injection; congruence].
                          exact Hload''.
                    -- simpl. intros off v' Hload'.
                       simpl in Hrename'.
                       destruct (Nat.eqb_spec b' bptr) as [Heq | Hneq].
                       ++ subst b'.
                          erewrite Memory.load_after_alloc_eq in Hload';
                            [| exact Halloc' | reflexivity].
                          simpl in Hload'.
                          eexists. split.
                          ** erewrite Memory.load_after_store_neq;
                               last exact Hstore';
                               last (injection; discriminate).
                             erewrite Memory.load_after_alloc_eq;
                               [| exact Halloc | reflexivity].
                             simpl.
                             exact Hload'.
                          ** destruct (off <? Z.of_nat (Z.to_nat n1))%Z; last discriminate.
                             destruct (0 <=? off)%Z; last discriminate.
                             injection Hload' as ?; subst v'.
                             now constructor.
                       ++ erewrite Memory.load_after_alloc in Hload';
                            [| exact Halloc' | injection; contradiction].
                          specialize (Hrename' _ _ Hload') as [v'' [Hload'' Hrename']].
                          eexists. split.
                          ** erewrite Memory.load_after_store_neq;
                               last exact Hstore';
                               last (injection; discriminate).
                             erewrite Memory.load_after_alloc;
                               [| exact Halloc | injection; contradiction].
                             erewrite Memory.load_after_store_neq;
                               last exact Hmem;
                               last (injection; discriminate).
                             exact Hload''.
                          ** exact Hrename'.

                  * intros next Hnext.
                    rewrite Hnexts0 in Hnext.
                    injection Hnext as ?; subst next.
                    erewrite next_block_store_stable;
                      last exact Hstore'.
                    exact Hnextmem'.
                  + intros C' Hcomp Hnext.
                    rewrite <- Hcomp1 in Hnext.
                    specialize (Hinitial _ Hcomp Hnext) as [Hsteady' | Hinitial].
                    * destruct Hsteady' as [Hinitflag [Hlocalbuf Hsteady']].
                      left. split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg0).
                         erewrite Memory.load_after_alloc;
                           [| exact Halloc | injection; now destruct reg0].
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg0).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg0).
                         erewrite Memory.load_after_alloc;
                           [| exact Halloc | injection; now destruct reg0].
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg0).
                         exact Hlocalbuf.
                      -- destruct Hsteady' as [Hsnapshot Hnextblock].
                         split.
                         ++ intros b Hlocal.
                            specialize (Hsnapshot b Hlocal) as [[cid bid] [Hshift' [Hrename Hrename']]].
                            destruct b as [| b']; first discriminate.
                            rewrite shift_S_Some in Hshift'.
                            injection Hshift' as ? ?; subst cid bid.
                            exists (C', b'). split; [| split].
                            ** rewrite shift_S_Some. reflexivity.
                            ** intros off v' Hload.
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hstore';
                                 last (injection; discriminate).
                               erewrite Memory.load_after_alloc in Hload;
                                 [| exact Halloc |];
                                 last (injection as ? ?; subst C' b';
                                       apply Hnext;
                                       now rewrite Hcomp1).
                               erewrite Memory.load_after_store_neq in Hload;
                                 last exact Hmem;
                                 last (injection; congruence).
                               specialize (Hrename off v' Hload) as [v'' [Hload'' Hrename]].
                               eexists. split.
                               --- erewrite Memory.load_after_alloc;
                                     [| exact Halloc' | simpl in *; injection; congruence].
                                   exact Hload''.
                               --- exact Hrename.
                            ** intros off v' Hload.
                               (* subst mem'. *)
                               (* simpl in *. *)
                               (* NOTE: Also in sub-case above! *)
                               simpl in Hload.
                               erewrite Memory.load_after_alloc in Hload;
                                 [| exact Halloc' | simpl in *; injection; congruence].
                               specialize (Hrename' _ _ Hload) as [v'' [Hload' Hrename']].
                               eexists. split.
                               --- erewrite Memory.load_after_store_neq;
                                     last exact Hstore';
                                     last (injection; congruence).
                                   erewrite Memory.load_after_alloc;
                                     [| exact Halloc | simpl in *; injection; congruence].
                                   erewrite Memory.load_after_store_neq;
                                     last exact Hmem;
                                     last (injection; congruence).
                                   exact Hload'.
                               --- exact Hrename'.
                         ++ (* Here the second proof on next block differs! *)
                           intros next Hnext'.
                           erewrite next_block_store_stable;
                             last exact Hstore'.
                           rewrite Hcomp1 in Hnext.
                           rewrite (next_block_alloc_neq Halloc Hnext).
                           erewrite next_block_store_stable;
                             last exact Hmem.
                           erewrite next_block_alloc_neq in Hnext';
                             [| exact Halloc' | exact Hnext].
                           apply Hnextblock.
                           exact Hnext'.
                    * right.
                      destruct Hinitial as [Hinitflag [Hlocalbuf Hinitial]].
                      split; [| split].
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg0).
                         erewrite Memory.load_after_alloc;
                           [| exact Halloc | injection; discriminate].
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg0).
                         exact Hinitflag.
                      -- erewrite Memory.load_after_store_neq;
                           last exact Hstore';
                           last (injection; now destruct reg0).
                         erewrite Memory.load_after_alloc;
                           [| exact Halloc | injection; discriminate].
                         erewrite Memory.load_after_store_neq;
                           last exact Hmem;
                           last (injection; now destruct reg0).
                         exact Hlocalbuf.
                      -- destruct Hinitial as [Hprealloc Hnextblock].
                         split.
                         ** destruct Hprealloc
                             as [Cmem [buf [HCmem [Hbuf [Hnextblock' Hprealloc]]]]].
                            exists Cmem, buf.
                            split; [| split; [| split]]; try assumption.
                            rewrite -HCmem. symmetry.
                            eapply component_memory_after_alloc_neq; eauto.
                            rewrite -Hcomp1. exact Hnext.
                         ** destruct Hnextblock as [Cmem [HCmem Hnextblock]].
                            exists Cmem. split; last assumption.
                            rewrite -HCmem. symmetry.
                            transitivity (mem C'); [| transitivity (mem' C')].
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
                            --- eapply component_memory_after_alloc_neq; eauto.
                                rewrite -Hcomp1. exact Hnext.
                            --- eapply component_memory_after_store_neq; eauto.
                                intro Hcontra. apply Hnext. rewrite -Hcontra. easy.
            }

      }

      destruct Star2 as (e' & s' & cs' & Star2 & wf_cs').
      (* NOTE: Now, case analysis on the event needs to take place early. *)
      exists cs', s',
             (prefix_inform ++ [:: e']), (prefix' ++ project_non_inform [:: e']),
             const_map.
      split; [| split; [| split]].
      + eapply (star_trans Star0); simpl; eauto.
        eapply (star_trans Star1); simpl; now eauto.
      + by rewrite -Hproj CS.CS.project_non_inform_append.
      + admit. (* Extend trace relation. *)
      + assumption.
    Admitted.


    (* Some other experiments on rephrasings of the definability lemma.

       First, a naive version of the original lemma, where reusing its proof
       leads to the usual prefix-suffix inconsistencies.

    Lemma definability_gen_rel_right s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state_r s prefix suffix cs ->
    exists cs' suffix_inform suffix' const_map,
      Star (CS.sem p) cs suffix' cs' /\
      project_non_inform suffix_inform = suffix' /\
      traces_shift_each_other metadata_size_lhs const_map (project_non_inform suffix) suffix' /\
      CS.final_state cs'.

       Using [t] for the induction directly is a little painful in the base
       case, but especially in the inductive case because of sectioning, and
       because [p] needs be defined in terms of [t] throughout the proof.

    (* Lemma definability_gen_rel_right (*s prefix suffix cs*) : *)
    (*   (* t = prefix ++ suffix -> *) *)
    (*   (* well_formed_state s prefix suffix cs -> *) *)
    (* exists cs' t_inform t' const_map, *)
    (*   (* Star (CS.sem p) cs suffix' cs' /\ *) *)
    (*   Star (CS.sem p) (CS.initial_machine_state p) t' cs' /\ *)
    (*   project_non_inform t_inform = t' /\ *)
    (*   traces_shift_each_other metadata_size_lhs const_map (project_non_inform t) t' /\ *)
    (*   CS.final_state cs'. *)

      Another idea: induction on the right on prefix.

    Lemma definability_gen_rel_right suffix cs :
      (*t = suffix ->*) (* TODO: Reestablish the connection later *)
      well_formed_state_right suffix cs ->
    exists cs' suffix_inform suffix' const_map,
      Star (CS.sem p) cs suffix' cs' /\
      project_non_inform suffix_inform = suffix' /\
      traces_shift_each_other metadata_size_lhs const_map (project_non_inform suffix) suffix' /\
      well_formed_state_right E0 cs' (* /\
      CS.final_state cs' *)
      .

    *)

    Lemma definability_gen_rel s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
    exists cs' suffix_inform suffix' const_map,
      Star (CS.sem p) cs suffix' cs' /\
      project_non_inform suffix_inform = suffix' /\
      traces_shift_each_other_option metadata_size_lhs const_map (project_non_inform suffix) suffix' /\
      CS.final_state cs'.
    Admitted.

    Lemma definability_gen s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
      exists2 cs',
      exists2 suffix', Star (CS.sem p) cs suffix' cs' &
                       project_non_inform suffix = suffix' &
                       CS.final_state cs'.
    Admitted.

    Lemma definability :
      forall procs, (* TODO: What to do with procs? *)
      well_formed_trace intf procs t ->
      program_behaves (CS.sem p) (Terminates (project_non_inform t)).
    Proof.
      move=> procs wf_t; eapply program_runs=> /=; try reflexivity.
      pose cs := CS.initial_machine_state p.
      suffices H : well_formed_state (StackState Component.main [::]) [::] t cs.
        have [cs' [suffix' run_cs Hsuffix'] final_cs'] := @definability_gen _ [::] t _ erefl H.
        subst suffix'. by econstructor; eauto.
      case/andP: wf_t => wb_t wf_t_events.
      rewrite /cs /CS.initial_machine_state /Source.prog_main /= find_procedures_of_trace_main //.
      econstructor; eauto; last by left; eauto.
        exists [::], [::]. by do ![split; trivial].
      constructor.
      - intros C.
        unfold component_buffer, Memory.load.
        simpl. repeat (rewrite mapmE; simpl); rewrite mem_domm.
        case HCint: (intf C) => [Cint|] //=.
        by rewrite ComponentMemory.load_prealloc /=.
      - intros C r Hbuf.
(* TODO: Rewrite lemma to turn [Memory.load] into [ComponentMemory.load]. *)
Local Transparent Memory.load. unfold Memory.load; simpl. Local Opaque Memory.load.
        unfold Source.prepare_buffers.
        rewrite mapmE. unfold omap, obind, oapp.
        destruct (Source.prog_buffers p C) as [Cbufs |] eqn:HCbufs;
          move: HCbufs;
          rewrite /p /program_of_trace /= mapmE /omap /obind /oapp => HCbufs.
        + destruct (intf C); last discriminate.
          rewrite ComponentMemory.load_prealloc.
          injection HCbufs as ?; subst.
          destruct r; simpl; by eauto.
        + destruct (intf C) eqn:Hcontra; first discriminate.
          move: Hbuf. rewrite /component_buffer => /dommPn. contradiction.
      - intros prefix e Hcontra. destruct prefix; discriminate.
    Qed.

End WithTrace.
End Definability.

(* NOTE: [DynShare] Do we need the metadata size to range over components?
   (Likely, for composition of partial programs.) We may not need the more
   general setup in this particular setting of back-translation, however. *)
(* NOTE: [DynShare] It is unlikely that we would ever need more than one block
   of metadata per component. That is, metadata would be an optional block for
   each component containing certain fixed data, such as the shift to apply to
   block identifiers. *)
Definition metadata_size : Component.id -> nat (* := uniform_shift metadata_size_per_cid*).
Admitted.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import S2I.Definitions.

(*Section MainDefinability.*)

(* FG : Put back some sanity checks ? some are present but commented in the premise and the move => *)
Lemma matching_mains_backtranslated_program p c intf back m:
  Intermediate.well_formed_program p ->
  Intermediate.well_formed_program c ->
  (* intf = unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c) -> *)
  back = program_of_trace intf m ->
  intf Component.main ->
  (* well_formed_trace intf m -> *)
  matching_mains (Source.program_unlink (domm (Intermediate.prog_interface p)) back) p.
Proof.
  move => wf_p wf_c (* intf' *) Hback intf_main (* wf_back *).
  unfold matching_mains.
  split.
  - (* <-, no main in intermediate implies no main in source bactkanslated *)
    unfold Source.prog_main, Source.program_unlink. simpl.
    rewrite Source.find_procedure_filter_comp.
    move => Hinterm.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hcase.
    + inversion wf_p as [_ _ _ _ _ _ Hmain_component].
      pose proof (proj1 (Intermediate.wfprog_main_component wf_p) Hcase) as Hmainp.
      done.
    + rewrite Hcase in Hinterm. done.
  - (* -> *) (* maybe can be done with more finesse *)
    unfold Source.prog_main. unfold Source.program_unlink. rewrite Hback. simpl. rewrite Source.find_procedure_filter_comp.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hmain_comp ; rewrite Hmain_comp.
    + intros Hprog_main.
      rewrite find_procedures_of_trace_main. done.
      assumption.
    + intros Hcontra.
      apply (Intermediate.wfprog_main_component wf_p) in Hcontra.
      rewrite Hmain_comp in Hcontra. done.
Qed.

(* Definability *)

(* RB: TODO: Refactor and relocate. *)
Lemma prefix_project m :
  not_wrong_finpref m ->
  prefix (project_finpref_behavior m)
         (Terminates (project_non_inform (finpref_trace m))).
Proof.
  unfold project_finpref_behavior, finpref_trace.
  destruct m as [t | t | t]; simpl.
  - reflexivity.
  - done.
  - intros _. exists (Terminates E0). simpl. rewrite E0_right. reflexivity.
Qed.

Lemma not_wrong_finpref_project m :
 not_wrong_finpref m ->
 not_wrong_finpref (project_finpref_behavior m).
Proof.
  now destruct m.
Qed.

(* RB: Relocate? As the S2I require above seems to indicate, this is not where
   this result belongs. *)

Lemma definability_with_linking:
  forall p c b m,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.closed_program (Intermediate.program_link p c) ->
    program_behaves (I.CS.sem_inform (Intermediate.program_link p c)) b ->
    prefix m b ->
    not_wrong_finpref m ->
  exists p' c' m' metadata_size,
    Source.prog_interface p' = Intermediate.prog_interface p /\
    Source.prog_interface c' = Intermediate.prog_interface c /\
    matching_mains p' p /\
    matching_mains c' c /\
    Source.well_formed_program p' /\
    Source.well_formed_program c' /\
    Source.closed_program (Source.program_link p' c') /\
    does_prefix (S.CS.sem (Source.program_link p' c')) m' /\
    behavior_rel_behavior metadata_size all_zeros_shift m' (project_finpref_behavior m).
Proof.
  move=> p c b m wf_p wf_c Hlinkable Hclosed Hbeh Hpre Hnot_wrong.
  pose intf := unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c).
  have Hclosed_intf : closed_interface intf by case: Hclosed.
  have intf_main : intf Component.main.
    case: Hclosed => [? [main_procs [? [/= e ?]]]].
    rewrite /intf -mem_domm domm_union.
    do 2![rewrite Intermediate.wfprog_defined_procedures //].
    by rewrite -domm_union mem_domm e.
  set m' := finpref_trace m. (* FIXME: Instantiate star simulation. *)
  have {Hbeh} [cs [cs' [Hcs Hstar]]] : (* TODO: This should come from a separate lemma. *)
      exists cs cs',
        I.CS.initial_state (Intermediate.program_link p c) cs /\
        Star (I.CS.sem_inform (Intermediate.program_link p c)) cs m' cs'.
  {
    case: b / Hbeh Hpre {Hnot_wrong}.
    - rewrite {}/m' => cs beh Hcs Hbeh Hpre.
      case: m Hpre=> [m|m|m] /= Hpre.
      + case: beh / Hbeh Hpre=> //= t cs' Hstar Hfinal -> {m}.
        by exists cs, cs'; split.
      + case: beh / Hbeh Hpre=> //= t cs' Hstar Hfinal Ht -> {m}.
        by exists cs, cs'; split.
      + destruct Hpre as [beh' ?]; subst beh.
        have [cs' [Hstar Hbehaves]] := state_behaves_app_inv (I.CS.singleton_traces_inform _) m beh' Hbeh.
        exists cs, cs'; split; assumption.
    - move=> _ Hpre; rewrite {}/m'.
      have {Hpre m} -> : finpref_trace m = E0.
        case: m Hpre => //= m [[t|t|t|t] //=].
        by case: m.
      do 2![exists (I.CS.initial_machine_state (Intermediate.program_link p c))].
      split; try reflexivity; exact: star_refl.
  }
  -
  set procs := Intermediate.prog_procedures (Intermediate.program_link p c).
  have wf_events : all (well_formed_event intf procs) m'.
    (* by apply: CS.intermediate_well_formed_events Hstar. *)
  {
    apply: CS.intermediate_well_formed_events Hstar.
    - by apply: Intermediate.linking_well_formedness.
    - assumption.
  }
  have {cs cs' Hcs Hstar} wf_m : well_formed_trace intf procs m'.
    have [mainP [HmainP _]] := Intermediate.cprog_main_existence Hclosed.
    have wf_p_c := Intermediate.linking_well_formedness wf_p wf_c Hlinkable.
    (* TODO: Duplicate assumption, new non-implicit parameters. *)
    by apply: (CS.intermediate_well_formed_trace _ wf_p_c Hclosed _ _ _ Hstar Hcs HmainP wf_p_c).
    (* exact: CS.intermediate_well_formed_trace Hstar Hcs HmainP wf_p_c. *)
  have := definability Hclosed_intf intf_main _ wf_m.
    (* RB: TODO: [DynShare] Check added assumptions in previous line. Section
       admits? *)
  set back := (program_of_trace intf m') => Hback.
  assert (Hback_ : program_behaves (CS.sem (program_of_trace intf m'))
                                   (Terminates (project_non_inform m'))).
  {
    (* This should follow directly from the definability lemma. *)
    apply Hback.
    (* All that is missing now is the metadata map. *)
    all:admit.
  }
    (* RB: TODO: [DynShare] Passing the section variables above should not be
       needed, nor should the additional assumption. *)
  exists (Source.program_unlink (domm (Intermediate.prog_interface p)) back).
  exists (Source.program_unlink (domm (Intermediate.prog_interface c)) back).
  (* Check project_finpref_behavior (FTerminates m'). *)
  exists (project_finpref_behavior m). (* FIXME: This should involve m'! *)
  eexists. (* RB: TODO: [DynShare] Provide witnesses. *)
  split=> /=.
    rewrite -[RHS](unionmK (Intermediate.prog_interface p) (Intermediate.prog_interface c)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  split.
    rewrite /intf unionmC; last by case: Hlinkable.
    rewrite -[RHS](unionmK (Intermediate.prog_interface c) (Intermediate.prog_interface p)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  (* have wf_back : Source.well_formed_program back by exact: well_formed_events_well_formed_program. *)
  have wf_back : Source.well_formed_program back.
    eapply well_formed_events_well_formed_program; auto.
    (* by exact: well_formed_events_well_formed_program. *)
    eassumption.
  have Hback' : back = program_of_trace intf m' by [].
    (* RB: TODO: [DynShare] Passing the section variables above should not be needed. *)
  split; first exact: matching_mains_backtranslated_program wf_p wf_c Hback' intf_main.
  split; first exact: matching_mains_backtranslated_program wf_c wf_p Hback' intf_main.
  clear Hback'.
  split; first exact: Source.well_formed_program_unlink.
  split; first exact: Source.well_formed_program_unlink.
  rewrite Source.program_unlinkK //; split; first exact: closed_program_of_trace.
  (* RB: TODO: [DynShare] New split, the existential is now given above and in modified form. *)
  split.
  exists (Terminates (project_non_inform m')).
  split; first by assumption.
  unfold m'. apply prefix_project; assumption.
  (* New subgoal: trace relation. *)
  (* apply behavior_rel_behavior_reflexive. *) admit.
  (* apply not_wrong_finpref_project; assumption. *)
Admitted.

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
Require Import Common.Renaming.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

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

  (* Variable prog_buffers : NMap {fmap Block.id -> nat + list value}. *)
  (* Hypothesis domm_buffers : domm intf = domm prog_buffers. *)
  (* (* Essentially a copy of the intermediate [wfprog_well_formed_buffers]. *) *)
  (* Hypothesis wf_buffers : *)
  (*   forall C bufs b, *)
  (*     prog_buffers C = Some bufs -> *)
  (*     b \in domm bufs -> *)
  (*     Buffer.well_formed_buffer_opt (bufs b). *)

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
      destruct (P =? Permission.data) eqn:EpermData; try discriminate.
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
        destruct (P =? Permission.data); try discriminate.
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
    do 5 take_step; [eauto|eauto|].
    - unfold Memory.load in C_local. simpl in C_local.
      destruct (P =? Permission.data); try discriminate.
      unfold Memory.load. simpl. eauto.
    - do 2 take_step.
      eapply (@star_step _ _ _ _ _ _ E0); try now (simpl; reflexivity).
      { apply CS.eval_kstep_sound. simpl.
        destruct (Z.eqb_spec (Z.of_nat n) (Z.of_nat (m - S (length es)))) as [n_eq_0|?]; simpl.
        - zify. omega.
        - reflexivity. }
      apply IH. omega.
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
      assert (H : (S (length es + length es') - length es' = S (length es))%nat) by omega.
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
    match reg with
    | E_R_ONE  => 1
    | E_R_COM  => 2
    | E_R_AUX1 => 3
    | E_R_AUX2 => 4
    | E_R_RA   => 5
    | E_R_SP   => 6
    | E_R_ARG  => 7
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

  Definition error_expr : expr := E_binop Mul (E_val (Int 0)) E_local.

  (* Translation of constant values to expressions, with special attention
     given to pointers. *)
  Definition expr_of_const_val (v : value) : expr :=
    match v with
    (* Integer values are simple. *)
    | Int n            => E_val (Int n)
    (* Pointer values need to take into account some amount of shifting, here
       corresponding to the counter and space reserved to locate register
       values. We make the implicit assumption that all such values refer to
       the local buffer, which should follow from well-formedness. *)
    (* FIXME: Offset vs. block-based shifting *)
    | Ptr (_, _, _, o) => E_binop Add E_local (E_val (Int (8 + o)))
    (* Undefined values are mapped to a well-formed but ill-typed expression
       (instead of some arbitrary but well-typed value, so as to preserve
       bad behavior). This choice might demand more work in some proofs,
       while possibly making other goals distinctly provable. *)
    | Undef            => error_expr
    end.

  Lemma values_are_integers_expr_of_const_val:
    forall v, Source.values_are_integers (expr_of_const_val v).
  Proof.
    intros [n | [[[p C] b ] o] |];
      reflexivity.
  Qed.

  Lemma called_procedures_expr_of_const_val:
    forall v, called_procedures (expr_of_const_val v) = fset0.
  Proof.
    intros [n | [[[p C] b ] o] |].
    - reflexivity.
    - simpl. unfold fsetU, val. simpl. rewrite fset0E. reflexivity.
    - simpl. unfold fsetU, val. simpl. rewrite fset0E. reflexivity.
  Qed.

  (** We use [switch] to define the following function [expr_of_trace], which
      converts a sequence of events to an expression that produces that sequence
      of events when run from the appropriate component.  We assume that all
      events were produced from the same component.  The [C] and [P] arguments
      are only needed to generate the recursive calls depicted above. *)

  (* We call this function when in component C executing P. *)
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (e: event_inform) : expr :=
    match e with
    | ECallInform _ P' arg _ _ C' =>
      E_seq (E_call C' P' (E_deref (loc_of_reg E_R_COM)))
            (E_call C  P  (E_val (Int 0))) (* This is really (C,P) calling itself. *)
    | ERetInform  _ ret_val _ _ _ => E_deref (loc_of_reg E_R_COM)
    (* Other events generate corresponding expressions, even though these do not
       generate any events in the source semantics. Like calls (but unlike
       returns), those "informative-only" events are followed by a recursive
       call to the current procedure. *)
    | EConst _ val reg _ _ =>
      E_seq (E_assign (loc_of_reg reg) (expr_of_const_val val))
            (E_call C P (E_val (Int 0)))
    | EMov _ reg1 reg2 _ _ =>
      E_seq (E_assign (loc_of_reg reg1) (loc_of_reg reg2))
            (E_call C P (E_val (Int 0)))
    | EBinop _ op r1 r2 r3 _ _ =>
      E_seq (E_assign (loc_of_reg r3) (E_binop (binop_of_Ebinop op)
                                               (E_deref (loc_of_reg r1))
                                               (E_deref (loc_of_reg r2))))
            (E_call C P (E_val (Int 0)))
    | ELoad _ r_dest r_src _ _ =>
      E_seq (E_assign (loc_of_reg r_dest)
                      (E_deref (loc_of_reg r_src)))
            (E_call C P (E_val (Int 0)))
    | EStore _ r_dest r_src _ _ =>
      E_seq (E_assign (loc_of_reg r_dest)
                      (E_deref (loc_of_reg r_src)))
            (E_call C P (E_val (Int 0)))
    | EAlloc _ r_dest r_size _ _ =>
      E_seq (E_assign (loc_of_reg r_dest)
                      (E_alloc (E_deref (loc_of_reg r_size))))
            (E_call C P (E_val (Int 0)))
    | EInvalidateRA cid _ _ =>
      E_seq (E_assign (loc_of_reg E_R_RA) (E_val (Int 0)))
            (E_call C P (E_val (Int 0)))
    end.

  (* RB: TODO: Avoid possible duplication in [Language] and [Machine]. *)
  Definition unfold_buffer (b : (nat + list value)%type) : list value :=
    match b with
    | inl n  => nseq n Undef
    | inr vs => vs
    end.

  (* The local buffer of back-translated programs is dedicated to private
     metadata: the trace step counter at position 0, followed by locations for
     the simulated machine registers.
     NOTE: Register indexes must match [loc_of_reg] and would ideally be defined
     in terms of [Register.to_nat], and their initial values in terms of
     [Register.init]. *)
  Definition meta_buffer : list value :=
    [Int 0; Undef; Undef; Undef; Undef; Undef; Undef; Undef].

  (* Compute component buffer side, assuming argument [C] is in the domain of
     [intf]. *)
  (* Definition buffer_size (C : Component.id) (b : Block.id) : nat := *)
  (*   match prog_buffers C with *)
  (*   | Some bufs => *)
  (*     match bufs b with *)
  (*     | Some buf => size (unfold_buffer buf) *)
  (*     | None => 0 (* Should not happen *) *)
  (*     end *)
  (*   | None => 0 (* Should not happen *) *)
  (*   end. *)

  (* Allocate a new buffer to serve as the local buffer of the back-translation.
     By convention this will be created immediately after program initialization
     and therefore its block identifier should be 1.

     NOTE: We are relying on knowledge of the implementation and behavior of the
     allocator. If these conditions are not satisfied, the offset shifting
     necessary for the trace relation will be incorrect.

     Note that buffers coming from well-formed program components must have size
     strictly greater than zero, so the behavior of alloc() is defined. *)
  (* Definition alloc_local_buffer_expr (C : Component.id) (b : Block.id) : expr := *)
  (*   E_alloc (E_val (Int (Z.of_nat (buffer_size C b)))). *)

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
  (* Definition init_local_buffer_expr (C : Component.id) (b : Block.id) : expr := *)
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

  Definition procedure_of_trace
             (C : Component.id) (P : Procedure.id) (t : trace event_inform)
    : expr :=
    expr_of_trace C P (comp_subtrace C t). (* RB: TODO: Substitute check. *)

  Definition procedures_of_trace (t: trace event_inform) : NMap (NMap expr) :=
    mapim (fun C Ciface =>
             let procs :=
                 if C == Component.main then
                   Procedure.main |: Component.export Ciface
                 else Component.export Ciface in
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
    case: eqP=> _; last by rewrite CI_P.
    by rewrite in_fsetU1 CI_P orbT.
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

  Lemma well_formed_events_well_formed_program t :
    all (well_formed_event intf) t ->
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
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: {t Ht} (comp_subtrace C t) (length _) => [|e t IH] n //=.
        case: e=> /=; try rewrite !values_are_integers_loc_of_reg; simpl; intros;
                    try apply IH; try rewrite !values_are_integers_loc_of_reg; simpl;
                      try rewrite values_are_integers_expr_of_const_val; try apply IH.
        pose call_of_event e := if e is ECall _ P _ _ C then Some (C, P) else None.
      have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (project_non_inform (comp_subtrace C t)))).
      {
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: {t Ht} (comp_subtrace C t) (length _)=> [|e t IH] n //=.
        exact: fsub0set.
        move/(_ n) in IH; rewrite !fset0U.
        case: e=> [C' P' v mem regs C''| | | | | | | |]
                    //=;
                    try by move=> C' e e0; rewrite !called_procedures_loc_of_reg !fset0U IH.
        * rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=.
          rewrite fsub0set.
            by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT.
        (* RB: TODO: Refactor cases. *)
        * move=> C' v r.
          by rewrite called_procedures_loc_of_reg
                     called_procedures_expr_of_const_val
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C' r1 r2.
          by rewrite 2!called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C' e r1 r2 r3.
          by rewrite 3!called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C' r1 r2.
          by rewrite 2!called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C' r1 r2.
          by rewrite 2!called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C' r1 r2.
          by rewrite 2!called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
        * move=> C'.
          by rewrite called_procedures_loc_of_reg
                     !fset0U fsetU0 fsubU1set in_fsetU1 eqxx /= IH.
      }
      move=> C' P' /sub/fsetU1P [[-> ->]|] {sub}.
        rewrite eqxx find_procedures_of_trace //.
        move: P_CI; case: eqP intf_C=> [->|_] intf_C.
          rewrite /valid_procedure.
          case/fsetU1P=> [->|P_CI]; eauto.
          by right; exists CI; split.
        by move=> P_CI; right; exists CI; split.
      rewrite in_fset /= => C'_P'.
      suffices ? : imported_procedure intf C C' P'.
        by case: eqP => [<-|] //; rewrite find_procedures_of_trace_exp; eauto.
      elim: {P P_CI} t Ht P' C'_P' => [|e t IH] //= /andP [He Ht] P.
      case: (C =P _) => [HC|]; last by eauto.
      case: e HC He=> [_ P' v _ _ C'' /= <-| | | | | | | |]; try by eauto.
      rewrite inE; case/andP=> [C_C'' /imported_procedure_iff imp_C''_P'].
      by case/orP=> [/eqP [-> ->] //|]; eauto.
    - by rewrite domm_map.
    - move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      (* assert (exists buf, prog_buffers C = Some buf) as [buf C_buf]. *)
      (* { *)
      (*   apply /dommP. rewrite -domm_buffers. apply /dommP. by eauto. *)
      (* } *)
      (* rewrite /Source.has_required_local_buffers /= mapmE C_buf /=. *)
      (* eexists; eauto => /=; omega. *)
      split.
      + rewrite /Source.has_required_local_buffers. eexists.
        * rewrite mapmE C_CI. reflexivity.
        * simpl. omega.
      + by rewrite /Buffer.well_formed_buffer_opt mapmE C_CI.
      (* { *)
      (*   eexists; [eexists |]. *)
      (*   - reflexivity. *)
      (*   - simpl. omega. *)
      (*   - assert (C_intf : C \in domm intf) by (apply /dommP; eauto). *)
      (*     specialize (wf_buffers C_intf). *)
      (*     setoid_rewrite C_buf in wf_buffers. *)
      (*     admit. *)
      (* } *)
    - rewrite /Source.prog_main find_procedures_of_trace //=.
      + split; first reflexivity.
        intros _.
        destruct (intf Component.main) as [mainP |] eqn:Hcase.
        * apply /dommP. exists mainP. assumption.
        * discriminate.
      + by left.
  Qed.

  Lemma closed_program_of_trace t :
    Source.closed_program (program_of_trace t).
  Proof.
    split=> //=; by rewrite /Source.prog_main find_procedures_of_trace_main.
  Qed.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace. (* RB: NOTE: Renaming *)

    Variable t : trace event_inform.

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

    (* RB: NOTE: We could make this stronger by noting which component is being
       executed, as this is the only one that can change its own metadata. *)
    Definition well_formed_memory_snapshot (mem_snapshot mem : Memory.t) : Prop :=
      (* forall ptr, *)
      (*   Pointer.block ptr <> Block.local -> *)
      (*   Memory.load mem_snapshot ptr = Memory.load mem ptr. *)
      forall Cb,
        memory_shifts_memory_at_addr
          all_zeros_shift (uniform_shift 1) Cb mem_snapshot mem /\
        memory_inverse_shifts_memory_at_addr
          all_zeros_shift (uniform_shift 1) Cb mem_snapshot mem.

    Lemma metadata_store_preserves_snapshot mem_snapshot mem Pm C o v mem' :
      well_formed_memory_snapshot mem_snapshot mem ->
      Memory.store mem (Pm, C, Block.local, o) v = Some mem' ->
      well_formed_memory_snapshot mem_snapshot mem'.
    Admitted. (* RB: TODO: Easy. *)

    Definition well_formed_memory_event (e : event_inform) (mem : Memory.t) : Prop :=
      match e with
      | ECallInform Csrc _ arg emem _ _ =>
        well_formed_memory_snapshot emem mem /\
        Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM)
        = Some arg
      | ERetInform Csrc ret emem _ _ =>
        well_formed_memory_snapshot emem mem /\
        Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM)
        = Some ret
      | EAlloc C _ rsize _ _ =>
        exists size,
          (size > 0)%Z /\
          Memory.load mem (Permission.data, C, Block.local, (reg_offset rsize)) =
          Some (Int size)
      | _ => True
      end.

    Record well_formed_memory (prefix: trace event_inform) (mem: Memory.t) : Prop :=
      {
        wfmem_counter:
          forall C,
            component_buffer C ->
            Memory.load mem (Permission.data, C, Block.local, 0%Z) =
            Some (Int (counter_value C prefix));
        wfmem_meta:
          forall C r,
            component_buffer C ->
          exists v,
            Memory.load mem (Permission.data, C, Block.local, reg_offset r) = Some v;
        (* NOTE: Reuse memory relation (renaming). *)
        wfmem_call:
          forall prefix' Csrc P arg mem' regs Cdst,
            prefix = prefix' ++ [:: ECallInform Csrc P arg mem' regs Cdst] ->
            component_buffer Csrc ->
            well_formed_memory_snapshot mem' mem /\
            Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM) = Some arg;
        wfmem_ret:
          forall prefix' Csrc ret mem' regs Cdst,
            prefix = prefix' ++ [:: ERetInform Csrc ret mem' regs Cdst] ->
            component_buffer Csrc ->
            well_formed_memory_snapshot mem' mem /\
            Memory.load mem (Permission.data, Csrc, Block.local, reg_offset E_R_COM) = Some ret;
        wfmem_alloc:
          forall prefix' C rptr rsize mem' regs,
            prefix = prefix' ++ [:: EAlloc C rptr rsize mem' regs] ->
            component_buffer C ->
          exists size,
            (size > 0)%Z /\
            Memory.load mem (Permission.data, C, Block.local, reg_offset rsize) = Some (Int size);
      }.

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

    Lemma well_formed_memory_store_counter prefix mem C e :
      component_buffer C ->
      well_formed_memory prefix mem ->
      C = cur_comp_of_event e ->
      well_formed_memory_event e mem ->
      exists mem',
        Memory.store mem (Permission.data, C, Block.local, 0%Z)
                     (Int (counter_value C (prefix ++ [e]))) = Some mem' /\
        well_formed_memory (prefix ++ [e]) mem'.
    Proof.
      move=> C_b wf_mem HC He.
      have C_local := (wfmem_counter wf_mem) _ C_b.
      have [mem' Hmem'] := Memory.store_after_load
                             _ _ _ (Int (counter_value C (prefix ++ [e])))
                             C_local.
      exists mem'. split; [now trivial |]. constructor.
      - move=> C' C'_b.
        (* exists mem'. split; trivial=> C' C'_b. *)
        have C'_local := (wfmem_counter wf_mem) _ C'_b.
        rewrite -> counter_value_snoc, <- HC, Nat.eqb_refl in *.
        case: (altP (C' =P C)) => [?|C_neq_C'].
        + subst C'.
          by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem').
        + have neq : (Permission.data, C, Block.local, 0%Z) <>
                     (Permission.data, C', Block.local, 0%Z)
            by move/eqP in C_neq_C'; congruence.
          rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
          now rewrite Z.add_0_r.
      - move=> C' r C'_b.
        destruct ((wfmem_meta wf_mem) C' r C'_b) as [v Hload].
        exists v.
        erewrite Memory.load_after_store_neq; try eassumption.
        intros Hcontra. injection Hcontra as Hcomp Hoffset.
        now destruct r.
      - move=> prefix' Csrc P arg mem'' regs Cdst Hprefix C'_b.
        apply rcons_inv in Hprefix as [? ?]; subst prefix' e.
        inversion He as [Hsnap Harg].
        split.
        + eapply metadata_store_preserves_snapshot; eassumption.
        + erewrite Memory.load_after_store_neq; try eassumption.
          now injection.
      - move=> prefix' Csrc ret mem'' regs Cdst Hprefix C'_b.
        apply rcons_inv in Hprefix as [? ?]; subst prefix' e.
        inversion He as [Hsnap Hret].
        split.
        + eapply metadata_store_preserves_snapshot; eassumption.
        + erewrite Memory.load_after_store_neq; try eassumption.
          now injection.
      - move=> prefix' C' rptr rsize mem'' regs Hprefix C'_b.
        apply rcons_inv in Hprefix as [? ?]; subst prefix' e.
        inversion He as [size [Hsize Hload]].
        exists size. split.
        + eassumption.
        + erewrite Memory.load_after_store_neq; try eassumption.
          injection as _ Hoffset. now destruct rsize.
    Qed.

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
    | WellFormedState C stk mem k exp arg P
      of C = cur_comp stk_st
      &  k = Kstop
      &  exp = procedure_of_trace C P t
      &  well_bracketed_trace stk_st suffix
      &  all (well_formed_event intf) suffix
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
  | WellFormedStateR C stk mem k exp arg P
    of C = cur_comp stk_st
    &  k = Kstop
    &  exp = procedure_of_trace C P t
    &  TracesInform.well_bracketed_trace_rev stk_st suffix
    &  all (well_formed_event intf) suffix
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
  | WellFormedStateRight C stk mem k exp arg P
  of
  (* C = cur_comp stk_s & *)
     k = Kstop
  &  exp = procedure_of_trace C P t
  &  TracesInform.well_bracketed_trace_r suffix
  &  all (well_formed_event intf) suffix
  (* &  well_formed_stack stk_st stk *)
  (* &  well_formed_memory prefix mem *) (* FIXME *)
  &  valid_procedure C P
  :  well_formed_state_right (* stk_st *) suffix [CState C, stk, mem, k, exp, arg].

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

    Lemma Eregister_eq_dec :
      forall r1 r2 : Eregister, Decidable.decidable (r1 = r2).
    Proof.
      intros [] [];
        try (left; reflexivity);
        right; intro Hcontra; now inversion Hcontra.
    Qed.

    (* TODO: [DynShare] Trace relation should appear here too!

       Well-bracketedness, etc., probably need to be rewritten to operate "in
       reverse", i.e., adding events at the end of the trace to match the
       definition of the trace relation.

       NOTE: Propositional and not boolean conjunction in the conclusion at the
       moment. *)

    (* A proof of relational definability on the right. Existential
      quantification is extended to [cs] and [s], and induction performed on
      the prefix, executing from the initial state. Separately, execution to a
      final state needs to be established. *)
    Lemma definability_gen_rel_right prefix suffix :
      t = prefix ++ suffix ->
    exists cs s prefix_inform prefix' const_map,
      Star (CS.sem p) (CS.initial_machine_state p) prefix' cs /\
      project_non_inform prefix_inform = prefix' /\
      traces_shift_each_other metadata_size_lhs const_map (project_non_inform prefix) prefix' /\
      well_formed_state_r s prefix suffix cs.
    Proof.
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = Source.prog_procedures p
        by [].
      (* Proof by induction on the prefix. Prior to inducting, generalize on
         the suffix. *)
      elim/rev_ind: prefix suffix => [|e prefix IH] /= suffix.
      - (* Base case. *)
        move=> <-.
        exists (CS.initial_machine_state p), (StackState Component.main []),
               E0, E0, (uniform_shift 1).
        split; [| split; [| split]].
        + now apply star_refl.
        + reflexivity.
        + now do 2 constructor.
        + unfold CS.initial_machine_state, Source.prog_main.
          rewrite find_procedures_of_trace_main.
          econstructor; eauto.
          * admit. (* Easy: should be an assumption about t. *)
          * admit. (* Easy: should be an assumption about t. *)
          * now exists [], [].
          * constructor.
            -- move=> C.
               rewrite /component_buffer /Memory.load //= mapmE // mapmE mem_domm.
               case HCint: (intf C) => [Cint|] //=.
               by rewrite ComponentMemory.load_prealloc.
            -- move=> C r.
               rewrite /component_buffer /Memory.load //= mapmE // mapmE mem_domm.
               case HCint: (intf C) => [Cint|] //=.
               rewrite /meta_buffer.
               rewrite ComponentMemory.load_prealloc //=.
               eexists; by case r => //=.
            -- by move=> [].
            -- by move=> [].
            -- by move=> [].
          * unfold valid_procedure. now auto.
    - (* Inductive step. *)
      rewrite -catA => Et.
      specialize (IH (e :: suffix) Et) as
          [cs [s [prefix_inform [prefix' [const_map [Star0 [Hproj [Hshift Hwf_cs]]]]]]]].

      move: Hwf_cs Star0.
      case: cs / => /= _ stk mem _ _ arg P -> -> -> [] wb /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.

      move=> Star0.

      have C_b := valid_procedure_has_block P_exp.
      have C_local := wfmem_counter _ C_b.
      have wf_C: cur_comp s = cur_comp_of_event e by admit.
      (* Requires reasonning about the memories *)
      have wf_mem_e: well_formed_memory_event e mem by admit.
      destruct (well_formed_memory_store_counter C_b wf_mem wf_C wf_mem_e) as
          [mem' [Hmem' wf_mem']].

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
      set C := cur_comp s.
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
        specialize (C_local prefix mem wf_mem).
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
        rewrite -> wf_C in Hmem'.
        (* rewrite <- wf_C in Hmem'. *)
        rewrite eq_refl in Hmem'.
        rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
        unfold counter_value in *.

        rewrite <- wf_C in Hmem'. unfold C in Hmem''.
        rewrite Hmem' in Hmem''.
        congruence. }

      assert (Star2 : exists e' s' cs',
                 Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] (event_non_inform_of [:: e']) cs' /\
                 well_formed_state_r s' (prefix ++ [e]) suffix cs' (* TODO: [e']? *)
             (* /\ e ~ e' *)
             (* NOTE: Here, too, we may need additional conjuncts... *)
             ).
      {

        clear Star1 wf_mem C_local Hmem'. revert mem' wf_mem'. rename mem into mem0. intros mem wf_mem.
        (* Case analysis on observable events, which in this rich setting
           extend to calls and returns and various memory accesses and related
           manipulations, of which only calls and returns are observable at
           both levels. *)
        destruct e as [C_ P' new_arg mem' regs C'|C_ ret_val mem' regs C' |C_ ptr v |C_ ptr v|C_ |C_ |C_ |C_ |C_];
          simpl in wf_C, wf_e(*, wb_suffix*); subst C_.

        - (* Event case: call. *)
          case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
          exists (ECallInform C P' new_arg mem regs C'). (* TODO: new_arg? *)
          exists (StackState C' (C :: callers s)).
          have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).

          destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg].
          simpl.
          exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem,
                  Kstop, procedure_of_trace C' P' t, new_arg].
          split.
          + (* Process memory invariant. *)
            (* destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg]. *)
            (* subst mem'. *)
            take_step.
Local Transparent loc_of_reg.
            unfold loc_of_reg.
Local Opaque loc_of_reg.
            do 7 take_step;
              [reflexivity | exact Harg |].
            (* RB: TODO: At this precise moment the call is executed, so the
               two memories should be identical. And nothing has changed [mem]
               in the execution of the previous steps. *)
            apply star_one. simpl.
            apply CS.eval_kstep_sound. simpl.
            rewrite (negbTE C_ne_C').
            rewrite -> imported_procedure_iff in Himport. rewrite Himport.
            rewrite <- imported_procedure_iff in Himport.
            by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
            (* rewrite (find_procedures_of_trace_exp t (closed_intf Himport)). *)
            (* admit. *)
            (* FIXME: Similar steps will break after this point. *)
          + econstructor; trivial.
            { admit. (* New subgoal. *) }
            { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
              eexists []; eexists; simpl; split; eauto.
              split; trivial.
              eexists arg, P, top, bot.
              by do 3 (split; trivial). }
            right. by apply: (closed_intf Himport).
            (* NOTE: These snippets continue to work, though they may incur
               modifications later on. *)

          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
      }

      destruct Star2 as (e' & s' & cs' & Star2 & wf_cs').
      (* NOTE: Now, case analysis on the event needs to take place early. *)
      exists cs', s',
             (prefix_inform ++ [:: e']), (prefix' ++ project_non_inform [:: e']),
             const_map.
      split; [| split; [| split]].
      + eapply (star_trans Star0); simpl; eauto.
        eapply (star_trans Star1); simpl; now eauto.
      + rewrite <- Hproj. admit. (* Easy lemma over list concatenation. *)
      + admit. (* Extend trace relation. *)
      + assumption.

      (* do 5 eexists. split; [| split; [| split]]. *)
      (* + (* Compose the stars *) *)
      (*   eapply star_trans. eapply Hstar. *)
      (*   rewrite /procedure_of_trace. *)
      (*   eapply star_trans with (s2 := [CState (cur_comp s), stk, mem', Kstop, expr_of_event (cur_comp s) P e, arg]). *)
      (*   {rewrite /expr_of_trace Et comp_subtrace_app //=. *)
      (*    set (C := cur_comp s). *)
      (*     (* rewrite wf_C eqxx. rewrite map_app. *) *)
      (*     (* set (C := cur_comp_of_event e). *) *)
      (*     assert (H := @switch_spec p Permission.data C stk mem *)
      (*                               (map (expr_of_event C P) (comp_subtrace C prefix)) *)
      (*                               (expr_of_event C P e) *)
      (*                               (map (expr_of_event C P) (comp_subtrace C suffix)) *)
      (*                               E_exit arg). *)
      (*     unfold C. *)
      (*     rewrite map_length in H. specialize (H (C_local _ mem wf_mem)). *)
      (*     destruct H as [mem'' [Hmem'' Hstar']]. *)
      (*     simpl in Hmem''. unfold C in Hmem''. *)
      (*     (* This looks extremely wrong. What are we doing? Why are we computing *)
      (*      the new memory twice and why are we proving the two are equal? *)
      (*      *) *)
      (*     enough (H : mem'' = mem'). *)
      (*     { subst mem''. unfold C in Hstar'. *)
      (*       simpl. rewrite wf_C eqxx map_cat. *)
      (*       rewrite wf_C in Hstar'. eauto. } *)
      (*     assert ((Int (Z.pos (Pos.of_succ_nat (length (comp_subtrace (cur_comp s) prefix))))) = (Int (counter_value (cur_comp s) (prefix ++ [:: e])))). *)
      (*     { unfold counter_value. rewrite comp_subtrace_app. *)
      (*       rewrite wf_C. destruct e; simpl; *)
      (*         rewrite eqxx app_length plus_comm //=. *)
      (*     } *)
      (*       rewrite H in Hmem''. rewrite Hmem'' in Hmem'. congruence. *)
      (*   } *)

      (*   rewrite wf_C. *)
      (*   (* And now we do the event e *) *)
      (*   (* ... *) *)
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
      traces_shift_each_other metadata_size_lhs const_map (project_non_inform suffix) suffix' /\
      CS.final_state cs'.
    Proof.
      (* NOTE: For now, trying to preserve the high-level structure of the
         non-relational proof. *)
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = Source.prog_procedures p by [].
      (* Proof by induction on the trace suffix. *)
      elim: suffix s prefix cs=> [|e suffix IH] /= [C callers] prefix.
      - (* Base case: empty suffix. The proof is straightforward. *)
        rewrite cats0 => cs <- {prefix}.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> _ _ wf_stk wf_mem P_exp.
        exists [CState C, stk, mem, Kstop, E_exit, arg], E0, E0, (uniform_shift 1).
        split; [| split; [| split]].
        + have C_b := valid_procedure_has_block P_exp.
          have C_local := (wfmem_counter wf_mem) _ C_b.
          rewrite /procedure_of_trace /expr_of_trace.
          (* eexists. *)
          apply: switch_spec_else; eauto.
          simpl. rewrite -> size_map; reflexivity.
        + reflexivity.
        + now repeat constructor.
        + now constructor.
      - (* Inductive case: cons of a head event and a tail continuation for
           the suffix. *)
        move=> cs Et /=.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> /andP [/eqP wf_C wb_suffix] /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := (wfmem_counter wf_mem) _ C_b.

        (* TODO: Getting ahead of ourselves here. *)
        assert (He : well_formed_memory_event e mem) by admit. (* FIXME *)
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C He)
          as [mem' [Hmem' wf_mem']].

        (* We can simulate the event-producing step as the concatenation of three
           successive stars:
            1. A silent star preceding the event.
            2. A star that contains a step that produces the event (which at the
               source level may now be silent).
            3. By the IH, a final star that produces the tail of the suffix.

           The first star, running up to the point where we are ready to execute
           the expression associated with the event of interest, is fairly
           simple to establish. *)
        (* NOTE: The base case was simple, but complications arise in the
           recursive case. The first star can be proved as before, but is it
           exactly what we need? *)
        assert (Star1 : Star (CS.sem p)
                             [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                             [CState C, stk, mem', Kstop, expr_of_event C P e, arg]).
        { unfold expr_of_trace. rewrite Et comp_subtrace_app. simpl.
          rewrite <- wf_C, Nat.eqb_refl, map_app. simpl.
          assert (H := @switch_spec p Permission.data C  stk mem
                                    (map (expr_of_event C P) (comp_subtrace C prefix))
                                    (expr_of_event C P e)
                                    (map (expr_of_event C P) (comp_subtrace C suffix))
                                    E_exit arg).
          rewrite map_length in H. specialize (H C_local).
          destruct H as [mem'' [Hmem'' Hstar]].
          enough (H : mem'' = mem') by (subst mem''; easy).
          rewrite -> counter_value_snoc in Hmem'.
          unfold cur_comp_of_event in Hmem'.
          simpl in Hmem'.
          rewrite <- wf_C in Hmem'.
          rewrite eq_refl in Hmem'.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
          unfold counter_value in *.
          unfold Memory.store in *. simpl in *.
          rewrite Hmem' in Hmem''.
          congruence. }
        (* NOTE: Try dividing into two:
            - Star2: call (NOT cross-compartment call, then Star2 = Star3)
            - Star3: event proper *)
        (* The second star "executes" the event proper. This part is more
           interesting. *)
        (* FIXME: This will not execute the exact event in the trace, but rather
           an event related to it. *)
        assert (Star2 : exists e' s' cs',
                   Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] (event_non_inform_of [:: e']) cs' /\
                   well_formed_state s' (prefix ++ [e]) suffix cs' (* TODO: [e']? *)
                   (* /\ e ~ e' *)
               (* NOTE: Here, too, we may need additional conjuncts... *)
               ).
        {
          (* clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem. *)
          clear Star1 wf_mem C_local mem Hmem' He. revert mem' wf_mem'. intros mem wf_mem.
          (* clear Star1 wf_mem C_local Hmem'. revert mem mem' wf_mem' He. intros mem_old mem wf_mem He. *)
          (* Case analysis on observable events, which in this rich setting
             extend to calls and returns and various memory accesses and related
             manipulations, of which only calls and returns are observable at
             both levels. *)
          destruct e as [C_ P' new_arg mem' regs C'|C_ ret_val mem' regs C' |C_ ptr v |C_ ptr v|C_ |C_ |C_ |C_ |C_];
          simpl in wf_C, wf_e, wb_suffix; subst C_.

          - (* Event case: call. *)
            case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
            exists (ECallInform C P' new_arg mem regs C'). (* TODO: new_arg? *)
            exists (StackState C' (C :: callers)).
            have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).

            (* Check Et. Search _ (_ ++ _ :: _). rewrite <- cat_rcons in Et. *)
            (* Check IH _ _ _ Et. *)
            (* Too early to use IH! *)
            destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg].
simpl.
            exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem,
                    Kstop, procedure_of_trace C' P' t, new_arg].
            split.
            (* + take_step. take_step. *)
            (*   apply star_one. simpl. *)
            (*   (* RB: TODO: [DynShare] For the proof to go through, we need to *)
            (*      establish (i.e., evaluate) beforehand the fact that the COM *)
            (*      register contains a values. This is probably what was intended *)
            (*      by [values_are_integers_loc_of_reg], though it does not let *)
            (*      us infer that. *) *)
            (*   assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v) *)
            (*     as [v Hregval] *)
            (*     by admit; *)
            (*     rewrite Hregval. *)
            (*   apply CS.eval_kstep_sound. simpl. *)
            (*   rewrite (negbTE C_ne_C'). *)
            (*   rewrite -> imported_procedure_iff in Himport. rewrite Himport. *)
            (*   rewrite <- imported_procedure_iff in Himport. *)
            (*   by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)). *)
            + (* Process memory invariant. *)
              (* destruct (wfmem_call wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg]. *)
              (* subst mem'. *)
              take_step.
Local Transparent loc_of_reg.
              unfold loc_of_reg.
Local Opaque loc_of_reg.
              do 7 take_step;
                [reflexivity | exact Harg |].
              (* RB: TODO: At this precise moment the call is executed, so the
                 two memories should be identical. And nothing has changed [mem]
                 in the execution of the previous steps. *)
              apply star_one. simpl.
              apply CS.eval_kstep_sound. simpl.
              rewrite (negbTE C_ne_C').
              rewrite -> imported_procedure_iff in Himport. rewrite Himport.
              rewrite <- imported_procedure_iff in Himport.
              by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
              (* rewrite (find_procedures_of_trace_exp t (closed_intf Himport)). *)
              (* admit. *)
              (* FIXME: Similar steps will break after this point. *)
            + econstructor; trivial.
              { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                eexists []; eexists; simpl; split; eauto.
                split; trivial.
                eexists arg, P, top, bot.
                by do 3 (split; trivial). }
              right. by apply: (closed_intf Himport).
              (* NOTE: These snippets continue to work, though they may incur
                 modifications later on. *)

          - (* Event case: return. *)
            move: wf_e=> /eqP C_ne_C'.
            destruct callers as [|C'_ callers]; try easy.
            case/andP: wb_suffix=> [/eqP HC' wb_suffix].
            exists (ERetInform C ret_val mem regs C'). (* TODO: ret_val? *)
            subst C'_. simpl. exists (StackState C' callers).
            destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot.
            (* The case proceeds by induction on [top]. However, before this we
               need to advance the execution a few steps, until the return value
               is available and the proper return can be performed. This star
               quantifies over the invariant stack and argument to accommodate
               the induction. *)
            assert (StarRet0 :
                      forall stk arg,
                        star CS.kstep (prepare_global_env p)
                             [CState C, stk, mem, Kstop, E_deref (loc_of_reg E_R_COM), arg]
                             E0
                             [CState C, stk, mem, Kstop, E_val ret_val, arg]).
                        (* star CS.kstep (prepare_global_env p) *)
                        (*      [CState C, top ++ bot, mem, Kstop, E_deref (loc_of_reg E_R_COM), arg] *)
                        (*      E0 *)
                        (*      [CState C, top ++ bot, mem, Kstop, E_val ret_val, arg]). *)
            {
              intros stk arg_.
Local Transparent loc_of_reg.
              unfold loc_of_reg.
Local Opaque loc_of_reg.
              do 6 take_step;
                [reflexivity | | now apply star_refl].
              destruct (wfmem_ret wf_mem Logic.eq_refl C_b) as [_ Hload].
              exact Hload.
            }
            (* Once this is done, it suffices to show that the return can be
               executed once the return value has been dereferenced from the
               simulated registers. This follows from [StarRet0] and
               transitivity of the star operator, applied inside the existential
               and without affecting the side sub-goals. *)
            suffices:
              exists cs' : CS.state,
                star CS.kstep (prepare_global_env p)
                     [CState C, top ++ bot, mem, Kstop, E_val ret_val, arg]
                     [:: ERet C ret_val mem C']
                     cs' /\
                well_formed_state {| cur_comp := C'; callers := callers |}
                                  (prefix ++ [:: ERetInform C ret_val mem' regs C']) suffix cs';
              [admit |].
            (* Proceed by induction on [top]. *)
            (* revert mem wf_mem arg. *)
            revert mem wf_mem arg StarRet0.
            induction top as [|[C_ saved k_] top IHtop].
            + clear Htop. rename bot into bot'.
              destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
              subst bot'. simpl.
              have C'_b := valid_procedure_has_block P'_exp.
              intros mem wf_mem arg.
              exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0].
              split.
              (* * (* RB: TODO: [DynShare] Similarly as above, but before we take *)
              (*      step to have the result of the evaluation in scope. *) *)
              (*   assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v) *)
              (*     as [v Hregval] *)
              (*     by admit; *)
              (*     rewrite Hregval. *)
              (*   eapply star_step. *)
              (*   -- eapply CS.KS_ExternalReturn; now eauto. *)
              (*   -- take_step. take_step; eauto. *)
              (*      apply star_one. apply CS.eval_kstep_sound. *)
              (*      by rewrite /= eqxx (find_procedures_of_trace t P'_exp). *)
              (*   -- now rewrite E0_right. *)
              * (* First assumption: R_COM contains the return_value. *)
                (* Process memory invariant. *)
                destruct (wfmem_ret wf_mem (Logic.eq_refl _) C_b) as [Hmem Harg].
                (* subst mem'. *)
                (* assert (Hrcom : Memory.load mem (Permission.data, C, Block.local, reg_offset E_R_COM) = Some ret_val) by admit. *)
(*                 take_step. *)
(* Local Transparent loc_of_reg. *)
(*                 unfold loc_of_reg. *)
(* Local Opaque loc_of_reg. *)
(*                 do 5 take_step; *)
(*                   [reflexivity | exact Harg |]. *)
                eapply star_step.
                -- eapply CS.KS_ExternalReturn; now eauto.
                -- take_step. take_step; eauto.
                   apply star_one. apply CS.eval_kstep_sound.
                   by rewrite /= eqxx (find_procedures_of_trace t P'_exp).
                -- now rewrite E0_right.
              * econstructor; trivial.
                exists (CS.Frame C' saved Kstop :: top), bot. simpl. eauto.
            + intros mem wf_mem arg StarRet0.
              simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
              specialize (IHtop Htop).
              specialize (IHtop _ wf_mem saved).
              (* assert (arg = saved) by admit; subst arg. *)
              specialize (IHtop StarRet0).
              destruct IHtop as [cs' [StarRet wf_cs']].
              exists cs'. split; trivial.
              eapply star_step; try eassumption.
              * (* RB: TODO: [DynShare] Same as above. *)
                (* assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v) *)
                (*   as [v Hregval] *)
                (*   by admit; *)
                (*   rewrite Hregval. *)
                by apply/CS.eval_kstep_sound; rewrite /= eqxx.
              * reflexivity.

          (* NOTE: ... And there is a series of new events to consider. *)

          - (* EConst *)
            (* Case analysis on concrete constant expression; all cases are
               similar.
               TODO: Refactoring. *)
            exists (EConst C ptr v s t0).
            destruct ptr as [n | [[[P' C'] b] o] |].
            + (* Before processing the goal, introduce existential witnesses. *)
              destruct (well_formed_memory_store_reg_offset v (Int n) C_b wf_mem) as [mem' Hstore].
              exists (StackState C callers). eexists. split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              do 8 take_step.
              -- reflexivity.
              -- exact Hstore.
              -- (* Do recursive call. *)
                  do 3 take_step.
                  ++ reflexivity.
                  ++ now apply find_procedures_of_trace.
                  ++ (* Now we are done with the event. *)
                     apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              (* Reestablish memory well-formedness.
                 TODO: Refactor, automate. *)
              {
                constructor.
                - intros C' C'_b.
                  rewrite <- ((wfmem_counter wf_mem) C' C'_b).
                  eapply Memory.load_after_store_neq; try eassumption.
                  intros Hcontra; destruct v; now inversion Hcontra.
                - intros C' reg C'_b.
                  destruct (dec_eq_nat C C') as [HeqC | HneqC].
                  + subst C'.
                    destruct (Eregister_eq_dec reg v) as [Heqreg | Hneqreg].
                    * subst reg. exists (Int n).
                      eapply Memory.load_after_store_eq; eassumption.
                    * destruct ((wfmem_meta wf_mem) C reg C_b) as [val Hval].
                      exists val.
                      erewrite Memory.load_after_store_neq; try eassumption.
                      intros Hcontra. injection Hcontra as Hoffset.
                      apply reg_offset_inj in Hoffset.
                      symmetry in Hoffset. contradiction.
                  + destruct ((wfmem_meta wf_mem) C' reg C'_b) as [val Hval].
                    exists val.
                    erewrite Memory.load_after_store_neq; try eassumption.
                    intros Hcontra. inversion Hcontra. contradiction.
                - intros prefix' Csrc P' arg' mem'' regs Cdst Hprefix Csrc_b.
                  apply rcons_inv in Hprefix as [Hprefix Hevent].
                  discriminate.
                - intros prefix' Csrc P' arg' regs Cdst Hprefix Csrc_b.
                  apply rcons_inv in Hprefix as [Hprefix Hevent].
                  discriminate.
                - intros prefix' C' rptr rsize mem'' regs Hprefix C'_b.
                  apply rcons_inv in Hprefix as [Hprefix Hevent].
                  discriminate.
              }

            + (* Before processing the goal, introduce existential witnesses. *)
              destruct (well_formed_memory_store_reg_offset v (eval_binop Add (Ptr (Permission.data, C, Block.local, 0%Z)) (Int (8 + o))) C_b wf_mem) as [mem' Hstore].
              exists (StackState C callers). eexists. split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              do 12 take_step.
              -- reflexivity.
              -- exact Hstore.
              -- (* Do recursive call. *)
                  do 3 take_step.
                  ++ reflexivity.
                  ++ now apply find_procedures_of_trace.
                  ++ (* Now we are done with the event. *)
                     apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Reestablish memory well-formedness, easy. *)

            + (* Before processing the goal, introduce existential witnesses. *)
              destruct (well_formed_memory_store_reg_offset v Undef C_b wf_mem) as [mem' Hstore].
              exists (StackState C callers). eexists. split.
            * (* Evaluate steps of back-translated event first. *)
Local Transparent expr_of_const_val loc_of_reg.
              do 12 take_step.
              -- reflexivity.
              -- exact Hstore.
              -- (* Do recursive call. *)
                  do 3 take_step.
                  ++ reflexivity.
                  ++ now apply find_procedures_of_trace.
                  ++ (* Now we are done with the event. *)
                     apply star_refl.
            * (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Reestablish memory well-formedness, easy. *)

          - (* EMov *)
            (* Before processing the goal, introduce existential witnesses. *)
            inversion wf_mem as [_ wfmem_meta].
            destruct (well_formed_memory_store_reg_offset ptr ((eval_binop Add (Ptr (Permission.data, C, Block.local, 0%Z)) (Int (reg_offset v)))) C_b wf_mem) as [mem' Hstore].
            exists (EMov C ptr v s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 12 take_step.
              * reflexivity.
              * exact Hstore.
              * (* Do recursive call. *)
                do 3 take_step.
                -- reflexivity.
                -- now apply find_procedures_of_trace.
                -- (* Now we are done with the event. *)
                  apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Restore memory invariant (easy, after first line). *)

          - (* EBinop *)
            (* Before processing the goal, introduce existential witnesses. *)
            inversion wf_mem as [_ wfmem_meta].
            destruct (wfmem_meta _ e0 C_b) as [v0 Hload0].
            destruct (wfmem_meta _ e1 C_b) as [v1 Hload1].
            destruct (well_formed_memory_store_reg_offset e2 (eval_binop (binop_of_Ebinop e) v0 v1) C_b wf_mem) as [mem' Hstore2].
            (* Proceed. *)
            exists (EBinop C e e0 e1 e2 s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 9 take_step.
              * reflexivity.
              * exact Hload0.
              * do 7 take_step.
                -- reflexivity.
                -- exact Hload1.
                -- do 7 take_step.
                   ++ reflexivity.
                   ++ exact Hstore2.
                   ++ (* Do recursive call. *)
                     do 3 take_step.
                     ** reflexivity.
                     ** now apply find_procedures_of_trace.
                     ** (* Now we are done with the event. *)
                        apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Reestablish memory invariant. *)

          - (* ELoad *)
            (* Before processing the goal, introduce existential witnesses. *)
            inversion wf_mem as [_ wfmem_meta].
            destruct (wfmem_meta _ e0 C_b) as [v0 Hload0].
            destruct (well_formed_memory_store_reg_offset e v0 C_b wf_mem) as [mem' Hstore1].
            (* Continue. *)
            exists (ELoad C e e0 s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 8 take_step.
              * reflexivity.
              * exact Hload0.
              * do 6 take_step.
                -- reflexivity.
                -- exact Hstore1.
                -- (* Do recursive call. *)
                   do 3 take_step.
                   ++ reflexivity.
                   ++ now apply find_procedures_of_trace.
                   ++ (* Now we are done with the event. *)
                     apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Restore invariant. *)

          - (* EStore *)
            (* Before processing the goal, introduce existential witnesses. *)
            inversion wf_mem as [_ wfmem_meta].
            destruct (wfmem_meta _ e0 C_b) as [v0 Hload0].
            destruct (well_formed_memory_store_reg_offset e v0 C_b wf_mem) as [mem' Hstore1].
            (* Continue. *)
            exists (EStore C e e0 s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 8 take_step.
              * reflexivity.
              * exact Hload0.
              * do 6 take_step.
                -- reflexivity.
                -- exact Hstore1.
                -- (* Do recursive call. *)
                   do 3 take_step.
                   ++ reflexivity.
                   ++ now apply find_procedures_of_trace.
                   ++ (* Now we are done with the event. *)
                     apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Restore invariant. *)

          - (* EAlloc *)
            (* Before processing the goal, introduce existential witnesses. *)
            destruct ((wfmem_alloc wf_mem) _ _ _ _ _ _ Logic.eq_refl C_b)
              as [size [Hsize Hload0]].
            destruct (Memory.alloc_after_load mem _ _ _ _ _ (Z.to_nat size) Hload0)
              as [mem' [b' [Hblock Halloc1]]].
            destruct (well_formed_memory_store_reg_offset
                        e ((Ptr (Permission.data, C, b', 0%Z))) C_b wf_mem)
              as [mem1 Hstore2].
            destruct (Memory.store_after_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ Halloc1 (not_eq_sym Hblock) Hstore2)
              as [mem1' Hstore2'].
            (* Continue with the goal. *)
            exists (EAlloc C e e0 s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 9 take_step.
              * reflexivity.
              * exact Hload0.
              * unfold loc_of_reg.
                do 1 take_step.
                -- (* Metadata-simulated register [e0] holds positive integer. *)
                   exact Hsize.
                -- exact Halloc1.
                -- do 6 take_step.
                   ++ reflexivity.
                   ++ exact Hstore2'.
                   ++ (* Do recursive call. *)
                      do 3 take_step.
                      ** reflexivity.
                      ** now apply find_procedures_of_trace.
                      ** (* Now we are done with the event. *)
                         apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Restore invariant. *)

          - (* EInvalidateRA *)
            (* Before processing the goal, introduce existential witnesses. *)
            inversion wf_mem as [_ wfmem_meta].
            destruct (well_formed_memory_store_reg_offset E_R_RA (Int 0) C_b wf_mem) as [mem' Hstore].
            (* Continue. *)
            exists (EInvalidateRA C s t0).
            exists (StackState C callers). eexists. split.
            + (* Evaluate steps of back-translated event first. *)
              Local Transparent loc_of_reg.
              do 8 take_step.
              * reflexivity.
              * exact Hstore.
              * (* Do recursive call. *)
                do 3 take_step.
                -- reflexivity.
                -- now apply find_procedures_of_trace.
                -- (* Now we are done with the event. *)
                   apply star_refl.
            + (* Reestablish invariant. *)
              econstructor; try reflexivity; try eassumption.
              destruct wf_stk as [top [bot [Heq [Htop Hbot]]]]; subst stk.
              eexists ({| CS.f_component := C; CS.f_arg := arg; CS.f_cont := Kstop |} :: top).
              exists bot. split; [| split]; easy.
              admit. (* RB: TODO: Restore invariant. *)
        }

        destruct Star2 as (e' & s' & cs' & Star2 & wf_cs').
        (* The third star is produced by the IH. *)
        specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
        specialize (IH Et wf_cs').
        destruct IH
          as [cs'' [suffix_inform [suffix' [const_map [Star3 [Hsuffix [Hrel final]]]]]]].
        (* NOTE: Now, case analysis on the event needs to take place early. *)
        destruct e' as [Ce Pe ve me re Ce' | | | | | | | |].
        + exists
            cs'',
            ((ECallInform Ce Pe ve me re Ce') :: suffix_inform),
            (ECall Ce Pe ve me Ce' :: suffix'),
            const_map.
          split; [| split; [| split]].
          * eapply (star_trans Star1); simpl; eauto.
            eapply (star_trans Star2); simpl; eauto.
          * simpl. congruence.
          * constructor.
            (* NOTE: At this point we hit the problem: trace relations add
               events at the end, whereas the current induction has them added
               at the beginning. *)
            admit.
          * assumption.
        + (* NOTE: Something similar probably happens on return. *)
          admit.
        + (* NOTE: Consider the case of an informative-only event now. This can
             be solved as before. All remaining sub-goals follow the same
             pattern.
             TODO: Restore some of the comments in the older version of the
             proof, if still relevant. *)
          exists cs'', suffix_inform, suffix', const_map.
          split; [| split; [| split]].
          * eapply (star_trans Star1); simpl; eauto.
            eapply (star_trans Star2); simpl; eauto.
          * assumption.
          * admit. (* TODO: Relate events. *)
            (* assumption. *)
          * assumption.
    Admitted.

    Lemma definability_gen s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
      exists2 cs',
      exists2 suffix', Star (CS.sem p) cs suffix' cs' &
                       project_non_inform suffix = suffix' &
                       CS.final_state cs'.
    Proof.
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = Source.prog_procedures p by [].
      (* Proof by induction on the trace suffix. *)
      elim: suffix s prefix cs=> [|e suffix IH] /= [C callers] prefix.
      - (* Base case: empty suffix. The proof is straightforward. *)
        rewrite cats0 => cs <- {prefix}.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> _ _ wf_stk wf_mem P_exp.
        exists [CState C, stk, mem, Kstop, E_exit, arg]; last by left.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := (wfmem_counter wf_mem) _ C_b.
        rewrite /procedure_of_trace /expr_of_trace.
        eexists. apply: switch_spec_else; eauto.
        cbn. rewrite -> size_map. reflexivity.
        reflexivity.
      - (* Inductive case: cons of a head event and a tail continuation for
           the suffix. *)
        move=> cs Et /=.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> /andP [/eqP wf_C wb_suffix] /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := (wfmem_counter wf_mem) _ C_b.
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']].
        {
          admit.
        }
        (* We can simulate the event-producing step as the concatenation of three
           successive stars:
            1. A silent star preceding the event.
            2. A star that contains a step that produces the event (which at the
               source level may now be silent).
            3. By the IH, a final star that produces the tail of the suffix.

           The first star, running up to the point where we are ready to execute
           the expression associated with the event of interest, is fairly
           simple to establish. *)
        assert (Star1 : Star (CS.sem p)
                             [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                             [CState C, stk, mem', Kstop, expr_of_event C P e, arg]).
        { unfold expr_of_trace. rewrite Et comp_subtrace_app. simpl.
          rewrite <- wf_C, Nat.eqb_refl, map_app. simpl.
          assert (H := @switch_spec p Permission.data C  stk mem
                                    (map (expr_of_event C P) (comp_subtrace C prefix))
                                    (expr_of_event C P e)
                                    (map (expr_of_event C P) (comp_subtrace C suffix))
                                    E_exit arg).
          rewrite map_length in H. specialize (H C_local).
          destruct H as [mem'' [Hmem'' Hstar]].
          enough (H : mem'' = mem') by (subst mem''; easy).
          rewrite -> counter_value_snoc in Hmem'.
          unfold cur_comp_of_event in Hmem'.
          simpl in Hmem'.
          rewrite <- wf_C in Hmem'.
          rewrite eq_refl in Hmem'.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
          unfold counter_value in *.
          unfold Memory.store in *. simpl in *.
          rewrite Hmem' in Hmem''.
          congruence. }
        (* The second star "executes" the event proper. This part is more
           interesting. *)
        assert (Star2 : exists s' cs',
                   Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] (event_non_inform_of [:: e]) cs' /\
                   well_formed_state s' (prefix ++ [e]) suffix cs').
        {
          clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem.
          (* Case analysis on observable events, which in this rich setting
             extend to calls and returns and various memory accesses and related
             manipulations, of which only calls and returns are observable at
             both levels. *)
          destruct e as [C_ P' new_arg mem' regs C'|C_ ret_val mem' regs C' |C_ ptr v |C_ ptr v|C_ |C_ |C_ |C_ |C_];
          simpl in wf_C, wf_e, wb_suffix; subst C_.
          - (* Event case: call. *)
            case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
            exists (StackState C' (C :: callers)).
            have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).
            exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem,
                    Kstop, procedure_of_trace C' P' t, new_arg].
            split.
            + take_step. take_step.
              apply star_one. simpl.
              (* RB: TODO: [DynShare] For the proof to go through, we need to
                 establish (i.e., evaluate) beforehand the fact that the COM
                 register contains a values. This is probably what was intended
                 by [values_are_integers_loc_of_reg], though it does not let
                 us infer that. *)
              assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v)
                as [v Hregval]
                by admit;
                rewrite Hregval.
              apply CS.eval_kstep_sound. simpl.
              rewrite (negbTE C_ne_C').
              rewrite -> imported_procedure_iff in Himport. rewrite Himport.
              rewrite <- imported_procedure_iff in Himport.
              by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
            + econstructor; trivial.
              { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                eexists []; eexists; simpl; split; eauto.
                split; trivial.
                eexists arg, P, top, bot.
                by do 3 (split; trivial). }
              right. by apply: (closed_intf Himport).
          - (* Event case: return. *)
            move: wf_e=> /eqP C_ne_C'.
            destruct callers as [|C'_ callers]; try easy.
            case/andP: wb_suffix=> [/eqP HC' wb_suffix].
            subst C'_. simpl. exists (StackState C' callers).
            destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot.
            revert mem wf_mem arg.
            induction top as [|[C_ saved k_] top IHtop].
            + clear Htop. rename bot into bot'.
              destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
              subst bot'. simpl.
              have C'_b := valid_procedure_has_block P'_exp.
              intros mem wf_mem arg.
              exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0].
              split.
              * (* RB: TODO: [DynShare] Similarly as above, but before we take
                   step to have the result of the evaluation in scope. *)
                assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v)
                  as [v Hregval]
                  by admit;
                  rewrite Hregval.
                eapply star_step.
                -- eapply CS.KS_ExternalReturn; now eauto.
                -- take_step. take_step; eauto.
                   apply star_one. apply CS.eval_kstep_sound.
                   by rewrite /= eqxx (find_procedures_of_trace t P'_exp).
                -- now rewrite E0_right.
              * econstructor; trivial.
                exists (CS.Frame C' saved Kstop :: top), bot. simpl. eauto.
            + intros mem wf_mem arg.
              simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
              specialize (IHtop Htop).
              specialize (IHtop _ wf_mem saved). destruct IHtop as [cs' [StarRet wf_cs']].
              exists cs'. split; trivial.
              eapply star_step; try eassumption.
              * (* RB: TODO: [DynShare] Same as above. *)
                assert (exists v, E_deref (loc_of_reg E_R_COM) = E_val v)
                  as [v Hregval]
                  by admit;
                  rewrite Hregval.
                by apply/CS.eval_kstep_sound; rewrite /= eqxx.
              * reflexivity.
          (* The remaining events correspond to silent events in the
             source. *)
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
        }
        destruct Star2 as (s' & cs' & Star2 & wf_cs').
        (* The third star is produced by the IH. *)
        specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
        specialize (IH Et wf_cs'). destruct IH as [cs'' [suffix' Star3 Hsuffix] final].
        exists cs''; trivial.
        (* At the end, we need to instantiate the suffix based on the target
           event. *)
        (* Before: *)
        (* eapply (star_trans Star1); simpl; eauto. *)
        (* now eapply (star_trans Star2); simpl; eauto. *)
        rewrite Hsuffix.
        destruct e.
          (* This snippet works for all cases. *)
          eexists; [| trivial];
          eapply (star_trans Star1); simpl; [| eauto];
          now eapply (star_trans Star2); simpl; eauto.
          (* ... *)
    Admitted.

    Lemma definability :
      well_formed_trace intf t ->
      program_behaves (CS.sem p) (Terminates (project_non_inform t)).
    Proof.
      move=> wf_t; eapply program_runs=> /=; try reflexivity.
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
      - admit.
    (* Qed. *)
    Admitted. (* RB: TODO: Prove new memory sub-goals, easy. *)

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
  set m' := finpref_trace m.
  have {Hbeh} [cs [cs' [Hcs Hstar]]] :
      exists cs cs',
        I.CS.initial_state (Intermediate.program_link p c) cs /\
        Star (I.CS.sem_inform (Intermediate.program_link p c)) cs m' cs'.
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
  -
  have wf_events : all (well_formed_event intf) m'.
    by apply: CS.intermediate_well_formed_events Hstar.
  have {cs cs' Hcs Hstar} wf_m : well_formed_trace intf m'.
    have [mainP [HmainP _]] := Intermediate.cprog_main_existence Hclosed.
    have wf_p_c := Intermediate.linking_well_formedness wf_p wf_c Hlinkable.
    exact: CS.intermediate_well_formed_trace Hstar Hcs HmainP wf_p_c.
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
  exists (project_finpref_behavior m).
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
  apply behavior_rel_behavior_reflexive.
  apply not_wrong_finpref_project; assumption.
Admitted.

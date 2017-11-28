Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.

Import ListNotations.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definability.
  Variable intf: Program.interface.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

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
            if (local[1] == 0) {
              local[1]++;
              C2.P2(1);
              C1.P1(0);
            } else if (local[1] == 1) {
              local[1]++;
              C2.P2(3);
              C1.P1(0);
            } else {
              exit();
            }
          }
        }

        C2 {
          P2() {
            if (local[1] == 0) {
              local[1]++;
              return 2;
            } else if (local[1] == 1) {
              local[1]++;
              mainC.mainP(4);
              C2.P2(0);
            } else {
              exit();
            }
          }
        } *)

  (** If a component has multiple procedures, they can share the same
      code. Notice that each branch that performs call performs a recursive call
      at the end.  This is needed to trigger multiple events from a single
      function.

      The first ingredient needed to perform this translation is a switch
      statement that runs code based on the value of the first local variable.

   *)

  Definition switch_clause n e_then e_else :=
    let one := E_val (Int 1%Z) in
    let count := E_binop Add E_local one in
    E_if (E_binop Eq (E_deref count) (E_val (Int n)))
         (E_seq (E_assign count (E_binop Add (E_deref count) one)) e_then)
         e_else.

  Ltac take_step :=
    eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; [econstructor|].

  Lemma switch_clause_spec p' C stk mem b n n' e_then e_else :
    PMap.find C (genv_buffers (globalenv (CS.sem p'))) = Some b ->
    Memory.load mem (C, b, 1) = Some (Int n) ->
    if n =? n' then
      exists mem',
        Memory.store mem (C, b, 1) (Int (Z.succ n)) = Some mem' /\
        Star (CS.sem p')
             (C, stk, mem , Kstop, switch_clause n' e_then e_else) E0
             (C, stk, mem', Kstop, e_then)
    else
      Star (CS.sem p')
           (C, stk, mem, Kstop, switch_clause n' e_then e_else) E0
           (C, stk, mem, Kstop, e_else).
  Proof.
    intros Eb Hload.
    destruct (Z.eqb_spec n n') as [n_n'|n_n'].
    - subst n'.
      assert (Hload' := Hload).
      unfold Memory.load in Hload'.
      unfold Memory.store.
      destruct (PMap.find C mem) as [memC|] eqn:EmemC; try discriminate.
      destruct (ComponentMemory.store_after_load _ _ _ _ (Int (Z.succ n)) Hload')
        as [memC' EmemC'].
      rewrite EmemC'.
      eexists; split; eauto.
      repeat take_step; trivial; try eassumption.
      repeat take_step; trivial; try eassumption.
      { rewrite Z.eqb_refl. discriminate. }
      { unfold Memory.store. rewrite EmemC. simpl. now rewrite Z.add_1_r, EmemC'. }
      apply star_refl.
    - unfold switch_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite <- Z.eqb_neq in n_n'. rewrite n_n'. simpl.
        eapply CS.KS_IfFalse. }
      apply star_refl.
  Qed.

  Definition switch_add_expr e res :=
    (pred (fst res), switch_clause (Z.of_nat (fst res)) e (snd res)).

  Definition switch (es: list expr) (e_else: expr) : expr :=
    snd (fold_right switch_add_expr (pred (length es), e_else) es).

  Lemma switch_spec_else p' C stk mem b n es e_else :
    PMap.find C (genv_buffers (globalenv (CS.sem p'))) = Some b ->
    Memory.load mem (C, b, 1) = Some (Int (Z.of_nat n)) ->
    (length es <= n)%nat ->
    Star (CS.sem p')
         (C, stk, mem, Kstop, switch es e_else) E0
         (C, stk, mem, Kstop, e_else).
  Proof. Admitted.

  Lemma switch_spec p' C stk mem b es e es' e_else :
    PMap.find C (genv_buffers (globalenv (CS.sem p'))) = Some b ->
    Memory.load mem (C, b, 1) = Some (Int (Z.of_nat (length es))) ->
    exists mem',
      Memory.store mem (C, b, 1) (Int (Z.of_nat (S (length es)))) = Some mem' /\
      Star (CS.sem p')
           (C, stk, mem , Kstop, switch (es ++ e :: es') e_else) E0
           (C, stk, mem', Kstop, e).
  Proof.
    intros Eb Hload.
    assert (Eswitch :
              exists e_else',
                switch (es ++ e :: es') e_else =
                switch es (switch_clause (Z.of_nat (length es)) e e_else')).
    { unfold switch. rewrite fold_right_app, app_length. simpl.
      assert (Efst : fst (fold_right switch_add_expr (pred (length es + S (length es'))%nat, e_else) es')
                     = length es).
      { rewrite Nat.add_comm.
        generalize (length es). simpl.
        induction es' as [|e' es' IH]; try easy. simpl.
        intros n. now rewrite <- Nat.add_succ_r, IH. }
      exists (snd (fold_right switch_add_expr (pred (length es + S (length es'))%nat, e_else) es')).
      repeat f_equal. rewrite surjective_pairing at 1. simpl. rewrite Efst. f_equal. }
    destruct Eswitch as [e_else' ->]. clear e_else. rename e_else' into e_else.
    assert (Hcont := switch_clause_spec stk (Z.of_nat (length es)) e e_else Eb Hload).
    rewrite Z.eqb_refl in Hcont.
    destruct Hcont as (mem' & Hstore & Hstar2).
    exists mem'. rewrite Nat2Z.inj_succ. split; trivial.
    apply (fun H => @star_trans _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial.
    apply (switch_spec_else stk _ Eb Hload).
    reflexivity.
  Qed.

  (** We use [switch] to define the following function [expr_of_trace], which
      converts a sequence of events to an expression that produces that sequence
      of events when run from the appropriate component.  We assume that all
      events were produced from the same component.  The [C] and [P] arguments
      are only needed to generate the recursive calls depicted above. *)

  Definition expr_of_event (C: Component.id) (P: Procedure.id) (e: event) : expr :=
    match e with
    | ECall _ P' arg C' =>
      E_seq (E_call C' P' (E_val (Int arg)))
            (E_call C  P  (E_val (Int 0)))
    | ERet  _ ret_val _ => E_val (Int ret_val)
    end.

  Definition expr_of_trace (C: Component.id) (P: Procedure.id) (t: trace) : expr :=
    switch (map (expr_of_event C P) t) E_exit.

  (** To compile a complete trace mixing events from different components, we
      split it into individual traces for each component and apply
      [expr_of_trace] to each one of them.  We also initialize the memory of
      each component to hold 0 at the second local variable. *)

  Definition cur_comp_of_event (e: event) : Component.id :=
    match e with
    | ECall C _ _ _ => C
    | ERet  C _ _   => C
    end.

  Definition program_of_trace (t: trace) : program :=
    let procedure_of_trace C P :=
        expr_of_trace C P (filter (fun e => Pos.eqb C (cur_comp_of_event e)) t) in
    {| prog_interface  := intf;
       prog_procedures :=
         PMap.mapi (fun C C_interface =>
                      fold_right (fun P C_procs =>
                                    PMap.add P (procedure_of_trace C P) C_procs)
                                 (PMap.empty _)
                                 (Component.export C_interface))
                   intf;
       prog_buffers    := PMap.map (fun _ => inr [Int 0; Int 0]) intf;
       prog_main       := (mainC, mainP) |}.

  (** To prove that [program_of_trace] is correct, we need to describe how the
      state of the program evolves as it emits events from the translated trace.
      One of the difficulties is the stack.  If a call to a component [C]
      performs [n] calls to other components before returning, the code
      generated by [expr_of_trace] will perform [n] *recursive* calls to [C].
      Thus, the final return to the calling component must be preceded by [n]
      returns from those recursive calls.  We describe this pattern with the
      following data structure.  *)

  Inductive stack_state := StackState {
    (* The current running component.  When set to [(C, n)], it means that the
       component [C] is running, and that during this execution it has called
       into [n] other components.  (Because of the recursive calls, this means
       that the top of the stack has [n] frames corresponding to calls from [C]
       into itself.)  *)
    cur_comp : Component.id * nat;

    (* Other running components further down the stack. *)
    callers  : list (Component.id * nat)

  }.

  (** The program necessarily starts executing from the [mainC] component, with
      an empty stack. *)
  Definition initial_state : stack_state := StackState (mainC, O) [].

  (** Given the current event and the call stack, compute the next value of
      cur_proc. *)
  Definition next_comp
    (e: event)
    (callers: list (Component.id * nat))
    : Component.id * nat :=
    match e with
    | ECall _ P' _ C' => (C', O)
    | ERet _ _ C'_ =>
      match callers with
      | (C', n) :: callers' =>
        (* When run on a trace produced by a program, [C'] and [C'_] should be equal. *)
        (C', S n)
      | [] =>
        (* This case should never happen, as a program cannot return from a
           component when the stack is empty *)
        (C'_, O)
      end
    end.

  (** Compute the next value of callers. *)
  Definition next_callers
    (e: event)
    (cur_proc: Component.id * nat)
    (callers: list (Component.id * nat))
    : list (Component.id * nat) :=
    match e with
    | ECall _ _ _ _ => cur_proc :: callers
    | ERet _ _ _ => tail callers
    end.

  Definition correct_event (e: event) (ps: stack_state) :=
    match e with
    | ECall _ _ _ _ => True
    | ERet  _ _ C1 =>
      match callers ps with
      | (C2, _) :: callers' => C1 = C2
      | []                  => False
      end
    end.

  (** Update the stack state with an event. *)
  Definition update_state (ps: stack_state) (e: event) : stack_state :=
    {| cur_comp := next_comp e (callers ps);
       callers  := next_callers e (cur_comp ps) (callers ps) |}.

  (* Representation predicates; not ready yet.

  Definition represent_cur_comp (g: global_env) (ps: stack_state) (s: PS.state) : Prop :=
    match cur_proc ps, s with
    | Some (cur_comp, P), PS.PC (C, _, _, k, exp) =>
      C = cur_comp /\
      k = Kstop    /\
      exists C_procs,
        PMap.find C (genv_procedures g) = Some C_procs /\
        PMap.find P C_procs             = Some exp
    | None              , PS.CC _               => True
    | _                 , _                     => False
    end.

  Definition represent_mem (g: global_env) (ps: state) (s: PS.state) : Prop :=
    match s with
    | PS.PC (_, _, mem, _, _)
    | PS.CC (_, _, mem) =>
      forall C : Component.id,
        match PMap.find C (procs ps), PMap.find C (genv_buffers g), PMap.find C mem with
        | Some (n_ps, _), Some b, Some C_mem =>
          match ComponentMemory.load C_mem b 1 with
          | Some n_s => n_s = Int n_ps
          | None     => False
          end
        | None, _, None => True
        | _, _, _ => False
        end
    end.

  Definition represent_state (g: global_env) (prefix suffix: trace) (s: PS.state) : Prop :=
    let ps := fold_left update_state prefix initial_state in
    represent_cur_comp g ps s /\
    represent_mem g ps s.

  Lemma preservation g prefix e suffix s :
    represent_state g prefix (e :: suffix) s ->
    exists s',
      step (PS.sem (build_context (prefix ++ e :: suffix)) (prog_interface p)) g s [e] s' /\
      represent_state g (prefix ++ [e]) suffix s'.
  Proof.
    unfold represent_state.
    intros [Hcur_comp Hmem].
    destruct s as [[[[[C stack] mem] k] exp]|].
    - (* s = PC (C, stack, mem, k, exp).  Note that, because of the switched
         roles, this means that s is running the generated context program *)
      unfold represent_cur_comp in Hcur_comp.
      destruct (cur_proc (fold_left update_state prefix initial_state)) as [[C' P]|] eqn:Ecur_proc; try easy.
      destruct Hcur_comp as (? & ? & C_procs & H1 & H2).
      subst C' k.



  Lemma context_definability_partial :
    forall s t s',
      Smallstep.initial_state (PS.sem p ictx) s ->
      Star (PS.sem p ictx) s t s' ->
      exists sctx sctx',
      Star (PS.sem (build_context t) (prog_interface p)) sctx t sctx'.
  Proof.
    simpl.
    intros s t s' Hinit.
    destruct Hinit as [scs sps scs_sps init_scs].




  Theorem context_definability:
    forall t beh,
      program_behaves (PS.sem p ictx) (behavior_app t beh) ->
    exists ctx,
      PMap.Equal (prog_interface ctx) ictx /\
      program_behaves (CS.sem (program_link p ctx mainC mainP)) (Terminates t).
  Proof.
    intros t beh Hbeh.
    remember (behavior_app t beh) as beh' eqn:E.
    destruct Hbeh as [s beh' s_is_init s_beh|].
    - (* Program has a valid initial state. *)
      subst beh'.

   *)
End Definability.

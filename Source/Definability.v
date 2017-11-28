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
  Variable p: program.
  Variable ictx: Program.interface.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  (** The definability proof takes an execution trace as its input and builds a
      source context that can produce that trace when linked with the
      appropriate program.  Roughly speaking, it does so by keeping one counter
      for each context component, and using that counter to track how many calls
      or returns have been executed by that component.

      To see how this works, suppose that we have a context with two procedures
      P1 and P2, which live in components C1 and C2.  Given the trace

        ECall mainC P1    0 C1
        ECall C1    P2    1 C2
        ERet  C2          2 C1
        ECall C1    P2    3 C2
        ECall C2    mainP 4 mainC

      we would produce the context *)

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

   (** Notice that each branch that performs call performs a recursive call at
       the end.  This is needed to trigger multiple events from a single
       function.

       To build a context as above, we traverse the trace of events while
       keeping track of the following data:

   *)

  Inductive state := State {
    (* Some P if the program is currently executing a context procedure P;
       otherwise None. *)
    cur_comp : option (Component.id * nat);

    (* Call stack with calling procedures. *)
    callers  : list (Component.id * nat)

  }.

  (** We start building the context from the following state.  Initially, the
      current procedure is set to mainC, there are no callers, and every
      procedure has no code.  Note that the actual current procedure takes into
      account whether mainC belongs to the context or not. *)
  Definition initial_state : state :=
    match PMap.find mainC ictx with
    | Some _ => State (Some (mainC, O)) []
    | None   => State None              []
    end.

  (** Given the current event and the call stack, compute the next value of
      cur_proc. *)
  Definition next_comp
    (e: event)
    (callers: list (Component.id * nat))
    : option (Component.id * nat) :=
    match e with
    | ECall _ next_proc _ next_comp =>
      match PMap.find next_comp ictx with
      | Some _ => Some (next_comp, O)
      | None   => None
      end
    | ERet _ _ next_comp =>
      match PMap.find next_comp ictx, callers with
      | Some _, (C, n) :: callers' => Some (C, S n)
      | Some _, []                 => (* Should never happen *) None
      | None  , _                  => None
      end
    end.

  (** Compute the next value of callers. *)
  Definition next_callers
    (e: event)
    (cur_proc: option (Component.id * nat))
    (callers: list (Component.id * nat))
    : list (Component.id * nat) :=
    match e with
    | ECall _ _ _ _ =>
      match cur_proc with
      | Some cur_proc => cur_proc :: callers
      | None          => callers
      end
    | ERet _ _ next_comp =>
      match PMap.find next_comp ictx with
      | Some _ => tail callers
      | None   => callers
      end
    end.

  Definition correct_event (e: event) (ps: state) :=
    match e with
    | ECall _ _ _ _ => True
    | ERet  _ _ next_comp =>
      match PMap.find next_comp ictx, (callers ps) with
      | Some _, (C, _) :: callers' => next_comp = C
      | Some _, []                 => False
      | None  , _                  => True
      end
    end.

  (** Update the state of the context building procedure with an event. *)
  Definition update_state (ps: state) (e: event) : state :=
    {| cur_comp := next_comp e (callers ps);
       callers  := next_callers e (cur_comp ps) (callers ps) |}.

  (** Given an event e, compute the expression needed to produce that event.
      Note that calls are compiled to two call expressions: one that produces
      the call event proper, and another one that performs a recursive call to
      continue executing the rest of the instructions in this procedure. *)
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (e: event) : expr :=
    match e with
    | ECall _ next_proc arg next_comp =>
      E_seq (E_call next_comp next_proc (E_val (Int arg)))
            (E_call C P (E_val (Int 0)))
    | ERet  _ ret_val _ => E_val (Int ret_val)
    end.

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

  (*

  (** After we apply update_state to all the events in the trace,
      linearize_instructions converts the representation of each procedure into
      the chain of if statements depicted above. *)
  Definition linearize_instructions
    (C: Component.id)
    (P: Procedure.id)
    (instrs: list event) : expr :=
    let one := E_val (Int 1%Z) in
    let count := E_binop Add E_local one in
    let add_instruction p exp :=
        let '(pos, e) := p in
        E_if (E_binop Eq count (E_val (Int pos)))
             (E_seq (E_assign count (E_binop Add (E_deref count) one))
                    (expr_of_event C P e))
             exp in
    fold_right add_instruction E_exit instrs.

  (** Combine all of the above steps to convert a trace into a context. *)
  Definition build_context (t: trace) : program :=
    let 'State cur_proc callers procs :=
        fold_left update_state t initial_state in
    let comp_code :=
        PMap.mapi (fun C p =>
                     let '(count, comp_procs) := p in
                     PMap.mapi (linearize_instructions C) comp_procs) procs in
    let comp_mem  := PMap.map (fun _ => inr [Int 0; Int 0]) ictx in
    {| prog_interface  := ictx;
       prog_procedures := comp_code;
       prog_buffers    := comp_mem;
       prog_main       := (mainC, mainP) |}.

  Definition represent_cur_comp (g: global_env) (ps: state) (s: PS.state) : Prop :=
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

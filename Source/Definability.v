Require Import Lib.Extra.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definability.
  Local Open Scope fset_scope.

  Variable intf: Program.interface.
  Variable closed_intf: closed_interface intf.
  Variable has_main: intf Component.main.

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
    match goal with
    | |- @star _ _ _ _ _ ?t _ =>
      eapply (@star_step _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
    end.

  Lemma switch_clause_spec p' C stk mem b n n' e_then e_else :
    getm (genv_buffers (globalenv (CS.sem p'))) C = Some b ->
    Memory.load mem (C, b, 1%Z) = Some (Int n) ->
    if (n =? n') % Z then
      exists mem',
        Memory.store mem (C, b, 1%Z) (Int (Z.succ n)) = Some mem' /\
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
      simpl in *.
      destruct (getm mem C) as [memC|] eqn:EmemC; try discriminate.
      destruct (ComponentMemory.store_after_load _ _ _ _ (Int (Z.succ n)) Hload')
        as [memC' EmemC'].
      rewrite EmemC'.
      eexists; split; eauto.
      repeat take_step; trivial; try eassumption.
      repeat take_step; trivial; try eassumption.
      { rewrite Z.eqb_refl. discriminate. }
      { unfold Memory.store. simpl. rewrite EmemC. simpl. now rewrite Z.add_1_r EmemC'. }
      apply star_refl.
    - unfold switch_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite <- Z.eqb_neq in n_n'. rewrite n_n'. simpl.
        eapply CS.KS_IfFalse. }
      apply star_refl.
  Qed.

  Definition switch_add_expr e res :=
    (Nat.pred (fst res), switch_clause (Z.of_nat (Nat.pred (fst res))) e (snd res)).

  Definition switch (es: list expr) (e_else: expr) : expr :=
    snd (fold_right switch_add_expr (length es, e_else) es).

  Lemma fst_switch n (e_else: expr) (es : list expr) :
    fst (fold_right switch_add_expr (n, e_else) es) = (n - length es)%nat.
  Proof.
    induction es as [|e' es IH]; try now rewrite Nat.sub_0_r.
    simpl. now rewrite IH Nat.sub_succ_r.
  Qed.

  Lemma switch_spec_else p' C stk mem b n es e_else :
    genv_buffers (globalenv (CS.sem p')) C = Some b ->
    Memory.load mem (C, b, 1%Z) = Some (Int (Z.of_nat n)) ->
    (length es <= n)%nat ->
    Star (CS.sem p')
         (C, stk, mem, Kstop, switch es e_else) E0
         (C, stk, mem, Kstop, e_else).
  Proof.
    intros C_b C_local es_n. unfold switch.
    enough (forall m,
               m <= n -> length es <= m ->
               Star (CS.sem p')
                    (C, stk, mem, Kstop, snd (fold_right switch_add_expr (m, e_else) es))
                    E0
                    (C, stk, mem, Kstop, e_else))%nat.
    { apply (H (length es)); trivial. }
    clear es_n. intros m m_le_n es_le_n.
    induction es as [|e es IH]; try apply star_refl.
    unfold switch. simpl. simpl in es_le_n. rewrite fst_switch -Nat.sub_succ_r. simpl.
    do 5 take_step; [now eauto|].
    do 3 take_step; eauto.
    do 2 take_step.
    eapply (@star_step _ _ _ _ _ E0); try now (simpl; reflexivity).
    { apply CS.eval_kstep_sound. simpl.
      destruct (Z.eqb_spec (Z.of_nat n) (Z.of_nat (m - S (length es)))) as [n_eq_0|?]; simpl.
      - zify. omega.
      - reflexivity. }
    apply IH. omega.
  Qed.

  Lemma switch_spec p' C stk mem b es e es' e_else :
    getm (genv_buffers (globalenv (CS.sem p'))) C = Some b ->
    Memory.load mem (C, b, 1%Z) = Some (Int (Z.of_nat (length es))) ->
    exists mem',
      Memory.store mem (C, b, 1%Z) (Int (Z.of_nat (S (length es)))) = Some mem' /\
      Star (CS.sem p')
           (C, stk, mem , Kstop, switch (es ++ e :: es') e_else) E0
           (C, stk, mem', Kstop, e).
  Proof.
    intros Eb Hload.
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

  Definition comp_subtrace (C: Component.id) (t: trace) :=
    filter (fun e => C == cur_comp_of_event e) t.

  Lemma filter_app {T} (P : T -> bool) (l1 l2 : list T) :
    filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    induction l1 as [|x l1 IH]; simpl; trivial.
    now rewrite IH; destruct (P x).
  Qed.

  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply filter_app. Qed.

  Definition procedure_of_trace C P t :=
    expr_of_trace C P (comp_subtrace C t).

  Definition procedures_of_trace (t: trace) : NMap (NMap expr) :=
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

  Lemma find_procedures_of_trace_exp (t: trace) C P :
    exported_procedure intf C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    intros [CI [C_CI CI_P]].
    unfold find_procedure, procedures_of_trace.
    rewrite mapimE C_CI /= mkfmapfE.
    case: eqP=> _; last by rewrite CI_P.
    by rewrite in_fsetU1 CI_P orbT.
  Qed.

  Lemma find_procedures_of_trace_main (t: trace) :
    find_procedure (procedures_of_trace t) Component.main Procedure.main
    = Some (procedure_of_trace Component.main Procedure.main t).
  Proof.
    rewrite /find_procedure /procedures_of_trace.
    rewrite mapimE eqxx.
    case: (intf Component.main) (has_main)=> [Cint|] //= _.
    by rewrite mkfmapfE in_fsetU1 eqxx.
  Qed.

  Lemma find_procedures_of_trace (t: trace) C P :
    valid_procedure C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    by move=> [[-> ->]|?];
    [apply: find_procedures_of_trace_main|apply: find_procedures_of_trace_exp].
  Qed.

  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapm (fun _ => inr [Int 0; Int 0]) intf |}.

  (** To prove that [program_of_trace] is correct, we need to describe how the
      state of the program evolves as it emits events from the translated trace.
      One of the difficulties is the stack.  If a call to a component [C]
      performs [n] calls to other components before returning, the code
      generated by [expr_of_trace] will perform [n] *recursive* calls to [C].
      Thus, the final return to the calling component must be preceded by [n]
      returns from those recursive calls.  We describe this pattern with the
      following data structure.  *)

  Inductive stack_state := StackState {
    (* The current running component.  *)
    cur_comp : Component.id;

    (* Other running components further down the stack. *)
    callers  : list Component.id
  }.

  Fixpoint well_bracketed_trace (s: stack_state) (t: trace) : Prop :=
    match t with
    | [] => True
    | e :: t' =>
      cur_comp s = cur_comp_of_event e /\
      match e with
      | ECall C _ _ C' =>
        well_bracketed_trace (StackState C' (C :: callers s)) t'
      | ERet C _ C' =>
        match callers s with
        | [] => False
        | head :: tail =>
          head = C' /\
          well_bracketed_trace (StackState C' tail) t'
        end
      end
    end.

  Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
    match l with
    | [] => True
    | x :: l' => P x /\ All P l'
    end.

  Definition well_formed_event (e: event) : Prop :=
    match e with
    | ECall C P _ C' => C <> C' /\ imported_procedure intf C C' P
    | ERet  C _   C' => C <> C'
    end.

  Definition well_formed_trace (t: trace) : Prop :=
    well_bracketed_trace (StackState Component.main []) t /\
    All well_formed_event t.

  Fixpoint well_formed_callers (callers: list Component.id) (stk: CS.stack) : Prop :=
    match callers with
    | [] => True
    | C :: callers' =>
      exists v P top bot,
      stk = (C, v, Kseq (E_call C P (E_val (Int 0))) Kstop) :: top ++ bot /\
      valid_procedure C P /\
      All (fun '(C', _, k) => C' = C /\ k = Kstop) top /\
      well_formed_callers callers' bot
    end.

  Definition well_formed_stack (s: stack_state) (stk: CS.stack) : Prop :=
    exists top bot,
      stk = top ++ bot /\
      All (fun '(C', _, k) => C' = cur_comp s /\ k = Kstop) top /\
      well_formed_callers (callers s) bot.

  Lemma well_formed_events_well_formed_program t :
    All well_formed_event t ->
    Source.well_formed_program (program_of_trace t).
  Proof.
    move=> Ht; split=> //=.
    - exact: closed_interface_is_sound.
    - by rewrite /procedures_of_trace domm_mapi.
    - move=> C P.
      rewrite /exported_procedure /Program.has_component /Component.is_exporting.
      case=> CI [C_CI P_CI].
      by rewrite find_procedures_of_trace_exp //; exists CI; split; eauto.
    - move=> C P Pexpr.
      rewrite /find_procedure /procedures_of_trace mapimE.
      case intf_C: (intf C)=> [CI|] //=.
      rewrite mkfmapfE; case: ifP=> //= P_CI [<-] {Pexpr}; split; last first.
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: {t Ht} (comp_subtrace C t) (length _) => [|e t IH] n //=.
        by case: e=> /=.
      pose call_of_event e := if e is ECall _ P _ C then Some (C, P) else None.
      have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (comp_subtrace C t))).
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: {t Ht} (comp_subtrace C t) (length _)=> [|e t IH] n //=.
          exact: fsub0set.
        move/(_ n) in IH; rewrite !fset0U.
        case: e=> [C' P' v C''|] //=; last by rewrite fset0U.
        rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=.
        by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT.
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
      elim: {P P_CI} t Ht P' C'_P' => [|e t IH] //= [He Ht] P.
      case: (C =P _) => [HC|]; last by eauto.
      case: e HC He=> [_ P' v C'' /= <-|]; last by eauto.
      by rewrite inE; case=> [C_C'' imp_C''_P'] /orP [/eqP [-> ->] //|]; eauto.
    - by rewrite domm_map.
    - move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      rewrite /has_required_local_buffers /= mapmE C_CI /=.
      eexists; eauto=> /=; omega.
  Qed.

  Lemma closed_program_of_trace t :
    Source.closed_program (program_of_trace t).
  Proof.
    split=> //=; by rewrite find_procedures_of_trace_main.
  Qed.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace.

    Variable t : trace.

    Let p    := program_of_trace t.
    Let init := prepare_buffers p.

    Local Definition component_buffer C b :=
      genv_buffers (prepare_global_env p) C = Some b.

    Lemma valid_procedure_has_block C P :
      valid_procedure C P ->
      exists b, component_buffer C b.
    Proof.
      case=> [[-> _ {C P}]|[CI]]; rewrite /component_buffer /=.
        rewrite !mapmE.
        case: (intf Component.main) (has_main)=> [CI|] //=; by eauto.
      rewrite /Program.has_component /Component.is_exporting /=.
      by case=> intf_C CI_P; rewrite !mapmE intf_C /=; eauto.
    Qed.

    Local Definition counter_value C prefix :=
      Z.of_nat (length (comp_subtrace C prefix)).

    Lemma counter_value_app C prefix1 prefix2 :
      counter_value C (prefix1 ++ prefix2)
      = (counter_value C prefix1 + counter_value C prefix2) % Z.
    Proof.
      unfold counter_value.
      now rewrite comp_subtrace_app app_length Nat2Z.inj_add.
    Qed.

    Definition well_formed_memory (prefix: trace) (mem: Memory.t) : Prop :=
      forall C b,
        component_buffer C b ->
        Memory.load mem (C, b, 1%Z) = Some (Int (counter_value C prefix)) /\
        exists v, Memory.load mem (C, b, 0%Z) = Some v.

    Lemma well_formed_memory_store_arg prefix mem C b v :
      component_buffer C b ->
      well_formed_memory prefix mem ->
      exists mem',
        Memory.store mem (C, b, 0%Z) v = Some mem' /\
        well_formed_memory prefix mem'.
    Proof.
      intros C_b wf_mem.
      destruct (wf_mem _ _ C_b) as [_ [v' Hv']].
      destruct (Memory.store_after_load _ _ _ v Hv') as [mem' Hmem'].
      exists mem'. split; trivial.
      intros C' b' C'_b'.
      destruct (wf_mem _ _ C'_b') as [C'_local [v'' Hv'']].
      assert (neq : (C, b, 0%Z) <> (C', b', 1%Z)) by congruence.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem'). clear neq.
      rewrite C'_local. split; trivial.
      destruct (Nat.eqb_spec C' C) as [?|C_neq_C'].
      - subst C'.
        assert (b' = b) by (unfold component_buffer in *; congruence).
        subst b'. clear C'_b'.
        exists v.
        now rewrite (Memory.load_after_store_eq _ _ _ _ Hmem').
      - exists v''.
        assert (neq : (C, b, 0%Z) <> (C', b', 0%Z)) by congruence.
        now rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
    Qed.

    Lemma counter_value_snoc prefix C e :
      counter_value C (prefix ++ [e])
      = (counter_value C prefix
        + if C == cur_comp_of_event e then 1 else 0) % Z.
    Proof.
      unfold counter_value, comp_subtrace.
      rewrite filter_app app_length. simpl.
      rewrite Nat2Z.inj_add.
      now destruct (_ == _).
    Qed.

    Lemma well_formed_memory_store_counter prefix mem C b e :
      component_buffer C b ->
      well_formed_memory prefix mem ->
      C = cur_comp_of_event e ->
      exists mem',
        Memory.store mem (C, b, 1%Z) (Int (counter_value C (prefix ++ [e]))) = Some mem' /\
        well_formed_memory (prefix ++ [e]) mem'.
    Proof.
      intros C_b wf_mem HC.
      destruct (wf_mem _ _ C_b) as [C_local [v Hv]].
      destruct (Memory.store_after_load
                  _ _ _ (Int (counter_value C (prefix ++ [e])))
                  C_local) as [mem' Hmem'].
      exists mem'. split; trivial.
      intros C' b' C'_b'.
      destruct (wf_mem _ _ C'_b') as [C'_local [v' Hv']].
      assert (neq : (C, b, 1%Z) <> (C', b', 0%Z)) by congruence.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem'). clear neq.
      split; eauto.
      rewrite -> counter_value_snoc, <- HC, Nat.eqb_refl in *.
      case: (altP (C' =P C)) => [?|C_neq_C'].
      - subst C'.
        assert (b' = b) by (unfold component_buffer in *; congruence).
        subst b'. clear C'_b'.
        by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem').
      - have neq : (C, b, 1%Z) <> (C', b', 1%Z) by move/eqP in C_neq_C'; congruence.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
        now rewrite Z.add_0_r.
    Qed.

    CoInductive well_formed_state (s: stack_state) (prefix suffix: trace) : CS.state -> Prop :=
    | WellFormedState C stk mem k exp P
      of C = cur_comp s
      &  k = Kstop
      &  exp = procedure_of_trace C P t
      &  well_bracketed_trace s suffix
      &  All well_formed_event suffix
      &  well_formed_stack s stk
      &  well_formed_memory prefix mem
      &  valid_procedure C P
      :  well_formed_state s prefix suffix (C, stk, mem, k, exp).

    Lemma definability_gen s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
      exists2 cs', Star (CS.sem p) cs suffix cs' &
                   CS.final_state cs'.
    Proof.
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = prog_procedures p by [].
      elim: suffix s prefix cs=> [|e suffix IH] /= [C callers] prefix.
      - rewrite cats0 => cs <- {prefix}.
        case: cs / => /= _ stk mem _ _ P -> -> -> _ _ wf_stk wf_mem P_exp.
        exists (C, stk, mem, Kstop, E_exit); last by left.
        have [b C_b] := valid_procedure_has_block P_exp.
        have [C_local _] := wf_mem _ _ C_b.
        rewrite /procedure_of_trace /expr_of_trace.
        apply: switch_spec_else; eauto.
        rewrite -> size_map; reflexivity.
      - move=> cs Et /=.
        case: cs / => /= _ stk mem _ _ P -> -> -> [wf_C wb_suffix] [wf_e wf_suffix] wf_stk wf_mem P_exp.
        destruct (valid_procedure_has_block P_exp) as [b C_b].
        destruct (wf_mem _ _ C_b) as [C_local _].
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']].
        assert (Star1 : Star (CS.sem p)
                             (C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t)) E0
                             (C, stk, mem', Kstop, expr_of_event C P e)).
        { unfold expr_of_trace. rewrite Et comp_subtrace_app. simpl.
          rewrite <- wf_C, Nat.eqb_refl, map_app. simpl.
          assert (H := @switch_spec p _ stk mem _
                                    (map (expr_of_event C P) (comp_subtrace C prefix))
                                    (expr_of_event C P e)
                                    (map (expr_of_event C P) (comp_subtrace C suffix))
                                    E_exit C_b).
          rewrite map_length in H. specialize (H C_local).
          destruct H as [mem'' [Hmem'' Hstar]].
          enough (H : mem'' = mem') by (subst mem''; easy).
          rewrite -> counter_value_snoc, <- wf_C, Nat.eqb_refl in Hmem'.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
          unfold counter_value in *.
          unfold Memory.store in *. simpl in *.
          rewrite Hmem' in Hmem''.
          congruence. }
        assert (Star2 : exists s' cs',
                   Star (CS.sem p) (C, stk, mem', Kstop, expr_of_event C P e) [e] cs' /\
                   well_formed_state s' (prefix ++ [e]) suffix cs').
        {
          clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem.
          destruct e as [C_ P' arg C'|C_ ret_val C'];
          simpl in wf_C, wf_e, wb_suffix; subst C_.
          - case: wf_e => /eqP C_ne_C' Himport.
            exists (StackState C' (C :: callers)).
            destruct (valid_procedure_has_block (or_intror (closed_intf Himport))) as [b' C'_b'].
            destruct (well_formed_memory_store_arg (Int arg) C'_b' wf_mem) as [mem' [Hmem' wf_mem']].
            destruct (wf_mem _ _ C_b) as [_ [v Hv]].
            exists (C', (C, v, Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem',
                    Kstop, procedure_of_trace C' P' t).
            split.
            + take_step. take_step.
              apply star_one. simpl.
              apply CS.eval_kstep_sound. simpl.
              rewrite (negbTE C_ne_C').
              rewrite -> imported_procedure_iff in Himport. rewrite Himport.
              rewrite <- imported_procedure_iff in Himport.
              rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
              unfold component_buffer in C_b, C'_b'. simpl in C_b, C'_b'.
              rewrite C_b. simpl in Hv.
              unfold Component.id, Block.id in *. rewrite Hv.
              generalize C'_b'. unfold component_buffer, Block.id. intros ->.
              simpl in Hmem'. now rewrite Hmem'.
            + econstructor; trivial.
              { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                eexists []; eexists; simpl; split; eauto.
                split; trivial.
                eexists v, P, top, bot.
                by do 3 (split; trivial). }
              right. by apply: (closed_intf Himport).
          - rename wf_e into C_ne_C'.
            destruct callers as [|C'_ callers]; try easy.
            destruct wb_suffix as [HC' wb_suffix].
            subst C'_. simpl. exists (StackState C' callers).
            destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot.
            revert mem wf_mem.
            induction top as [|[[C_ saved] k_] top IHtop].
            + clear Htop. rename bot into bot'.
              destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
              subst bot'. simpl.
              destruct (valid_procedure_has_block P'_exp) as [b' C'_b'].
              intros mem wf_mem.
              destruct (well_formed_memory_store_arg saved   C'_b' wf_mem)  as [mem'  [Hmem' wf_mem']].
              destruct (well_formed_memory_store_arg (Int 0) C'_b' wf_mem') as [mem'' [Hmem'' wf_mem'']].
              exists (C', (C', saved, Kstop) :: top ++ bot, mem'', Kstop, procedure_of_trace C' P' t).
              split.
              * eapply star_step.
                -- now eapply CS.KS_ExternalReturn; eauto.
                -- take_step. take_step; eauto.
                   apply star_one. apply CS.eval_kstep_sound.
                   simpl. rewrite -> Nat.eqb_refl.
                   rewrite (find_procedures_of_trace t P'_exp). simpl in *.
                   unfold component_buffer, Component.id, Block.id in *. simpl in *.
                   unfold component_buffer, Component.id, Block.id in *. simpl in *.
                   now rewrite C'_b' (Memory.load_after_store_eq _ _ _ _ Hmem') Hmem''.
                -- now rewrite E0_right.
              * econstructor; trivial.
                exists ((C', saved, Kstop) :: top), bot. simpl. eauto.
            + intros mem wf_mem.
              simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
              specialize (IHtop Htop).
              destruct (well_formed_memory_store_arg saved C_b wf_mem) as [mem' [Hmem' wf_mem']].
              simpl.
              specialize (IHtop _ wf_mem'). destruct IHtop as [cs' [StarRet wf_cs']].
              exists cs'. split; trivial.
              eapply star_step; try eassumption.
              * apply CS.eval_kstep_sound. simpl.
                unfold component_buffer in *. simpl in *.
                rewrite C_b. unfold Component.id, Block.id in *.
                rewrite -> Hmem', Nat.eqb_refl. eauto.
              * reflexivity. }
        destruct Star2 as (s' & cs' & Star2 & wf_cs').
        specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
        specialize (IH Et wf_cs'). destruct IH as [cs'' Star3 final].
        exists cs''; trivial.
        eapply (star_trans Star1); simpl; eauto.
        now eapply (star_trans Star2); simpl; eauto.
    Qed.

    Lemma definability :
      well_formed_trace t ->
      program_behaves (CS.sem p) (Terminates t).
    Proof.
      move=> wf_t; eapply program_runs=> /=; try reflexivity.
      pose cs := CS.initial_machine_state p.
      suffices H : well_formed_state (StackState Component.main [::]) [::] t cs.
        have [cs' run_cs final_cs'] := @definability_gen _ [::] t _ erefl H.
        by econstructor; eauto.
      case: wf_t => wb_t wf_t_events.
      rewrite /cs /CS.initial_machine_state /= find_procedures_of_trace_main //.
      econstructor; eauto; last by left; eauto.
        exists [::], [::]. by do ![split; trivial].
      intros C b.
      unfold component_buffer, CS.prepare_initial_memory, Memory.load.
      simpl. repeat (rewrite mapmE; simpl).
       destruct (intf C) as [Cint|] eqn:HCint; try easy. simpl.
      intros H. inversion H; subst b; clear H.
      rewrite ComponentMemory.load_prealloc. simpl.
      split; trivial.
      exists (Int 0).
      by rewrite ComponentMemory.load_prealloc.
    Qed.

End WithTrace.
End Definability.

Require Import Intermediate.CS.
Require Import Intermediate.Machine.
Require Import S2I.Definitions.

Definition stack_state_of (cs:CS.state) : stack_state :=
  let '(gps, mem, regs, pc) := cs in
  StackState (Pointer.component pc) (List.map Pointer.component gps).

Lemma intermediate_well_bracketed_trace : forall p t cs cs',
  Star (CS.sem p) cs t cs' ->
  well_bracketed_trace (stack_state_of cs) t.
Proof.
  intros p0 t cs cs' H. induction H.
  - compute. now trivial.
  - destruct H; subst t; simpl in *;
    try match goal with
     | [ H : context[Pointer.component (Pointer.inc _)] |- _] =>
         rewrite Pointer.inc_preserves_component in H
     | [ H : GlobalEnv.find_label_in_component
               (GlobalEnv.prepare_global_env ?p0) ?pc ?l = Some ?pc' |- _] =>
         apply GlobalEnv.find_label_in_component_1 in H; rewrite H
     | [ H : GlobalEnv.find_label_in_procedure
               (GlobalEnv.prepare_global_env ?p0) ?pc ?l = Some ?pc' |- _] =>
         apply GlobalEnv.find_label_in_procedure_1 in H; rewrite H
    end; trivial; try congruence; easy.
Qed.

Lemma intermediate_well_formed_trace : forall p mainP t cs cs',
  Star (CS.sem p) cs t cs' ->
  CS.initial_state p cs ->
  Intermediate.prog_main p = Some mainP ->
  Intermediate.well_formed_program p ->
  well_formed_trace (Intermediate.prog_interface p) t.
Proof.
  intros p0 mainP t cs cs' H H' H'' H'''.
  unfold well_formed_trace. split.
  - apply intermediate_well_bracketed_trace in H.
    unfold CS.CS.initial_state, CS.CS.initial_machine_state in H'.
    rewrite H'' in H'.
    destruct ( Machine.Intermediate.prepare_procedures p0
           (Machine.Intermediate.prepare_initial_memory p0)) as [[mem]].
    destruct (Intermediate.wfprog_main_existence H''' H'') as [main_procs [H43 H44]].
    destruct (Machine.Intermediate.EntryPoint.get Component.main mainP t0).
    now rewrite H' in H.
    + rewrite H' in H. simpl in H. admit. (* should be impossible from well-formedness? *)
  - clear H'' H'. induction H as [| cs t1 cs'' t2 cs''' t HStep HStar IH Ht]. easy.
    simpl in HStep. destruct HStep; try (subst t; easy).
    subst t. simpl. split; try easy. split. easy.
    unfold GlobalEnv.prepare_global_env in H1.
    destruct (Intermediate.prepare_procedures p0
                (Intermediate.prepare_initial_memory p0)) as [[]]. easy.
Admitted.

  (* Definability *)
  (* CH: this should now be related to what Arthur proved:
         - TODO his proof is for complete programs, no linking
           + might need to use source decomposition too?
           + just disjointness + partialization of things might be enough? (weaker than decomposition)
         - TODO his current proof gives us at most the program_behaves conclusion,
           not the conclusions about interfaces and closedness,
           and linkability (maybe from previous point) *)

Lemma definability_with_linking:
  forall p c b m,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.closed_program (Intermediate.program_link p c) ->
    program_behaves (I.CS.sem (Intermediate.program_link p c)) b ->
    prefix m b ->
  exists p' c' b',
    Source.prog_interface p' = Intermediate.prog_interface p /\
    Source.prog_interface c' = Intermediate.prog_interface c /\
    Source.well_formed_program p' /\
    Source.well_formed_program c' /\
    Source.closed_program (Source.program_link p' c') /\
    program_behaves (S.CS.sem (Source.program_link p' c')) b' /\
    prefix m b'.
Proof.
  move=> p c b m wf_p wf_c Hlinkable Hclosed Hbeh Hpre.
  pose intf := unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c).
  have Hclosed_intf : closed_interface intf by case: Hclosed.
  have intf_main : intf Component.main.
    case: Hclosed => _ [? [main_procs [? [/= e ?]]]].
    rewrite /intf -mem_domm domm_union.
    do 2![rewrite Intermediate.wfprog_defined_procedures //].
    by rewrite -domm_union mem_domm e.
  have Hatomic : Atomic (I.CS.sem (Intermediate.program_link p c)) by admit.
  set m' := finpref_trace m.
  have {Hbeh} [cs [cs' [Hcs Hstar]]] :
      exists cs cs',
        I.CS.initial_state (Intermediate.program_link p c) cs /\
        Star (I.CS.sem (Intermediate.program_link p c)) cs m' cs'.
    case: b / Hbeh Hpre.
      move=> cs beh Hcs Hbeh Hpre. (* [beh' e]; subst beh. *)
    (* RB: TODO: Refactor and adapt to SSReflect style. *)
    - destruct m as [m|m|m]; simpl in m'.
      + inversion Hbeh as [t cs' Hstar Hfinal Ht|?|?|?];
          subst; try (inversion Hpre; fail).
        inversion Hpre; subst. exists cs, cs'. split; assumption.
      + (* Essentially the same as the previous one. *)
        inversion Hbeh as [?|?|?|t cs' Hstar Hfinal Ht];
          subst; try (inversion Hpre; fail).
        inversion Hpre; subst. exists cs, cs'. split; assumption.
      + destruct Hpre as [beh' ?]; subst beh.
        pose proof state_behaves_app_inv Hatomic m beh' Hbeh as Hstate.
        destruct Hstate as [cs' [Hstar Hbehaves]].
        exists cs, cs'; split; assumption.
    - intros Hini Hpre.
      destruct m as [m|m|m].
      + inversion Hpre.
      + inversion Hpre; subst.
        do 2![exists (I.CS.initial_machine_state (Intermediate.program_link p c))].
        split; try reflexivity; exact: star_refl.
      + inversion Hpre as [beh' Hbeh'].
        destruct beh' as [t|t|t|t]; try (inversion Hbeh'; fail).
        inversion Hbeh' as [HE0]. symmetry in HE0. apply Eapp_E0_inv in HE0.
        destruct HE0; subst.
        (* This last bit is repeated from the previous branch (and proof). *)
        do 2![exists (I.CS.initial_machine_state (Intermediate.program_link p c))].
        split; try reflexivity; exact: star_refl.
(*
      case/(state_behaves_app_inv Hatomic): Hbeh=> cs' [Hstar Hbeh'].
      by exists cs, cs'; split; eauto.
    (* Program goes wrong initially and produces empty trace.  Thus, any state
       works. *)
    move=> _ [[ | | |beh'] //=]; case: m=> [|//] _.
    do 2![exists (I.CS.initial_machine_state (Intermediate.program_link p c))].
    split; try reflexivity; exact: star_refl.
*)
  have {cs cs' Hcs Hstar} wf_m : well_formed_trace intf m'.
    have [mainP [_ [HmainP _]]] := Intermediate.cprog_main_existence Hclosed.
    have wf_p_c := Intermediate.linking_well_formedness wf_p wf_c Hlinkable.
    exact: intermediate_well_formed_trace Hstar Hcs HmainP wf_p_c.
  have := definability Hclosed_intf intf_main wf_m.
  set back := (program_of_trace intf m') => Hback.
  exists (program_unlink (domm (Intermediate.prog_interface p)) back).
  exists (program_unlink (domm (Intermediate.prog_interface c)) back).
  exists (Terminates m'); split=> /=.
    rewrite -[RHS](unionmK (Intermediate.prog_interface p) (Intermediate.prog_interface c)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  split.
    rewrite /intf unionmC; last by case: Hlinkable.
    rewrite -[RHS](unionmK (Intermediate.prog_interface c) (Intermediate.prog_interface p)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  (* Needs properties about unlinking. *)
  admit.
Admitted.

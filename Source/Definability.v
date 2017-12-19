Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
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
  Variable closed_intf: closed_interface intf.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.
  Variable main_export : exported_procedure intf mainC mainP.

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
      { unfold Memory.store. simpl. rewrite EmemC. simpl. now rewrite Z.add_1_r, EmemC'. }
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
    simpl. now rewrite IH, Nat.sub_succ_r.
  Qed.

  Lemma switch_spec_else p' C stk mem b n es e_else :
    getm (genv_buffers (globalenv (CS.sem p'))) C = Some b ->
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
    unfold switch. simpl. simpl in es_le_n. rewrite fst_switch, <- Nat.sub_succ_r. simpl.
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
    { unfold switch. rewrite fold_right_app, app_length. simpl.
      exists (snd (fold_right switch_add_expr ((length es + S (length es'))%nat, e_else) es')).
      repeat f_equal. rewrite surjective_pairing at 1. simpl.
      rewrite fst_switch, Nat.add_succ_r.
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
    filter (fun e => Component.eqb C (cur_comp_of_event e)) t.

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
    mkfmap (map (fun Ciface =>
                   let '(C, C_interface) := Ciface in
                   (C, fold_right (fun P C_procs =>
                                     setm C_procs P (procedure_of_trace C P t))
                                  emptym
                                  (Component.export C_interface)))
                     (elementsm intf)).

  Lemma find_procedures_of_trace (t: trace) C P :
    exported_procedure intf C P ->
    find_procedure (procedures_of_trace t) C P
    = Some (procedure_of_trace C P t).
  Proof.
    intros [CI [C_CI CI_P]].
    unfold find_procedure, procedures_of_trace.
    (*
    rewrite PMapFacts.mapi_o; try now intros ? ? ? ->.
    apply PMap.find_1 in C_CI. rewrite C_CI. simpl.
    unfold Component.is_exporting in CI_P.
    revert CI_P. generalize (Component.export CI). intros Ps.
    induction Ps as [|P' Ps IH]; simpl; try easy.
    rewrite PMapFacts.add_o.
    intros HP.
    destruct (PMapFacts.eq_dec P' P) as [->|ne]; trivial.
    destruct HP as [|P_in_Ps]; try easy.
    now apply IH.
  Qed.
    *)
  Admitted.

  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapm (fun _ => inr [Int 0; Int 0]) intf;
       prog_main       := Some (mainC, mainP) |}.

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
        head (callers s) = Some C' /\
        well_bracketed_trace (StackState C' (tail (callers s))) t'
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
    well_bracketed_trace (StackState mainC []) t /\
    All well_formed_event t.

  Fixpoint well_formed_callers (callers: list Component.id) (stk: CS.stack) : Prop :=
    match callers with
    | [] => True
    | C :: callers' =>
      exists v P top bot,
      stk = (C, v, Kseq (E_call C P (E_val (Int 0))) Kstop) :: top ++ bot /\
      exported_procedure intf C P /\
      All (fun '(C', _, k) => C' = C /\ k = Kstop) top /\
      well_formed_callers callers' bot
    end.

  Definition well_formed_stack (s: stack_state) (stk: CS.stack) : Prop :=
    exists top bot,
      stk = top ++ bot /\
      All (fun '(C', _, k) => C' = cur_comp s /\ k = Kstop) top /\
      well_formed_callers (callers s) bot.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace.

    Variable t : trace.

    Local Definition p    := program_of_trace t.
    Local Definition init := prepare_buffers p.

    Local Definition component_buffer C b :=
      getm (genv_buffers (prepare_global_env p)) C = Some b.

    Lemma exported_procedure_has_block C P :
      exported_procedure intf C P ->
      exists b, component_buffer C b.
    Proof. Admitted.

    Local Definition counter_value C prefix :=
      Z.of_nat (length (comp_subtrace C prefix)).

    Lemma counter_value_app C prefix1 prefix2 :
      counter_value C (prefix1 ++ prefix2)
      = (counter_value C prefix1 + counter_value C prefix2) % Z.
    Proof.
      unfold counter_value.
      now rewrite comp_subtrace_app, app_length, Nat2Z.inj_add.
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
        + if Component.eqb C (cur_comp_of_event e) then 1 else 0) % Z.
    Proof.
      unfold counter_value, comp_subtrace.
      rewrite filter_app, app_length. simpl.
      rewrite Nat2Z.inj_add.
      now destruct (Component.eqb _ _).
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
      rewrite counter_value_snoc, <- HC, Nat.eqb_refl in *.
      destruct (Nat.eqb_spec C' C) as [?|C_neq_C'].
      - subst C'.
        assert (b' = b) by (unfold component_buffer in *; congruence).
        subst b'. clear C'_b'.
        (*
        now rewrite (Memory.load_after_store_eq _ _ _ _ Hmem').
      - assert (neq : (C, b, 1%Z) <> (C', b', 1%Z)) by congruence.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
        now rewrite Z.add_0_r.
    Qed.
         *)
    Admitted.

    Definition well_formed_state
               (s: stack_state) (prefix suffix: trace) (cs: CS.state) : Prop :=
      let '(C, stk, mem, k, exp) := cs in
      well_bracketed_trace s suffix /\
      All well_formed_event suffix /\
      C = cur_comp s /\
      well_formed_stack s stk /\
      well_formed_memory prefix mem /\
      k = Kstop /\
      exists P,
        exported_procedure intf C P /\
        exp = procedure_of_trace C P t.

    (* AAA: We could probably refine this result and require that [cs'] be a final state. *)

    Lemma definability_gen s prefix suffix cs :
      t = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
      exists cs', Star (CS.sem p) cs suffix cs'.
    Proof.
      assert (Eintf : genv_interface (prepare_global_env p) = intf).
      { unfold prepare_global_env. now destruct (prepare_buffers p). }
      assert (Eprocs : genv_procedures (prepare_global_env p) = prog_procedures p).
      { unfold prepare_global_env. now destruct (prepare_buffers p). }
      revert s prefix cs.
      induction suffix as [|e suffix IH].
      - intros s prefix cs _ _. exists cs. apply star_refl.
      - intros [C callers] prefix [[[[C_ stk] mem] k] exp] Et. simpl.
        intros ([wf_C wb_suffix] & [wf_e wf_suffix] & ? & wf_stk & wf_mem & ? &
                P & P_exp & ?).
        subst C_ k exp.
        destruct (exported_procedure_has_block P_exp) as [b C_b].
        destruct (wf_mem _ _ C_b) as [C_local _].
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']].
        assert (Star1 : Star (CS.sem p)
                             (C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t)) E0
                             (C, stk, mem', Kstop, expr_of_event C P e)).
        { unfold expr_of_trace. rewrite Et, comp_subtrace_app. simpl.
          rewrite <- wf_C, Nat.eqb_refl, map_app. simpl.
          assert (H := @switch_spec p _ stk mem _
                                    (map (expr_of_event C P) (comp_subtrace C prefix))
                                    (expr_of_event C P e)
                                    (map (expr_of_event C P) (comp_subtrace C suffix))
                                    E_exit C_b).
          rewrite map_length in H. specialize (H C_local).
          destruct H as [mem'' [Hmem'' Hstar]].
          enough (H : mem'' = mem') by (subst mem''; easy).
          rewrite counter_value_snoc, <- wf_C, Nat.eqb_refl in Hmem'.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''.
          unfold counter_value in *.
          unfold Memory.store in *. simpl in *.
          rewrite Hmem' in Hmem''.
          congruence. }
        assert (Star2 : exists s' cs',
                   Star (CS.sem p) (C, stk, mem', Kstop, expr_of_event C P e) [e] cs' /\
                   well_formed_state s' (prefix ++ [e]) suffix cs').
        { (*
          clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem.
          destruct e as [C_ P' arg C'|C_ ret_val C'];
          simpl in wf_C, wf_e, wb_suffix; subst C_.
          - destruct wf_e as [C_ne_C' Himport].
            exists (StackState C' (C :: callers)).
            destruct (exported_procedure_has_block (closed_intf Himport)) as [b' C'_b'].
            destruct (well_formed_memory_store_arg (Int arg) C'_b' wf_mem) as [mem' [Hmem' wf_mem']].
            destruct (wf_mem _ _ C_b) as [_ [v Hv]].
            exists (C', (C, v, Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem',
                    Kstop, procedure_of_trace C' P' t).
            split.
            + take_step. take_step. { simpl. rewrite Eintf. auto. }
              apply star_one. simpl.
              apply CS.eval_kstep_sound. simpl.
              rewrite Eprocs. simpl.
              rewrite (find_procedures_of_trace t (closed_intf Himport)), C_b.
              unfold Component.id, PMap.key, Block.id in *. rewrite Hv.
              generalize C'_b'. unfold component_buffer, Block.id. intros ->.
              rewrite Hmem'.
              apply Pos.eqb_neq in C_ne_C'.
              now rewrite C_ne_C'.
            + do 4 (split; trivial).
              { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                eexists []; eexists; simpl; split; eauto.
                split; trivial.
                eexists v, P, top, bot.
                do 3 (split; trivial). }
              do 2 (split; trivial).
              exists P'; split; trivial.
              apply (closed_intf Himport).
          - rename wf_e into C_ne_C'.
            destruct wb_suffix as [HC' wb_suffix].
            destruct callers as [|C'_ callers]; try easy.
            simpl in HC', wb_suffix. assert (C'_ = C') by congruence. subst C'_. clear HC'.
            simpl. exists (StackState C' callers).
            destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot.
            revert mem wf_mem.
            induction top as [|[[C_ saved] k_] top IHtop].
            + clear Htop. rename bot into bot'.
              destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
              subst bot'. simpl.
              destruct (exported_procedure_has_block P'_exp) as [b' C'_b'].
              intros mem wf_mem.
              destruct (well_formed_memory_store_arg saved   C'_b' wf_mem)  as [mem'  [Hmem' wf_mem']].
              destruct (well_formed_memory_store_arg (Int 0) C'_b' wf_mem') as [mem'' [Hmem'' wf_mem'']].
              exists (C', (C', saved, Kstop) :: top ++ bot, mem'', Kstop, procedure_of_trace C' P' t).
              split.
              * eapply star_step.
                -- now eapply CS.KS_CallRet; eauto.
                -- take_step. take_step; eauto.
                   apply star_one. apply CS.eval_kstep_sound.
                   simpl. rewrite C'_b'.
                   rewrite Eprocs. simpl.
                   rewrite (find_procedures_of_trace t P'_exp).
                   unfold Component.id, PMap.key, Block.id in *.
                   now rewrite (Memory.load_after_store_eq _ _ _ _ Hmem'), Hmem'', Pos.eqb_refl.
                -- apply Pos.eqb_neq in C_ne_C'. now rewrite C_ne_C'.
              * do 4 (split; trivial).
                { exists ((C', saved, Kstop) :: top), bot. simpl. eauto. }
                do 2 (split; trivial).
                exists P'. split; trivial.
            + intros mem wf_mem.
              simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
              specialize (IHtop Htop).
              destruct (well_formed_memory_store_arg saved C_b wf_mem) as [mem' [Hmem' wf_mem']].
              simpl.
              specialize (IHtop _ wf_mem'). destruct IHtop as [cs' [StarRet wf_cs']].
              exists cs'. split; trivial.
              eapply star_step; try eassumption.
              * apply CS.eval_kstep_sound. simpl.
                rewrite C_b. unfold Component.id, PMap.key, Block.id in *.
                rewrite Hmem', Pos.eqb_refl. eauto.
              * reflexivity. *) admit. }
        destruct Star2 as (s' & cs' & Star2 & wf_cs').
        specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
        specialize (IH Et wf_cs'). destruct IH as [cs'' Star3].
        exists cs''.
        eapply (star_trans Star1); simpl; eauto.
        eapply (star_trans Star2); simpl; eauto.
    Admitted.

    Lemma definability cs :
      well_formed_trace t ->
      initial_state (CS.sem p) cs ->
      exists cs', Star (CS.sem p) cs t cs'.
    Proof.
      intros wf_t init_cs.
      enough (H : well_formed_state (StackState mainC []) [] t cs).
      { apply (@definability_gen _ [] t _ eq_refl H). }
      destruct cs as [[[[C stk] mem] k] e].
      destruct wf_t as [wb_t wf_t_events].
      unfold initial_state in init_cs. simpl in *.
      unfold CS.initial_state, CS.initial_machine_state in init_cs.
      destruct (prog_main p) as [[mainC' mainP']|] eqn:Hmain;
        try discriminate.
      destruct (find_procedure (prog_procedures p) mainC' mainP') eqn:Hproc;
        inversion init_cs; subst.
      - do 3 (split; trivial).
        admit.
        split.
        + { exists [], []. repeat (split; trivial). }
        + split.
          * split.
            ** admit.
            ** admit.
          * split; trivial.
            ** admit.
      - (* bad case, should probably be ruled out by the fact that the program
           is well-formed and closed *)
        admit.
    Admitted.
End WithTrace.
End Definability.

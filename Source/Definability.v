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

  (** If a component has multiple procedures, they can share the same
      code. Notice that each branch that performs call performs a recursive call
      at the end.  This is needed to trigger multiple events from a single
      function.

      The first ingredient needed to perform this translation is a switch
      statement that runs code based on the value of the first local variable.

   *)

  Definition switch_clause n e_then e_else :=
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

  (** We use [switch] to define the following function [expr_of_trace], which
      converts a sequence of events to an expression that produces that sequence
      of events when run from the appropriate component.  We assume that all
      events were produced from the same component.  The [C] and [P] arguments
      are only needed to generate the recursive calls depicted above. *)

  Variable loc_of_reg : Eregister -> expr.
  Hypothesis values_are_integers_loc_of_reg:
    forall r, Source.values_are_integers (loc_of_reg r).
  Hypothesis called_procedures_loc_of_reg:
    forall r, called_procedures (loc_of_reg r) = fset0.
  
  Variable binop_of_Ebinop : Ebinop -> binop.
  
  Variable expr_of_const_val : value -> expr.
  Hypothesis values_are_integers_expr_of_const_val:
    forall v, Source.values_are_integers (expr_of_const_val v).
  Hypothesis called_procedures_expr_of_const_val:
    forall v, called_procedures (expr_of_const_val v) = fset0.

  (* We call this function when in component C executing P. *)
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (e: event_inform) : expr :=
    match e with
    | ECallInform _ P' arg _ C' =>
      E_seq (E_call C' P' (E_deref (loc_of_reg E_R_COM)))
            (E_call C  P  (E_val (Int 0))) (* This is really (C,P) calling itself. *)
    | ERetInform  _ ret_val _ _ => E_deref (loc_of_reg E_R_COM)
    (* NOTE: At the moment, no read and write events are generated by the
       semantics, so we just generate garbage here. *)
    | EConst cid val reg => E_assign (loc_of_reg reg) (expr_of_const_val val)
    | EMov cid reg1 reg2 => E_assign (loc_of_reg reg1) (loc_of_reg reg2)
    | EBinop cid bop r1 r2 r3 => E_assign (loc_of_reg r3) (E_binop
                                                             (binop_of_Ebinop bop)
                                                             (E_deref (loc_of_reg r1))
                                                             (E_deref (loc_of_reg r2))
                                                          )
    | ELoad cid r_dest r_src => E_assign (loc_of_reg r_dest) (E_deref (loc_of_reg r_src))
    | EStore cid r_dest r_src => E_assign (loc_of_reg r_dest) (E_deref (loc_of_reg r_src))
    | EAlloc cid r_size r_dest => E_assign (loc_of_reg r_dest)
                                           (E_alloc
                                              (E_deref (loc_of_reg r_size))
                                           )
    | EInvalidateRA cid => E_assign (loc_of_reg E_R_RA) (E_val (Int 0))
    end.

  Definition expr_of_trace (C: Component.id) (P: Procedure.id) (t: trace event_inform)
    : expr :=
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

  Definition procedure_of_trace C P t :=
    expr_of_trace C P (comp_subtrace C t).

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
       Source.prog_buffers    := mapm (fun _ => inr [Int 0]) intf |}.

  (** To prove that [program_of_trace] is correct, we need to describe how the
      state of the program evolves as it emits events from the translated trace.
      One of the difficulties is the stack.  If a call to a component [C]
      performs [n] calls to other components before returning, the code
      generated by [expr_of_trace] will perform [n] *recursive* calls to [C].
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
  Admitted.
     (* have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (comp_subtrace C t))).
      {
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: {t Ht} (comp_subtrace C t) (length _)=> [|e t IH] n //=.
        exact: fsub0set.
        move/(_ n) in IH; rewrite !fset0U.
        case: e=> [C' P' v mem C''| | | | | | | |]
                    //=;
                    try by move=> C' e e0; rewrite !called_procedures_loc_of_reg !fset0U IH.
        * rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=.
          rewrite called_procedures_loc_of_reg fsub0set.
            by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT.
        * by move=> C' P' e; rewrite called_procedures_loc_of_reg
                                     called_procedures_expr_of_const_val !fset0U IH.
        * by move=> C' e0 e1 e2 e; rewrite !called_procedures_loc_of_reg !fset0U IH.
        * by move=> C'; rewrite !called_procedures_loc_of_reg !fset0U IH.
      }
      (*unfold valid_calls. intros C0 P0 Hin.
      destruct (C0 == C) eqn:C0_C.
      SearchAbout find_procedure prog_procedures.
      + apply wfprog_exported_procedures_existence.
        SearchAbout well_formed_program program_of_trace
      SearchAbout C.
      Check find_procedures_of_trace.*)
      (*Check find_procedures_of_trace_exp.
      SearchAbout sub_mem fsubset.
      SearchAbout fsubset in_mem.*)
      (*unfold valid_calls.*)

      (*[DynShare]: Why is sub useful? *)
      
      (*move=> /sub/fsetU1P [[-> ->]|] {sub}. 
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
      case: e HC He=> [_ P' v C'' /= <-| | |]; try by eauto.
      rewrite inE; case/andP=> [C_C'' /imported_procedure_iff imp_C''_P'].
      by case/orP=> [/eqP [-> ->] //|]; eauto.
       *)
      admit.
    - by rewrite domm_map.
    - move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      rewrite /has_required_local_buffers /= mapmE C_CI /=.
      eexists; eauto=> /=; omega.
    - rewrite /prog_main find_procedures_of_trace //=.
      + split; first reflexivity.
        intros _.
        destruct (intf Component.main) as [mainP |] eqn:Hcase.
        * apply /dommP. exists mainP. assumption.
        * discriminate.
      + by left.
*)

  Lemma closed_program_of_trace t :
    Source.closed_program (program_of_trace t).
  Proof.
    split=> //=; by rewrite /Source.prog_main find_procedures_of_trace_main.
  Qed.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace.

    Variable t_inform : trace event_inform.

    (* Let t    :=  *)
    (* [DynShare]: This should be the projection of t_inform.
       This projection function may be defined in the Intermedicate/CS.v *)
    Let p    := program_of_trace t_inform.
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

    Definition well_formed_memory (prefix: trace event_inform) (mem: Memory.t) : Prop :=
      forall C,
        component_buffer C ->
        Memory.load mem (Permission.data, C, Block.local, 0%Z) =
        Some (Int (counter_value C prefix)).

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

    Lemma well_formed_memory_store_counter prefix mem C e :
      component_buffer C ->
      well_formed_memory prefix mem ->
      C = cur_comp_of_event e ->
      exists mem',
        Memory.store mem (Permission.data, C, Block.local, 0%Z)
                     (Int (counter_value C (prefix ++ [e]))) = Some mem' /\
        well_formed_memory (prefix ++ [e]) mem'.
    Proof.
      move=> C_b wf_mem HC.
      have C_local := wf_mem _ C_b.
      have [mem' Hmem'] := Memory.store_after_load
                             _ _ _ (Int (counter_value C (prefix ++ [e])))
                             C_local.
      exists mem'. split; trivial=> C' C'_b.
      have C'_local := wf_mem _ C'_b.
      rewrite -> counter_value_snoc, <- HC, Nat.eqb_refl in *.
      case: (altP (C' =P C)) => [?|C_neq_C'].
      - subst C'.
        by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem').
      - have neq : (Permission.data, C, Block.local, 0%Z) <>
                   (Permission.data, C', Block.local, 0%Z) by move/eqP in C_neq_C'; congruence.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
        now rewrite Z.add_0_r.
    Qed.

    Variant well_formed_state (s: stack_state)
            (prefix suffix: trace event_inform) : CS.state -> Prop :=
    | WellFormedState C stk mem k exp arg P
      of C = cur_comp s
      &  k = Kstop
      &  exp = procedure_of_trace C P t_inform
      &  well_bracketed_trace s suffix
      &  all (well_formed_event intf) suffix
      &  well_formed_stack s stk
      &  well_formed_memory prefix mem
      &  valid_procedure C P
      :  well_formed_state s prefix suffix [CState C, stk, mem, k, exp, arg].

    (* [DynShare] We will probably need a variant of well formedness that is defined
     on non-informative traces as well. *)

    Lemma definability_gen s prefix suffix cs :
      t_inform = prefix ++ suffix ->
      well_formed_state s prefix suffix cs ->
      exists2 cs', exists2 suffix_non_inform, Star (CS.sem p) cs suffix_non_inform cs' &
                                     project_non_inform suffix = suffix_non_inform &
                                     CS.final_state cs'.
    Admitted.
   (* Proof.
      have Eintf : genv_interface (prepare_global_env p) = intf by [].
      have Eprocs : genv_procedures (prepare_global_env p) = prog_procedures p by [].
      elim: suffix s prefix cs=> [|e suffix IH] /= [C callers] prefix.
      - rewrite cats0 => cs <- {prefix}.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> _ _ wf_stk wf_mem P_exp.
        exists [CState C, stk, mem, Kstop, E_exit, arg]; last by left.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := wf_mem _ C_b.
        rewrite /procedure_of_trace /expr_of_trace.
        apply: switch_spec_else; eauto.
        rewrite -> size_map; reflexivity.
      - move=> cs Et /=.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> /andP [/eqP wf_C wb_suffix] /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := wf_mem _ C_b.
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']].
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
        assert (Star2 : exists s' cs',
                   Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] [:: e] cs' /\
                   well_formed_state s' (prefix ++ [e]) suffix cs').
        {
          clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem.
          destruct e as [C_ P' new_arg C'|C_ ret_val C' |C_ ptr v |C_ ptr v];
          simpl in wf_C, wf_e, wb_suffix; subst C_.
          - case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
            exists (StackState C' (C :: callers)).
            have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).
            exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem,
                    Kstop, procedure_of_trace C' P' t, Int new_arg].
            split.
            + take_step. take_step.
              apply star_one. simpl.
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
          - move: wf_e=> /eqP C_ne_C'.
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
              intros mem wf_mem.
              exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0].
              split.
              * eapply star_step.
                -- now eapply CS.KS_ExternalReturn; eauto.
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
              * by apply/CS.eval_kstep_sound; rewrite /= eqxx.
              * reflexivity.
          (* At the moment we might discharge these by noting that no such
             events are being generated. *)
          - admit.
          - admit.
        }
        destruct Star2 as (s' & cs' & Star2 & wf_cs').
        specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
        specialize (IH Et wf_cs'). destruct IH as [cs'' Star3 final].
        exists cs''; trivial.
        eapply (star_trans Star1); simpl; eauto.
        now eapply (star_trans Star2); simpl; eauto.
    Admitted.
*)

    Lemma definability :
      well_formed_trace intf t_inform ->
      program_behaves (CS.sem p) (Terminates (project_non_inform t_inform)).
    Admitted.
    (*
    Proof.
      move=> wf_t; eapply program_runs=> /=; try reflexivity.
      pose cs := CS.initial_machine_state p.
      suffices H : well_formed_state (StackState Component.main [::]) [::] t cs.
        have [cs' run_cs final_cs'] := @definability_gen _ [::] t _ erefl H.
        by econstructor; eauto.
      case/andP: wf_t => wb_t wf_t_events.
      rewrite /cs /CS.initial_machine_state /prog_main /= find_procedures_of_trace_main //.
      econstructor; eauto; last by left; eauto.
        exists [::], [::]. by do ![split; trivial].
      intros C.
      unfold component_buffer, Memory.load.
      simpl. repeat (rewrite mapmE; simpl); rewrite mem_domm.
      case HCint: (intf C) => [Cint|] //=.
      by rewrite ComponentMemory.load_prealloc /=.
    Qed.
     *)
End WithTrace.
End Definability.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.

(*Section MainDefinability.*)
  Definition loc_of_reg : Eregister -> expr. Admitted.
  
  Definition binop_of_Ebinop : Ebinop -> binop. Admitted.
  
  Definition expr_of_const_val : value -> expr. Admitted.


(* FG : Put back some sanity checks ? some are present but commented in the premise and the move => *)
Lemma matching_mains_backtranslated_program p c intf back m:
  Intermediate.well_formed_program p ->
  Intermediate.well_formed_program c ->
  (* intf = unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c) -> *)
  back = program_of_trace intf loc_of_reg binop_of_Ebinop expr_of_const_val m ->
  intf Component.main ->
  (* well_formed_trace intf m -> *)
  matching_mains (Source.program_unlink (domm (Intermediate.prog_interface p)) back) p.
Admitted.
(*Proof.
  move => wf_p wf_c (* intf' *) Hback intf_main (* wf_back *).
  unfold matching_mains.
  split.
  - (* <-, no main in intermediate implies no main in source bactkanslated *)
    unfold prog_main, program_unlink. simpl.
    rewrite find_procedure_filter_comp.
    move => Hinterm.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hcase.
    + inversion wf_p as [_ _ _ _ _ _ Hmain_component].
      pose proof (proj1 (Intermediate.wfprog_main_component wf_p) Hcase) as Hmainp.
      done.
    + rewrite Hcase in Hinterm. done.
  - (* -> *) (* maybe can be done with more finesse *)
    unfold prog_main. unfold program_unlink. rewrite Hback. simpl. rewrite find_procedure_filter_comp.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hmain_comp ; rewrite Hmain_comp.
    + intros Hprog_main.
      rewrite find_procedures_of_trace_main. done.
      assumption.
    + intros Hcontra.
      apply (Intermediate.wfprog_main_component wf_p) in Hcontra.
      rewrite Hmain_comp in Hcontra. done.
Qed.*)

(* Definability *)

(* RB: Relocate? As the S2I require above seems to indicate, this is not where
   this result belongs. *)
Print Module Intermediate.
Import Intermediate.CS.

Lemma definability_with_linking:
  forall p c b m,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.closed_program (Intermediate.program_link p c) ->
    program_behaves (Intermediate.sem (Intermediate.program_link p c)) b ->
    prefix m b ->
    not_wrong_finpref m ->
  exists p' c',
    Source.prog_interface p' = Intermediate.prog_interface p /\
    Source.prog_interface c' = Intermediate.prog_interface c /\
    matching_mains p' p /\
    matching_mains c' c /\
    Source.well_formed_program p' /\
    Source.well_formed_program c' /\
    Source.closed_program (Source.program_link p' c') /\
    does_prefix (S.CS.sem (Source.program_link p' c')) m.
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
        Star (I.CS.sem (Intermediate.program_link p c)) cs m' cs'.
    case: b / Hbeh Hpre {Hnot_wrong}.
    - rewrite {}/m' => cs beh Hcs Hbeh Hpre.
      case: m Hpre=> [m|m|m] /= Hpre.
      + case: beh / Hbeh Hpre=> //= t cs' Hstar Hfinal -> {m}.
        by exists cs, cs'; split.
      + case: beh / Hbeh Hpre=> //= t cs' Hstar Hfinal Ht -> {m}.
        by exists cs, cs'; split.
      + destruct Hpre as [beh' ?]; subst beh.
        have [cs' [Hstar Hbehaves]] := state_behaves_app_inv (I.CS.singleton_traces _) m beh' Hbeh.
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
  have := definability Hclosed_intf intf_main wf_m.
  set back := (program_of_trace intf m') => Hback.
  exists (program_unlink (domm (Intermediate.prog_interface p)) back).
  exists (program_unlink (domm (Intermediate.prog_interface c)) back).
  split=> /=.
    rewrite -[RHS](unionmK (Intermediate.prog_interface p) (Intermediate.prog_interface c)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  split.
    rewrite /intf unionmC; last by case: Hlinkable.
    rewrite -[RHS](unionmK (Intermediate.prog_interface c) (Intermediate.prog_interface p)).
    by apply/eq_filterm=> ??; rewrite mem_domm.
  have wf_back : well_formed_program back by exact: well_formed_events_well_formed_program.
  have Hback' : back = program_of_trace intf m' by [].
  split; first exact: matching_mains_backtranslated_program wf_p wf_c Hback' intf_main.
  split; first exact: matching_mains_backtranslated_program wf_c wf_p Hback' intf_main.
  clear Hback'.
  split; first exact: well_formed_program_unlink.
  split; first exact: well_formed_program_unlink.
  rewrite program_unlinkK //; split; first exact: closed_program_of_trace.
  exists (Terminates m').
  split=> // {wf_events back Hback wf_back wf_m}.
  rewrite {}/m'; case: m {Hpre} Hnot_wrong=> //= t _.
  by exists (Terminates nil); rewrite /= E0_right.
Qed.

End MainDefinability.
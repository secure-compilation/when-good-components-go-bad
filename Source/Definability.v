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
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq path.
From mathcomp Require ssrnat.

Import Source.

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
      source program that can produce that trace. Roughly speaking, it does so
      by keeping one counter for each component, and using that counter to track
      how many calls or returns have been executed by that component.

      To see how this works, suppose that we have an interface with two
      procedures P1 and P2, which live in components C1 and C2, and with C1 and
      C2 having a public buffer of size 2. Given the trace *)


  (**   ECall mainC P1    0 C1
        ECall C1    P2    1 C2
        ERet  C2          2 C1
        ECall C1    P2    3 C2
        ECall C2    mainP 4 mainC *)

  (** we would produce the program *)

  (**   C1 {
          P1() {
            if (local.private[0] == 0) {
              local.private[0]++;
              C2.P2(1);
              C1.P1(0);
            } else if (local.private[0] == 1) {
              local.private[0]++;
              C2.P2(3);
              C1.P1(0);
            } else {
              exit();
            }
          }
        }

        C2 {
          P2() {
            if (local.private[0] == 0) {
              local.private[0]++;
              return 2;
            } else if (local.private[0] == 1) {
              local.private[0]++;
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

  Definition counter_idx : Block.offset := 0%Z.
  Definition counter_loc : expr := E_local Block.priv.
  Definition increment exp_val := E_binop Add exp_val (E_val (Int 1%Z)).

  Hint Unfold increment counter_idx counter_loc.
  Hint Transparent increment counter_idx counter_loc.

  (** Simple clause for switching on the different events. Gives an if
      expression that branches on the given expressions, depending on the value
      of the private local counter. This counter, initialized at 0, is
      incremented when the 'then' branch is taken. *)
  Definition switch_clause n e_then e_else :=
    E_if (E_binop Eq (E_deref (E_local Block.priv)) (E_val (Int n)))
         (E_seq (E_assign (E_local Block.priv)
                          (increment (E_deref counter_loc))) e_then)
         e_else.

  Ltac take_step :=
    match goal with
    | |- @star _ _ _ _ _ ?t _ =>
      eapply (@star_step _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
    end.

  (** States which branch is taken wrt. the incrementation of the counter in the
      semantics (on a single switch clause) *)
  Lemma switch_clause_spec p' C stk mem n n' e_then e_else arg :
    Memory.load mem (C, Block.private, counter_idx) = Some (Int n) ->
    if (n =? n') % Z then
      exists mem',
        Memory.store mem (C, Block.private, counter_idx) (Int (Z.succ n)) = Some mem' /\
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
      destruct (getm mem C) as [memC|] eqn:EmemC; try discriminate.
      destruct (ComponentMemory.store_after_load _ _ _ _ (Int (Z.succ n)) Hload')
        as [memC' EmemC'].
      rewrite EmemC'.
      eexists; split; eauto.
      repeat take_step; trivial; try eassumption.
      repeat take_step; trivial; try eassumption.
      rewrite Z.eqb_refl -[_ != _]/(true) /=.
      repeat take_step; trivial; try eassumption.
      { unfold Memory.store. simpl. rewrite EmemC. simpl. now rewrite Z.add_1_r EmemC'. }
      apply star_refl.
    - unfold switch_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite <- Z.eqb_neq in n_n'. rewrite n_n'. simpl.
        eapply CS.KS_If2. }
      apply star_refl.
  Qed.

  Definition switch_add_expr e res :=
    (Nat.pred (fst res), switch_clause (Z.of_nat (Nat.pred (fst res))) e (snd res)).

  (** Constructs the full switch expression branching on the different
      expressions of the 'es' argument, with the last branch being the 'e_else'.
      *)
  Definition switch (es: list expr) (e_else: expr) : expr :=
    snd (fold_right switch_add_expr (length es, e_else) es).

  Lemma fst_switch n (e_else: expr) (es : list expr) :
    fst (fold_right switch_add_expr (n, e_else) es) = (n - length es)%nat.
  Proof.
    induction es as [|e' es IH]; try now rewrite Nat.sub_0_r.
    simpl. now rewrite IH Nat.sub_succ_r.
  Qed.

  (** States that the final else branch is taken if the number of remaining
      'then' expressions (those of 'es') is inferior to the current value of the
      counter (in a potentially full switch expression), allowing us to not
      evaluate these *)
  Lemma switch_spec_else p' C stk mem n es e_else arg :
    Memory.load mem (C, Block.private, counter_idx) = Some (Int (Z.of_nat n)) ->
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
    do 2 take_step.
    eapply (@star_step _ _ _ _ _ E0); try now (simpl; reflexivity).
    { apply CS.eval_kstep_sound. simpl.
      destruct (Z.eqb_spec (Z.of_nat n) (Z.of_nat (m - S (length es)))) as [n_eq_0|?]; simpl.
      - zify. omega.
      - reflexivity. }
    apply IH. omega.
  Qed.

  Lemma switch_spec p' C stk mem es e es' e_else arg :
    Memory.load mem (C, Block.private, counter_idx) = Some (Int (Z.of_nat (length es))) ->
    exists mem',
      Memory.store mem (C, Block.private, counter_idx) (Int (Z.of_nat (S (length es)))) = Some mem' /\
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
    apply (fun H => @star_trans _ _ _ _ _ E0 _ H E0 _ _ Hstar2); trivial.
    apply (switch_spec_else p' stk _ arg Hload).
    reflexivity.
  Qed.

  (** Before back-translating the events themselves directly into expressions,
      we may need to add assignments expressions.

      When a call or a return is encountered in the program, this means that the
      component is giving its turn to another one, so recreating the fitting
      expression can be done with only the corresponding event and its data.

      This is not as simple when dereferencing another component's memory.
      Indeed, recreating directly an expression triggering a load event would
      dereference a part of memory that has not necessarily been set to the
      right value beforehand and the load events would generally yield an
      undefined value.

      Thus, we need to initialize the public memory ahead of time, while it's
      still the turn of the component owning memory. This is done by inserting a

   *)

  (** Gives a map of the different indexes of a component's public memory to
      bool, all initialized at false *)
  (* Definition indexes_read_init (comp: Component.interface) :  NMap bool := *)
  (*   let size_buf := *)
  (*       Component.public_buffer_size comp in *)
  (*   mkfmap (combine (iota 0 size_buf) (nseq size_buf false)). *)


  (* Would be nicer to use an empty map indexed by integers, so that we don't
     have a useless double check :
     if empty, we can just state that (getm indexes i) = None <-> ...= Some false
     (for the previous definition). That way we don't even have to worry about
     out of bounds since this would be insured by the well-formedness of events *)
  Fail Definition indexes (* : {fmap Z -> bool} *) := @emptym Z unit.
  (* Fails since Z isn't yet an ordType *)

  (* In fact, we don't even have to have a map, just a set or a list containing the
     indexes that we read would be enough, and checking for membership and cons-ing
     the list would suffice *)
  (* The only issue would be that we won't be terminating as early as we could
     (since prefill_read_aux can stop when all indexes have been read), but that's
     not too bad *)
  (* Z is not an ordType could be changed in extructures but not worth it for this *)
  Fail Definition indexes (* : {fset Z} *) := @fset0 Z.
  Definition indexes := seq Z.

  Definition indexes_read_init : indexes := nil.

  Definition lookup_index (ind:indexes) (i:Z) : bool := i \in ind.
  Definition add_index (ind:indexes) (i:Z) : indexes := i::ind.

  (** Flattens a list of expr into a single E_seq expr. *)
  Local Definition E_seq_of_exprs_right (ex : expr) (exprs : list expr) : expr :=
    foldr E_seq
          (last ex exprs)
          (belast ex exprs).

  Definition E_seq_of_list_expr (exprs : list expr) : option expr :=
    match exprs with
    | nil => None
    | expr :: exprs' => Some (E_seq_of_exprs_right expr exprs')
    end.

  Definition E_seq_of_list_expr' (exprs : list expr) : option expr :=
    match exprs with
    | [] => None
    | expr :: exprs' => Some (fold_left (fun exp1 exp__added => E_seq exp1 exp__added)
                                      exprs' expr)
    end.

  Lemma E_seq_of_list_expr_integers (exprs : list expr) : forall (e : expr),
    all (values_are_integers) exprs ->
    E_seq_of_list_expr exprs = Some e ->
    values_are_integers e.
  Proof.
    rewrite /E_seq_of_list_expr/E_seq_of_exprs_right ; destruct exprs => //.
    generalize dependent e.
    elim:exprs => //=.
    - by move => e e' /andP[Hval _] Hsome ; inversion Hsome ; subst.
    - move => e' seq IH e e_seq /andP[Hval_e] ;
               move => /andP [Hval_seq Hval_e'] Hsome.
      inversion Hsome as [H].
      apply /andP ; rewrite -/values_are_integers ; split; first done.
      by apply IH with (e:= e') ; first by apply/andP.
  Qed.


  Lemma e_seq_assoc p exprs exp_prefill exp_prefill' C s mem mem' k arg evs last_e:
    E_seq_of_list_expr  (rcons exprs last_e) = Some exp_prefill  ->
    E_seq_of_list_expr' (rcons exprs last_e) = Some exp_prefill' ->
    Plus (CS.sem p)
         [CState C, s, mem,  k, exp_prefill, arg] evs
         [CState C, s, mem', k, last_e, arg] <->
    Plus (CS.sem p)
         [CState C, s, mem,  k, exp_prefill', arg] evs
         [CState C, s, mem', k, last_e, arg].
  Proof.
    case: exprs => [|first_e exprs] ; rewrite /E_seq_of_exprs_right/= => Hexp Hexp';
      inversion Hexp ; inversion Hexp' ; subst ; clear Hexp Hexp' ; first reflexivity.
    move: first_e last_e C s mem mem' k arg evs. rewrite /E_seq_of_exprs_right /=.
    induction exprs as [| second_e exprs IHexprs] => //= ; split (* => [ Hfoldr | Hfoldl ] *).
    - move => Hfoldr. apply IHexprs.
      move: Hfoldr; rewrite !last_rcons !belast_rcons /= => Hfoldr.
      inversion Hfoldr as [? ? ? ? ? ? Hstep Hstar] ; subst.
      (* erewrite CS.seq_assoc_in_CS. *)
  Admitted.

  (** Gives an assignement expression of the public memory (at index off) to val *)
  Definition assign_public off val :=
    E_assign (E_binop Add (E_local Block.pub) (E_val (Int off))) (E_val val).

    (** Gives a list of assignement depending on the ELoad events in the future of
      the trace (accumulated)
      This list is in reverse order since append costs more than cons
      (actually the order doesn't matter since we just want to initialize memory
      with all these expressions)
      (well maybe this matters because we may have some malformed events, so we
      want to still have the well-formed before these)
   *)
  Fixpoint assignment_values_fun
           {T:Type} (f: (Block.offset * value) -> T)
           (C: Component.id)
           (suffix: trace)
           (acc :list T)
           (indexes_read:indexes) : list T :=
    let stop := acc in
    match suffix with
    | [] => stop            (* if no further events, give back exprs created *)
    | ev :: suffix' =>
      let keep_on := (assignment_values_fun f C suffix' acc indexes_read) in
      match ev with
      | ELoad Cdrf off val Cown =>   (* component is read *)
        (* kinda useless check since the trace is well formed, we shouldn't
             have "wild" ELoad events *)
        if Cown == C then
          if (lookup_index indexes_read off)
          then keep_on (* already read so go on *)
          else assignment_values_fun f C suffix' ((f(off, val)) :: acc)
                                     (add_index indexes_read off)
        else keep_on
      (* if the component is given turn again, give back exprs created *)
      | ERet _(* C *) _ _  | ECall _(* C *) _ _ _  => stop
      end
    end.

  Fixpoint assignment_values_fun_ntr
           {T:Type} (f: (Block.offset * value) -> T )
           (C: Component.id)
           (suffix: trace)
           (indexes_read:indexes) : list T :=
    let stop := [] in
    match suffix with
    | [] => stop            (* if no further events, give back exprs created *)
    | ev :: suffix' =>
      let keep_on :=  (assignment_values_fun_ntr f C suffix' indexes_read) in
      match ev with
      | ELoad Cdrf off val Cown =>   (* component is read *)
        (* kinda useless check since the trace is well formed, we shouldn't
             have "wild" ELoad events *)
        if Cown == C then
          if (lookup_index indexes_read off)
          then keep_on (* already read so go on *)
          else (f (off, val)) ::
                              (assignment_values_fun_ntr f C
                                                     suffix'
                                                     (add_index indexes_read off))
        else keep_on
      (* if the component is given turn again, give back exprs created *)
      | ERet _(* C *) _ _  | ECall _(* C *) _ _ _  => stop
      end
    end.


  Definition prefill_read_aux := assignment_values_fun (prod_curry assign_public).
  Definition prefill_read_aux_ntr := assignment_values_fun_ntr (prod_curry assign_public).

  Definition values_read_of_trace := assignment_values_fun (fun x => x).
  (** Can be used to simplify (or even solve) a goal consisting of a (boolean)
      property on a prefill_read_aux(_ntr)-constructed expression *)
  Tactic Notation "destruct_and_simpl" constr(term) := destruct term eqn:?; simpl ; subst ; try done.
  Ltac simplify_prefill_read_aux :=
    repeat
      match goal with
      | |- is_true
            (_ match ?term with | _ => _
               end
            )
        => match type of term with
          | event => destruct_and_simpl term
          | option bool => destruct_and_simpl term
          | bool => destruct_and_simpl term
          end
      | _ => fail
      end.


  Lemma prefill_read_aux_invar : forall suffix C comp acc indexes res,
      intf C = Some comp ->
      (* Add a restriction on the indexes wrt comp.public_buffer_size ? case
         analysis on indexes_read_init comp should suffice *)
      prefill_read_aux C suffix acc indexes (* (indexes_read_init comp) *) = res ->
      exists res', prefill_read_aux_ntr C suffix indexes = res' /\
              res = rev res' ++ acc.
  Proof.
    induction suffix as [| ev suffix IHsuffix] ; intros C comp acc indexes res Hintf.
    - simpl.  exists [] ; subst ;  split ; done.
    - elim: ev => [ Ccur proc arg Cnext | Cret ret Cnext  | CSrc o v CTrg ] ;
                   subst ; try (exists [] ; split ; done).
      rewrite/prefill_read_aux/prefill_read_aux_ntr/=.

      (* simplify_prefill_read_aux. *)
      (* repeat match goal with *)
      (*        | |- _ -> match ?term with | _ => _ *)
      (*               end *)
      (*               = _ *)
      (*          => match type of term with *)
      (*            | event => destruct_and_simpl term *)
      (*            (* | option bool => destruct_and_simpl term *) *)
      (*            | bool => destruct_and_simpl term *)
      (*            end *)
      (*        | _ => fail *)
      (*        end. *)
      (* Load event *)
      destruct (CTrg == C) eqn:WhichTrgComp => //;
      (* Case analysis on presence of the index in the map *)
        case: (lookup_index indexes o) => //;
          try by apply (IHsuffix C comp).
      + (* TODO surely can be simplified *)
        set indexes_upd := add_index indexes o.
        set res_IH := prefill_read_aux C suffix (assign_public o v :: acc) indexes_upd.
        set res'_IH := prefill_read_aux_ntr C suffix indexes_upd.
        set acc_IH := (assign_public o v :: acc).
        specialize (IHsuffix C comp acc_IH indexes_upd res_IH Hintf).
        have refl: prefill_read_aux C suffix acc_IH indexes_upd = res_IH by [].
        apply IHsuffix in refl.
        destruct refl as [? [? H]]. exists (assign_public o v::x). subst.
        (* exists (assign_public o v :: prefill_read_aux_ntr C suffix indexes_upd). *)
        rewrite rev_cons cat_rcons.
        split ; done.
  Qed.

  Lemma prefill_read_aux_equiv : forall suffix C comp,
      intf C = Some comp ->
      prefill_read_aux_ntr C suffix indexes_read_init =
      rev (prefill_read_aux C suffix [] indexes_read_init).
  Proof.
    intros suffix C comp Hintf.
      by apply prefill_read_aux_invar with (suffix := suffix)
                                           (indexes := indexes_read_init)
                                           (res := prefill_read_aux C suffix [] indexes_read_init)
                                           (acc := []) in Hintf ;
        first destruct Hintf as [? [? H]] ; subst ; [by rewrite H cats0 revK | done].
  Qed.

  (* Since we only backtranslate, and we got a well-formed program if the events
     are well-formed, we can just assign any value transmitted in the load
     events (if it's a pointer or an undef, the event is not well-formed) *)
  Definition expr_assign_public (C:Component.id) (e:expr) :=
    match e with
    | E_assign (E_binop Add (E_local Block.pub)
                        (E_val (Int index)))
               (E_val  _ (* value *)) => in_bounds intf C index
    | _ => false
    end.

  Lemma prefill_read_aux_only_assign (C : Component.id) (comp : Component.interface) (suffix : trace):
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    all (expr_assign_public C) (prefill_read_aux C suffix [] indexes_read_init).
  Proof.
    intros (* Hwf_p *) Hwf_evs Hintf.
    (* translating to non-tail-recursive function *)
    have : prefill_read_aux_ntr C suffix indexes_read_init =
           rev (prefill_read_aux C suffix [] indexes_read_init) by apply (@prefill_read_aux_equiv suffix C comp Hintf).
    rewrite -[prefill_read_aux_ntr C suffix indexes_read_init]revK.
    move => Hequiv ; apply rev_inj in Hequiv.
    rewrite -Hequiv all_rev ; clear Hequiv.

    generalize dependent indexes_read_init.
    (* move => indexes ; elim:suffix => [|ev suffix] //=. *)
    generalize dependent C ; generalize dependent comp.
    induction suffix  as [| ev suffix IHsuffix ] => comp C Hintf indexes //.
    rewrite /prefill_read_aux_ntr/=.

    case: ev Hwf_evs => [ Ccur proc arg Cnext | Cret ret Cnext  | CSrc o v CTrg ] => //.
    move => /= /andP[] /andP[] /andP[] Hcomps_diff Htransf Hbounds Hsuffix.
    simplify_prefill_read_aux ; try by apply (@IHsuffix Hsuffix comp C Hintf indexes).
    (* bit dangerous since no control on naming of equations generated by
       simplify_prefill_read_aux *)
    move:Heqb => /eqP ? ; subst.
    apply/andP ; split => //.
      by apply (IHsuffix Hsuffix comp C Hintf (add_index indexes o)).
  Qed.



  Lemma prefill_read_aux_ntr_only_assign (C : Component.id) (comp : Component.interface) indexes (suffix : trace) :
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    all (expr_assign_public C) (prefill_read_aux_ntr C suffix indexes).
  Proof.
    intros Hwf_evs Hintf.
    (* 1st attempt with induction principle *)
    (* elim/prefill_read_aux_ntr_last_ind: *)
    (*   (prefill_read_aux_ntr C suffix indexes) => [| suffix' last_ev ] //. *)
    (* rewrite -cats1. rewrite /prefill_read_aux_ntr /=. case:suffix' Hsuffix' => //=. *)

    (* 2nd attempt *)
    (* elim/prefill_read_aux_ntr_ind:(prefill_read_aux_ntr C suffix indexes) => *)
    (* [| new_ev suffix' IHsuffix] //=. *)

    elim:suffix indexes Hwf_evs => [| new_ev suffix IHsuffix] indexes //.
    rewrite /prefill_read_aux_ntr/=.
    move => /= /andP[] Hwf_e Hsuffix.
    simplify_prefill_read_aux ; try by eapply IHsuffix.
    move:Heqb => /eqP ? ; subst.
    move:Hwf_e => /andP[_ ?]. apply/andP ; split ; first done.
      by apply (IHsuffix (add_index indexes o)).
  Qed.

  (* Should we use well_formed_event instead ? (We would need the program interface) *)
  (* Filters out non transferable values in load events, so it doesn't touches the others *)
  Definition only_transferable_values_in_ELoad (e:event) :=
    match e with
    | ELoad _ _ v _ => is_transferable_value v
    | _ => true
    end.

  Remark wf_event_implies_transf :
    subpred (well_formed_event intf) only_transferable_values_in_ELoad.
  Proof. move => ev ; by case:ev => [????|???|????] //= /andP[] /andP[] ???. Qed.

  (* This might be silly to not use well_formed_event instead of
     only_transferable since we have access to the program interface *)

  Lemma prefill_read_aux_only_values_integers (C : Component.id) (comp : Component.interface) (suffix : trace):
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    all only_transferable_values_in_ELoad suffix ->
    (* all (well_formed_event intf) suffix -> *)
    all values_are_integers (prefill_read_aux C suffix [] indexes_read_init).
  Proof.

    intros Hwf_evs Hintf Htransf_sfx.
    have Hassign: all (expr_assign_public C) (prefill_read_aux C suffix [] indexes_read_init)
       by apply (prefill_read_aux_only_assign Hwf_evs Hintf).
    (* would be nice to prove the goal almost directly from this *)

    (* In the meantime... *)
    (* translating to non-tail-recursive function *)
    have : prefill_read_aux_ntr C suffix indexes_read_init =
           rev (prefill_read_aux C suffix [] indexes_read_init ) by apply (@prefill_read_aux_equiv suffix C comp Hintf).
    rewrite -[prefill_read_aux_ntr C suffix indexes_read_init]revK.
    move => Hequiv ; apply rev_inj in Hequiv.
    rewrite -Hequiv all_rev ; rewrite -Hequiv in Hassign ; clear Hequiv.

    generalize dependent indexes_read_init.
    induction suffix as [| ev sfx IHsfx] => // indexes ;
      rewrite /prefill_read_aux_ntr/=.
    destruct ev as [ | | CSrc o v CTrg ] => //. rewrite -/prefill_read_aux_ntr.
    (* Load event *)
    (* Getting rid of the trivial cases *)
    case: (CTrg == C) => // ; case: (lookup_index indexes o) => // ;
        move: Htransf_sfx Hwf_evs => /= /andP[Htransf_v Htransf_sfx] /andP[Hwf_e Hwf_evs] ;
        try by apply (IHsfx Hwf_evs Htransf_sfx indexes).

    (* Case in which we produce an assignement and the indexes_map is updated *)
    set indexes_upd := add_index indexes o.
    move => Hassign ; apply /andP. split.

    move : Htransf_v ; rewrite /is_transferable_value. done.
    apply (IHsfx Hwf_evs Htransf_sfx indexes_upd).
       move: Hassign ; rewrite !all_rev /=. by move =>/andP[].
  Qed.

  Lemma prefill_read_aux_ntr_only_values_integers (suffix : trace) (C : Component.id) (comp : Component.interface) :
    (intf C = Some comp) ->
    all only_transferable_values_in_ELoad suffix ->
    (* all (well_formed_event intf) suffix -> *)
    all values_are_integers (prefill_read_aux_ntr C suffix indexes_read_init).
  Proof.
    intros Hintf Htransf_sfx.
    generalize dependent indexes_read_init ;
      induction suffix ; intro indexes ; first (by []).
    move:Htransf_sfx => /andP[Htransf_a Htransf_sfx] /=.
    (* apply IHsuffix in Htransf_sfx. *) rewrite /prefill_read_aux_ntr/=.
    simplify_prefill_read_aux ; try by apply (IHsuffix Htransf_sfx).
    simpl in Htransf_a. apply/andP ; split ; first now apply Htransf_a.
      by apply (IHsuffix Htransf_sfx).
  Qed.


  (** Gives Some expr that is the (sequence of) assignement(s) or None if it's
      not the case. *)
  Definition prefill_read (C: Component.id) (suffix: trace) : option expr :=
    (* Only used to accomodate with the fact that the interface is a map.
       None is never returned by this match, but can be returned by
       E_seq_of_list_expr on an empty list of expressions. *)
    match intf C with
    | Some _ => E_seq_of_list_expr (rev (prefill_read_aux
                                          C
                                          suffix
                                          []
                                          indexes_read_init))
    | None => None
    end.

  Fixpoint e_seq_right_assign_public (C:Component.id) (e:expr) : bool :=
    let exp_ass := (expr_assign_public C) in
    exp_ass e
    || match e with
      | E_seq e1 e2 =>
        exp_ass e1 && (e_seq_right_assign_public C) e2
      | _ => false
      end.

  Fixpoint e_seq_right_assign_public_prop (C:Component.id) (e:expr) :=
    let exp_ass := (expr_assign_public C) in
    exp_ass e
    \/ match e with
      | E_seq e1 e2 =>
        exp_ass e1 /\ (e_seq_right_assign_public_prop C) e2
      | _ => False
      end.

  Remark e_seq_subpred C :
    subpred (expr_assign_public C) (e_seq_right_assign_public C).
  Proof. move => e. case:e => // e_ptr e_val (* => /eqP/eqP *). by rewrite /= orbF.
  Qed.

  Lemma prefill_read_only_seq_assign (C : Component.id) (comp : Component.interface) (expr_seq : expr) (suffix : trace) :
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    prefill_read C suffix = Some expr_seq ->
    e_seq_right_assign_public C expr_seq.
  Proof.
    rewrite /prefill_read.
    move => Hwf_evs Hcomp ; rewrite Hcomp.
    have: prefill_read_aux_ntr C suffix indexes_read_init =
          rev (prefill_read_aux C suffix [::] indexes_read_init)
      by apply prefill_read_aux_equiv with (comp:=comp), Hcomp.
    move => <- .
    set prefill := prefill_read_aux_ntr C suffix indexes_read_init.
    have: all (expr_assign_public C) prefill by
        rewrite /prefill ; rewrite -> prefill_read_aux_equiv with (comp:=comp) => // ;
      rewrite all_rev ; apply prefill_read_aux_only_assign with (comp:=comp), Hcomp.
    generalize dependent expr_seq.
    rewrite/E_seq_of_list_expr/E_seq_of_exprs_right.
    case: prefill (* eqn:pref *)  => //= e prefill.
    elim: prefill e => //= e.
    - move => expr_seq /andP[Hass_e _] Hsome ;
               inversion Hsome as [H] ; subst ; clear Hsome.
      destruct expr_seq eqn:Hexpr_seq => //=. rewrite/e_seq_right_assign_public ;
       by rewrite orbF.
    - move => prefill IH a expr_seq /andP[Hass_a] /andP[Hass_e Hass_prefill] Hsome ;
               inversion Hsome as [H] ; subst ; clear Hsome => /=.
      apply /andP ; split ; first done.
      by apply IH with (e := e) ; first by apply /andP.
  Qed.

  Lemma prefill_read_only_values_integers (C : Component.id) (comp : Component.interface) (e:expr) (suffix : trace) :
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    prefill_read C suffix = Some e ->
    values_are_integers e.
  Proof.
    rewrite /prefill_read. move => Hwf Hcomp ; rewrite Hcomp.
    have Honly: all only_transferable_values_in_ELoad suffix
      by apply (sub_all wf_event_implies_transf Hwf).
    have: all values_are_integers (rev' (prefill_read_aux C suffix [::] indexes_read_init)).
       apply (@prefill_read_aux_only_values_integers C comp)
      in Honly => // ; by rewrite all_rev.
    by apply E_seq_of_list_expr_integers.
  Qed.

  Remark expr_assign_public_implies_e_seq_right_assign_public C:
    subpred (expr_assign_public C) (e_seq_right_assign_public C).
  Proof.
    by case => //= ?? ; rewrite orbF.
  Qed.

  Lemma prefill_read_no_calls (C : Component.id) (comp : Component.interface) (e:expr) (suffix : trace):
    all (well_formed_event intf) suffix ->
    (intf C = Some comp) ->
    prefill_read C suffix = Some e ->
    called_procedures e = fset0.
  Proof.
    move => Hwf Hcomp Hpref.
    have: (e_seq_right_assign_public C) e by apply (prefill_read_only_seq_assign Hwf Hcomp Hpref).
    elim: e {Hpref} => // e IH_e e_seq IH_e_seq ; first last.
    - (* Attempt to avoid the case analysis *)
      (* move: IH_e IH_e_seq ; rewrite /e_seq_right_assign_public orbF. *)
      (* simpl in H. *)

      (* Silly case analysis; to refactor or replace *)
      rewrite /e_seq_right_assign_public orbF. (* simpl. move => <-. *) case: e {IH_e IH_e_seq} => // bin_add e_loc e_index.
      case: bin_add => //. case: e_loc => // bk_pub.
      case: bk_pub => //. case:e_index => // val_int.
      case: val_int => // i.
      case: e_seq => // val. case: val => // [z|t|] /= ; by rewrite !fset0U.
    - (* Real part of the induction *)
      move => /andP[Hass_e Hass_seq_right].
      rewrite -/e_seq_right_assign_public in Hass_seq_right.
      apply IH_e_seq in Hass_seq_right. rewrite /= Hass_seq_right fsetU0.
      case: e IH_e Hass_e => //= e_ass e_val. by rewrite orbF.
  Qed.

  (** We use [switch] to define the following function [expr_of_trace], which
      converts a sequence of events to an expression that produces that sequence
      of events when run from the appropriate component. We assume that all
      events were produced from the same component, or reach the memory of this
      component in case of a load event. The [C] and [P] arguments are only
      needed to generate the recursive calls depicted above. *)

  (** Recreates the fitting expression for triggering an event.

      In the case we give turn to the component we're recreating (if it is
      called/ returned to), goes forward in the trace to make sure the
      subsequent ELoad would be successful. *)
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (suffix: trace) : option expr :=
    match suffix with
    | nil => None
    | ECall _ P' arg C' :: suffix' =>
      let call_trigger := E_seq (E_call C' P' (E_val (Int arg)))
                                (E_call C  P  (E_val (Int 0))) in
      match (prefill_read C suffix') with
      | None => Some call_trigger
      | Some prefill => Some (E_seq prefill call_trigger)
      end
    | ERet _ ret_val _ :: suffix' =>
      let return_trigger := E_val (Int ret_val) in
      match prefill_read C suffix' with
      | None => Some return_trigger
      | Some prefill => Some (E_seq prefill return_trigger)
      end
    | ELoad C' off _ C'' :: suffix' =>
      (* In case of load performed by the current component *)
      if C == C' then
        Some (E_deref (E_binop Add (E_component_buf C'') (E_val (Int off))))
      else
        (* In the case the memory from the current component is loaded, we don't
           do anything here (this kind of event is used in prefill_read) *)
        None
    end.

  Definition expr_of_trace (C: Component.id) (P: Procedure.id) (t: trace) : expr :=
    switch (pmap (expr_of_event C P) (suffixes_of_seq t)) E_exit.

  (** To compile a complete trace mixing events from different components, we
      split it into individual traces for each component and apply
      [expr_of_trace] to each one of them.  We also initialize the memory of
      each component to hold 0 at the first local variable. *)

  Definition filter_comp_subtrace (C: Component.id) (ev:event) :=
    (C == cur_comp_of_event ev)
    || match ev with
      | ELoad _ _ _ C' => (C == C')
      | _ => false
      end.
  Hint Transparent filter_comp_subtrace.

  Definition comp_subtrace (C: Component.id) (t: trace) :=
    filter (filter_comp_subtrace C) t.

  Lemma expr_of_event_cases C P suf ev :
    C == cur_comp_of_event ev ->
    exists exp, expr_of_event C P (ev::suf) = Some exp.
  Proof.
    intros. subst. case: ev H => [????|??? |??? Cown] /=; last by move => -> ; eexists.
    all : case: (prefill_read _ _ ) => [exp_trig|] ; by eexists.
  Qed.

  Remark subseq_comp_subtrace C t : subseq (comp_subtrace C t) t.
  Proof. by apply filter_subseq. Qed.

  Lemma length_comp_subtrace C P t : length (pmap (expr_of_event C P) (suffixes_of_seq (comp_subtrace C t))) =
                                   length (filter (fun ev => ( C == cur_comp_of_event ev)) t).
  Proof.
    rewrite /comp_subtrace/filter_comp_subtrace. rewrite -!size_length size_pmap.
    elim: t => //= ev t IHt.
    case: ev => /= [????|??? |??? Cown] ; destruct (C == _) eqn:Ceq => //= ;
        try (rewrite suffixes_of_seq_cons /= IHt -ssrnat.add1n ; apply/eqP ; rewrite ssrnat.eqn_add2r ;
             case: (prefill_read _ _) => // ; by rewrite Ceq).
    destruct (C == Cown) eqn:Ceq' ; last by rewrite IHt.
    by rewrite suffixes_of_seq_cons /= IHt Ceq.
  Qed.

  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply: filter_cat. Qed.

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

  Definition public_buffer_of_trace C Cintf t: (* mapm *) seq (Block.offset * value) :=
    let rel_indexes := (fun (p1:(Z*_)) (p2:(Z*_)) => Z.leb (fst p1) (fst p2)) in
    let loaded_values := sort rel_indexes
                           (values_read_of_trace
                                   C (comp_subtrace C t) [::] indexes_read_init) in
    let buffer_size := Component.public_buffer_size Cintf in
    let values := (repeat Undef buffer_size) in
    let indexes := map Z.of_nat (iota 0 buffer_size) in
    (* let pub_buffer := mkfmapf (fun _ => Undef) indexes in *)
    let pub_buffer := zip indexes values in

(*   set_nth x0 s i y == s where item i has been changed to y; if s does not  *)
(*                       have an item i, it is first padded with copies of x0 *)
(*                       to size i+1.                                         *)

  (* foldr (fun kv m => setm m kv.1 kv.2) pub_buffer loaded_values *)
    foldr (fun kv m => set_nth (kv.1(* don't really know how to put right indexes but it doesn't matter since the default isn't supposed to be used *),
                             Undef) m (Z.to_nat kv.1) kv) pub_buffer loaded_values
  .

  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapim (fun Cid Cintf => (
                                     (* public buffer *)
                                     inr (unzip2 (public_buffer_of_trace Cid Cintf t)),
                                     (* private buffer *)
                                     inr [Int 0])) intf |}.

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
      have Hwf_sbt: all (well_formed_event intf) (comp_subtrace C t)
        by apply (all_subseq Ht (subseq_comp_subtrace C t)).
      rewrite /find_procedure /procedures_of_trace mapimE.
      case intf_C: (intf C)=> [CI|] //=.
      rewrite mkfmapfE; case: ifP=> //= P_CI [<-] {Pexpr}; split; last first.
      + (* values_are_integers *)
        rewrite /procedure_of_trace /expr_of_trace /switch.
        (* Btw, would it be simpler to do induction by appending an event at the
           end (with last_ind)? *)
        elim: {t Ht} (comp_subtrace C t) (length _) Hwf_sbt => [| e t IH] //= n /andP [_ Ht].
        have Hpref: forall expr, prefill_read C t = Some expr ->
                            values_are_integers expr
            by move => ? ; apply (prefill_read_only_values_integers Ht intf_C) ;
                        apply (sub_all wf_event_implies_transf Ht).
        move: IH ; rewrite !suffixes_of_seq_equiv => IH.
        specialize (IH n Ht).
        case: e => /= [ C' p arg ? | C' ret ? | Cderef off ? Cown] ;
          case: (prefill_read C t) Hpref => /= [ex|] Hpref ;
            try (apply/andP ; split ; first by (rewrite andbT ; apply Hpref)) ;
            try done.
        all : by case:(C==_).
      + (* Valid calls *)
        pose call_of_event e := if e is ECall _ P _ C then Some (C, P) else None.
        have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (comp_subtrace C t))).
        { rewrite /procedure_of_trace /expr_of_trace /switch suffixes_of_seq_equiv.
          elim: {t Ht} (comp_subtrace C t) (length _) Hwf_sbt => [|e t IH] /= n Ht ;
              first exact: fsub0set.
          move:Ht => /andP[_ Ht].
          have Hpref: forall expr, prefill_read C t = Some expr ->
                              called_procedures expr = fset0
              by move => ? ; apply (prefill_read_no_calls Ht intf_C).
          specialize (IH n Ht).
          case: e => [C' P' arg C''| C' ret C'' | C' i v C''] ;
                      last by (case: (C== _) => /= ; first rewrite !fset0U).
          all: case: (prefill_read C t) Hpref => [ex|] Hpref //= ;
                                                  first (rewrite (Hpref ex); last done);
                                                  rewrite !fset0U => //.
          all: rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=.
          all: by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT.
        }
        (* Back to Valid calls *)
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
      elim: {P P_CI} t Ht {Hwf_sbt} P' C'_P' => [|e t IH] //= /andP [He Ht] P. rewrite /filter_comp_subtrace.
      case: (C =P _) => [HC|].
      case: e HC He=> [_ P' v C'' /= <-| |]; try by eauto.
      rewrite inE; case/andP=> [C_C'' /imported_procedure_iff imp_C''_P'].
      by case/orP=> [/eqP [-> ->] //|]; eauto.
      case: e He => [ ? ? ? ? | ? ? ? | ? ? ? ?] ; try by eauto.
      move => /andP => [[? ?]] ;
      case: (_==_) ; by eauto.
    - (* by rewrite domm_map. *) admit.
    - split; first last.
      (* Required local buffers *)
      move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      rewrite /has_required_local_buffers /= (* mapmE C_CI /= *).
      (* eexists; eauto=> /=; omega. *)
      (* (* valid_buffers *) *)
      (* rewrite/valid_buffers/program_of_trace -eq_fmap /= => Cid ; rewrite !mapmE. *)
      (*   by case: (intf Cid) => //. *)
      + admit.
      + admit.
    - rewrite /prog_main find_procedures_of_trace //=.
      + split; first reflexivity.
        intros _.
        destruct (intf Component.main) as [mainP |] eqn:Hcase.
        * apply /dommP. exists mainP. assumption.
        * discriminate.
      + by left.
  Admitted.

  Lemma closed_program_of_trace t :
    Source.closed_program (program_of_trace t).
  Proof.
    split=> //=; by rewrite /prog_main find_procedures_of_trace_main.
  Qed.

  Arguments Memory.load  : simpl nomatch.
  Arguments Memory.store : simpl nomatch.

  Section WithTrace.

    Variable t : trace.

    Let p    := program_of_trace t.
    Let init := prepare_buffers p.

    Local Definition component_buffer C := C \in domm intf.

    Lemma valid_procedure_has_block C P :
      valid_procedure C P ->
      component_buffer C.
    Proof.
      case=> [[-> _ {C P}]|[CI]]; rewrite /component_buffer /=.
        by rewrite mem_domm.
      rewrite /Program.has_component /Component.is_exporting /=.
      by rewrite mem_domm; case=> ->.
    Qed.

    (** equals to the number of events triggered by the component at this point
     *)
    Local Definition counter_value C prefix :=
      Z.of_nat (length (filter (fun ev => C == cur_comp_of_event ev) prefix)).

    Definition well_formed_memory (prefix: trace) (mem: Memory.t) : Prop :=
      forall C,
        component_buffer C ->
        Memory.load mem (C, Block.private, counter_idx) = Some (Int (counter_value C prefix)).

    (* star_refl is trivial but never used, so go for plus *)
    Lemma well_formed_memory_plus prefix s1 s2 :
      Plus (CS.sem p) s1 E0 s2 -> (* could be any trace really since we just look at wf_mem wrt to prefix *)
      well_formed_memory prefix (CS.s_memory s1) ->
      well_formed_memory prefix (CS.s_memory s2).
    Proof.
      intros Hplus wf_mem1.
      (* we just have to relate memory between to exec points of a program *)
      (* Since we cannot de-allocate, this should be simple. When de-allocation
         would be possible, we'll have to rule out this kind of step in the Plus
         hypothesis *)

    Admitted.

    Lemma counter_value_snoc prefix C e :
      counter_value C (prefix ++ [e])
      = (counter_value C prefix
         + if C == cur_comp_of_event e
           then 1 else 0) % Z.
    Proof.
      rewrite /counter_value.
      rewrite filter_cat app_length. simpl.
      rewrite Nat2Z.inj_add.
      now destruct (_ == _) ; destruct e as [| |? ? ? C' ]=> //= ; case: (_ == _) => //.
    Qed.

    Lemma well_formed_memory_store_counter prefix mem C e :
      component_buffer C ->
      well_formed_memory prefix mem ->
      C = cur_comp_of_event e ->
      exists mem',
        Memory.store mem (C, Block.private, counter_idx)
                     (Int (counter_value C (prefix ++ [e]))) = Some mem' /\
        well_formed_memory (prefix ++ [e]) mem'.
    Proof.
      move=> C_b wf_mem HC.
      have C_local := wf_mem _ C_b.
      have [mem' Hmem'] := Memory.store_after_load
                             _ _ _ (Int (counter_value C (prefix ++ [e])))
                             C_local.

      exists mem'. split; trivial => C' C'_b.
      have C'_local := wf_mem _ C'_b.
      move:Hmem' ;
        rewrite !counter_value_snoc -!HC => Hmem'.
      rewrite -> Nat.eqb_refl in Hmem'.
      case: (altP (C' =P C)) => [?|C_neq_C'].
      - subst C'.
        by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem').
      - have neq : (C, Block.private, counter_idx) <> (C', Block.private, counter_idx)
          by move/eqP in C_neq_C'; congruence.
        rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem').
        case: e HC => [????|???|??? Cown] HC; last case:(C'==Cown) => // ;
        rewrite Z.add_0_r ; assumption.
    Qed.

    CoInductive well_formed_state (s: stack_state) (prefix suffix: trace) : CS.state -> Prop :=
    | WellFormedState C stk mem k exp arg P
      of C = cur_comp s
      &  k = Kstop
      &  exp = procedure_of_trace C P t
      &  well_bracketed_trace s suffix
      &  all (well_formed_event intf) suffix
      &  well_formed_stack s stk
      &  well_formed_memory prefix mem
      &  valid_procedure C P
      :  well_formed_state s prefix suffix [CState C, stk, mem, k, exp, arg].

    (* Maybe polish a bit the definition of the lemma to have more implicit arguments : *)
    (* Arguments C, comp, sub_suffix, exp_prefill are implicit *)
    (* stk, mem, c, e and arg are not (cannot be inferred thanks to the hypothesis) *)
    Lemma reachable_state_from_prefill (* s0 *) (* main_expr t0 t1 *) C comp stk mem c sub_suffix exp_prefill e arg :
      (* First two : Maybe overkill for saying it comes from an initial state *)
      (* CS.initial_state p [CState Component.main, [::], init, Kstop, main_expr, Int 0] -> *)
      (* Star (CS.sem p) [CState Component.main, [::], init, Kstop, main_expr, Int 0] t0 [CState C, stk, mem, c, E_seq exp_prefill e, arg] -> *)
      (* Maybe useless *)
      (* subseq sub_suffix t1 -> *)
      (* Surely useless *)
      (* t = t0 ** t1 -> *)

      all (well_formed_event intf) sub_suffix ->
      intf C = Some comp ->
      prefill_read C sub_suffix = Some exp_prefill ->
      exists mem', Plus (CS.sem p)
                   [CState C, stk, mem,  c, E_seq exp_prefill e, arg] [::]
                   [CState C, stk, mem', c, e, arg].
    Proof.
      intros (* Hinit Hstar_init Hsub_suf Ht *) Hwf Hintf Hprefill.

      (* unfold CS.initial_state, CS.initial_machine_state, prog_main in Hinit. *)
      (* move: Hinit. *)
      (* destruct (find_procedure (prog_procedures p) Component.main Procedure.main) => //. *)

      have: (e_seq_right_assign_public C) exp_prefill
        by apply (@prefill_read_only_seq_assign C comp exp_prefill sub_suffix Hwf Hintf Hprefill).
      move {Hprefill}.
      move: mem c e (* Hstar_init *).
      elim: exp_prefill => //.
      - (* Sequence of assignements *)
        move => e1 IHe1 e2 IHe2 mem c e (* Hstar_init *).
        move => /andP[He1 He2].
        (* useful evidence from IHe1 *)
        apply expr_assign_public_implies_e_seq_right_assign_public in He1.
        apply (IHe1 mem (Kseq e c) e2) in He1. destruct He1 as [mem1 Hplus1].
        (* useful evidence from IHe2 *)
        apply (IHe2 mem1 c e) in He2.
        destruct He2 as [mem' Hplus2].
        (* going from (E_seq e2 e) in hypothesis to e2 with right continuation  *)
        inversion Hplus2 as [? ? ? t2 ? ? Hstep Hstar Htrace] ; subst.
        inversion Hstep ; subst.
        destruct t2 ; last done.

        eexists.
        (* Seq1 step *)
        eapply plus_left' with (t1:=E0) ; last by [].
        now apply CS.KS_Seq1.
        (* e1 steps *)
        eapply plus_star_trans with (t1:=E0) ; last by [].
        now apply Hplus1.
        (* e2 steps *)
        apply Hstar.
      - (* single assignment *)
        move => e_ass _ e_val _ mem c e. (* induction is useless here *)
        simpl. rewrite orbF.
        case: e_ass => // bin_add e_loc e_index.
        case: bin_add => //. case: e_loc => // bk_pub.
        case: bk_pub => //. case:e_index => // val_int.
        case: val_int => // i.
        case: e_val => // v Hin_bounds.
        (* Need to prove that the assignments are correct before *)
        eexists.
        (* Take steps until final assignment step *)
        do 7 (eapply plus_left' with (t1:=E0) ; last by [] ; first now constructor).
        eapply plus_left' with (t1:=E0) ; last by [].
        econstructor => //.
        rewrite /Memory.store/=.

        (* add a link between mem and init so that (mem C) gives Some memory *)
        admit.
    Admitted.

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
        case: cs / => /= _ stk mem _ _ arg P -> -> -> _ _ wf_stk wf_mem P_exp.
        exists [CState C, stk, mem, Kstop, E_exit, arg]; last by left.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := wf_mem _ C_b.
        rewrite /procedure_of_trace /expr_of_trace.
        apply: switch_spec_else; eauto.
        by rewrite length_comp_subtrace.
      - move=> cs Et /=.
        case: cs / => /= _ stk mem _ _ arg P -> -> -> /andP [/eqP wf_C wb_suffix] /andP [wf_e wf_suffix] wf_stk wf_mem P_exp.
        have C_b := valid_procedure_has_block P_exp.
        have C_local := wf_mem _ C_b.
        destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']].
        (* Maybe we can eliminate the None case of expr_of_event since wf_e,
           wf_C and the fact that expr_of_event _ _ _ = None are in contradiction
           in this case *)
        (* Indeed, when expr_of_event C _ _ = None, then the current event
           backtranslated is an ELoad Cderef _ _ Cown such that Cderef != Cown ;
           (cur_comp_of_event Cderef) and (C = Cown), so we get  *)
        inversion wf_e as [wf_e']. unfold well_formed_event in wf_e'.
        inversion wf_C as [wf_C']. unfold cur_comp_of_event in wf_C'.
        assert (Star1 : match expr_of_event C P (e::comp_subtrace C suffix) with
                        | Some exp =>
                          Star (CS.sem p)
                             [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                             [CState C, stk, mem', Kstop, exp, arg]
                        | None =>
                          (* Star on the suffix ? Don't exactly know what to do in the None case *)
                          Star (CS.sem p)
                             [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                             [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t (* suffix ? *) ), arg]
                             end
               ).
        { destruct (expr_of_event C P (e::comp_subtrace C suffix)) as [exp_produced|] eqn:some_expr_of_event ;
            last by constructor.
          unfold expr_of_trace.
          have: length (pmap (expr_of_event C P) (suffixes_of_seq (comp_subtrace C t))) =
                                length [seq ev <- t | C == cur_comp_of_event ev]
            by rewrite length_comp_subtrace. unfold counter_value in C_local.
          rewrite !Et comp_subtrace_app /=.
          unfold filter_comp_subtrace.
          rewrite <- wf_C, Nat.eqb_refl, suffixes_of_seq_cat, pmap_cat ; simpl.
          rewrite suffixes_of_seq_cons. rewrite pmap_cons. rewrite some_expr_of_event. move => /= length_comp_sbt.
          assert (H := @switch_spec p C  stk mem
                                    (pmap (expr_of_event C P)
                                          [seq x ++ e :: comp_subtrace C suffix
                                        | x <- suffixes_of_seq (comp_subtrace C prefix)]
                                    )
                                    exp_produced
                                    (* formerly *)
                                    (* (expr_of_event C P e) *)

                                    (pmap (expr_of_event C P)
                                          (suffixes_of_seq (comp_subtrace C suffix))
                                    )
                                    E_exit arg).

          have Hprefix_length: Memory.load mem (C, Block.private, counter_idx) =
                Some (Int (Z.of_nat (length (pmap (expr_of_event C P) [seq x ++ e :: comp_subtrace C suffix | x <- suffixes_of_seq (comp_subtrace C prefix)])))).
          move: length_comp_sbt. rewrite C_local.

          (* getting rid of length of the suffix *)
          (* To clean up, there's a lot of going back and forth between size<->length *)
          rewrite -!size_length !size_filter count_cat /=. move: wf_C => /eqP -> /=.
          rewrite !size_cat ssrnat.add1n.
          rewrite !size_length /=.
          rewrite !length_comp_subtrace. rewrite -!size_filter !size_length. move=> /eqP. rewrite ssrnat.eqn_add2r. move => /eqP ->. done.
          (* to clean up *)
          rewrite Hprefix_length in C_local. inversion C_local as [H'].

          specialize (H Hprefix_length).
          destruct H as [mem'' [Hmem'' Hstar]].
          enough (H : mem'' = mem') by (subst mem''; easy).
          rewrite -> counter_value_snoc, <- wf_C, Nat.eqb_refl in Hmem'.
          rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''. rewrite H' in Hmem''.
          rewrite Hmem' in Hmem''.
          congruence. }
        assert (Star2 :
                   match expr_of_event C P (e::comp_subtrace C suffix) with
                   | Some exp =>
                     exists s' cs',
                     Star (CS.sem p) [CState C, stk, mem', Kstop, exp, arg] [:: e] cs' /\
                     well_formed_state s' (prefix ++ [e]) suffix cs'
                   (* Still the useless case *)
                   | None =>
                     Star (CS.sem p)
                          [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0
                          [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg]
                   end).
        {
          destruct (expr_of_event C P (e::comp_subtrace C suffix)) as [exp_produced|] eqn:some_expr_of_event ;
            last by constructor.
          clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem.
          destruct e as [C_ P' new_arg C'|C_ ret_val C'| C_ o loaded_val C'];
          simpl in wf_C, wf_e, wb_suffix; subst C_.
          - (* ECall *)
            case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport.
            exists (StackState C' (C :: callers)).
            have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)).
            (* Added boilerplate to treat prefill expressions *)
            simpl in some_expr_of_event.
            move: some_expr_of_event ;
              destruct (prefill_read _ _) as [exp_prefill|] eqn:prefill'
            => some_expr_of_event ; inversion some_expr_of_event as [exp_of_event] ; first last.
            + (* Case with simple "1 event -> 1 expression" back-translation *)
              exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem,
                 Kstop, procedure_of_trace C' P' t, Int new_arg].
              split.
              * (* star to a reachable state *)
                take_step. take_step.
                apply star_one. simpl.
                apply CS.eval_kstep_sound. simpl.
                rewrite (negbTE C_ne_C').
                rewrite -> imported_procedure_iff in Himport. rewrite Himport.
                rewrite <- imported_procedure_iff in Himport.
                  by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
              * (* well_formed reachable state *)
                econstructor; trivial.
                { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                  eexists []; eexists; simpl; split; eauto.
                  split; trivial.
                  eexists arg, P, top, bot.
                    by do 3 (split; trivial). }
                right. by apply: (closed_intf Himport).
            + (* Case with prefill *)
              (* Get the memory before instantiating cs' *)
              have [mem' Hplus]: exists mem',
                Plus (CS.sem p)
                     [CState C, stk, mem, Kstop, E_seq exp_prefill (E_seq (E_call C' P' (E_val (Int new_arg))) (E_call C P (E_val (Int 0)))), arg] [::]
                     [CState C, stk, mem', Kstop, (E_seq (E_call C' P' (E_val (Int new_arg))) (E_call C P (E_val (Int 0)))), arg].
              {
                inversion Himport as [Cintf [hasCintf _]]. unfold Program.has_component in hasCintf.
                apply reachable_state_from_prefill with
                    (comp:=Cintf)
                    (sub_suffix:= (comp_subtrace C suffix)) => //.
                apply (all_subseq wf_suffix (subseq_comp_subtrace C suffix)).
              }
              (* TODO refactor, same as simple case *)
              exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem', (* mem is altered by the assignments in the prefill *)
                       Kstop, procedure_of_trace C' P' t, Int new_arg].
              split.
              * (* star to a reachable state *)
                eapply star_trans with (t1 := E0)
                                       (s2 :=  [CState C, stk, mem', Kstop, (E_seq (E_call C' P' (E_val (Int new_arg))) (E_call C P (E_val (Int 0)))), arg]) ; first last.
                  by rewrite E0_left.
                ** take_step. take_step.
                   apply star_one. simpl.
                   apply CS.eval_kstep_sound. simpl.
                   rewrite (negbTE C_ne_C').
                   rewrite -> imported_procedure_iff in Himport. rewrite Himport.
                   rewrite <- imported_procedure_iff in Himport.
                     by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)).
                ** apply (plus_star Hplus).
              * (* well_formed reachable state *)
                econstructor; trivial ; last by right; apply: (closed_intf Himport).
                { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk.
                  eexists []; eexists; simpl; split; eauto.
                  split; trivial.
                  eexists arg, P, top, bot.
                    by do 3 (split; trivial).
                }
                by eapply (well_formed_memory_plus Hplus).
          - (* ERet *)
            move: wf_e=> /eqP C_ne_C'.
            destruct callers as [|C'_ callers]; try easy.
            case/andP: wb_suffix=> [/eqP HC' wb_suffix].
            subst C'_. simpl. exists (StackState C' callers).
            destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot.
            revert mem wf_mem arg.
            (* Get back the fact that intf C = bla *)
            have [Cintf hasCintf] : exists Cintf, intf C = Some Cintf.
            {
              rewrite /valid_procedure in P_exp.
              destruct P_exp as [[HCmain HPmain] | [Cintf [hasCintf _]] ] ;
                first last.
              - by rewrite /Program.has_component in hasCintf ; exists Cintf.
              - move: has_main. rewrite -mem_domm => /dommP [Cintf hasCintf].
                rewrite -> HCmain in *.
                by rewrite /Program.has_component in hasCintf ; exists Cintf.
            }
              inversion some_expr_of_event as [exp_of_event].
              destruct (prefill_read _ _) as [exp_prefill|] eqn:prefill ;
                first last ; inversion_clear exp_of_event.
            + (* straightforward case *)
              induction top as [|[C_ saved k_] top IHtop].
              * clear Htop. rename bot into bot'.
                destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
                subst bot'. simpl.
                have C'_b := valid_procedure_has_block P'_exp.
                intros mem wf_mem.
                exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0].
                split.
                -- eapply star_step.
                   ++ now eapply CS.KS_ExternalReturn; eauto.
                   ++ take_step. take_step; eauto.
                      apply star_one. apply CS.eval_kstep_sound.
                        by rewrite /= eqxx (find_procedures_of_trace t P'_exp).
                   ++ now rewrite E0_right.
                -- econstructor; trivial.
                   exists (CS.Frame C' saved Kstop :: top), bot. simpl. eauto.
              * intros mem wf_mem arg.
                simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
                specialize (IHtop Htop).
                specialize (IHtop _ wf_mem saved). destruct IHtop as [cs' [StarRet wf_cs']].
                exists cs'. split; trivial.
                eapply star_step; try eassumption.
                -- by apply/CS.eval_kstep_sound; rewrite /= eqxx.
                -- reflexivity.
            + (* case with prefill *)

              (* We do some forward reasoning to have the fact that we can go
                 from the 'initial' state to a state where the exp_prefill has
                 been processed, and then from here to the final state (to still
                 have the existential in the goal and to reason by induction on
                 the top of the stack) *)

              intros mem Hwf_mem arg.
                have:
                  forall stack, exists mem',
                    Plus (CS.sem p)
                         [CState C, stack, mem, Kstop, E_seq exp_prefill (E_val (Int ret_val)), arg] [::]
                         [CState C, stack, mem', Kstop, E_val (Int ret_val), arg]
                    by (move => stack; eapply (reachable_state_from_prefill _ _ _ _ _ (all_subseq wf_suffix (subseq_comp_subtrace C suffix))) ; eassumption).
                move: mem Hwf_mem arg.

                have Hstar_ret:
                  forall mem : Memory.t,
                    well_formed_memory (prefix ++ [:: ERet C ret_val C']) mem ->
                    forall arg, exists cs' : CS.state,
                      star CS.kstep (prepare_global_env p) [CState C, top ++ bot, mem, Kstop, E_val (Int ret_val), arg] [:: ERet C ret_val C'] cs' /\
                      well_formed_state {| cur_comp := C'; callers := callers |} (prefix ++ [:: ERet C ret_val C']) suffix cs'.
                {
                  (* TODO refactor, exact same proof as straightforward case *)
                  induction top as [|[C_ saved k_] top IHtop].
                  - clear Htop. rename bot into bot'.
                    destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot).
                    subst bot'. simpl.
                    have C'_b := valid_procedure_has_block P'_exp.
                    intros mem wf_mem.
                    exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0].
                    split.
                    + eapply star_step.
                      * now eapply CS.KS_ExternalReturn; eauto.
                      * take_step. take_step; eauto.
                        apply star_one. apply CS.eval_kstep_sound.
                          by rewrite /= eqxx (find_procedures_of_trace t P'_exp).
                      * now rewrite E0_right.
                    + econstructor; trivial.
                      exists (CS.Frame C' saved Kstop :: top), bot. simpl. eauto.
                  - intros mem wf_mem arg.
                    simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_.
                    specialize (IHtop Htop).
                    specialize (IHtop _ wf_mem saved). destruct IHtop as [cs' [StarRet wf_cs']].
                    exists cs'. split; trivial.
                    eapply star_step; try eassumption.
                    + by apply/CS.eval_kstep_sound; rewrite /= eqxx.
                    + reflexivity.
                }
                move => mem Hwf_mem arg Hplus_prefill.
                destruct (Hplus_prefill (top++bot)) as [mem' Hplus].
                have Hwf_mem': well_formed_memory (prefix ++ [:: ERet C ret_val C']) mem' by eapply (well_formed_memory_plus Hplus).
                destruct (Hstar_ret mem' Hwf_mem' arg) as [cs' [Hstar Hstate]].
                exists cs'; split ; last assumption.
                eapply plus_star, plus_star_trans ; try eassumption.
                by rewrite E0_left.
          - (* ELoad *)
            move: wf_e => /andP[]/andP[].
            simpl in some_expr_of_event.
            rewrite eq_refl in some_expr_of_event.
            inversion_clear some_expr_of_event.
            (* Stack state should be the same *)
            move => /eqP CC' Htransf_val Hin_bounds.
            exists (CS.stack_state_of ([CState C, stk, mem, Kstop, E_deref (E_binop Add (E_component_buf C') (E_val (Int o))), arg])).
            (* the final state should just be the result of the dereferenced value *)
            exists [CState C, stk, mem, Kstop, E_val loaded_val, arg].
            split.
            + do 5 take_step.
              (* If done automatically via take_step, the rule CS.KS_DerefEval is chosen
                 instead of CS.KS_DerefComponentEval *)
              (* Should we have another continuation for dereferencing a foreign
                 pointer ? Since e is not evaluated at the point where we create
                 the continuation, I guess it's not possible *)
              eapply star_one, CS.KS_DerefComponentEval => //.
              rewrite /Memory.load. move: Htransf_val Hin_bounds. rewrite /is_transferable_value/in_bounds. simpl.
              (* rewrite /ComponentMemory.load. *)

              (* Still, what is left is to exhibit the link between the memory and the definition of the program (interface, buffers) *)
              admit.
            + simpl.
              admit.
        }
        destruct (expr_of_event _ _ _) as [exp|] eqn:expr_event.
        + destruct Star2 as (s' & cs' & Star2 & wf_cs').
          specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH.
          specialize (IH Et wf_cs'). destruct IH as [cs'' Star3 final].
          exists cs''; trivial. rewrite -wf_C.
          eapply (star_trans Star1); simpl; eauto.
          now eapply (star_trans Star2); simpl; eauto.
        + move:expr_event. rewrite/expr_of_event/=.
          destruct e ; last (by rewrite wf_C' ifT) ; by case: (prefill_read _ _).
    Admitted.
    (* Qed. *)

    Lemma definability :
      well_formed_trace intf t ->
      program_behaves (CS.sem p) (Terminates t).
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
      (* by rewrite ComponentMemory.load_prealloc /=. *)
      admit.
    Admitted.

End WithTrace.
End Definability.

Require Import Intermediate.CS.
Require Import Intermediate.Machine.
Require Import S2I.Definitions.

(* FG : Put back some sanity checks ? some are present but commented in the premise and the move => *)
Lemma matching_mains_backtranslated_program p c intf back m:
  Intermediate.well_formed_program p ->
  Intermediate.well_formed_program c ->
  (* intf = unionm (Intermediate.prog_interface p) (Intermediate.prog_interface c) -> *)
  back = program_of_trace intf m ->
  intf Component.main ->
  (* well_formed_trace intf m -> *)
  matching_mains (program_unlink (domm (Intermediate.prog_interface p)) back) p.
Proof.
  move => wf_p wf_c (* intf' *) Hback intf_main (* wf_back *).
  unfold matching_mains.
  split.
  - (* -> *) (* maybe can be done with more finesse *)
    unfold prog_main. unfold program_unlink. rewrite Hback. simpl. rewrite find_procedure_filter_comp.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hmain_comp ; rewrite Hmain_comp.
    + (* contra *)
      rewrite (find_procedures_of_trace_main intf_main). intro contra. inversion contra.
    + (*  *)
      intro Htauto ; clear Htauto.
      (* either contra or trivial case *)
      destruct (Intermediate.prog_main p) as [ id | ] eqn: Hmain_prog; first exfalso ; last by [].
      (* contra : Component.main is not in interface of p but is in its procedures *)
      (* contradiction with wfprog_defined_procedures (Intermediate.well_formed_program p)  *)
      apply (Intermediate.wfprog_main_existence wf_p) in Hmain_prog.
      destruct Hmain_prog as [main_procs [Hcontra _]].
      have Hcontra_def : domm (Intermediate.prog_interface p) = domm (Intermediate.prog_procedures p) by apply wf_p.
      have Hcontra' : Component.main \in domm (Intermediate.prog_procedures p) by apply /dommP ; exists main_procs.
      have Hmain_contra : Component.main \in domm (Intermediate.prog_interface p) by rewrite Hcontra_def.
      rewrite Hmain_contra in Hmain_comp. inversion Hmain_comp.
  - (* <-, no main in intermediate implies no main in source bactkanslated *)
    unfold prog_main, program_unlink. simpl.
    rewrite find_procedure_filter_comp.
    move => Hinterm.
    destruct (Component.main \in domm (Intermediate.prog_interface p)) eqn:Hcase.
    + inversion wf_p as [_ _ _ _ _ _ Hmain_component].
      pose proof (proj1 (Intermediate.wfprog_main_component wf_p) Hcase) as Hmainp.
      inversion Hmainp as [Hmainp']. rewrite Hinterm in Hmainp'. discriminate.
    + rewrite Hcase. done.
Qed.

(* Definability *)

(* RB: Relocate? As the S2I require above seems to indicate, this is not where
   this result belongs. *)
Lemma definability_with_linking:
  forall p c b m,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.closed_program (Intermediate.program_link p c) ->
    program_behaves (I.CS.sem (Intermediate.program_link p c)) b ->
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
    case: Hclosed => _ [? [main_procs [? [/= e ?]]]].
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
    have [mainP [_ [HmainP _]]] := Intermediate.cprog_main_existence Hclosed.
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

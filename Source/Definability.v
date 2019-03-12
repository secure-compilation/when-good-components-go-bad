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
Require Import Source.PS.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

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
  Definition increment exp_val := E_binop Add exp_val (E_val (Int 1%Z)).

  Definition FAIL : expr := E_val Undef.
  (* Maybe define NOP in language in order to avoir such a workaround (or use
     another expression).
     Should be fine since this would just set R_COM to 0, and R_COM would be
     redefined before used *)
  Definition NOP : expr := E_val (Int 0).

  Hint Unfold increment counter_idx NOP.

  Definition switch_clause n e_then e_else :=
    E_if (E_binop Eq (E_deref (E_local Block.priv)) (E_val (Int n)))
         (E_seq (E_assign (E_local Block.priv)
                          (increment (E_deref (E_local Block.priv)))) e_then)
         e_else.

  Ltac take_step :=
    match goal with
    | |- @star _ _ _ _ _ ?t _ =>
      eapply (@star_step _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
    end.

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

  Definition switch (es: list expr) (e_else: expr) : expr :=
    snd (fold_right switch_add_expr (length es, e_else) es).

  Lemma fst_switch n (e_else: expr) (es : list expr) :
    fst (fold_right switch_add_expr (n, e_else) es) = (n - length es)%nat.
  Proof.
    induction es as [|e' es IH]; try now rewrite Nat.sub_0_r.
    simpl. now rewrite IH Nat.sub_succ_r.
  Qed.

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

  (* TODO relocate *)
  Lemma nseq_add {T:Type} (n1 n2:nat) (x:T) : nseq (n1+n2) x = nseq n1 x ++ nseq n2 x.
  Proof.
    by elim: n1 => //= n1 IHn1 ; rewrite IHn1.
  Qed.

  (* TODO relocate *)
  Lemma cat_app {T:Type} (l1 l2:list T) :
    app l1 l2 = cat l1 l2.
  Proof. by elim: l1. Qed.

  (* TODO relocate *)
  (* Coq or ssr conventions (cat/app, length/size) ? *)
  Lemma combine_cat {A B : Type} : forall (beg1 end1:list A), forall (beg2 end2:list B),
    size beg1 = size beg2 ->
    (* Not useful *)
    (* size end1 = size end2 -> *)
    combine (beg1 ++ end1) (beg2 ++ end2) = combine beg1 beg2 ++ combine end1 end2.
  Proof.
    induction beg1 as [|a1 beg1' IHbeg1'] => end1 beg2 end2 Hbeg.
    - by inversion Hbeg as [Hsize0] ; symmetry in Hsize0 ;
        apply size0nil in Hsize0 ; subst.
    - destruct beg2 as [| a2 beg2'] => //.
      inversion Hbeg as [Hsize]. apply (IHbeg1' end1 _ end2) in Hsize => /=.
        by rewrite Hsize.
  Qed.

  (* TODO relocate *)
  Lemma mkfmap_cat {T:ordType} (S:Type) (s1 s2:seq (T*S)) :
    (* Is it necessary ? *)
    (* all (fun x => (mkfmap s1) x) (split s2).1  -> *)
    (* Or *)
    (* fdisjoint (mkfmap s1) (mkfmap s2) -> *)
    mkfmap (s1 ++ s2) = unionm (mkfmap s1) (mkfmap s2).
  Proof.
(*     generalize dependent s2. *)
(*     induction s1 as [| a1 s1 IHs1] ; first done. *)

(*   (*   setm_union: *) *)
(*   (* forall (T : ordType) (S : Type) (m1 m2 : {fmap T -> S}) (k : T) (v : S), *) *)
(*   (* setm (unionm m1 m2) k v = unionm (setm m1 k v) m2 *) *)

(* rewrite /unionm/mkfmap.  *)
    rewrite /unionm/mkfmap. rewrite -foldr_cat. rewrite-/mkfmap.
    generalize dependent s2 ; induction s1 ; first done.
    move => s2. simpl. rewrite /setm.
    rewrite -/mkfmap.
    (* rewrite (IHs1 s2). *)
    (* rewrite -/setm_subproof. *)

    (* rewrite -(foldr _ (foldr _ (_++_))/[mkfmap _++_]. *)
    Admitted.


  (** Gives a map of the different indexes of a component's public memory to
      bool, all initialized at false *)
  Definition indexes_read_init (comp: Component.interface) :  NMap bool :=
    let size_buf :=
        Component.public_buffer_size comp in
    mkfmap (combine (iota 0 size_buf) (nseq size_buf false)).

  Lemma indexes_read_init_correct (comp: Component.interface) :
    all (fun b:bool => b == false) (codomm (indexes_read_init comp)) /\
    domm (indexes_read_init comp) = fset (iota 0 (Component.public_buffer_size comp)).
  Proof.
    split.
  (*   (* all at false *) *)
  (*   - rewrite /indexes_read_init/codomm/invm domm_mkfmap'. *)
  (*     admit. *)
  (*   (* Correct indexing *) *)
  (*   - admit. *)
  (* Admitted. *)

    - rewrite /indexes_read_init.
      set (size_buf := Component.public_buffer_size comp). induction size_buf.
      + move => /=. rewrite codomm0. apply all_nil.
      + move: IHsize_buf.
        rewrite /codomm/invm !domm_mkfmap'.
        have:iota 0 (S size_buf) = iota 0 (size_buf) ++ [size_buf]
          by rewrite -ssrnat.addn1 iota_add.
        move => -> IHsize_buf.
        have:nseq (S size_buf) false = nseq size_buf false ++ [false]
          by rewrite -ssrnat.addn1 nseq_add.
        move => -> ; rewrite combine_cat ; last by rewrite size_iota size_nseq.
        (* rewrite mkfmap_cat. *)

        admit.

    (* domm_union:
       forall (T : ordType) (S : Type) (m1 m2 : {fmap T -> S}),
       domm (unionm m1 m2) = domm m1 :|: domm m2 *)
    (* How does it goes with codomm ? *)

        (* rewrite mapm_unionm. *)

        (* rewrite map_cat. *)

        (* rewrite /nseq/ncons ssrnat.iterSr. rewrite cats1/rcons. *)
     - admit.
  Admitted.

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

  (* Quick sanity check (unrealistic) *)
  Example test_E_seq_of_list_expr :
    let list_expr := [E_val (Int 0); E_val (Int 1); E_val (Int 2)] in
    let seq_expr  := E_seq (E_val (Int 0))
                           (E_seq (E_val (Int 1))
                                  (E_val (Int 2))) in
    E_seq_of_list_expr list_expr = Some seq_expr.
  Proof. reflexivity. Qed.

  (** Gives an assignement expression of the public memory (at index off) to val *)
  Definition assign_public off val :=
    E_assign (E_binop Add (E_local Block.pub) (E_val (Int off))) (E_val val).

  (** Gives a list of assignement depending on the ELoad events in the future of
      the trace (accumulated)
      This list is in reverse order since append costs more than cons
   *)
  Fixpoint prefill_read_aux
           (C: Component.id)
           (suffix: trace)
           (acc:list expr)
           (indexes_read:NMap bool) : list expr:=

    let stop := acc in
    (* Maybe express it in an other way than membership of codomain *)
    if (false \in codomm indexes_read)
    then                        (* a read is still possible *)
      match suffix with
      | [] => stop            (* if no further events, give back exprs created *)
      | ev :: suffix' =>
        let keep_on :=  (prefill_read_aux C suffix' acc indexes_read) in
        match ev with
        | ELoad Cdrf off val Cown =>   (* component is read *)
          (* kinda useless check since the trace is well formed, we shouldn't
             have "wild" ELoad events *)
          if Cown == C then
            (* TODO fix this Z.to_nat, too permissive *)
            (* Do Memory.load ? Check if positive ? *)
            match indexes_read (Z.to_nat off) with
            | None => []           (* Never happens *)
            | Some true => keep_on (* already read so go on *)
            | Some false => prefill_read_aux C
                                            suffix'
                                            ((assign_public off val) :: acc)
                                            (* TODO fix this Z.to_nat, too permissive *)
                                            (* TODO should use updm but knowing
                                               that it would return (Some _)
                                               each time *)
                                            (setm indexes_read (Z.to_nat off) true)


            end
          else keep_on
        (* if the component is given turn again, give back exprs created *)
        | ERet _(* C *) _ _  | ECall _(* C *) _ _ _  => stop
        end
      end
    else stop.     (* if all offset have been read, give back exprs created *)

   Fixpoint prefill_read_aux_ntr
           (C: Component.id)
           (suffix: trace)
           (indexes_read:NMap bool) : list expr:=
    let stop := [] in
    (* Maybe express it in an other way than membership of codomain *)
    if (false \in codomm indexes_read)
    then                        (* a read is still possible *)
      match suffix with
      | [] => stop            (* if no further events, give back exprs created *)
      | ev :: suffix' =>
        let keep_on :=  (prefill_read_aux_ntr C suffix' indexes_read) in
        match ev with
        | ELoad Cdrf off val Cown =>   (* component is read *)
          (* kinda useless check since the trace is well formed, we shouldn't
             have "wild" ELoad events *)
          if Cown == C then
            (* TODO fix this Z.to_nat, too permissive *)
            (* Do Memory.load ? Check if positive ? *)
            match indexes_read (Z.to_nat off) with
            | None => []           (* Never happens but mandatory *)
            | Some true => keep_on (* already read so go on *)
            | Some false =>
              (assign_public off val)
                ::(prefill_read_aux_ntr C
                                       suffix'
                                       (* TODO fix this Z.to_nat, too permissive *)
                                       (setm indexes_read (Z.to_nat off) true))


            end
          else keep_on
        (* if the component is given turn again, give back exprs created *)
        | ERet _(* C *) _ _  | ECall _(* C *) _ _ _  => stop
        end
      end
    else stop.     (* if all offset have been read, give back exprs created *)



  (* I find that checking fmap membership, even for map with given static data,
     is a bit of a pain. It would be nice to add these to the 'done' tactical or
     some other automation mean *)
  Example setm_thingy :
    let fmap_thing := [fmap (0, false); (1, false); (2, false)] in
    let fset_thing := [fset 0; 1; 2] in
     1 \in domm fmap_thing /\ false \in codomm fmap_thing /\ 1 \in fset_thing.
  Proof.
    simpl. split.
    (* \in domm of something is usually solved automatically once mem_domm has
         been used *)
    rewrite mem_domm ; done. Undo.
      (* I guess dommP(n) can be used too *)
    apply /dommP. eexists. done.
    split.

    (* codomm is a bit more subtle, either use codommP(n) *)
    apply /codommP ; exists 1 ; done. Undo. (* Not automatic so not really useful *)
    (* eexists doesn't help much : in the previous case we had m k = some ?v,
       there we have  m ?k = some v, which is less trivial *)
    apply /codommP ; eexists. Undo.
    (* Rewriting codomm with its definition works much better *)
    rewrite /codomm. rewrite /invm. simpl. (* from there, its' just as with domm *)
    apply /dommP ; eexists ; done. Undo.
    rewrite mem_domm ; done.

    (* Since [fset a1; .. ; an ] is a notation for nested (fsetU (fset a1) ..
       (fsetU (fset an))), we can rewrite it easily *)
      by rewrite !in_fsetU1.
  Qed.

  (* In the meantime, let's use these notations for examples *)
  Tactic Notation "find_in_domm" :=
    rewrite mem_domm.
  Tactic Notation "find_in_domm_goal" :=
    apply /dommP ; eexists.
  Tactic Notation "find_in_codomm" :=
    rewrite /codomm ; rewrite /invm ; simpl ;
    find_in_domm.
  Tactic Notation "find_in_codomm_goal" int_or_var(n) :=
    apply /codommP ; exists n.
  Tactic Notation "find_in_fset" :=
    rewrite !in_fsetU1.

  Example test_prefill_read_aux0 :
    let '(C1,P1) := (1,1) in
    let '(arg1, ret1) := (17%Z, 42%Z) in
    let '(off0, load0, off1, load1, off2, load2) := (0%Z, Int 17%Z, 1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
    let ev1 := ECall Component.main P1 arg1 C1 in
    let ev1':= ELoad C1 off0 load0 Component.main in
    let ev2 := ERet C1 ret1 Component.main in
    let ev3 := ELoad Component.main off1 load1 C1 in
    let ev4 := ELoad Component.main off2 load2 C1 in
    let acc := [] in
    let offsets := mkfmap[(0,false);(1,false);(2,false)] in
    prefill_read_aux Component.main [  ev1'; ev2;  ev3 ; ev4 ] acc offsets  = [(assign_public off0 load0)] /\
    prefill_read_aux_ntr Component.main [  ev1'; ev2;  ev3 ; ev4 ] offsets  = [(assign_public off0 load0)]
  .
  Proof. split ; by repeat (find_in_codomm ; simpl). Qed.

  Example test_prefill_read_aux1 :
    let '(C1,P1) := (1,1) in
    let '(arg1, ret1) := (17%Z, 42%Z) in
    let '(off0, load0, off1, load1, off2, load2) := (0%Z, Int 17%Z, 1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
    let ev1 := ECall Component.main P1 arg1 C1 in
    let ev1':= ELoad C1 off0 load0 Component.main in
    let ev2 := ERet C1 ret1 Component.main in
    let ev3 := ELoad Component.main off1 load1 C1 in
    let ev4 := ELoad Component.main off2 load2 C1 in
    let acc := [] in
    let offsets := emptym in
    prefill_read_aux Component.main [  ev3 ; ev4 ] acc offsets  = []
  /\ prefill_read_aux_ntr Component.main [  ev3 ; ev4 ] offsets  = [].
  Proof. split ; by simpl ; rewrite codomm0. Qed.

  Example test_prefill_read_aux2 :
    let '(C1,P1) := (1,1) in
    let '(arg1, ret1) := (17%Z, 42%Z) in
    let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
    let ev1 := ECall Component.main P1 arg1 C1 in
    let ev2 := ERet C1 ret1 Component.main in
    let ev3 := ELoad Component.main off1 load1 C1 in
    let ev4 := ELoad Component.main off2 load2 C1 in
    let acc := [] in
    let offsets := mkfmap[(0,false);(1,false);(2,false)] in
    prefill_read_aux C1 [ ev3 ; ev4 ] acc offsets = [(assign_public 2 (Int 1337)); (assign_public 1 (Int 420))] /\
  prefill_read_aux_ntr C1 [ ev3 ; ev4 ] offsets = [ (assign_public 1 (Int 420)); (assign_public 2 (Int 1337))].
  Proof. split ; by repeat (find_in_codomm ; simpl). Qed.

  Example test_prefill_read_tricky :
    let '(C1,P1,C2,P2) := (1,1,2,2) in
    let Pintf := [fmap
                    (Component.main, Component.mkCompInterface fset0 [fset (C1, P1)] 3  );
                    (C1, Component.mkCompInterface [fset P1] [fset (C2, P2)] 3 );
                    (C2, Component.mkCompInterface [fset P2] [fset (C1, P1)] 3 )] in
    (* we are not interested in call args and return values *)
    let '(arg, ret) := (17%Z, 42%Z) in
        let '(load1, load2, load3, load4,
          load5, load6, load7, load8,
          load9, load10, load11, load12,
          load13, load14) := (Int 1%Z, Int 2%Z, Int 3%Z, Int 4%Z,
                              Int 5%Z, Int 6%Z, Int 3%Z, Int 8%Z,
                              Int 5%Z, Int 10%Z, Int 3%Z, Int 12%Z,
                              Int 13%Z, Int 14%Z) in
    let '(off1, off2, off3, off4,
          off5, off6, off7, off8,
          off9, off10, off11, off12,
          off13, off14) :=  (0%Z, 0%Z, 0%Z, 1%Z,
                             1%Z, 0%Z, 0%Z, 1%Z,
                             1%Z, 1%Z, 0%Z, 0%Z,
                             1%Z, 1%Z) in
    let load_ev1 := ELoad Component.main off1 load1 C1 in
    let load_ev2 := ELoad Component.main off2 load2 C2 in
    let call_ev1 := ECall Component.main P1 arg C1 in

    let load_ev3 := ELoad C1 off3 load3 Component.main in
    let load_ev4 := ELoad C1 off4 load4 C2 in
    let call_ev2 := ECall C1 P2 arg C2 in

    let load_ev5 := ELoad C2 off5 load5 Component.main in
    let load_ev6 := ELoad C2 off6 load6 C1 in
    let call_ev3 := ECall C2 P1 arg C1 in

    let load_ev7 := ELoad C1 off7 load7 Component.main in
    let load_ev8 := ELoad C1 off8 load8 C2 in
    let ret_ev1  := ERet C1 ret C2 in

    let load_ev9 := ELoad C2 off9 load9 Component.main in
    let load_ev10:= ELoad C2 off10 load10 C1 in
    let ret_ev2  := ERet C2 ret C1 in

    let load_ev11:= ELoad C1 off11 load11 Component.main in
    let load_ev12:= ELoad C1 off12 load12 C2 in
    let ret_ev3  := ERet C1 ret Component.main in

    let load_ev13:= ELoad Component.main off13 load13 C1 in
    let load_ev14:= ELoad Component.main off14 load14 C2 in

    let acc := [::] in
    let offsets := mkfmap[(0,false);(1,false);(2,false)] in
    let cst :=  fun (C: Component.id) (t: trace) =>
                            filter (fun e => (C == cur_comp_of_event e) ||
                                          match e with
                                          | ELoad _ _ _ C => true
                                          | _ => false end) t in
    let trace := [load_ev1;  load_ev2;  call_ev1;
                  load_ev3;  load_ev4;  call_ev2;
                  load_ev5;  load_ev6;  call_ev3;
                  load_ev7;  load_ev8;  ret_ev1;
                  load_ev9;  load_ev10;  ret_ev2;
                  load_ev11;  load_ev12;  ret_ev3;
                    load_ev13;  load_ev14] in
    (* be careful to not have too many suffixes! suffixes_of_trace (or _seq)
       produces all of them ! *)
    let sfx1 := [ load_ev3;  load_ev4;  call_ev2;
                  load_ev5;  load_ev6;  call_ev3;
                  load_ev7;  load_ev8;  ret_ev1;
                  load_ev9;  load_ev10;  ret_ev2;
                  load_ev11;  load_ev12;  ret_ev3;
                  load_ev13;  load_ev14] in
    let sfx2 := [ load_ev5;  load_ev6;  call_ev3;
                  load_ev7;  load_ev8;  ret_ev1;
                  load_ev9;  load_ev10;  ret_ev2;
                  load_ev11;  load_ev12;  ret_ev3;
                  load_ev13;  load_ev14] in
    let sfx3 := [ load_ev7;  load_ev8;  ret_ev1;
                  load_ev9;  load_ev10;  ret_ev2;
                  load_ev11;  load_ev12;  ret_ev3;
                  load_ev13;  load_ev14] in
    let sfx4 := [ load_ev9;  load_ev10;  ret_ev2;
                  load_ev11;  load_ev12;  ret_ev3;
                  load_ev13;  load_ev14] in
    let sfx5 := [ load_ev11;  load_ev12;  ret_ev3;
                    load_ev13;  load_ev14] in
    let sfx6 := [ load_ev13;  load_ev14] in
    let '(ssfx1, ssfx2,
          ssfx3, ssfx4, ssfx5, ssfx6) :=
        (cst Component.main sfx1, cst C1 sfx2,
         cst C2 sfx3, cst C1 sfx4, cst C2 sfx5, cst C1 sfx6 ) in
    let st0 := stack_state0 in
    let st1 := StackState C1 [Component.main] in
    let st2 := StackState C2 [C1; Component.main] in
    let st3 := StackState C1 [C2; C1; Component.main] in
    let st4 := StackState C2 [C1; Component.main] in
    let st5 := StackState C1 [Component.main] in
    all (well_formed_event Pintf) trace /\
    (well_bracketed_trace st0 (call_ev1::sfx1) /\
     prefill_read_aux Component.main ssfx1 acc offsets =
         [(assign_public off5 load5); (assign_public off3 load3)] /\
     prefill_read_aux_ntr Component.main ssfx1 offsets =
         [(assign_public off3 load3); (assign_public off5 load5)]) /\
    (well_bracketed_trace st1 (call_ev2::sfx2) /\
     prefill_read_aux C1 ssfx2 acc offsets = [(assign_public off6 load6)] /\
     prefill_read_aux_ntr C1 ssfx2 offsets = [(assign_public off6 load6)]) /\
    (well_bracketed_trace st2 (call_ev3::sfx3) /\
     prefill_read_aux C2 ssfx3 acc offsets  = [(assign_public off8 load8)] /\
     prefill_read_aux_ntr C2 ssfx3 offsets  = [(assign_public off8 load8)]) /\
    (well_bracketed_trace st3 (ret_ev1::sfx4) /\
     prefill_read_aux C1 ssfx4 acc offsets  = [(assign_public off10 load10)] /\
     prefill_read_aux_ntr C1 ssfx4 offsets  = [(assign_public off10 load10)]) /\
    (well_bracketed_trace st4 (ret_ev2::sfx5) /\
     prefill_read_aux C2 ssfx5 acc offsets  =
         [(assign_public off14 load14) ; (assign_public off12 load12)] /\
     prefill_read_aux_ntr C2 ssfx5 offsets  =
         [(assign_public off12 load12) ; (assign_public off14 load14)]) /\
    (well_bracketed_trace st5 (ret_ev3::sfx6) /\
     prefill_read_aux C1 ssfx6 acc offsets  =
         [(assign_public off13 load13)] /\
     prefill_read_aux_ntr C1 ssfx6 offsets  =
       [(assign_public off13 load13)]).
  Proof.
    (* well formed events sanity check *)
    simpl ; rewrite /imported_procedure_b ; simpl. split.
    find_in_fset ; done.

    (* getting rid of the membership tests *)
    repeat (find_in_codomm ; simpl).
    by repeat (split ; first reflexivity).
 Qed.

  Lemma prefill_read_aux_invar : forall suffix C comp acc indexes res ,
      intf C = Some comp ->
      (* Add a restriction on the indexes wrt comp.public_buffer_size *)
      prefill_read_aux C suffix acc indexes (* (indexes_read_init comp) *) = res ->
      exists res', prefill_read_aux_ntr C suffix indexes = res' /\
              res = rev res' ++ acc.
  Proof.
    induction suffix as [| ev suffix IHsuffix] ; intros C comp acc indexes res Hintf.
    - simpl. case : (_ \in _) ; exists [] ; subst ;  split ; done.
    - generalize dependent C ; generalize dependent comp ; generalize dependent acc ;
      generalize dependent indexes ; generalize dependent res.
      rewrite /prefill_read_aux/prefill_read_aux_ntr ;
        elim: ev => [ Ccur proc arg Cnext | Cret ret Cnext  | CSrc o v CTrg ] ;
                     intros res indexes acc comp C Hintf ;
      case: (_ \in _) => <- ; try (exists [] ; split ; done).
      rewrite -/prefill_read_aux -/prefill_read_aux_ntr.
      (* Load event *)
      destruct (CTrg == C) eqn:WhichTrgComp => // ;
      (* Case analysis on presence of the index in the map,
         case None never happens, how to avoid it ? *)
        case: (indexes (Z.to_nat o)) => // ;
          try case  ; (* if the index is present, trivial  *)
          try by apply (IHsuffix C comp).
      + set indexes_upd := setm indexes (Z.to_nat o) true.
        set res_IH :=prefill_read_aux C suffix (assign_public o v :: acc) indexes_upd.
        set res'_IH := prefill_read_aux_ntr C suffix indexes_upd.
        set acc_IH := (assign_public o v :: acc).
        specialize (IHsuffix C comp acc_IH indexes_upd res_IH Hintf).
        have refl: prefill_read_aux C suffix acc_IH indexes_upd = res_IH by [].
        apply IHsuffix in refl.
        destruct refl as [? [? H]]. exists (assign_public o v::x). subst.
        (* exists (assign_public o v :: prefill_read_aux_ntr C suffix indexes_upd). *)
        rewrite rev_cons cat_rcons.
        split ; done.
       + (* ELoad event with index out of bounds... *)
         admit.
  Admitted.

  Lemma prefill_read_aux_equiv : forall suffix C comp,
      intf C = Some comp ->
      prefill_read_aux_ntr C suffix (indexes_read_init comp) =
      rev (prefill_read_aux C suffix [] (indexes_read_init comp)).
  Proof.
    intros suffix C comp Hintf.
    set indexes := indexes_read_init comp.
      by apply prefill_read_aux_invar with (suffix := suffix)
                                           (indexes := indexes)
                                           (res := prefill_read_aux C suffix [] indexes)
                                           (acc := []) in Hintf ;
        first destruct Hintf as [? [? H]] ; subst ; [by rewrite H cats0 revK | done].
  Qed.

  (* Since we only backtranslate, and we got a well-formed program if the events
     are well-formed, we can just assign any value transmitted in the load
     events (if it's a pointer or an undef, the event is not well-formed) *)
  Definition expr_assign_public (e:expr) :=
    match e with
    | E_assign (E_binop Add (E_local Block.pub) (E_val (Int _(* index *))))
               (E_val  _ (* value *)) => true
    | _ => false
    end.

  (* To relocate *)
  Lemma rev_inj {T:Type} : injective (@rev T).
  Proof. by apply (can_inj revK). Qed.

  Lemma prefill_read_aux_only_assign (suffix : trace) (C : Component.id) (comp : Component.interface) :
    (intf C = Some comp) ->
    all expr_assign_public (prefill_read_aux C suffix [] (indexes_read_init comp)).
  Proof.
    intro Hintf.
    (* translating to non-tail-recursive function *)
    have : prefill_read_aux_ntr C suffix (indexes_read_init comp) =
           rev (prefill_read_aux C suffix [] (indexes_read_init comp)) by apply (@prefill_read_aux_equiv suffix C comp Hintf).
    rewrite -[prefill_read_aux_ntr C suffix (indexes_read_init comp)]revK.
    move => Hequiv ; apply rev_inj in Hequiv.
    rewrite -Hequiv all_rev ; clear Hequiv.

    generalize dependent (indexes_read_init comp).
    induction suffix  as [| ev suffix IHsuffix ] ; rewrite /prefill_read_aux_ntr => indexes ; case: (_ \in _) => //.
    (* generalize dependent C ; generalize dependent comp. *)
    elim: ev => [ Ccur proc arg Cnext | Cret ret Cnext  | CSrc o v CTrg ] => //.
    case: (CTrg == C) => // ; case: (indexes (Z.to_nat o)) => // is_in_offs.
    case: is_in_offs => //=.
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
  Proof. by case => [_ _ _ _|_ _ _|_ _ ? _] //= /andP [_ ?]. Qed.

  (* This might be silly to not use well_formed_event instead of
     only_transferable since we have access to the program interface *)

  Lemma prefill_read_aux_only_values_integers (suffix : trace) (C : Component.id) (comp : Component.interface) :
    (intf C = Some comp) ->
    all only_transferable_values_in_ELoad suffix ->
    (* all (well_formed_event intf) suffix -> *)
    all values_are_integers (prefill_read_aux C suffix [] (indexes_read_init comp)).
  Proof.

    intros Hintf Htransf_sfx.
    have Hassign: all expr_assign_public (prefill_read_aux C suffix [] (indexes_read_init comp))
       by apply (prefill_read_aux_only_assign suffix Hintf).
    (* would be nice to prove the goal almost directly from this *)

    (* In the meantime... *)
    (* translating to non-tail-recursive function *)
    have : prefill_read_aux_ntr C suffix (indexes_read_init comp) =
           rev (prefill_read_aux C suffix [] (indexes_read_init comp)) by apply (@prefill_read_aux_equiv suffix C comp Hintf).
    rewrite -[prefill_read_aux_ntr C suffix (indexes_read_init comp)]revK.
    move => Hequiv ; apply rev_inj in Hequiv.
    rewrite -Hequiv all_rev ; rewrite -Hequiv in Hassign ; clear Hequiv.

    generalize dependent (indexes_read_init comp).
    induction suffix as [| ev sfx IHsfx] ; rewrite (* /values_are_integers *)/prefill_read_aux_ntr ; intro indexes.
    - by case:(_ \in _).
    - (* rewrite -/prefill_read_aux_ntr. *) (* more clear now *)
      induction ev as [ | | CSrc o v CTrg ]; case: (_ \in _) => //. rewrite -/prefill_read_aux_ntr.
      (* Load event *)
      (* Getting rid of the trivial cases *)
      case: (CTrg == C) => // ; case: (indexes (Z.to_nat o)) => // is_in_offs ;
      (* TODO change this bit, is_in_offs is not binded to a boolean in the last case *)
      case: is_in_offs => //= ;  move: Htransf_sfx ; simpl ; move => /andP => [ [Htransf_v Htransf_sfx ] ].
        all: try apply (IHsfx Htransf_sfx indexes).

      (* Case in which we produce an assignement and the indexes_map is updated *)
      set indexes_upd := (setm indexes (Z.to_nat o) true).
      move => Hassign ; apply /andP. split.

      move : Htransf_v ; rewrite /is_transferable_value. done.
      apply (IHsfx Htransf_sfx indexes_upd).
        by move: Hassign ; rewrite !all_rev.
  Qed.


  (** Gives Some expr that is the (sequence of) assignement(s) or None if it's
      not the case.
      As said above, we can use rev' before flattening the list of expressions
      to keep this tail-recursive *)
  Definition prefill_read (C: Component.id) (suffix: trace) : option expr :=
    (* Only used to accomodate with the fact that the interface is a map.
       None is never returned by this match, but can be returned by
       E_seq_of_list_expr on an empty list of expressions. *)
    match intf C with
    | Some comp => E_seq_of_list_expr (rev (prefill_read_aux
                                                  C
                                                  suffix
                                                  []
                                                  (indexes_read_init comp)))
    | None => None
    end.


  Lemma prefill_read_only_values_integers (suffix : trace) (C : Component.id) (comp : Component.interface) (e:expr):
    (intf C = Some comp) ->
    all only_transferable_values_in_ELoad suffix ->
    prefill_read C suffix = Some e ->
    values_are_integers e.
  Proof.
    rewrite /prefill_read. move => Hcomp ; rewrite Hcomp => Hpref.
    have: all values_are_integers (rev' (prefill_read_aux C suffix [::] (indexes_read_init comp)))
      by apply prefill_read_aux_only_values_integers with (C:=C) (comp:= comp)
      in Hpref => // ; rewrite all_rev.
    by apply E_seq_of_list_expr_integers.
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
  Definition expr_of_event (C: Component.id) (P: Procedure.id) (suffix: trace) : expr :=
    match suffix with
    (* Never happens except for an empty trace *)
    | nil => NOP
    | ECall _ P' arg C' :: suffix' =>
      let call_trigger := E_seq (E_call C' P' (E_val (Int arg)))
                                (E_call C  P  (E_val (Int 0))) in
      match (prefill_read C suffix') with
      | None => call_trigger
      | Some prefill => E_seq prefill call_trigger
      end
    | ERet _ ret_val _ :: suffix' =>
      let return_trigger := E_val (Int ret_val) in
      match prefill_read C suffix' with
      | None => return_trigger
      | Some prefill => E_seq prefill return_trigger
      end
    | ELoad C' off _ C'' :: suffix' =>
      (* In case of load performed by the current component *)
      if C == C' then E_seq (E_deref (E_binop Add (E_component_buf C'') (E_val (Int off))))
                            (E_assign (E_local Block.priv)
                                      (increment (E_deref (E_local Block.priv))))
      else
        (* In the case the memory from the current component is loaded, we don't
           do anything here (this kind of event is used in prefill_read) *)
        (* problem(?) : should produce nothing, we use a kind of NOP (otherwise
           switch should handle option as a parameter, too many useless changes) *)
        NOP
    end.

  Definition expr_of_trace (C: Component.id) (P: Procedure.id) (t: trace) : expr :=
    switch (map (expr_of_event C P) (suffixes_of_seq t)) E_exit.

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

  Remark subseq_comp_subtrace C t : subseq (comp_subtrace C t) t.
  Proof. by apply filter_subseq. Qed.

  (* To relocate *)
  Lemma all_subseq {T:eqType} (s ss : seq T) (a : pred T) :
    all a s -> subseq ss s -> all a ss.
  Proof.
    by move => /all_filterP <- ; rewrite subseq_filter => /andP [? _].
  Qed.

  Example test_comp_subtrace0 :
    let '(C1,P1) := (1,1) in
    let '(arg1, ret1) := (17%Z, 42%Z) in
    let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
    let ev1 := ECall Component.main P1 arg1 C1 in
    let ev2 := ERet C1 ret1 Component.main in
    let ev3 := ELoad Component.main off1 load1 C1 in
    let ev4 := ELoad Component.main off2 load2 C1 in
    comp_subtrace Component.main [ ev1; ev2; ev3 ; ev4 ] = [ev1 ; ev3 ; ev4].
  Proof.
    simpl. reflexivity. Qed.

  Example test_comp_subtrace1 :
    let '(C1,P1) := (1,1) in
    let '(arg1, ret1) := (17%Z, 42%Z) in
    let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
    let ev1 := ECall Component.main P1 arg1 C1 in
    let ev2 := ERet C1 ret1 Component.main in
    let ev3 := ELoad Component.main off1 load1 C1 in
    let ev4 := ELoad Component.main off2 load2 C1 in
    comp_subtrace C1 [ ev1; ev2; ev3 ; ev4 ] = [ev2 ; ev3 ; ev4].
  Proof.
    simpl. reflexivity. Qed.

  Lemma comp_subtrace_app (C: Component.id) (t1 t2: trace) :
    comp_subtrace C (t1 ++ t2) = comp_subtrace C t1 ++ comp_subtrace C t2.
  Proof. apply: filter_cat. Qed.

  Definition procedure_of_trace C P t :=
    expr_of_trace C P (comp_subtrace C t).

  (* Lemma procedure_of_trace_correct *)

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

  (* TODO modify to accomodate to public buffers (plus, what is happening ? no static buffer is allocated ? where is the counter stored ???) *)
  Definition program_of_trace (t: trace) : program :=
    {| prog_interface  := intf;
       prog_procedures := procedures_of_trace t;
       prog_buffers    := mapm (fun Cintf => (inl (Component.public_buffer_size Cintf) , inr [Int 0])) intf |}.

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
      rewrite /find_procedure /procedures_of_trace mapimE.
      case intf_C: (intf C)=> [CI|] //=.
      rewrite mkfmapfE; case: ifP=> //= P_CI [<-] {Pexpr}; split; last first.
      + (* values_are_integers *)
        rewrite /procedure_of_trace /expr_of_trace /switch.
        elim: t Ht (length _) => [| e t] IH //= /andP [Hwf_e Hwf_t].
        move: IH ; rewrite !suffixes_of_seq_equiv => IH n /=.
        destruct e as [ C' p arg ? | C' ret ? | Cderef off ? Cown] eqn:H_ev ;
          rewrite /filter_comp_subtrace ;
          destruct (C == _) eqn:C_eq => /= ; try by apply (IH Hwf_t).
        all : try (apply /andP ; split ; last by apply (IH Hwf_t)).
        1-2 : destruct (C == _) eqn:C_eq' ; try discriminate ; (* rule out FAILs *)
          destruct (prefill_read C (comp_subtrace C t)) eqn:prefill.
        5-6: destruct (C==Cown) eqn:C_eq_Cown.
        all :have Hpref: forall expr, prefill_read C (comp_subtrace C t) = Some expr ->
                                 values_are_integers expr
              by intro ; apply (prefill_read_only_values_integers intf_C) ;
                 apply (sub_all well_formed_event_implies_only_transferable_values_in_ELoad) ;
                 apply (all_subseq Hwf_t (subseq_comp_subtrace C t)).
        (* apply IH in Hwf_t. *) (* if we don't reuse Hwf_t, would be shorter that way *)
        all : try apply Hpref in prefill ;
          try done ;
          try by (simpl ; rewrite prefill).
        * simpl. apply/andP ; split ; last by apply (IH Hwf_t). by case: (C == Cown) => //.
        * by apply (IH Hwf_t).
      + (* Valid calls *)
        pose call_of_event e := if e is ECall _ P _ C then Some (C, P) else None.
        have /fsubsetP sub :
          fsubset (called_procedures (procedure_of_trace C P t))
                  ((C, P) |: fset (pmap call_of_event (comp_subtrace C t))).
        rewrite /procedure_of_trace /expr_of_trace /switch.
        (* This induction should replace many elements by fset0 in the base case *)
        elim: {t Ht} (comp_subtrace C t) (length _)=> [|e t IH] n //=.
          exact: fsub0set.
        move/(_ n) in IH (* ; rewrite !fset0U *).
        case: e=> [C' P' v C''| |] //= (* ; try  by rewrite fset0U *).
        (* ECall *)
        admit.
        (* ERet *)
        admit.
        (* ELoad *)
        admit.
        (* rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT /=. *)
        (* by rewrite fsetUA [(C, P) |: _]fsetUC -fsetUA fsubsetU // IH orbT. *)

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
      elim: {P P_CI} t Ht P' C'_P' => [|e t IH] //= /andP [He Ht] P. rewrite /filter_comp_subtrace.
      case: (C =P _) => [HC|].
      case: e HC He=> [_ P' v C'' /= <-| |]; try by eauto.
      rewrite inE; case/andP=> [C_C'' /imported_procedure_iff imp_C''_P'].
      by case/orP=> [/eqP [-> ->] //|]; eauto.
      case: e He => [ ? ? ? ? | ? ? ? | ? ? ? ?] ; try by eauto.
      move => /andP => [[? ?]] ;
      case: (_==_) ; by eauto.
    - by rewrite domm_map.
    - split; first last.
      move=> C; rewrite -mem_domm => /dommP [CI C_CI].
      rewrite /has_required_local_buffers /= mapmE C_CI /=.
      eexists; eauto=> /=; omega.
    (* valid_buffers *)
      admit.
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

    (* So, either we change the definition to get what we had before (we filter
       the ELoad events not triggered by the component out of the comp_subtrace)
       or we take into account the ELoad events, *)
    (* In the end, we just end up ruling out all ELoad events. But since this
       affects the spec 'switch_spec_else', we won't change anything *)
    Local Definition counter_value C prefix :=
      Z.of_nat (length (comp_subtrace C prefix)).

    Lemma counter_value_app C prefix1 prefix2 :
      counter_value C (prefix1 ++ prefix2)
      = (counter_value C prefix1 + counter_value C prefix2) % Z.
    Proof.
      unfold counter_value.
      now rewrite comp_subtrace_app  app_length Nat2Z.inj_add.
    Qed.

    Definition well_formed_memory (prefix: trace) (mem: Memory.t) : Prop :=
      forall C,
        component_buffer C ->
        Memory.load mem (C, Block.private, counter_idx) = Some (Int (counter_value C prefix)).

    Lemma counter_value_snoc prefix C e :
      counter_value C (prefix ++ [e])
      = (counter_value C prefix
         + if (filter_comp_subtrace C) e
           then 1 else 0) % Z.
    Proof.
      Print counter_value. rewrite /counter_value.
      unfold counter_value, comp_subtrace, filter_comp_subtrace.
      rewrite filter_cat app_length. simpl.
      rewrite Nat2Z.inj_add.
      now destruct (_ == _) ; destruct e as [| |? ? ? C' ]=> //= ; case: (_ == _) => //.
    Qed.

    Lemma well_formed_memory_store_counter prefix mem C e :
      component_buffer C ->
      well_formed_memory prefix mem ->
      C = cur_comp_of_event e ->
      exists mem',
        Memory.store mem (C, Block.private, counter_idx) (Int (counter_value C (prefix ++ [e]))) = Some mem' /\
        well_formed_memory (prefix ++ [e]) mem'.
    Proof.
      move=> C_b wf_mem HC.
      have C_local := wf_mem _ C_b.
      have [mem' Hmem'] := Memory.store_after_load
                             _ _ _ (Int (counter_value C (prefix ++ [e])))
                             C_local.
    (* RB: STATIC_READ: To fix. *)
    (*   exists mem'. split; trivial=> C' C'_b. *)
    (*   have C'_local := wf_mem _ C'_b. *)
    (*   rewrite -> counter_value_snoc, <- HC, Nat.eqb_refl in *. *)
    (*   case: (altP (C' =P C)) => [?|C_neq_C']. *)
    (*   - subst C'. *)
    (*     by rewrite -> (Memory.load_after_store_eq _ _ _ _ Hmem'). *)
    (*   - have neq : (C, Block.local, counter_idx) <> (C', Block.local, counter_idx) by move/eqP in C_neq_C'; congruence. *)
    (*     rewrite (Memory.load_after_store_neq _ _ _ _ _ neq Hmem'). *)
    (*     now rewrite Z.add_0_r. *)
    (* Qed. *)
    Admitted.

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
      (* RB: STATIC_READ: To fix. *)
      (*   rewrite -> size_map; reflexivity. *)
      (* - move=> cs Et /=. *)
      (*   case: cs / => /= _ stk mem _ _ arg P -> -> -> /andP [/eqP wf_C wb_suffix] /andP [wf_e wf_suffix] wf_stk wf_mem P_exp. *)
      (*   have C_b := valid_procedure_has_block P_exp. *)
      (*   have C_local := wf_mem _ C_b. *)
      (*   destruct (well_formed_memory_store_counter C_b wf_mem wf_C) as [mem' [Hmem' wf_mem']]. *)
      (*   assert (Star1 : Star (CS.sem p) *)
      (*                        [CState C, stk, mem , Kstop, expr_of_trace C P (comp_subtrace C t), arg] E0 *)
      (*                        [CState C, stk, mem', Kstop, expr_of_event C P e, arg]). *)
      (*   { unfold expr_of_trace. rewrite Et comp_subtrace_app. simpl. *)
      (*     rewrite <- wf_C, Nat.eqb_refl, map_app. simpl. *)
      (*     assert (H := @switch_spec p C  stk mem *)
      (*                               (map (expr_of_event C P) (comp_subtrace C prefix)) *)
      (*                               (expr_of_event C P e) *)
      (*                               (map (expr_of_event C P) (comp_subtrace C suffix)) *)
      (*                               E_exit arg). *)
      (*     rewrite map_length in H. specialize (H C_local). *)
      (*     destruct H as [mem'' [Hmem'' Hstar]]. *)
      (*     enough (H : mem'' = mem') by (subst mem''; easy). *)
      (*     rewrite -> counter_value_snoc, <- wf_C, Nat.eqb_refl in Hmem'. *)
      (*     rewrite <- Nat.add_1_r, Nat2Z.inj_add in Hmem''. simpl in Hmem''. *)
      (*     unfold counter_value in *. *)
      (*     unfold Memory.store in *. simpl in *. *)
      (*     rewrite Hmem' in Hmem''. *)
      (*     congruence. } *)
      (*   assert (Star2 : exists s' cs', *)
      (*              Star (CS.sem p) [CState C, stk, mem', Kstop, expr_of_event C P e, arg] [:: e] cs' /\ *)
      (*              well_formed_state s' (prefix ++ [e]) suffix cs'). *)
      (*   { *)
      (*     clear Star1 wf_mem C_local mem Hmem'. revert mem' wf_mem'. intros mem wf_mem. *)
      (*     destruct e as [C_ P' new_arg C'|C_ ret_val C'| C_ loaded_val C']; *)
      (*     simpl in wf_C, wf_e, wb_suffix; subst C_. *)
      (*     - case/andP: wf_e => C_ne_C' /imported_procedure_iff Himport. *)
      (*       exists (StackState C' (C :: callers)). *)
      (*       have C'_b := valid_procedure_has_block (or_intror (closed_intf Himport)). *)
      (*       exists [CState C', CS.Frame C arg (Kseq (E_call C P (E_val (Int 0))) Kstop) :: stk, mem, *)
      (*               Kstop, procedure_of_trace C' P' t, Int new_arg]. *)
      (*       split. *)
      (*       + take_step. take_step. *)
      (*         apply star_one. simpl. *)
      (*         apply CS.eval_kstep_sound. simpl. *)
      (*         rewrite (negbTE C_ne_C'). *)
      (*         rewrite -> imported_procedure_iff in Himport. rewrite Himport. *)
      (*         rewrite <- imported_procedure_iff in Himport. *)
      (*         by rewrite (find_procedures_of_trace_exp t (closed_intf Himport)). *)
      (*       + econstructor; trivial. *)
      (*         { destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. *)
      (*           eexists []; eexists; simpl; split; eauto. *)
      (*           split; trivial. *)
      (*           eexists arg, P, top, bot. *)
      (*           by do 3 (split; trivial). } *)
      (*         right. by apply: (closed_intf Himport). *)
      (*     - move: wf_e=> /eqP C_ne_C'. *)
      (*       destruct callers as [|C'_ callers]; try easy. *)
      (*       case/andP: wb_suffix=> [/eqP HC' wb_suffix]. *)
      (*       subst C'_. simpl. exists (StackState C' callers). *)
      (*       destruct wf_stk as (top & bot & ? & Htop & Hbot). subst stk. simpl in Htop, Hbot. *)
      (*       revert mem wf_mem arg. *)
      (*       induction top as [|[C_ saved k_] top IHtop]. *)
      (*       + clear Htop. rename bot into bot'. *)
      (*         destruct Hbot as (saved & P' & top & bot & ? & P'_exp & Htop & Hbot). *)
      (*         subst bot'. simpl. *)
      (*         have C'_b := valid_procedure_has_block P'_exp. *)
      (*         intros mem wf_mem. *)
      (*         exists [CState C', CS.Frame C' saved Kstop :: top ++ bot, mem, Kstop, procedure_of_trace C' P' t, Int 0]. *)
      (*         split. *)
      (*         * eapply star_step. *)
      (*           -- now eapply CS.KS_ExternalReturn; eauto. *)
      (*           -- take_step. take_step; eauto. *)
      (*              apply star_one. apply CS.eval_kstep_sound. *)
      (*              by rewrite /= eqxx (find_procedures_of_trace t P'_exp). *)
      (*           -- now rewrite E0_right. *)
      (*         * econstructor; trivial. *)
      (*           exists (CS.Frame C' saved Kstop :: top), bot. simpl. eauto. *)
      (*       + intros mem wf_mem arg. *)
      (*         simpl in Htop. destruct Htop as [[? ?] Htop]. subst C_ k_. *)
      (*         specialize (IHtop Htop). *)
      (*         specialize (IHtop _ wf_mem saved). destruct IHtop as [cs' [StarRet wf_cs']]. *)
      (*         exists cs'. split; trivial. *)
      (*         eapply star_step; try eassumption. *)
      (*         * by apply/CS.eval_kstep_sound; rewrite /= eqxx. *)
      (*         * reflexivity. *)
      (*         * admit. *)
      (*   } *)
      (*   destruct Star2 as (s' & cs' & Star2 & wf_cs'). *)
      (*   specialize (IH s' (prefix ++ [e]) cs'). rewrite <- app_assoc in IH. *)
      (*   specialize (IH Et wf_cs'). destruct IH as [cs'' Star3 final]. *)
      (*   exists cs''; trivial. *)
      (*   eapply (star_trans Star1); simpl; eauto. *)
      (*   now eapply (star_trans Star2); simpl; eauto. *)
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
      by rewrite ComponentMemory.load_prealloc /=.
    Qed.

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

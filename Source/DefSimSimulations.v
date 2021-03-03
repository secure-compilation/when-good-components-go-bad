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
Require Import Common.Tree.
Require Import Source.DefSimLanguages.
Require Import Source.DefSimComp.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq order.
From mathcomp Require ssrnat.
Require Import Lia.
From extructures Require Import fmap.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Ltac fwd_sim M :=
  apply Forward_simulation with (order := Nat.lt) (match_states := M);
  constructor;
  [now apply lt_wf | | |].

Ltac inv H :=
  inversion H;
  clear H;
  subst.


Inductive match_states1 (i: nat): Tree.state -> NumberedTree.state -> Prop :=
| match_states_1: forall t (trees: NMap (list tree)) (trees': NMap (list numbered_tree)) locs,
    (forall C ls, trees C = Some ls -> exists n, trees' C = Some (give_nums ls n)) ->
    match_states1 i (t, trees) (t, trees', locs)
.


Lemma sim1 (p: Tree.prg): forward_simulation (Tree.sem p) (NumberedTree.sem (compile_tree p)).
Proof.
  fwd_sim match_states1.
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor. eauto.
    + econstructor.
      move=> C ls0 H.
      eexists; by rewrite mapmE H //=.
  - move=> i s1 s2 H H0.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    constructor.
  - move=> s1 t s1' H i s2 H0.
    inv H; inv H0.
    destruct (H6 _ _ H4) as [n Htree];
      destruct (give_nums_app_comm l1 l2 e ls n) as [? [? [? Heq]]].
    destruct (H6 _ _ H5) as [n' Htree'];
      destruct (give_nums_app_comm l1' l2' e ls' n') as [? [? [? Heq']]].
    exists 0; eexists.
    split.
    + left. econstructor.
      { econstructor.
        eauto.
        eauto.
        reflexivity. reflexivity.
        now rewrite Htree Heq.
        now rewrite Htree' Heq'. }
      eapply star_refl.
      eauto.
    + econstructor.
      move=> C ls''.
      rewrite 4!setmE.
      case: (C == next_comp_of_event e); [move=> [] -> |].
      eexists; reflexivity.
      case: (C == cur_comp_of_event e); [move=> [] -> |].
      eexists; reflexivity.
      now apply H6.
Qed.


Inductive match_states2 (intf: Program.interface) (i: nat): NumberedTree.state -> ParentAwareTree.state -> Prop :=
| match_states_2: forall t (trees: NMap (list numbered_tree)) (trees': NMap (list parent_aware_tree)) (locs: NMap nat),
    (forall C, C \in (domm intf) -> exists n, locs C = Some n) ->
    (forall C ls n, trees C = Some ls -> locs C = Some n ->
               trees' C = Some (List.map (fun x => add_parent_loc x n) ls)) ->
    match_states2 intf i (t, trees, locs) (t, trees', locs)
.

Lemma sim2 (p: NumberedTree.prg):
  forward_simulation (NumberedTree.sem p) (ParentAwareTree.sem (compile_numbered_tree p)).
Proof.
  fwd_sim (match_states2 (NumberedTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor.
      eauto.
    + econstructor.
      move=> C H; exists 0; by rewrite mkfmapfE H.
      move=> C ls n H H'.
      suff: n = 0; [move=> ->; by rewrite mapmE H |].
      move: H'; rewrite mkfmapfE.
      case: (C \in domm (NumberedTree.prog_interface p));
        [by move=> [] -> //= | by []].
  - move=> i s1 s2 H H0.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    constructor.
  - move=> s1 t s1' H i s2 H0.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (cur_comp_of_event e \in domm (NumberedTree.prog_interface p)) as Hcomp by (now destruct H1).
    assert (next_comp_of_event e \in domm (NumberedTree.prog_interface p)) as Hcomp' by (now destruct H1).
    destruct (H7 (cur_comp_of_event e) Hcomp) as [pa Hlocs].
    destruct (H7 (next_comp_of_event e) Hcomp') as [pa' Hlocs'].
    case: (H8 _ _ _ H4 Hlocs) => Htree.
    case: (H8 _ _ _ H5 Hlocs') => Htree'.
    exists 0; eexists. split.
    + left. econstructor.
      { econstructor.
        eauto. eauto.
        reflexivity. reflexivity.
        by rewrite Htree map_app //.
        by rewrite Htree' map_app //.
        by []. by []. }
      eapply star_refl.
      reflexivity.
    + econstructor.
      * move=> C H; rewrite 2!setmE.
        case: (C == next_comp_of_event e); [eexists; eauto |].
        case: (C == cur_comp_of_event e); [eexists; eauto |].
          by apply H7.
      * move=> C ls0 n0.
        rewrite 6!setmE.
        case: (C == next_comp_of_event e); [move=> [] -> [] -> |].
        eexists; reflexivity.
        case: (C == cur_comp_of_event e); [move=> [] -> [] -> |].
        eexists; reflexivity.
        now apply H8.
Qed.



Inductive match_states3 (intf: Program.interface) (i: nat): ParentAwareTree.state -> CallerAwareTree.state -> Prop :=
| match_states_3: forall t (trees: NMap (list parent_aware_tree)) (trees': NMap (list caller_aware_tree))
                    (locs: NMap nat) (callers: NMap (list (Z * nat))),
    (forall C ls, trees C = Some ls ->
              trees' C = Some (List.map (add_caller C) ls)) ->
    (forall C1 P z C2 p n zs l1 ls l2,
              trees' C2 = Some (l1 ++ node (p, ECall C1 P z C2, n, zs) ls :: l2) ->
              exists zs1 zs2, callers C2 = Some (zs1 ++ (z, n) :: zs2)) ->
    match_states3 intf i (t, trees, locs) (t, trees', locs, callers)
.

Lemma sim3 (p: ParentAwareTree.prg):
  forward_simulation (ParentAwareTree.sem p) (CallerAwareTree.sem (compile_parent_aware_tree p)).
Proof.
  fwd_sim (match_states3 (ParentAwareTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor.
      eauto.
    + econstructor.
      (* move=> C H; exists 0; by rewrite mkfmapfE H. *)
      move=> C ls H; by rewrite mapimE H.
      move=> C1 P z C2 p0 n zs l1 ls l2 H.
      remember (compile_parent_aware_tree p) as p'.
      (* unfold CallerAwareTree.initial_callers. *)
      rewrite mapimE H //=.
      rewrite DefSimLanguages.CallerAwareTree.collect_callers_initial_app
              DefSimLanguages.CallerAwareTree.collect_callers_initial_cons.
      eexists; eexists.
      unfold DefSimLanguages.CallerAwareTree.collect_callers_initial.
      rewrite //= eqxx. simpl. reflexivity.
  - move=> i s1 s2 H H0.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    constructor.
  - move=> s1 t s1' H i s2 H0.
    inv H; inv H0.
    assert (cur_comp_of_event e \in domm (ParentAwareTree.prog_interface p)) as Hcomp by (now destruct H1).
    assert (next_comp_of_event e \in domm (ParentAwareTree.prog_interface p)) as Hcomp' by (now destruct H1).
    (* case: (H8 (cur_comp_of_event e) Hcomp) => [pa Hlocs]. *)
    (* case: (H8 (next_comp_of_event e) Hcomp') => [pa' Hlocs']. *)
    case: (H9 _ _ H4) => Htree.
    case: (H9  _ _ H5) => Htree'.
    simpl in Htree.
    destruct e as [Ccaller P z Ccallee | Ccallee z Ccaller]; simpl in *.
    + (* Call case *)
      exists 0; eexists; split.
      * left; econstructor.
        rewrite map_app in Htree'.
        specialize (H10 _ _ _ _ _ _ _ _ _ _ Htree') as [zs1' [zs2' Hcallee]].
        rewrite -map_app in Htree'.
        { econstructor.
          eauto. eauto.
          by [].
          by rewrite Htree map_app //.
          by rewrite Htree' map_app //.
          apply Hcallee.
          by []. by [].
        }
        by eapply star_refl.
        by [].
      * econstructor.
        -- move=> C ls0 H.
           fold add_caller.
           destruct (C == Ccallee) eqn:Heq.
           rewrite setmE Heq.
           move: H; rewrite setmE Heq // => [] [] ->.
           by move: Heq => /eqP ->.
           rewrite setmE Heq.
           destruct (C == Ccaller) eqn:Heq'.
           rewrite setmE Heq'.
           move: H; rewrite setmE Heq setmE Heq' // => [] [] ->.
           by move: Heq' => /eqP ->.
           move: H; rewrite setmE Heq setmE Heq' //.
           rewrite setmE Heq'.
           apply H9.
        -- move=> C1 P0 z0 C2 p1 n0 zs l0 ls0 l3; fold add_caller; move=> H.
           rewrite map_app in Htree'.
           destruct (H10 _ _ _ _ _ _ _ _ _ _ Htree') as [zs1' [zs2' Hcallee]].
           rewrite -map_app in Htree'.
           move: H.
           destruct (C2 == Ccallee) eqn:Heq.
           ++ rewrite setmE Heq => [] [] H.
              rewrite setmE Heq.
              apply map_eq_app in H as [ls1' [ls2' [? [? ?]]]].
              rewrite H.
              apply map_eq_cons in H2 as [ls3' [ls4' [? [? ?]]]].
              rewrite H2.
              exists (collect_callers Ccallee ls1'), (collect_callers Ccallee ls4').
              rewrite collect_callers_app collect_callers_cons.
              destruct ls3'. inversion H2. inversion H3. destruct p2. destruct p2. inversion H3. subst.
              unfold collect_callers; simpl. rewrite eq_sym Heq. reflexivity.
           ++ destruct (C2 == Ccaller) eqn:Heq'.
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 apply map_eq_app in H as [ls1' [ls2' [? [? ?]]]].
                 rewrite H.
                 apply map_eq_cons in H2 as [ls3' [ls4' [? [? ?]]]].
                 rewrite H2.
                 exists (collect_callers Ccaller ls1'), (collect_callers Ccaller ls4').
                 rewrite collect_callers_app collect_callers_cons.
                 destruct ls3'. inversion H3. inversion H3. destruct p2. destruct p2. inversion H12. subst.
                 unfold collect_callers; simpl. rewrite eq_sym Heq'. simpl. reflexivity.
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 eapply H10. eauto.
    + (* Return case *)
      exists 0; eexists; split.
      * left; econstructor.
        { eapply CallerAwareTree.step_ret.
          eauto. eauto.
          by [].
          by rewrite Htree map_app //.
          by rewrite Htree' map_app //.
          by []. by [].
        }
        by eapply star_refl.
        by [].
      * econstructor.
        -- move=> C ls0 H.
           fold add_caller.
           destruct (C == Ccaller) eqn:Heq.
           rewrite setmE Heq.
           move: H; rewrite setmE Heq // => [] [] ->.
           by move: Heq => /eqP ->.
           rewrite setmE Heq.
           destruct (C == Ccallee) eqn:Heq'.
           rewrite setmE Heq'.
           move: H; rewrite setmE Heq setmE Heq' // => [] [] ->.
           by move: Heq' => /eqP ->.
           move: H; rewrite setmE Heq setmE Heq' //.
           rewrite setmE Heq'.
           apply H9.
        -- move=> C1 P0 z0 C2 p1 n0 zs l0 ls0 l3; fold add_caller; move=> H.
           (* rewrite map_app List.map_cons in Htree'; simpl in Htree'. *)
           (* destruct (H9 _ _ _ _ _ _ _ _ _ _ Htree') as [zs1' [zs2' Hcallee]]. *)
           (* rewrite -map_app in Htree'. *)
           move: H.
           destruct (C2 == Ccaller) eqn:Heq.
           ++ rewrite setmE Heq => [] [] H.
              rewrite setmE Heq.
              apply map_eq_app in H as [ls1' [ls2' [? [? ?]]]].
              rewrite H.
              apply map_eq_cons in H2 as [ls3' [ls4' [? [? ?]]]].
              rewrite H2.
              exists (collect_callers Ccaller ls1'), (collect_callers Ccaller ls4').
              rewrite collect_callers_app collect_callers_cons.
              destruct ls3'. inversion H3. inversion H3. destruct p2. destruct p2. inversion H12. subst.
              unfold collect_callers; simpl. rewrite eq_sym Heq; simpl. reflexivity.
           ++ destruct (C2 == Ccallee) eqn:Heq'.
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 apply map_eq_app in H as [ls1' [ls2' [? [? ?]]]].
                 rewrite H.
                 apply map_eq_cons in H2 as [ls3' [ls4' [? [? ?]]]].
                 rewrite H2.
                 exists (collect_callers Ccallee ls1'), (collect_callers Ccallee ls4').
                 rewrite collect_callers_app collect_callers_cons.
                 destruct ls3'. inversion H3. inversion H3. destruct p2. destruct p2. inversion H12. subst.
                 unfold collect_callers; simpl. rewrite eq_sym Heq'. simpl. reflexivity.
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 eapply H10. eauto.
Qed.

Definition simpl_stack (st: stack): seq Component.id :=
  List.map fst st.

Inductive reaches_corresponding_return_at: nat -> NMap (list call_return_tree) -> trace -> (nat * Z * nat) -> Prop :=
| reaches_call: forall k (trees: NMap (list call_return_tree)) C1 P z' C2 t p z n
                  l1 p1 rts1 n1 cls1 ls1 l1'
                  l2 p2 rts2 n2 cls2 ls2 l2',
    trees C1 = Some (l1 ++ node (p1, XECall C1 P z' C2 rts1, n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XECall C1 P z' C2 rts2, n2, cls2) ls2 :: l2') ->
    reaches_corresponding_return_at (S k) (setm (setm trees C1 ls1) C2 ls2) t (p, z, n) ->
    reaches_corresponding_return_at k trees (ECall C1 P z C2 :: t) (p, z, n)
| reaches_ret: forall k (trees: NMap (list call_return_tree)) C1 z C2 t p n
                 l1 cls ls1 l1',
    trees C2 = Some (l1 ++ node (p, XERet C1 z C2, n, cls) ls1 :: l1') ->
    reaches_corresponding_return_at k trees (ERet C1 z C2 :: t) (p, z, n)
.

Fixpoint get_in_stack_at (k: nat) (st: stack): option (Component.id * possible_returns) :=
  match st, k with
  | [], _ => None
  | (C, rts) :: st', 0 => Some (C, rts)
  | _ :: st', S k' => get_in_stack_at k' st'
  end.
Definition in_stack_at k st '(C, rts) :=
  get_in_stack_at k st = Some (C, rts).


Inductive returns_at: nat -> NMap (list call_return_tree) -> trace -> (nat * Z * nat) -> Prop :=
| returns_at_zero: forall (trees: NMap (list call_return_tree)) C1 z C2 t p n
                 l1 cls ls1 l1',
    trees C2 = Some (l1 ++ node (p, XERet C1 z C2, n, cls) ls1 :: l1') ->
    returns_at 0 trees (ERet C1 z C2 :: t) (p, z, n)
| returns_at_call: forall k (trees: NMap (list call_return_tree)) C1 P z' C2 t p z n
                    l1 p1 cls1 ls1 l1' n1 rts1
                    l2 p2 cls2 ls2 l2' n2 rts2,
    trees C1 = Some (l1 ++ node (p1, XECall C1 P z' C2 rts1, n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XECall C1 P z' C2 rts2, n2, cls2) ls2 :: l2') ->
    returns_at (S k) (setm (setm trees C1 ls1) C2 ls2) t (p, z, n) ->
    returns_at k trees (ECall C1 P z' C2 :: t) (p, z, n)
| returns_at_ret: forall k (trees: NMap (list call_return_tree)) C1 z' C2 t p z n
                    l1 p1 cls1 ls1 l1' n1
                    l2 p2 cls2 ls2 l2' n2,
    trees C1 = Some (l1 ++ node (p1, XERet C1 z' C2, n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XERet C1 z' C2, n2, cls2) ls2 :: l2') ->
    returns_at k (setm (setm trees C1 ls1) C2 ls2) t (p, z, n) ->
    returns_at (S k) trees (ERet C1 z' C2 :: t) (p, z, n)
.


Definition invariant (trees: NMap (list call_return_tree)) (st: stack) (t: trace) :=
  forall k C rts p z n,
    in_stack_at k st (C, rts) ->
    returns_at k trees t (p, z, n) ->
    exists rts1 rts2, rts = rts1 ++ (p, z, n) :: rts2.

Inductive match_states4 (intf: Program.interface) (i: nat): CallerAwareTree.state -> CallReturnTree.state -> Prop :=
| match_states_4: forall t (trees: NMap (list caller_aware_tree)) (trees': NMap (list call_return_tree))
                    (locs: NMap nat) (callers: NMap (list (Z * nat))) (st: stack),
    (forall C ls, trees C = Some ls ->
             trees' C = Some (List.map build_call_return_tree ls)) ->
    wb_trace (simpl_stack st) t ->
    invariant trees' st t ->
    match_states4 intf i (t, trees, locs, callers) (t, trees', locs, callers, st)
.

Lemma helper1: forall l1'' l2'',
  ((fix get_corresp_returns_list (stack : nat) (ls0 : seq caller_aware_tree) {struct ls0} : seq caller_aware_tree :=
      match ls0 with
      | [::] => [::]
      | tr :: ls'0 => get_corresp_returns_tree stack tr ++ get_corresp_returns_list stack ls'0
      end) 1 (l1'' ++ l2'') = (fix get_corresp_returns_list (stack : nat) (ls0 : seq caller_aware_tree) {struct ls0} : seq caller_aware_tree :=
                                 match ls0 with
                                 | [::] => [::]
                                 | tr :: ls'0 => get_corresp_returns_tree stack tr ++ get_corresp_returns_list stack ls'0
                                 end) 1 l1'' ++ (fix get_corresp_returns_list (stack : nat) (ls0 : seq caller_aware_tree) {struct ls0} : seq caller_aware_tree :=
                                                   match ls0 with
                                                   | [::] => [::]
                                                   | tr :: ls'0 => get_corresp_returns_tree stack tr ++ get_corresp_returns_list stack ls'0
                                                   end) 1 l2'').
Proof. induction l1''.
       - reflexivity.
       - intros. simpl. rewrite IHl1''. rewrite <- app_assoc. reflexivity.
Qed.

Lemma sim4 (p: CallerAwareTree.prg):
  forward_simulation (CallerAwareTree.sem p) (CallReturnTree.sem (compile_caller_aware_tree p)).
Proof.
  fwd_sim (match_states4 (CallerAwareTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst.
    exists 0; eexists; split.
    + constructor.
      eauto.
    + rewrite initial_callers_same.
      econstructor.
      * move=> C ls H1.
        rewrite mapmE H1 //=.
      * simpl. now destruct H0. (* By well-formedness *)
      * unfold invariant.
        move=> k C rts p0 z n H1 H2.
        unfold initial_stack in H0.
        destruct k; simpl in H1; congruence.
  - move=> i s1 s2 H H0.
    inversion H; subst.
    inversion H0; subst.
    econstructor.
  - move=> s1 t s1' H i s2 H0.
    inv H; inv H0.
    + (* Call case *)
      assert (C1 \in domm (CallerAwareTree.prog_interface p)) as Hcomp by now destruct H1.
      case: (H11 _ _ H4) => Htree'.
      case: (H11 _ _ H3) => Htree.
      exists 0; eexists; split.
      * left; econstructor.
        econstructor; try now eauto.
        eauto.
        rewrite Htree map_app //=.
        rewrite Htree' map_app //=.
        apply star_refl.
        reflexivity.
      * econstructor.
        -- move=> C ls0.
           rewrite 4!setmE.
           destruct (C == C2); destruct (C == C1); try now move=> [] ->.
           eauto.
        -- assumption.
        -- unfold invariant in *.
           move=> k C rts p1 z0 n0 H H0.
           destruct k.
           ++ simpl in *.
              inv H.
              set (f := (fun x : t (nat * event * nat * seq (Z * nat)) =>
                           match x with
                           | leaf _ => (0, 0%Z, 0)
                           | node (lc, ECall _ _ _ _, _, _) _ => (0, 0%Z, 0)
                           | node (lc, ERet _ v _, i0, _) _ => (lc, v, i0)
                           end)).
              { inv H0.
                - inversion H12. move: H0 => /andP [] HC Hwb.
                  rewrite 2!setmE in H10.
                  assert (HnC: C0 == C2 = false).
                  { apply /eqP. move: HC => /eqP <-.
                    now destruct H1. }
                  rewrite HnC in H10. rewrite (eq_sym) in H10. rewrite HC in H10.
                  inversion H10.
                  apply map_eq_app in H0.
                  destruct H0 as [l1'' [l2'' [Heqlist [Heqmap1 Heqmap2]]]].
                  rewrite Heqlist.
                  rewrite helper1. rewrite map_app.
                  apply map_eq_cons in Heqmap2.
                  destruct Heqmap2 as [a [l3'' [Heqlist2 [Heqfun Heqmap]]]].
                  rewrite Heqlist2.
                  simpl. rewrite map_app.
                  unfold build_call_return_tree in Heqfun. destruct a as [| [[[]]]]; first inversion Heqfun.
                  destruct e; simpl in *. inversion Heqfun; subst.
                  inversion Heqfun; subst.
                  simpl. eexists; eexists; reflexivity.
                - (* This admitted result should hold by induction *)
                  admit.
              }
           ++ simpl in *.
              eapply H13. eauto.
              econstructor. rewrite map_app in Htree Htree'. eauto. rewrite map_app in Htree'. eauto.
              simpl.
              unfold build_call_return_tree in H0. eauto.
    + (* Return case *)
      assert (C2 \in domm (CallerAwareTree.prog_interface p)) as Hcomp by now destruct H1.
      case: (H10 _ _ H4) => Htree'.
      case: (H10 _ _ H3) => Htree.
      simpl in H11.
      assert (exists rts st', st = (C2, rts) :: st') as [rts [st' Hst]].
      { clear -H11.
        destruct st.
        - simpl in H11. congruence.
        - destruct p as [C rts].
          exists rts, st. simpl in H11.
          move: H11 => /andP [] /eqP -> _ //=. }
      rewrite Hst. rewrite Hst in H12.
      destruct (H12 0 C2 rts p' z n' Logic.eq_refl) as [rts1 [rts2 Heq_rts]].
      { econstructor. rewrite map_app in Htree'. eauto. }
      exists 0; eexists; split.
      * left; econstructor.
        (* clear Heq_rts. *)
        econstructor; eauto.
        now apply allowed_event_allowed_xevent.
        rewrite Htree map_app //=.
        rewrite Htree' map_app //=.
        (* Invariant:
         *)
        rewrite Heq_rts.
        eapply star_refl.
        reflexivity.
      * constructor.
        -- move=> C ls0.
           rewrite 4!setmE.
           destruct (C == C2); destruct (C == C1); try now move=> [] ->.
           eauto.
        -- rewrite Hst in H11. simpl in H11.
           move: H11 => /andP [] ? ?. assumption.
        -- unfold invariant.
           move=> k C rts0 p1 z0 n0 H H0.
           specialize (H12 (S k) C rts0 p1 z0 n0).
           edestruct H12 as [rts3 [rts4 Heq_rts0]].
           simpl. assumption.
           econstructor. rewrite map_app in Htree. eauto. rewrite map_app in Htree'. eauto.
           eauto.
           eexists; eexists; eauto.
Admitted.

Inductive match_stacks: stack -> CS.stack -> Prop :=
| match_stacks_nil: match_stacks [] []
| match_stacks_cons: forall st s_stack C rts arg k,
    match_stacks st s_stack ->
    match_stacks ((C, rts) :: st) (CS.Frame C arg k :: s_stack).

Inductive match_states5 (intf: Program.interface) (p: TreeWithCallers.prg) (ge: TreeWithCallers.genv) (i: nat): CallReturnTree.state -> TreeWithCallers.state -> Prop :=
| match_states_5: forall t (trees: NMap (list call_return_tree))
                    (locs: NMap nat) (callers: NMap (list (Z * nat))) (st: stack) cs,
    forall (CUR_LOC: forall C n, locs C = Some n ->
                Memory.load (CS.s_memory cs) (location C) = Some (Int (Z.of_nat n)))
      (CUR_INT: forall C, C \in domm intf ->
          Memory.load (CS.s_memory cs) (intcall C) = some (Int 1%Z))
      (CUR_COMP: forall C, next_comp t = Some C ->
                      CS.s_component cs = C)
      (CALLERS: forall C zs, callers C = Some zs ->
                        unique_key zs)
      (STACK: match_stacks st (CS.s_stack cs))
      (MEM: forall C, C \in domm intf ->
                 exists z, Memory.load (CS.s_memory cs) (ret C) = Some (Int z))

      (CONT: CS.s_cont cs = Kstop)
      (CONT': forall F, In F (CS.s_stack cs) -> CS.f_cont F = Kstop),
      match_states5 intf p ge i (t, trees, locs, callers, st)
                  {| TreeWithCallers.ghost_state := (t, trees, locs, callers, st);
                     TreeWithCallers.concrete_state := cs;
                     TreeWithCallers.can_silent := false |}
.

Lemma helper2: forall (A B C: eqType) (a a': A) (b b': B) (c c': C), a <> a' -> ((a, b, c) == (a', b', c')) = false.
Proof.
  move=> A B C a a' b b' c c' H.
  apply /pair_eqP. intros Hcontra. inversion Hcontra. contradiction.
Qed.


Lemma helper2': forall (A B C: eqType) (a a': A) (b b': B) (c c': C), c <> c' -> ((a, b, c) == (a', b', c')) = false.
Proof.
  move=> A B C a a' b b' c c' H.
  apply /pair_eqP. intros Hcontra. inversion Hcontra. contradiction.
Qed.

Lemma compiled_expr_callers: forall (p: CallReturnTree.prg) C P call_exp ge,
    ge = globalenv (TreeWithCallers.sem (compile_call_return_tree p)) ->
    find_procedure (genv_procedures ge) C P = Some call_exp ->
    call_exp = guard_call (callexp (get_all_handle_calls C P (CallReturnTree.prog_trees p C))).
Proof.
  move=> p C P call_exp ge ->.
  rewrite /find_procedure //= mapimE.
  case: (CallReturnTree.prog_interface p C) => //= Ciface.
  rewrite mkfmapfE.
  case: (P \in (if C == Component.main then (Procedure.main |: Component.export Ciface)%fset else Component.export Ciface));
    move=> //=.
  move=> [] <- //=.
Qed.

(* Admitted: Unicity lemma *)
Lemma wf_trees_unique_key: forall C P p,
    TreeWithCallers.wf p ->
    unique_key (get_all_handle_calls C P (TreeWithCallers.prog_trees p C)).
Proof.
  move=> C P p H.
  unfold get_all_handle_calls.
  destruct (TreeWithCallers.prog_trees p C); last first.
  unfold unique_key; intros. destruct ls1; inversion H0.
  unfold unique_key.
  move=> ls1 a1 b1 ls2 a2 b2 ls3 H0.
Admitted.

(* Admitted: Well-formedness lemma *)
Lemma find_proc_callers (p: CallReturnTree.prg): forall C P,
    find_procedure (mapim
                      (fun (C : nat) (Ciface : Component.interface) => mkfmapf ((comp_call_handle C)^~ (CallReturnTree.prog_trees p C))
                                                                          (if C == Component.main then (Procedure.main |: Component.export Ciface)%fset else Component.export Ciface)) (CallReturnTree.prog_interface p)) C P =
    Some (guard_call (callexp (get_all_handle_calls C P (CallReturnTree.prog_trees p C)))).
Proof.
Admitted.


Lemma sim5 (p: CallReturnTree.prg) (wf: CallReturnTree.wf p):
  forward_simulation (CallReturnTree.sem p) (TreeWithCallers.sem (compile_call_return_tree p)).
Proof.
  pose (p' := compile_call_return_tree p).
  assert (WF: TreeWithCallers.wf p').
  eapply comp_is_well_formed; eauto.
  pose (ge := globalenv (TreeWithCallers.sem (compile_call_return_tree p))).
  fwd_sim (match_states5 (CallReturnTree.prog_interface p) p' ge).
  - move=> s1 H.
    inv H.
    exists 0; eexists; split.
    + constructor.
      eauto.
    + econstructor.
      * move=> C n //=.
        rewrite /Memory.load /TreeWithCallers.initial_memory /initial_locs 2!mkfmapfE.
        case: (C \in domm (CallReturnTree.prog_interface p)) => [[] | ]; last by [].
        move=> <- //=.
        rewrite ComponentMemory.load_prealloc //=.
      * move=> C //=.
        rewrite /Memory.load /TreeWithCallers.initial_memory /initial_locs mkfmapfE => -> //=.
        rewrite ComponentMemory.load_prealloc //=.
      * move=> C H. simpl.
        destruct H0. destruct H1. destruct H2. congruence.
      * unfold compile_call_return_tree. simpl.
        (* Unicity result: this holds because in that case, zs is a subset of all the caller information,
         which satisfy unicity by [wf_trees_unique_key] *)
        admit.
      * constructor.
      * move=> C H.
        simpl. unfold TreeWithCallers.initial_memory.
        exists (Z.of_nat 0). simpl. unfold Memory.load. simpl.
        rewrite mkfmapfE H. rewrite ComponentMemory.load_prealloc //=.
      * reflexivity.
      * simpl. move=> F H. contradiction.

  - move=> i s1 s2 H H0.
    inv H; inv H0.
    constructor.
  - move=> s1 t s1' H i s2 H0.
    inv H; inv H0.
    + (* Call case *)
      destruct cs as [? ? ? ? ? ?].
      specialize (CUR_COMP C1 Logic.eq_refl).
      destruct (Memory.store_after_load _ (C1, Block.local, 0%Z) _ (Int (Z.of_nat n)) (CUR_LOC _ _ H7)) as [m' Hm'].
      destruct (Memory.store_after_load m' (C2, Block.local, 0%Z) (Int (Z.of_nat p'0)) (Int (Z.of_nat n'))) as [m'' Hm''].
      rewrite (Memory.load_after_store _ _ _ _ _ Hm').
      rewrite helper2. eauto. move=> CONTRA; move: CONTRA H1 ->; now case.
      destruct (Memory.store_after_load m'' (C2, Block.local, 1%Z) (Int 1%Z) (Int 1%Z)) as [m''' Hm'''].
      rewrite (Memory.load_after_store _ _ _ _ _ Hm''). rewrite helper2'.
      rewrite (Memory.load_after_store _ _ _ _ _ Hm'). rewrite helper2'.
      simpl. eapply CUR_INT. now destruct H1. lia. lia.
      exists 0; eexists; split.
      * left; econstructor.
        -- simpl in *; subst.
           eapply TreeWithCallers.step_call with
               (call_exp := guard_call (callexp (get_all_handle_calls C2 P (CallReturnTree.prog_trees p C2))));
                            eauto.
           eapply find_proc_callers.
        -- eapply star_trans.
           ++ destruct (TreeWithCallers.wf_has_trees WF) with (C := C2). now destruct H1.
              eapply call_handling_expression_correct. eauto.
              eapply wf_trees_unique_key; eauto.
              eapply CALLERS. eauto. eauto.
              (* Admitted: Unicity lemma that again relates to subtrees *)
              eapply callers_in_subtrees; admit.
              simpl; eauto. simpl; eauto.
              erewrite (Memory.load_after_store _ _ _ _ _ Hm'). simpl.
              rewrite helper2. eauto. move=> CONTRA; move: CONTRA H1 ->; now case.
              erewrite (Memory.load_after_store _ _ _ _ _ Hm'). simpl.
              rewrite helper2. eapply CUR_INT. now destruct H1. destruct H1 as [[] ]; congruence.
              simpl. eauto.
           ++ do 4 (take_step; eauto; [econstructor | eauto]); simpl. eauto. eauto.
              simpl in *; subst. simpl. unfold update_can_silent. simpl.
              do 8 (take_step; eauto; [econstructor | eauto]); simpl. eauto. eauto.
              eapply star_refl.
           ++ reflexivity.
        -- rewrite -CUR_COMP. reflexivity.
      * rewrite -CUR_COMP.
        simpl. simpl in CONT. rewrite CONT.
        unfold update_can_silent. simpl.
        econstructor.

        -- move=> C n0 H.
           simpl.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'''); simpl. rewrite helper2'; last lia.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm''); simpl.
           move: H; rewrite 2!setmE.
           destruct (C == C2) eqn:Heq. move: Heq => /eqP -> => [] [] ->.
           unfold location; rewrite eqxx. eauto.
           destruct (C == s_component) eqn:Heq'.
           move: Heq' => /eqP -> => [] [] <-. simpl in CUR_COMP. rewrite CUR_COMP.
           rewrite helper2.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl.
           rewrite /location eqxx. eauto. now destruct H1 as [[] ].
           move=> H. move: Heq => /eqP Heq. rewrite helper2.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl.
           rewrite /location.
           move: Heq' => /eqP Heq'. rewrite helper2.
           eauto. simpl in CUR_COMP. congruence. eauto.
        -- move=> C H.
           simpl.
           destruct (C == C2) eqn:HC2.
           ++ move: HC2 => /eqP HC2. rewrite HC2.
              rewrite (Memory.load_after_store_eq _ _ _ _ Hm'''). reflexivity.
           ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''').
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'').
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm').
              eapply CUR_INT. eauto.
              apply /eqP; rewrite helper2'; eauto; lia.
              apply /eqP; rewrite helper2'; eauto; lia.
              move: HC2 => /eqP HC2. rewrite /intcall. apply /eqP. rewrite helper2. auto. congruence.
        -- move=> C H. simpl in *.
           destruct t0; first inversion H.
           inv H. inv SEQOK. reflexivity.
        -- move=> C zs0 H.
           (* Admitted: unicity result *)
           admit.
        -- simpl in *.
           econstructor. destruct H1 as [[] ]; congruence.
        -- move=> C H.
           destruct (MEM C) as [oldz Holdz].
           eauto. exists oldz; simpl.
           rewrite (Memory.load_after_store_neq m'' _ (Int 1%Z) m''' _ _ Hm''').
           rewrite (Memory.load_after_store_neq m' _ (Int (Z.of_nat n')) m'' _ _ Hm'').
           rewrite (Memory.load_after_store_neq s_memory _ _ m' _ _ Hm'). eauto.
           apply /eqP; rewrite helper2'. reflexivity. congruence.
           apply /eqP; rewrite helper2'. reflexivity. congruence.
           apply /eqP; rewrite helper2'. reflexivity. congruence.
        -- simpl. reflexivity.
        -- simpl. move=> F [H | H].
           ++ simpl in *. rewrite <- H. eauto.
           ++ eauto.

    + (* Return case *)
      destruct cs as [? ? ? ? ? ?].
      specialize (CUR_COMP C1 Logic.eq_refl).
      destruct (Memory.store_after_load _ (C1, Block.local, 0%Z) (Int (Z.of_nat p0)) (Int (Z.of_nat n)) (CUR_LOC _ _ H5)) as [m' Hm'].
      destruct (MEM C2) as [oldz Holdz]. now destruct H1.
      destruct (Memory.store_after_load m' (ret C2)  (Int oldz) (Int z)) as [m'' Hm''].
      rewrite (Memory.load_after_store _ _ _ _ _ Hm').
      rewrite helper2'. eauto. congruence.
      destruct (Memory.store_after_load m'' (C2, Block.local, 0%Z) (Int (Z.of_nat p'0)) (Int (Z.of_nat n'))) as [m''' Hm'''].

      { rewrite (Memory.load_after_store _ _ _ _ _ Hm'').
        rewrite helper2'.
        rewrite (Memory.load_after_store _ _ _ _ _ Hm').
        assert (Hloc: (C2, Block.local, 0%Z) == (C1, Block.local, 0%Z) = false).
        { assert (C2 <> C1). destruct H1. congruence.
          apply /pair_eqP; intros Hcontra. inversion Hcontra. contradiction. }
        rewrite Hloc; simpl. eauto. congruence. }
      inversion STACK; subst; clear STACK.
      exists 0; eexists; split.
      * left.
        eapply plus_right.
        econstructor.
        -- simpl in *; subst.
           eapply TreeWithCallers.step_ret with (C1 := s_component) (C2 := C2); eauto.
        -- reflexivity.
      * econstructor.
        -- move=> C n0 H; simpl in *.

           move: H; rewrite 2!setmE.
           destruct (C == C2) eqn:Heq. rewrite Heq.
           move => [] [] <-.
           move: Heq => /eqP ->.
           erewrite Memory.load_after_store_eq. reflexivity. eapply Hm'''.
           rewrite Heq. move: Heq => Hneq.
           destruct (C == s_component) eqn:Heq.
           move: Heq => /eqP Heq. rewrite Heq eqxx //=.
           move=> [] [] <-.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'''); simpl. rewrite helper2.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm''); simpl. rewrite helper2.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl.
           move: Heq => /eqP Hneq'. rewrite eqxx. reflexivity.
           move: Hneq => /eqP Hneq; congruence.
           move: Hneq => /eqP Hneq; congruence.
           rewrite Heq. move: Hneq => /eqP Hneq; move: Heq => /eqP Heq.
           intros Hloc.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'''); simpl. rewrite helper2; last congruence.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm''); simpl. rewrite helper2; last congruence.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl. rewrite helper2; last congruence.
           eapply CUR_LOC. eauto.
        -- move=> C H. simpl in *.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'''); simpl. rewrite helper2'; last congruence.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm''); simpl. rewrite helper2'; last congruence.
           rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl. rewrite helper2'; last congruence.
           eapply CUR_INT. eauto.
        -- move=> C H. simpl in *.
           destruct t0; inversion H. congruence.
        -- (* Admitted: unicity result *)
          admit.
        -- eauto.
        -- move=> C H.
           destruct (C2 == C) eqn:Heq.
           ++ exists z. move: Heq => /eqP <-. simpl.
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''').
              eapply Memory.load_after_store_eq. apply Hm''. unfold ret; congruence.
           ++ destruct (MEM C) as [oldz' Holdz']. eauto.
              exists oldz'; simpl.
              rewrite (Memory.load_after_store_neq m'' _ _ m''' _ _ Hm''').
              rewrite (Memory.load_after_store_neq m' _ _ m'' _ _ Hm'').
              rewrite (Memory.load_after_store_neq s_memory _ _ m' _ _ Hm'). eauto.
              simpl. unfold ret; congruence.
              move: Heq => /eqP Heq. unfold ret; congruence.
              unfold ret; congruence.
        -- simpl. simpl in CONT. eauto.
        -- move=> F H.
           simpl in *.
           apply CONT'. rewrite <- H0. right. eauto.
Admitted.

Inductive match_concrete_stacks: Component.id -> stack -> CS.stack -> Prop :=
| match_concrete_stacks_nil: forall C, match_concrete_stacks C [] []
| match_concrete_stacks_int: forall C s st old_arg,
    match_concrete_stacks C s st ->
    match_concrete_stacks C s (CS.Frame C old_arg Kstop :: st)
| match_concrete_stacks_ext: forall C C' rts s st old_arg,
    C <> C' ->
    match_concrete_stacks C' s st ->
    match_concrete_stacks C ((C', rts) :: s) (CS.Frame C' old_arg (Kassign1 (RETURN_p)
                                                       (Kseq ((E_seq (return_handling_expression rts)
                                                                     (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                                            (E_call C' Procedure.main (E_val (Int (Z.of_nat 0)))))))
                                                             Kstop)) :: st)
.

Lemma unfold_stack: forall ge C1 C2 rts st stack m z arg,
    match_concrete_stacks C1 ((C2, rts) :: st) stack ->
    exists stack' stack'' arg' arg'',
      stack' = CS.Frame C2 arg'
                        (Kassign1 RETURN_p
                                  (Kseq (E_seq (return_handling_expression rts)
                                               (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                      (E_call C2 Procedure.main (E_val (Int (Z.of_nat 0)))))) Kstop))
                        :: stack''
      /\ match_concrete_stacks C2 st stack''
      /\ star CS.kstep ge [CState C1, stack, m, Kstop, E_val (Int z), arg] E0
             [CState C1, stack', m, Kstop, E_val (Int z), arg''].
Proof.
  move=> ge C1 C2 rts st stack m z arg H.
  remember ((C2, rts):: st) as st0.
  generalize dependent arg.
  induction H; intros.
  - inversion Heqst0.
  - specialize (IHmatch_concrete_stacks Heqst0) as
        [stack1 [stack2 [arg1 [arg2 [IH1 [IH2 IH3]]]]]].
    subst.
    eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + take_step. eauto. eapply IH3.
  - inv Heqst0.
    eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + eapply star_refl.
Qed.

(* Admitted: match_cont k1 k2 when
  k2 is k1 where the Kstop continuation is replaced by the continuation that corresponds
  to what follows the call-handler *)
Axiom match_cont: cont -> cont -> Prop.
Lemma match_cont_step: forall ge cs1 k cs1' cs2,
    cs2 = [CState (CS.s_component cs1), CS.s_stack cs1, CS.s_memory cs1, k, CS.s_expr cs1, CS.s_arg cs1] ->
    match_cont (CS.s_cont cs1) k ->
    CS.kstep ge cs1 E0 cs1' ->
    exists k',
    CS.kstep ge cs2 E0
             [CState (CS.s_component cs1'), CS.s_stack cs1', CS.s_memory cs1', k', CS.s_expr cs1', CS.s_arg cs1']
               /\ match_cont (CS.s_cont cs1') k'.
Proof.
Admitted.
Lemma match_cont_Kstop: match_cont Kstop Kstop.
Admitted.


Variant match_states6 (p: TreeWithCallers.prg) (ge: global_env) (i: nat): TreeWithCallers.state -> CS.state -> Prop :=
| match_states_initial: forall s s',
    TreeWithCallers.initial p s ->
    CS.initial_state (compile_tree_with_callers p) s' ->
    match_states6 p ge i s s'
| match_states_silent: forall gs cs cs' t trees locs cls st,
    gs = (t, trees, locs, cls, st) ->
    forall (COMP: CS.s_component cs = CS.s_component cs')
      (STACK: match_concrete_stacks (CS.s_component cs') st (CS.s_stack cs'))
      (MEM: CS.s_memory cs = CS.s_memory cs')
      (CONT: match_cont (CS.s_cont cs) (CS.s_cont cs'))
      (EXPR: CS.s_expr cs =  CS.s_expr cs')
      (ARG: CS.s_arg cs = CS.s_arg cs'),
      match_states6 p ge i {| TreeWithCallers.ghost_state := gs;
                              TreeWithCallers.concrete_state := cs;
                              TreeWithCallers.can_silent := true |} cs'
| match_states_6: forall gs cs cs' t trees locs cls st,
    gs = (t, trees, locs, cls, st) ->
    forall (COMP: CS.s_component cs = CS.s_component cs')
      (STACK: match_concrete_stacks (CS.s_component cs') st (CS.s_stack cs'))
      (MEM: CS.s_memory cs = CS.s_memory cs')
      (CONT: CS.s_cont cs' = Kstop)
      (EXPR: CS.s_expr cs' = build_event_expression (CS.s_component cs') (TreeWithCallers.prog_trees p (CS.s_component cs')))
      (ARG: CS.s_arg cs = CS.s_arg cs'),
      match_states6 p ge i {| TreeWithCallers.ghost_state := gs;
                              TreeWithCallers.concrete_state := cs;
                              TreeWithCallers.can_silent := false |} cs'.
Module Src.

  (* We use this simplified definition of the source semantics *)

  Definition sem (p: program) :=
    {| state := CS.state;
       genvtype := global_env;
       step := CS.kstep;
       initial_state := CS.initial_state p;
       final_state := fun s => True;
       globalenv := prepare_global_env p |}.


End Src.

(* Four well-formedness results *)
Lemma find_procedure_find (p: TreeWithCallers.prg):
  forall C P,
    find_procedure (genv_procedures (prepare_global_env (compile_tree_with_callers p))) C P =
    Some (E_seq (comp_call_handle C P (TreeWithCallers.prog_trees p C))
                (build_event_expression C (TreeWithCallers.prog_trees p C))).
Admitted.

Lemma find_proc_some (p: TreeWithCallers.prg):
  forall C P call_exp,
  find_procedure (TreeWithCallers.prog_procedures p) C P = Some call_exp ->
  call_exp = comp_call_handle C P (TreeWithCallers.prog_trees p C).
Admitted.

Lemma find_main (p: TreeWithCallers.prg):
  prog_main (compile_tree_with_callers p) =
  Some (E_seq (comp_call_handle Component.main Procedure.main (TreeWithCallers.prog_trees p Component.main))
              (build_event_expression Component.main (TreeWithCallers.prog_trees p Component.main))).
Admitted.

Lemma initial_buffers: forall p C,
    Memory.load (prepare_buffers (compile_tree_with_callers p)) (C, Block.local, (0 + 1)%Z) = Some (Int 0).
  move=> p C.
  unfold prepare_buffers. simpl.
Admitted.



(* Admitted, but we are very close to completing it. The goals are all admitted, but  *)
Lemma sim6 (p: TreeWithCallers.prg):
  forward_simulation (TreeWithCallers.sem p) (Src.sem (compile_tree_with_callers p)).
Proof.
  pose (p_compiled := compile_tree_with_callers p).
  pose (ge := globalenv (CS.sem p_compiled)).
  fwd_sim (match_states6 p ge).
  - move=> s1 H.
    exists 0; exists (CS.initial_machine_state (compile_tree_with_callers p)).
    split.
    + rewrite /CS.initial_state //=.
    + constructor; [by [] | rewrite /CS.initial_state //=].
  - move=> i s1 s2 H H0. reflexivity.
  - move=> s1 t s1' H i [? ? ? ? ? ?] H0.
    inv H.
    + (* Step call *)
      inv H0.
      * simpl in *; subst.
        unfold CS.initial_state in H2.
        unfold CS.initial_machine_state in H2.
        rewrite find_main in H2. inversion H2; subst.
        destruct (Memory.store_after_load (prepare_buffers (compile_tree_with_callers p))
                                          (Component.main, Block.local, 1%Z) (Int 0) (Int 1)) as [m'' MEM''].
        eapply initial_buffers. simpl.
        eexists; eexists; split.
        admit. admit.
        (* -- left. *)
        (*    eapply star_plus_trans. *)
        (*    do 10 take_step. eauto. eapply initial_buffers. *)
        (*    do 11 take_step. eauto. simpl. eauto. *)
        (*    take_step. *)
        (*    eapply build_event_expression_correct. simpl; eauto. simpl. *)
        (*    (* Well-formedness result *) *)
        (*    admit. *)
        (*    reflexivity. simpl in *. *)
        (*    (* Idem *) *)
        (*    admit. *)
        (*    simpl. reflexivity. *)
        (*    eapply call_event_correct. *)
        (*    simpl; eauto. *)
        (*    (* Well-formedness result: the execution always starts in Main *) *)
        (*    admit. *)
        (*    simpl; eauto. admit. *)
        (*    eapply find_procedure_find. *)
        (*    simpl. admit. *)
        (*    eauto. reflexivity. *)
        (* -- simpl in *. *)
        (*    eapply match_states_silent; simpl; eauto. *)
        (*    econstructor; eauto. now destruct H1 as [[] []]; congruence. *)
        (*    admit. *)
        (*    apply match_cont_Kstop. *)
        (*    admit. *)

      * simpl in *; subst.
        eexists; eexists; split.
        -- left.
           eapply star_plus_trans.
           (* Using this lemma requires a unicity result *)
           eapply build_event_expression_correct; admit.
           admit. reflexivity.
        -- eapply match_states_silent; admit.
    + (* Step return *)
      (* destruct (Memory.store_after_load m''' (C1, Block.local, 1%Z) (Int (Z.of_nat 0)) (Int (Z.of_nat 1))) as [m'''' Hm'''']. *)
      admit.
    + (* Step silent *)
      (* destruct s2 as [? ? ? ? ? ?]. *) simpl in *.
      (* Rely on match_cont *)
      admit.
Admitted.

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

Require Import Coq.Logic.FunctionalExtensionality.

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
    (forall C ls, trees C = Some ls -> exists n, trees' C = Some (give_num_list ls n).1) ->
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
      destruct (give_nums_app_comm l1 l2 (loc_ev_out_of_event e) ls n) as [? [? [? Heq]]].
    destruct (H6 _ _ H5) as [n' Htree'];
      destruct (give_nums_app_comm l1' l2' (loc_ev_in_of_event e) ls' n') as [? [? [? Heq']]].
    exists 0; eexists.
    split.
    + left. econstructor.
      { econstructor.
        eauto.
        eauto.
        reflexivity. reflexivity.
        now rewrite Htree Heq.
        now rewrite Htree' Heq'.
        now eapply give_nums_determinate.
        now eapply give_nums_determinate.
      }
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

Lemma det_tree_list_add_parent_loc:
  forall ls,
    determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls ->
    forall n,
      determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) (List.map (fun tr => add_parent_loc tr n) ls).
Proof.
  induction ls using tree_ind_list with (P := fun tr => determinate_tree (fun '(e1, _) '(e2, _) => e1 = e2) tr ->
                                                     forall n, determinate_tree (fun '(_, e1, _) '(_, e2, _) => e1 = e2) (add_parent_loc tr n)).
  - now constructor.
  - move=> H n; split; eauto.
    ++ by move=> [].
    ++ by move=> ? [].
  - move=> H n.
    case: a H => e n' //= H.
    inv H.
    assert (DET: determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls) by now split.
    destruct (IHls DET n') as [IH1 IH2].
    now constructor.
  - move=> H n.
    simpl.
    have: (determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls).
    { inv H. split.
      - move=> p p' ? ? ? ? nth nth' EQ.
        specialize (H0 (S p) (S p') _ _ _ _ nth nth' EQ); now inversion H0.
      - move=> tr' IN.
        now specialize (H1 tr' (or_intror IN)). }
    (* move=> DET; specialize (IHls0 DET n). *)
    assert (forall ls p x y z l, nth_error (List.map (add_parent_loc^~ n) ls) p = Some (node (x, y, z) l) ->
                            exists l',
                              nth_error ls p = Some (node (y, z) l') /\ l = List.map (add_parent_loc^~ z) l') as nth_add_parent_loc_inv.
    { clear.
      induction ls.
      - by move=> [].
      - move=> [| p] x y z l H.
        + simpl in H. inv H.
          destruct a as [| [y' z'] l']; first by inv H1.
          simpl in H1; inv H1; eexists; split; simpl; eauto.
        + specialize (IHls p x y z l H) as [l' [EQ1 EQ2]].
          exists l'; split; eauto.
    }
    move=> DET.
    split.
    + move=> p p' [[? ?] ?] ? [[? ?] ?] ? nth nth' EQ; eauto.
        replace (add_parent_loc tr n :: List.map (add_parent_loc^~ n) ls)
          with (List.map (add_parent_loc^~ n) (tr :: ls)) in nth; last reflexivity.
        apply nth_add_parent_loc_inv in nth as [l [EQl _]].
        replace (add_parent_loc tr n :: List.map (add_parent_loc^~ n) ls)
          with (List.map (add_parent_loc^~ n) (tr :: ls)) in nth'; last reflexivity.
        apply nth_add_parent_loc_inv in nth' as [l' [EQl' _]].

        destruct H as [UNIQ ?]. eapply UNIQ; simpl; eauto.
    + move=> tr0 [EQ | INR].
      * subst.
        eapply IHls.
        inversion H. eapply H1. now left.
      * specialize (IHls0 DET n).
        inversion IHls0.
        eapply H1. eauto.
Qed.

Lemma sim2 (p: NumberedTree.prg):
  forward_simulation (NumberedTree.sem p) (ParentAwareTree.sem (compile_numbered_tree p)).
Proof.
  fwd_sim (match_states2 (NumberedTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor.
      eauto.
      intros C.
      rewrite /compile_numbered_tree //= mapmE.
      case: ((NumberedTree.prog_trees p C)) => //=.
      intros. inversion H.
      { clear H.
        revert l1 p0 xe n ls l2 H2.
        induction a.
        now destruct l1.
        intros.
        destruct l1. simpl in H2. inversion H2; subst.
        destruct a as [| [[]]]; inversion H1; eauto.
        simpl in H2. inversion H2.
        eapply IHa. eauto.
      }
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
          by []. by [].
          by eapply det_tree_list_add_parent_loc.
          by eapply det_tree_list_add_parent_loc.
      }
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
                    (locs: NMap nat) (callers: NMap (list (Procedure.id * Z * nat))),
    (forall C ls, trees C = Some ls ->
              trees' C = Some (List.map (add_caller C) ls)) ->
    (forall P z C2 p n zs l1 ls l2,
              trees' C2 = Some (l1 ++ node (p, ECallIn P z, n, zs) ls :: l2) ->
              exists zs1 zs2, callers C2 = Some (zs1 ++ (P, z, n) :: zs2)) ->
    forall UNIQ: (forall C zs, callers C = Some zs ->
                     unique_p_z zs),
    match_states3 intf i (t, trees, locs) (t, trees', locs, callers)
.



Lemma det_unique_z: forall C ls,
    determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) ls ->
    unique_p_z (collect_callers C ls).
Proof.
  intros C.
  induction ls using tree_ind_list with (P := fun tr => determinate_tree (fun '(_, e1, _) '(_, e2, _) => e1 = e2) tr ->
                                                     match tr with
                                                     | leaf _ => True
                                                     | node x ls => unique_p_z (collect_callers C ls)
                                                     end).

  - by [].
  - by move=> H [] //=.
  - move=> H. inversion H; subst; clear H.
    by eapply IHls; eauto.
  - case: tr IHls IHls0 => //=.
    + move=> H1 H2 H3.
      unfold collect_callers. simpl. eapply H2.
      inversion H3.
      constructor.
      * intros ? ? ? ? ? ? nth1 nth2 EQ.
        now specialize (H (S _) (S _) _ _ _ _ nth1 nth2 EQ); inversion H.
      * intros ? ?. eapply H0. now right.
    + move=> a l H1 H2 H3.
      have: (determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) ls).
      { inv H3. split.
      - move=> p p' ? ? ? ? nth nth' EQ.
        specialize (H (S p) (S p') _ _ _ _ nth nth' EQ); now inversion H.
      - move=> tr' IN.
        now specialize (H0 tr' (or_intror IN)). }
      move: a l H1 H2 H3.

      assert (H: forall ls, exists f, injective f /\ forall p P z n, nth_error (collect_callers C ls) p = Some (P, z, n) ->
              exists b l, nth_error ls (f p) = Some (node (b, ECallIn P z, n) l)).
      { clear.
        induction ls.
        - exists id. split. eapply inj_id. by move=> [].
        - destruct IHls as [f [IH1 IH2]].
          destruct a as [| [[? e] ?]].
          + exists (fun n => S (f n)); split.
            * eapply inj_comp. eapply ssrnat.succn_inj.
              eapply IH1.
            * move=> p P z n H.
              specialize (IH2 p P z n H) as [b [l IH]].
              now (exists b, l).
          + destruct e as [| | |].
            * exists (fun n => match n with
                       | 0 => 0
                       | S n' => S (f n')
                       end); split; eauto.
                   (* if n == 0 then 0 else S (f n)); split; eauto. *)
              -- clear -IH1.
                 intros x1 x2.
                 induction x1.
                 ++ by case x2.
                 ++ case: x2 IHx1; first by [].
                    move=> n IHx1 H.
                    inversion H.
                    eapply IH1 in H1. now subst.
              -- move=> [| p] P z1 n1 H.
                 ++ inv H.
                    now (exists n, l).
                 ++ simpl in H.
                    specialize (IH2 p P z1 n1 H) as [b' [l' IH]].
                    now exists b', l'.
            * exists (fun n => S (f n)); split; eauto.
              eapply inj_comp. eapply ssrnat.succn_inj. eapply IH1.
            * exists (fun n => S (f n)); split; eauto.
              eapply inj_comp. eapply ssrnat.succn_inj. eapply IH1.
            * exists (fun n => S (f n)); split; eauto.
              eapply inj_comp. eapply ssrnat.succn_inj. eapply IH1.
      }
      intros ? ? H1 H2 H3 H4.
      destruct (H (node a l :: ls)) as [f [INJ H']].
      intros p p' P0 z n n' nth nth'.
      eapply H' in nth as [b1 [l1 EQ1]].
      eapply H' in nth' as [b1' [l1' EQ1']].
      destruct H3 as [UNIQ _].
      specialize (UNIQ _ _ _ _ _ _ EQ1 EQ1' Logic.eq_refl).
      now eapply INJ in UNIQ.
Qed.

Lemma sim3 (p: ParentAwareTree.prg) (WF: ParentAwareTree.wf p):
  forward_simulation (ParentAwareTree.sem p) (CallerAwareTree.sem (compile_parent_aware_tree p)).
Proof.
  assert (WF': CallerAwareTree.wf (compile_parent_aware_tree p)) by now eapply compile_parent_aware_tree_wf.
  fwd_sim (match_states3 (ParentAwareTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor.
      eauto.
      intros.
      assert (exists l1' ls' l2', ParentAwareTree.prog_trees p C = Some (l1' ++ node (p0, xe, n) ls' :: l2')) as [l1' [ls' [l2' EQ]]].
      clear -H.
      move: H => //=; rewrite mapimE; case: (ParentAwareTree.prog_trees p C) => //= a.
      elim: a l1.
      * now destruct l1.
      * intros.
        simpl in H0. destruct l1.
        -- inversion H0; subst.
           destruct a as [| [[]]]; inversion H2; subst.
           exists []; eexists; eexists; simpl; eauto.
        -- inversion H0; subst.
           specialize (H l1); rewrite H3 in H; specialize (H Logic.eq_refl) as [l1' [ls' [l2' EQ]]].
           inversion EQ; subst.
           exists (a :: l1'); eexists; eexists; simpl; eauto.
      * now eapply INIPARENT; eauto.
    + econstructor.
      (* move=> C H; exists 0; by rewrite mkfmapfE H. *)
      move=> C ls H; by rewrite mapimE H.
      move=> P z C2 p0 n zs l1 ls l2 H.
      remember (compile_parent_aware_tree p) as p'.
      (* unfold CallerAwareTree.initial_callers. *)
      rewrite mapimE H //=.
      rewrite DefSimLanguages.CallerAwareTree.collect_callers_initial_app
              DefSimLanguages.CallerAwareTree.collect_callers_initial_cons.
      eexists; eexists.
      unfold DefSimLanguages.CallerAwareTree.collect_callers_initial.
      rewrite //= eqxx. (* simpl. reflexivity. *)
      move=> C zs H.
      move: H => //=; rewrite 2!mapimE.
      move: (ParentAwareTree.determinacy WF) => /(_ C) //=.
      case: (ParentAwareTree.prog_trees p C) => [trs |] //= /(_ trs Logic.eq_refl) H [] <-.
      (* /(_ (List.map (add_caller C) trs) Logic.eq_refl) H [] <-. *)
      apply det_unique_z with (C := C) in H.
      unfold collect_callers in H. unfold DefSimLanguages.CallerAwareTree.collect_callers_initial.
      simpl. unfold CallerAwareTree.call_information_initial.
      rewrite List.map_map. unfold call_information in H.
      assert (EQ: (fun tr : parent_aware_tree => match tr with
                                                    | node (_, ECallIn P arg, n) _ => Some (P, arg, n)
                                                    | _ => None
                                          end) =
              (fun x : parent_aware_tree => match add_caller C x with
                                         | node (_, ECallIn P arg, n, _) _ => Some (P, arg, n)
                                         | _ => None
                                         end)
             ).
      { eapply functional_extensionality. intros [|[[? ?] ?] ?]; eauto. }
      now rewrite EQ in H.

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
        specialize (H10 _ _ _ _ _ _ _ _ _ Htree') as [zs1' [zs2' Hcallee]].
        rewrite -map_app in Htree'.
        { econstructor.
          eauto. eauto.
          by [].
          by rewrite Htree map_app //.
          by rewrite Htree' map_app //.
          apply Hcallee.
          by []. by [].
          by eapply det_tree_list_add_caller.
          by eapply det_tree_list_add_caller.
          eapply UNIQ. eauto.
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
        -- move=> P0 z0 C2 p1 n0 zs l0 ls0 l3; fold add_caller; move=> H.
           rewrite map_app in Htree'.
           destruct (H10 _ _ _ _ _ _ _ _ _ Htree') as [zs1' [zs2' Hcallee]].
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
              simpl. reflexivity.
              (* unfold collect_callers; simpl. rewrite eq_sym Heq. reflexivity. *)
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
                 unfold collect_callers; simpl. reflexivity.
                 (* rewrite eq_sym Heq'. simpl. reflexivity. *)
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 eapply H10. eauto.
        -- move=> C zs.
           rewrite 2!setmE.
           case: ifP => _.
           ++ move=> [] <-. by eapply det_unique_z.
           ++ case: ifP => _.
              ** move=> [] <-. by eapply det_unique_z.
              ** eapply UNIQ.

    + (* Return case *)
      exists 0; eexists; split.
      * left; econstructor.
        { eapply CallerAwareTree.step_ret.
          eauto. eauto.
          by [].
          by rewrite Htree map_app //.
          by rewrite Htree' map_app //.
          by []. by [].
          by eapply det_tree_list_add_caller.
          by eapply det_tree_list_add_caller.
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
        -- move=> P0 z0 C2 p1 n0 zs l0 ls0 l3; fold add_caller; move=> H.
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
              unfold collect_callers; simpl. reflexivity.
              (* rewrite eq_sym Heq; simpl. reflexivity. *)
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
                 unfold collect_callers; simpl. reflexivity.
                 (* rewrite eq_sym Heq'. simpl. reflexivity. *)
              ** rewrite setmE Heq setmE Heq' => [] [] H.
                 rewrite setmE Heq setmE Heq'.
                 eapply H10. eauto.
        -- move=> C zs.
           rewrite 2!setmE.
           case: ifP => _.
           ++ move=> [] <-. by eapply det_unique_z.
           ++ case: ifP => _.
              ** move=> [] <-. by eapply det_unique_z.
              ** eapply UNIQ.
Qed.

Definition simpl_stack (st: stack): seq Component.id :=
  List.map fst st.

Inductive reaches_corresponding_return_at: nat -> NMap (list call_return_tree) -> trace -> (nat * Z * nat) -> Prop :=
| reaches_call: forall k (trees: NMap (list call_return_tree)) C1 P z' C2 t p z n
                  l1 p1 rts1 n1 cls1 ls1 l1'
                  l2 p2 n2 cls2 ls2 l2',
    trees C1 = Some (l1 ++ node (p1, XECallOut P z' C2 rts1, n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XECallIn P z', n2, cls2) ls2 :: l2') ->
    reaches_corresponding_return_at (S k) (setm (setm trees C1 ls1) C2 ls2) t (p, z, n) ->
    reaches_corresponding_return_at k trees (ECall C1 P z C2 :: t) (p, z, n)
| reaches_ret: forall k (trees: NMap (list call_return_tree)) C1 z C2 t p n
                 l1 cls ls1 l1',
    trees C2 = Some (l1 ++ node (p, XERetIn z, n, cls) ls1 :: l1') ->
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
    trees C2 = Some (l1 ++ node (p, XERetIn z, n, cls) ls1 :: l1') ->
    returns_at 0 trees (ERet C1 z C2 :: t) (p, z, n)
| returns_at_call: forall k (trees: NMap (list call_return_tree)) C1 P z' C2 t p z n
                    l1 p1 cls1 ls1 l1' n1 rts1
                    l2 p2 cls2 ls2 l2' n2,
    trees C1 = Some (l1 ++ node (p1, XECallOut P z' C2 rts1, n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XECallIn P z', n2, cls2) ls2 :: l2') ->
    returns_at (S k) (setm (setm trees C1 ls1) C2 ls2) t (p, z, n) ->
    returns_at k trees (ECall C1 P z' C2 :: t) (p, z, n)
| returns_at_ret: forall k (trees: NMap (list call_return_tree)) C1 z' C2 t p z n
                    l1 p1 cls1 ls1 l1' n1
                    l2 p2 cls2 ls2 l2' n2,
    trees C1 = Some (l1 ++ node (p1, XERetOut z', n1, cls1) ls1 :: l1') ->
    trees C2 = Some (l2 ++ node (p2, XERetIn z', n2, cls2) ls2 :: l2') ->
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
                    (locs: NMap nat) (callers: NMap (list (Procedure.id * Z * nat))) (st: stack),
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

Lemma det_tree_list_build_call_return_tree: forall ls,
  determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls ->
  determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) (List.map build_call_return_tree ls).
Proof.
  induction ls using tree_ind_list with (P := fun tr => determinate_tree (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) tr ->
                                                     determinate_tree (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) (build_call_return_tree tr)).
  - now constructor.
  - move=> H; split; eauto.
    ++ by move=> [].
    ++ by move=> ? [].
  - move=> H.
    case: a H => [] [] p e n //= H.
    inversion H; subst; clear H.
    assert (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls) by now split.
    destruct (IHls DET) as [IH1 IH2].
    destruct p as [? []]; now constructor.
  - move=> H.
    simpl.
    have: (determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls).
    { inversion H; subst; clear H. split.
      - move=> p p' ? ? ? ? nth nth' EQ.
        specialize (H0 (S p) (S p') _ _ _ _ nth nth' EQ); now inversion H0.
      - move=> tr' IN.
        now specialize (H1 tr' (or_intror IN)). }
    (* move=> DET; specialize (IHls0 DET n). *)
    assert (forall ls p w x xe z l, nth_error (List.map build_call_return_tree ls) p = Some (node (x, xe, z, w) l) ->
                              exists l',
                                nth_error ls p = Some (node (x, xevent_to_loc_event xe, z, w) l')) as nth_build_call_return_tree_inv.
    { clear.
      induction ls.
      - by move=> [].
      - move=> [| p] w x xe z l H.
        + simpl in H. inversion H; subst; clear H.
          destruct a as [| [[x' y'] z'] l']; first by inversion H1.
          destruct x' as [? [| | |]];
            simpl in H1; inversion H1; subst; clear H1; eexists; split; simpl; eauto.
        + specialize (IHls p w x xe z l H) as [l' EQ].
          exists l'; eauto.
    }
    move=> DET.
    split.
    + move=> p p' [[[? ?] ?] ?] ? [[[? ?] ?] ?] ? nth nth' EQ; eauto.
      replace (build_call_return_tree tr :: List.map build_call_return_tree ls)
        with (List.map build_call_return_tree (tr :: ls)) in nth; last reflexivity.
      apply nth_build_call_return_tree_inv in nth as [l EQl].
      replace (build_call_return_tree tr :: List.map build_call_return_tree ls)
        with (List.map build_call_return_tree (tr :: ls)) in nth'; last reflexivity.
      apply nth_build_call_return_tree_inv in nth' as [l' EQl'].

      destruct H as [UNIQ ?]. eapply UNIQ; subst; eauto; simpl; eauto.
    + move=> tr0 [EQ | INR].
      * subst.
        eapply IHls.
        inversion H. eapply H1. now left.
      * specialize (IHls0 DET).
        inversion IHls0.
        eapply H1. eauto.
Qed.

Lemma sim4 (p: CallerAwareTree.prg):
  forward_simulation (CallerAwareTree.sem p) (CallReturnTree.sem (compile_caller_aware_tree p)).
Proof.
  fwd_sim (match_states4 (CallerAwareTree.prog_interface p)).
  - move=> s1 H.
    inversion H; subst; clear H.
    exists 0; eexists; split.
    + constructor.
      eauto.
      intros.
      assert (exists l1' e ls' l2', CallerAwareTree.prog_trees p C = Some (l1' ++ node (p0, e, n, zs) ls' :: l2'))
        as [l1' [e [ls' [l2' EQ]]]].
      clear -H.
      move: H => //=; rewrite mapmE; case: (CallerAwareTree.prog_trees p C) => //= a.
      elim: a l1.
      * now destruct l1.
      * intros.
        simpl in H0. destruct l1.
        -- inversion H0; subst.
           destruct a as [| [[[? []] ?] ?] ?]; inversion H2; subst;
             now exists []; eexists; eexists; eexists; simpl; eauto.
        -- inversion H0; subst.
           specialize (H l1); rewrite H3 in H; specialize (H Logic.eq_refl) as [l1' [e [ls' [l2' EQ]]]].
           inversion EQ; subst.
           now exists (a :: l1'); eexists; eexists; eexists; simpl; eauto.
      * now eapply INIPARENT; eauto.
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
          by apply det_tree_list_build_call_return_tree.
          by apply det_tree_list_build_call_return_tree.

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
              set (f := (fun x : t (nat * loc_ev * nat * seq (Procedure.id * Z * nat)) =>
                           match x with
                           | leaf _ => (0, 0%Z, 0)
                           | node (lc, ERetIn v, i0, _) _ => (lc, v, i0)
                           | node (lc, ECallIn _ _, _, _) _ | node (lc, ECallOut _ _ _, _, _) _ | node (lc, ERetOut _, _, _) _
                                                                                                  => (0, 0%Z, 0)
                           end)).
              { remember 0 as zero. clear Heqzero.
                remember (setm (setm trees' C (List.map build_call_return_tree ls)) C2 (List.map build_call_return_tree ls')) as f0.
                rename C into C1.
                generalize dependent C1. generalize dependent C2.
                (* revert Heqf0. *)
                remember (p1, z0, n0) as ev. generalize dependent p1. generalize dependent z0. generalize dependent n0.
                generalize dependent trees'. generalize dependent trees.
                revert l1 l1' ls ls' l2 l2' DET DET'.
                revert zs zs' zs1 zs2 UNIQ.
                induction H0.
                (* inv H0. *)
                - move=> zs zs' zs1 zs2 UNIQ l0 l0' ls ls' l2 l2' DET DET' trees0 trees0' Htrees n1 z1 p2 Heqev C0
                           SEQOK H5 H7 C3 H1 H3 H4 H6 Htree Htree' Hcomp H13 H12 Heqf0.

                  inversion H13. move: H2 => /andP [] HC Hwb; subst.
                  (* rewrite EQtrees0 in H. *)
                  rewrite 2!setmE in H.
                  assert (HnC: C2 == C0 = false).
                  { apply /eqP. move: HC => /eqP <-.
                    now destruct H4 as [[? ?] [? ?]]; congruence. }
                  rewrite HnC in H. rewrite (eq_sym) in H. rewrite HC in H.
                  inversion H.
                  apply map_eq_app in H2.
                  destruct H2 as [l1'' [l2'' [Heqlist [Heqmap1 Heqmap2]]]].
                  rewrite Heqlist.
                  rewrite helper1. rewrite map_app.
                  apply map_eq_cons in Heqmap2.
                  destruct Heqmap2 as [a [l3'' [Heqlist2 [Heqfun Heqmap]]]].
                  rewrite Heqlist2.
                  simpl. rewrite map_app.
                  unfold build_call_return_tree in Heqfun. destruct a as [| [[[? e]]]]; first inversion Heqfun.
                  destruct e; simpl in *. inversion Heqfun; subst.
                  inversion Heqfun; subst.
                  simpl. eexists; eexists. admit. admit.
                - move=> zs zs' zs1 zs2 l0 l0' ls ls' l3 l3' DET DET' trees0 trees0' Htrees n3 z1 p4 Heqev C0
                           SEQOK H5 H7 C3 H2 H3 H4 H6 Htree Htree' Hcomp H13 H12 Heqf0; subst.
                  admit.
                - move=> zs zs' zs1 zs2 l0 l1'0 ls ls' l3 l2'0 DET DET' trees0 trees' H11 n3 z1 p4 Heqev C0
                           SEQOK H5 H7 C3 H2 H3 H4 H6 Htree Htree' Hcomp H13 H12 Heqf0; subst.
                  admit.

                (* - inversion H12. move: H0 => /andP. [] HC Hwb. *)
                (*   rewrite 2!setmE in H10. *)
                (*   assert (HnC: C0 == C2 = false). *)
                (*   { apply /eqP. move: HC => /eqP <-. *)
                (*     now destruct H1. } *)
                (*   rewrite HnC in H10. rewrite (eq_sym) in H10. rewrite HC in H10. *)
                (*   inversion H10. *)
                (*   apply map_eq_app in H0. *)
                (*   destruct H0 as [l1'' [l2'' [Heqlist [Heqmap1 Heqmap2]]]]. *)
                (*   rewrite Heqlist. *)
                (*   rewrite helper1. rewrite map_app. *)
                (*   apply map_eq_cons in Heqmap2. *)
                (*   destruct Heqmap2 as [a [l3'' [Heqlist2 [Heqfun Heqmap]]]]. *)
                (*   rewrite Heqlist2. *)
                (*   simpl. rewrite map_app. *)
                (*   unfold build_call_return_tree in Heqfun. destruct a as [| [[[]]]]; first inversion Heqfun. *)
                (*   destruct e; simpl in *. inversion Heqfun; subst. *)
                (*   inversion Heqfun; subst. *)
                (*   simpl. eexists; eexists; reflexivity. *)
                (* - (* This admitted result should hold by induction *) *)
                  (* admit. *)
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
      rewrite Hst.
      rewrite Hst in H12.
      destruct (H12 0 C2 rts p' z n' Logic.eq_refl) as [rts1 [rts2 Heq_rts]].
      { econstructor. rewrite map_app in Htree'. simpl in Htree'. eauto. }
      exists 0; eexists; split.
      * left; econstructor.
        (* clear Heq_rts. *)
        econstructor; eauto.
        (* now apply allowed_event_allowed_xevent. *)
        rewrite Htree map_app //=.
        rewrite Htree' map_app //=.
        (* Invariant:
         *)
          by eapply det_tree_list_build_call_return_tree.
          by eapply det_tree_list_build_call_return_tree.
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
           econstructor. rewrite map_app in Htree. simpl in Htree; eauto. rewrite map_app in Htree'. simpl in Htree'; eauto.
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
                    (locs: NMap nat) (callers: NMap (list (Procedure.id * Z * nat))) (st: stack) cs,
    forall (CUR_LOC: forall C n, locs C = Some n ->
                Memory.load (CS.s_memory cs) (location C) = Some (Int (Z.of_nat n)))
      (CUR_INT: forall C, C \in domm intf ->
          Memory.load (CS.s_memory cs) (intcall C) = some (Int 1%Z))
      (CUR_COMP: forall C, next_comp t = Some C ->
                      CS.s_component cs = C)
      (* (CALLERS: forall C zs, callers C = Some zs -> *)
      (*                   unique_key zs) *)
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
    call_exp = guard_call (callexp (get_all_handle_calls P (CallReturnTree.prog_trees p C))).
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
(* Lemma wf_trees_unique_key: forall C P p, *)
(*     TreeWithCallers.wf p -> *)
(*     unique_key (get_all_handle_calls P (TreeWithCallers.prog_trees p C)). *)
(* Proof. *)
(*   move=> C P p H. *)
(*   unfold get_all_handle_calls. *)
(*   destruct (TreeWithCallers.prog_trees p C); last first. *)
(*   unfold unique_key; intros. destruct ls1; inversion H0. *)
(*   unfold unique_key. *)
(*   move=> ls1 a1 b1 ls2 a2 b2 ls3 H0. *)
(* Admitted. *)

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
      (* 1 *)
      destruct (Memory.store_after_load _ (C1, Block.local, 0%Z) _ (Int (Z.of_nat n)) (CUR_LOC _ _ H7)) as [m' Hm'].
      (* 2 *)
      destruct (Memory.store_after_load m' (C1, Block.local, 1%Z) (Int 1%Z) (Int 1%Z)) as [m'' Hm''].
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'); last by congruence.
      eapply CUR_INT. now destruct H1.
      (* 3 *)
      destruct (Memory.store_after_load m'' (C2, Block.local, 0%Z) (Int (Z.of_nat p'0)) (Int (Z.of_nat n'))) as [m''' Hm'''].
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''); last by congruence.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'); last by (now destruct H1 as [[] []]; congruence).
      eauto.
      (* 4 *)
      (* rewrite (Memory.load_after_store _ _ _ _ _ Hm'). *)
      (* rewrite helper2. eauto. move=> CONTRA; move: CONTRA H1 ->; now case. *)
      destruct (Memory.store_after_load m''' (C2, Block.local, 1%Z) (Int 1%Z) (Int 1%Z)) as [m'''' Hm''''].
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'''); last by congruence.
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''); last by (now destruct H1 as [[] []]; congruence).
      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'); last by congruence.
      eapply CUR_INT. now destruct H1.
      (* rewrite (Memory.load_after_store _ _ _ _ _ Hm''). rewrite helper2'. *)
      (* rewrite (Memory.load_after_store _ _ _ _ _ Hm'). rewrite helper2'. *)
      (* simpl. eapply CUR_INT. now destruct H1. lia. lia. *)
      exists 0; eexists; split.
      * left; econstructor.
        -- simpl in *; subst.
           eapply TreeWithCallers.step_call with
               (call_exp := guard_call (callexp (get_all_handle_calls P (CallReturnTree.prog_trees p C2))));
                            eauto.
           simpl.
           pose proof (TreeWithCallers.wfprog_exported_procedures_existence WF) as H.
           assert (exported_procedure (TreeWithCallers.prog_interface p') C2 P) by now destruct H1.
           unfold p' in H. simpl in H.
           specialize (H _ _ H0).
           clear -H H1.
           assert (exists v, (CallReturnTree.prog_interface p C2) = Some v) as [v EQ].
           { apply /dommP. now destruct H1. }
           move: H; rewrite /find_procedure //= mapimE EQ //= mkfmapfE.
           case: ifP => //=.
        -- eapply star_trans.
           ++ assert (exists ts, TreeWithCallers.prog_trees p' C2 = Some ts) as [ts TREES].
              { apply /dommP. rewrite -(TreeWithCallers.wfprog_defined_trees WF).
                now destruct H1. }
              (* assert ( exists ls1 ls2 : seq (nat * seq (Procedure.id * Z * nat)), *)
              (*            get_all_handle_calls P (Some (l1 ++ node (p0, XECallIn P z, n, zs) ls :: l2)) = *)
              (*            ls1 ++ (n, zs1 ++ (P, z, n) :: zs2) :: ls2). *)
              (* { admit. } *)

              eapply call_handling_expression_correct with (trs := (l1 ++ node (p0, XECallIn P z, n, zs) ls :: l2)). eauto.
              admit.
              admit.
              eapply UNIQ.
              simpl. admit.
              (* eapply CALLERS. eauto. admit. *)
              (* Admitted: Unicity lemma that again relates to subtrees *)
              (* eapply callers_in_subtrees; admit. *)
              simpl; eauto. simpl; eauto.
              (* Memory *)
              simpl.
              erewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'').
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'). eauto.
              unfold location; now destruct H1 as [[] []]; congruence.

              simpl.
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'').
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'). eapply CUR_INT.
              now destruct H1.
              unfold intcall; now congruence.
              unfold intcall; now destruct H1 as [[] []]; congruence.
              (* (* rewrite helper2. eauto. move=> CONTRA; move: CONTRA H1 ->; now case. *) *)
              (* erewrite (Memory.load_after_store _ _ _ _ _ Hm'). simpl. *)
              (* rewrite helper2. eapply CUR_INT. now destruct H1. destruct H1 as [[] ]; congruence. *)
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
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''''); last by unfold location; congruence.
           (* rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'''); simpl. rewrite helper2'; last lia. *)
           (* rewrite (Memory.load_after_store _ _ _ _ _ Hm''); simpl. *)
           move: H; rewrite 2!setmE.
           destruct (C == C2) eqn:Heq. move: Heq => /eqP -> => [] [] EQ; subst.
           rewrite (Memory.load_after_store_eq _ _ _ _ Hm'''); eauto.
           (* unfold location; rewrite eqxx. eauto. *)
           destruct (C == s_component) eqn:Heq'.
           move: Heq' => /eqP -> => [] [] <-. simpl in CUR_COMP. rewrite CUR_COMP.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'''); last by unfold location; now destruct H1 as [[] []]; congruence.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''); last by unfold location; congruence.
           rewrite (Memory.load_after_store_eq _ _ _ _ Hm'); eauto.
           (* rewrite helper2. *)
           (* rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl. *)
           (* rewrite /location eqxx. eauto. now destruct H1 as [[] ]. *)
           move=> H. move: Heq => /eqP Heq.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'''); last by unfold location; now destruct H1 as [[] []]; congruence.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''); last by unfold location; congruence.
           rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'); eauto. unfold location.
           move: Heq' => /eqP Heq'. simpl in CUR_COMP. congruence.

           (* rewrite helper2. *)
           (* rewrite (Memory.load_after_store _ _ _ _ _ Hm'); simpl. *)
           (* rewrite /location. *)
           (* move: Heq' => /eqP Heq'. rewrite helper2. *)
           (* eauto. simpl in CUR_COMP. congruence. eauto. *)
        -- move=> C H.
           simpl.
           destruct (C == C2) eqn:HC2.
           ++ move: HC2 => /eqP HC2. rewrite HC2.
              rewrite (Memory.load_after_store_eq _ _ _ _ Hm''''). reflexivity.
           ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'''').
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm''').
              {
              destruct (C == C1) eqn:HC1.
              ** move: HC1 => /eqP HC1; rewrite HC1.
                 rewrite (Memory.load_after_store_eq _ _ _ _ Hm''). reflexivity.
              ** rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm'').
                 rewrite (Memory.load_after_store_neq _ _ _ _ _ _ Hm').
                 eapply CUR_INT. eauto.
                 unfold intcall; congruence.
                 move: HC1 => /eqP HC1; unfold intcall; congruence.
              }
              move: HC2 => /eqP HC1; unfold intcall; congruence.
              move: HC2 => /eqP HC1; unfold intcall; congruence.
        -- move=> C H. simpl in *.
           destruct t0; first inversion H.
           inv H. inv SEQOK. reflexivity.
        -- simpl in *.
           econstructor. destruct H1 as [[] ]; congruence.
        -- move=> C H.
           destruct (MEM C) as [oldz Holdz].
           eauto. exists oldz; simpl.
           rewrite (Memory.load_after_store_neq m''' _ _ _ _ _ Hm'''').
           rewrite (Memory.load_after_store_neq m'' _ _ _ _ _ Hm''').
           rewrite (Memory.load_after_store_neq m' _ _ _ _ _ Hm'').
           rewrite (Memory.load_after_store_neq s_memory _ _ _ _ _ Hm'). eauto.
           unfold ret; congruence.
           unfold ret; congruence.
           unfold ret; congruence.
           unfold ret; congruence.
        -- simpl. reflexivity.
        -- simpl. move=> F [H | H].
           ++ simpl in *. rewrite <- H. eauto.
           ++ eauto.

    + (* Return case *)
      destruct cs as [? ? ? ? ? ?].
      specialize (CUR_COMP C1 Logic.eq_refl).
      destruct (Memory.store_after_load _ (C1, Block.local, 0%Z) (Int (Z.of_nat p0)) (Int (Z.of_nat n)) (CUR_LOC _ _ H6)) as [m' Hm'].
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
| match_concrete_stacks_ext: forall C C' rts s st old_arg P,
    C <> C' ->
    match_concrete_stacks C' s st ->
    match_concrete_stacks C ((C', rts) :: s) (CS.Frame C' old_arg (Kassign1 (RETURN_p)
                                                       (Kseq ((E_seq (return_handling_expression rts)
                                                                     (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                                            (E_call C' P (E_val (Int (Z.of_nat 0)))))))
                                                             Kstop)) :: st)
.

Lemma unfold_stack: forall ge C1 C2 rts st stack m z arg,
    match_concrete_stacks C1 ((C2, rts) :: st) stack ->
    exists stack' stack'' arg' arg'' P,
      stack' = CS.Frame C2 arg'
                        (Kassign1 RETURN_p
                                  (Kseq (E_seq (return_handling_expression rts)
                                               (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                      (E_call C2 P (E_val (Int (Z.of_nat 0)))))) Kstop))
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
        [stack1 [stack2 [arg1 [arg2 [P [IH1 [IH2 IH3]]]]]]].
    subst.
    eexists; eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + take_step. eauto. eapply IH3.
  - inv Heqst0.
    eexists; eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + eapply star_refl.
Qed.

Fixpoint concat_cont (k1 k2: cont): cont :=
  match k1 with
  | Kstop => k2
  | Kbinop1 b e k1' => Kbinop1 b e (concat_cont k1' k2)
  | Kbinop2 b v k1' => Kbinop2 b v (concat_cont k1' k2)
  | Kseq e k1' => Kseq e (concat_cont k1' k2)
  | Kif e e' k1' => Kif e e' (concat_cont k1' k2)
  | Kalloc k1' => Kalloc (concat_cont k1' k2)
  | Kderef k1' => Kderef (concat_cont k1' k2)
  | Kassign1 e k1' => Kassign1 e (concat_cont k1' k2)
  | Kassign2 v k1' => Kassign2 v (concat_cont k1' k2)
  | Kcall C P k1' => Kcall C P (concat_cont k1' k2)
  end.

Definition concat_event_expr (p: TreeWithCallers.prg) (C: Component.id) (P: Procedure.id) (k1: cont) :=
  concat_cont k1 (Kseq (build_event_expression C P (TreeWithCallers.prog_trees p C)) Kstop).

Definition match_cont (p: TreeWithCallers.prg) (C: Component.id) (P: Procedure.id) (k1 k2: cont): Prop :=
  k2 = concat_event_expr p C P k1.


Lemma match_cont_step (p: TreeWithCallers.prg) (C: Component.id) (P: Procedure.id): forall ge ge' cs1 cs1' cs2 st,
    cs2 = [CState (CS.s_component cs1), st, CS.s_memory cs1,
           concat_event_expr p C P (CS.s_cont cs1), CS.s_expr cs1, CS.s_arg cs1] ->
    CS.s_stack cs1 = CS.s_stack cs1' -> (* No internall call/returns allowed *)
    CS.kstep ge cs1 E0 cs1' ->
    CS.kstep ge' cs2 E0
             [CState (CS.s_component cs1'), st, CS.s_memory cs1',
              concat_event_expr p C P (CS.s_cont cs1'), CS.s_expr cs1', CS.s_arg cs1'].
Proof.
  move=> ge ge' [? ? ? ? ? ?] cs1' cs2 st EQ STACKS STEP; simpl in *; subst.
  inv STEP; try now econstructor.
  - simpl. destruct cs1' as [? s ? ? ? ?].
    inversion H1.
    clear -H2. exfalso.
    induction s.
    + congruence.
    + inversion H2. apply IHs. eauto.
  - simpl in H1.
    exfalso.
    induction s.
    + congruence.
    + inversion H1. apply IHs. eauto.
Qed.


Definition mem_agree (intf: Program.interface) mem mem' :=
  forall C b o, C \in domm intf ->
                 Memory.load mem (C, b, o) = Memory.load mem' (C, b, o).


Variant match_states6 (p: TreeWithCallers.prg) (ge: global_env) (i: nat): TreeWithCallers.state -> CS.state -> Prop :=
| match_states_initial: forall s s',
    TreeWithCallers.initial p s ->
    CS.initial_state (compile_tree_with_callers p) s' ->
    forall (SUBTREE: forall C ls ls',
          TreeWithCallers.prog_trees p C = Some ls ->
          (let '(_, trees, _, _, _) := TreeWithCallers.ghost_state s in trees) C = Some ls' ->
          subtrees ls' ls),
    match_states6 p ge i s s'
| match_states_silent: forall (gs:trace * NMap (seq call_return_tree) * NMap nat * NMap (seq (Procedure.id * Z * nat)) * stack)
                               cs cs' t trees locs cls st P,
    gs = (t, trees, locs, cls, st) ->
    forall (COMP: CS.s_component cs = CS.s_component cs')
      (STACK: match_concrete_stacks (CS.s_component cs') st (CS.s_stack cs'))
      (* (MEM: CS.s_memory cs = CS.s_memory cs') *)
      (MEM: mem_agree (TreeWithCallers.prog_interface p) (CS.s_memory cs) (CS.s_memory cs'))
      (CONT: match_cont p (CS.s_component cs) P (CS.s_cont cs) (CS.s_cont cs'))
      (EXPR: CS.s_expr cs =  CS.s_expr cs')
      (* (INT: forall C, *)
      (*     C \in domm (TreeWithCallers.prog_interface p) -> *)
      (*     Memory.load (CS.s_memory cs) (intcall C) = Some (Int 1%Z)) *)
      (ARG: CS.s_arg cs = CS.s_arg cs'),
    forall (SUBTREE: forall C ls ls',
          TreeWithCallers.prog_trees p C = Some ls ->
          (let '(_, trees, _, _, _) := gs in trees) C = Some ls' ->
          subtrees ls' ls),
      match_states6 p ge i {| TreeWithCallers.ghost_state := gs;
                              TreeWithCallers.concrete_state := cs;
                              TreeWithCallers.can_silent := true |} cs'
| match_states_6: forall (gs:trace * NMap (seq call_return_tree) * NMap nat * NMap (seq (Procedure.id * Z * nat)) * stack)
                    cs cs' t trees locs cls st P,
    gs = (t, trees, locs, cls, st) ->
    forall (COMP: CS.s_component cs = CS.s_component cs')
      (STACK: match_concrete_stacks (CS.s_component cs') st (CS.s_stack cs'))
      (* (MEM: CS.s_memory cs = CS.s_memory cs') *)
      (MEM: mem_agree (TreeWithCallers.prog_interface p) (CS.s_memory cs) (CS.s_memory cs'))
      (CONT: CS.s_cont cs' = Kseq (build_event_expression (CS.s_component cs') P (TreeWithCallers.prog_trees p (CS.s_component cs'))) Kstop)
      (* (EXPR: CS.s_expr cs' = build_event_expression (CS.s_component cs') (TreeWithCallers.prog_trees p (CS.s_component cs'))) *)
      (* (EXPR: CS.s_expr cs' = E_val (Int 1)) *)
      (EXPR: expr_is_done (CS.s_expr cs'))
      (INT: forall C,
          C \in domm (TreeWithCallers.prog_interface p) ->
          Memory.load (CS.s_memory cs) (intcall C) = Some (Int 1%Z))
      (ARG: CS.s_arg cs = CS.s_arg cs'),
    forall (SUBTREE: forall C ls ls',
          TreeWithCallers.prog_trees p C = Some ls ->
          (let '(_, trees, _, _, _) := gs in trees) C = Some ls' ->
          subtrees ls' ls),
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
  forall C P procs,
    TreeWithCallers.prog_procedures p C = Some procs ->
    procs P = Some (comp_call_handle P (TreeWithCallers.prog_trees p C)) ->
    find_procedure (genv_procedures (prepare_global_env (compile_tree_with_callers p))) C P =
    Some (E_seq (comp_call_handle P (TreeWithCallers.prog_trees p C))
                (build_event_expression C P (TreeWithCallers.prog_trees p C))).
Proof.
  move=> C P procs H1 H2.
  rewrite /find_procedure /compile_tree_with_callers //= mapimE H1 //= mapimE H2 //=.
Qed.

Lemma find_main (p: TreeWithCallers.prg) (WF: TreeWithCallers.wf p):
  prog_main (compile_tree_with_callers p) =
  Some (E_seq (comp_call_handle Procedure.main (TreeWithCallers.prog_trees p Component.main))
              (build_event_expression Component.main Procedure.main (TreeWithCallers.prog_trees p Component.main))).
Proof.
  rewrite /prog_main.
  assert (exists procs, TreeWithCallers.prog_procedures p Component.main = Some procs) as [procs EQ].
  apply /dommP. rewrite -TreeWithCallers.wfprog_defined_procedures //= mem_domm TreeWithCallers.wf_has_main //=.
  eapply find_procedure_find; eauto.
  eapply TreeWithCallers.wf_main_expression; eauto.
Qed.

(* Lemma initial_location: forall p C, *)
(*     Memory.load (prepare_buffers (compile_tree_with_callers p)) (C, Block.local, 0%Z) = Some (Int (Z.of_nat 0)). *)
(* Proof. *)
(*   Admitted. *)

(* Lemma initial_buffers: forall p C, *)
(*     Memory.load (prepare_buffers (compile_tree_with_callers p)) (C, Block.local, (0 + 1)%Z) = Some (Int 0). *)
(*   move=> p C. *)
(*   unfold prepare_buffers. simpl. *)
(* Admitted. *)

Lemma initial_location: forall p (C: Component.id),
    C \in domm (TreeWithCallers.prog_interface p) ->
  Memory.load (TreeWithCallers.initial_memory (TreeWithCallers.prog_interface p)) (location C) =
  Memory.load (prepare_buffers (compile_tree_with_callers p)) (location C).
Proof.
  intros p C in_domm.
  rewrite /TreeWithCallers.initial_memory /prepare_buffers //=.
  rewrite /Memory.load mkfmapfE mapmE //= in_domm.
  (* rewrite mem_domm in in_domm. *)
  move: in_domm => /dommP [v Hv].
  rewrite mapimE Hv //=.
  case: ifP => //=.
  move=> i. simpl.
  rewrite 2!ComponentMemory.load_prealloc //=.
Qed.


Lemma initial_intcall: forall p C,
  (C == Component.main) = false ->
  C \in domm (TreeWithCallers.prog_interface p) ->
  Memory.load (TreeWithCallers.initial_memory (TreeWithCallers.prog_interface p)) (intcall C) =
  Memory.load (prepare_buffers (compile_tree_with_callers p)) (intcall C).
Proof.
  intros p C NEQ in_domm.
  rewrite /TreeWithCallers.initial_memory /prepare_buffers //=.
  rewrite /Memory.load mkfmapfE mapmE //= in_domm.
  (* rewrite mem_domm in in_domm. *)
  move: in_domm => /dommP [v Hv].
  rewrite mapimE Hv //=.
  case: ifP => //=.
  by rewrite NEQ.
Qed.


Lemma initial_ret: forall p (C: Component.id),
    C \in domm (TreeWithCallers.prog_interface p) ->
          Memory.load (TreeWithCallers.initial_memory (TreeWithCallers.prog_interface p)) (ret C) =
          Memory.load (prepare_buffers (compile_tree_with_callers p)) (ret C).
Proof.
  intros p C in_domm.
  rewrite /TreeWithCallers.initial_memory /prepare_buffers //=.
  rewrite /Memory.load mkfmapfE mapmE //= in_domm.
  (* rewrite mem_domm in in_domm. *)
  move: in_domm => /dommP [v Hv].
  rewrite mapimE Hv //=.
  case: ifP => //=.
  move=> i. simpl.
  rewrite 2!ComponentMemory.load_prealloc //=.
Qed.

Lemma step_silent_mem_agree:
  forall ge C stk m0 m0' k k' e e' arg,
    CS.kstep ge [CState C, stk, m0, k, e, arg] E0 [CState C, stk, m0', k', e', arg] ->
    forall m1, mem_agree (genv_interface ge) m0 m1 ->
          exists m1',
            CS.kstep ge [CState C, stk, m1, k, e, arg] E0 [CState C, stk, m1', k', e', arg] /\
            mem_agree (genv_interface ge) m0' m1'.
Proof.
  move=> ge C stk m0 m0' k k' e e' arg H m1 H0.
  inversion H; subst; try now (eexists; split; [econstructor | eauto]).
  - assert (exists m1', Memory.alloc m1 C (Z.to_nat size) = Some (m1', ptr)) as [m1' MEM].
    assert (same_mem: mem_agree (genv_interface ge) m0 m1 -> m0 C = m1 C) by admit.
    move: H11; rewrite /Memory.alloc.
    rewrite -(same_mem H0).
    case: (m0 C); last by [].
    move=> Cmem; case: (ComponentMemory.alloc Cmem (Z.to_nat size)) => Cmem1 b [] ? <-.
    eexists; reflexivity.
    exists m1'; split; [econstructor | eauto].
    eauto. eauto.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.



Lemma subtrees_in_all_ev: forall trs p xe n zs l ls,
    In (node (p, xe, n, zs) l) ls ->
    subtrees ls trs ->
    node_of_comp (p, xe, n , zs) ->
    In (p, xe, n) (List.map event_info (List.filter node_of_comp (concat (List.map tree_to_list trs)))).
Proof.
  move=> trs p xe n zs l ls IN SUB FILTER.
  induction SUB.
  - move: IN FILTER.
    elim: trs.
    + by [].
    + move=> a l0 H IN //= FILTER.
      case: IN.
      * intros EQ; subst.
        rewrite //= filter_app FILTER //=.
        now left.
      * rewrite //= filter_app //= List.map_app => IN.
        eapply in_app_iff; right.
        now eapply H.
  - specialize (IHSUB IN).
    assert (EQ: List.map event_info (List.filter node_of_comp (concat (List.map tree_to_list (trs1 ++ node x trs' :: trs2))))
                = (List.map event_info (List.filter node_of_comp (concat (List.map tree_to_list trs1))))
                    ++ (List.map event_info (List.filter node_of_comp [x]))
                    ++ (List.map event_info (List.filter node_of_comp (concat (List.map tree_to_list trs'))))
                    ++ (List.map event_info (List.filter node_of_comp (concat (List.map tree_to_list trs2))))).
    { rewrite !List.map_app !concat_app !filter_app !List.map_app //=.
      case: (node_of_comp x) => //=.
    }
    rewrite EQ.
    eapply in_app_iff. right.
    eapply in_app_iff. right.
    eapply in_app_iff. now left.
Qed.


Lemma sim6 (p: TreeWithCallers.prg) (Hwf: TreeWithCallers.wf p):
  forward_simulation (TreeWithCallers.sem p) (Src.sem (compile_tree_with_callers p)).
Proof.
  pose (p_compiled := compile_tree_with_callers p).
  pose (ge := globalenv (CS.sem p_compiled)).
  assert (WF: well_formed_program (compile_tree_with_callers p)) by now eapply wf_compile.
  fwd_sim (match_states6 p ge).
  - move=> s1 H.
    exists 0; exists (CS.initial_machine_state (compile_tree_with_callers p)).
    split.
    + rewrite /CS.initial_state //=.
    + constructor; [by [] | rewrite /CS.initial_state //= |].
      move=> C ls ls' H0 H1. inversion H; simpl in H1; subst.
      unfold TreeWithCallers.ghost_state in H1. rewrite H0 in H1; inversion H1; subst; econstructor.

  - move=> i s1 s2 H H0. reflexivity.
  - move=> s1 t s1' H i [C stk m k e arg] H0.
    inv H.
    + (* Step call *)
      inv H0.
      * simpl in *; subst.
        inv H.
        unfold CS.initial_state in H2.
        unfold CS.initial_machine_state in H2.
        rewrite find_main in H2. inversion H2; subst.
        (* Memory operations *)
        destruct (Memory.store_after_load (prepare_buffers (compile_tree_with_callers p))
                                          (Component.main, Block.local, 1%Z) (Int 0) (Int 1)) as [m''' MEM'''].
        assert (exists v, TreeWithCallers.prog_interface p Component.main = Some v) as [v Hv].
        { apply /dommP.
          rewrite mem_domm. eapply TreeWithCallers.wf_has_main; eauto. }
        rewrite /compile_tree_with_callers /prepare_buffers /Memory.load mapmE //= mapimE //= Hv //= ComponentMemory.load_prealloc //=.
        destruct (Memory.store_after_load m''' (Component.main, Block.local, 0%Z) (Int 0%Z) (Int (Z.of_nat n))) as [m'''' MEM''''].
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''').
        rewrite /prepare_buffers /Memory.load mapmE //= mapimE //=.
        assert (exists v, TreeWithCallers.prog_interface p Component.main = Some v) as [v Hv].
        { apply /dommP.
          rewrite mem_domm. eapply TreeWithCallers.wf_has_main; eauto. }
        rewrite Hv //=.
        rewrite ComponentMemory.load_prealloc //=.
        congruence.
        (* Star *)
        simpl.
        eexists; eexists; split.
        -- left.
           eapply star_plus_trans.
           do 10 take_step. eauto.
           assert (exists v, TreeWithCallers.prog_interface p Component.main = Some v) as [v Hv].
           { apply /dommP.
             rewrite mem_domm. eapply TreeWithCallers.wf_has_main; eauto. }
           rewrite /compile_tree_with_callers /prepare_buffers /Memory.load mapmE //= mapimE //= Hv //= ComponentMemory.load_prealloc //=.
           do 11 take_step. eauto. simpl. eauto.
           (* assert (exists trs, TreeWithCallers.prog_trees p Component.main = Some trs) as [trs has_main]. *)
           (* { clear -Hwf. *)
           (*   apply /dommP. *)
           (*   inversion Hwf. *)
           (*   rewrite -wfprog_defined_trees. *)
           (*   now rewrite mem_domm. } *)

           { eapply build_event_expression_correct with (xe := XECallOut P z C2 rts1).
             - eapply TreeWithCallers.det_loc. eauto. eauto.
             - eapply subtrees_in_all_ev with (ls := l1 ++ node (p0, XECallOut P z C2 rts1, n, zs) ls :: l2).
               eapply in_app_iff; right. now left.
               eapply SUBTREE; eauto.
               reflexivity.
             - eauto.
             - simpl. rewrite H4. eauto.
             - simpl. rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''').
               assert (exists v, TreeWithCallers.prog_interface p Component.main = Some v) as [v Hv].
               { apply /dommP.
                 rewrite mem_domm. eapply TreeWithCallers.wf_has_main; eauto. }
               rewrite /compile_tree_with_callers /prepare_buffers /Memory.load mapmE //= mapimE //= Hv //= ComponentMemory.load_prealloc //=.
               assert (p0 = 0) by now eapply INIPARENT; eauto.
               now subst.
               unfold location; congruence.
             - eauto.
           }
           assert (H1' := H1).
           destruct H1 as [[? [? EXPORTED]]].
           destruct EXPORTED as [C_CI [EXP1 EXP2]].
           assert (exists v, TreeWithCallers.prog_procedures p C2 = Some v) as [v Hv].
           now apply /dommP; rewrite -(TreeWithCallers.wfprog_defined_procedures Hwf) //=.
           (* now destruct H1'. *)
           eapply plus_star_trans.
           { eapply call_event_correct; simpl; eauto.

             eapply find_procedure_find; eauto.
             eapply TreeWithCallers.wf_procedures_expression; eauto. now destruct H1'. }
           take_step.
           eapply star_refl.
           reflexivity.
           reflexivity.
        -- eapply match_states_silent; simpl; eauto.
           econstructor; eauto. now destruct H1 as [[] []]; congruence.
           econstructor.
           unfold mem_agree.
           move=> C b o Hintf.
           { destruct (b == Block.local) eqn:Hblock.
             - move: Hblock => /eqP Hblock; subst.
               destruct (C == Component.main) eqn:HC1.
               + move: HC1 => /eqP ->.
                 destruct (o == 0%Z) eqn:Ho; move: Ho => /eqP Ho; subst.
                 * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                   rewrite (Memory.load_after_store_eq _ _ _ _ H9).
                   rewrite (Memory.load_after_store_eq _ _ _ _ MEM''''); eauto.
                   unfold intcall, location; congruence.
                 * destruct (o == 1%Z) eqn:Ho'; move: Ho' => /eqP Ho'; subst.
                   -- rewrite (Memory.load_after_store_eq _ _ _ _ H10).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM'''').
                      rewrite (Memory.load_after_store_eq _ _ _ _ MEM'''); eauto.
                      unfold intcall; congruence.
                   -- destruct (o == 2%Z) eqn:Ho''; move: Ho'' => /eqP Ho''; subst.
                      ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM'''').
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''').
                         eapply initial_ret.
                         rewrite mem_domm. eapply TreeWithCallers.wf_has_main; eauto.
                         unfold ret; congruence.
                         unfold ret; congruence.
                         unfold location, ret; congruence.
                         unfold intcall, ret; congruence.
                      ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM'''').
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''').
                         rewrite /TreeWithCallers.initial_memory /prepare_buffers /Memory.load //= mkfmapfE mapmE mapimE //=.
                         rewrite mem_domm.
                         case: ((TreeWithCallers.prog_interface p Component.main)) => [?|] //=.
                         rewrite 2!ComponentMemory.load_prealloc //=.
                         case: (0 <=? o)%Z => //=.
                         { clear -Ho Ho' Ho''.
                           destruct (Z.to_nat o) as [| [| ]] eqn:Heq; eauto.
                           exfalso. eapply Ho'.
                           unfold Z.to_nat in Heq.
                           destruct o; lia. }
                         congruence. congruence. unfold location; congruence.
                         unfold intcall; congruence.
               + (* move: HC1 => /eqP HC1. *)
                 rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                   rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                   rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''''); eauto.
                   rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM'''); eauto.
                   rewrite /TreeWithCallers.initial_memory /prepare_buffers /Memory.load //= mkfmapfE mapmE mapimE //=.
                   rewrite mem_domm.
                   case: ((TreeWithCallers.prog_interface p C)) => [?|] //=.
                   now rewrite 2!ComponentMemory.load_prealloc //= HC1.
                   move: HC1 => /eqP HC1 //=; congruence.
                   move: HC1 => /eqP HC1 //=; congruence.
                   unfold location; move: HC1 => /eqP HC1 //=; congruence.
                   unfold intcall; move: HC1 => /eqP HC1 //=; congruence.
             - move: Hblock => /eqP Hblock.
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM'''').
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM''').
               rewrite /TreeWithCallers.initial_memory /prepare_buffers /Memory.load //= mkfmapfE mapmE mapimE //=.
               rewrite mem_domm.
               case: ((TreeWithCallers.prog_interface p C)) => [?|] //=.
               rewrite 2!ComponentMemory.load_prealloc //=.
               case: (0 <=? o)%Z => //=; rewrite 2!setmE.
               destruct (b == 0) eqn:Hb; rewrite Hb => //=.
               move: Hb => /eqP //=.

               congruence. congruence.
               unfold location; congruence.
               unfold intcall; congruence.
           }
           reflexivity.
           { clear -H4 H5 SUBTREE.
             move=> C.
             rewrite 2!setmE.
             case: eqP => HC2; subst.
             - move=> ls0 ls'0; rewrite H5 => [] [] <- [] <-.
               econstructor; econstructor.
             - case: eqP => HC1; subst.
               + move=> ls0 ls'0; rewrite H4 => [] [] <- [] <-.
                 econstructor; econstructor.
               + eapply SUBTREE. }
        -- eauto.

      * simpl in *; subst.

        (* Memory.store m (location C) (Int (Z.of_nat ?n)) = Some ?m' *)
        destruct (Memory.store_after_load m (location C) (Int (Z.of_nat p0)) (Int (Z.of_nat n))).
        rewrite -(MEM C Block.local 0%Z). eauto.
        (* destruct (MEM C Block.local 0%Z) as [MEM1 [MEM2 MEM3]]. *)
        now destruct H1 as [[] []].
        (* rewrite -MEM1. eauto. *)
        eexists; eexists; split.
        -- left.
           eapply star_plus_trans.

           assert (exists v, TreeWithCallers.prog_trees p C = Some v) as [v Hv].
           { apply /dommP. rewrite <- TreeWithCallers.wfprog_defined_trees; eauto. now destruct H1. }

           (* Using this lemma requires a unicity result *)
           { eapply build_event_expression_correct with (xe := XECallOut P z C2 rts1).
             - eapply TreeWithCallers.det_loc. eauto. eauto.
             - eapply subtrees_in_all_ev with (ls := l1 ++ node (p0, XECallOut P z C2 rts1, n, zs) ls :: l2).
               eapply in_app_iff; right; now left.
               eapply SUBTREE; eauto.
               eauto.
             - eauto.
             - simpl. rewrite Hv. reflexivity.
             - simpl. unfold location; rewrite <- MEM; eauto.
               now destruct H1.
             - eauto.
           }
           assert (H1' := H1).
           destruct H1 as [[? [? EXPORTED]]].
           destruct EXPORTED as [C_CI [EXP1 EXP2]].
           assert (exists v, TreeWithCallers.prog_procedures p C2 = Some v) as [v Hv].
           now apply /dommP; rewrite -(TreeWithCallers.wfprog_defined_procedures Hwf) //=.
           (* now destruct H1'. *)
           eapply plus_star_trans.
           { eapply call_event_correct; simpl; eauto.

             eapply find_procedure_find; eauto.
             eapply TreeWithCallers.wf_procedures_expression; eauto. now destruct H1'. }
           take_step.
           eapply star_refl.
           reflexivity. reflexivity.
        -- eapply match_states_silent; eauto.
           ++ econstructor. simpl.
              now destruct H1 as [[] []]; congruence.
              now inversion H12.
           ++ simpl.
              move=> C' b o Hintf.
              { destruct (b == Block.local) eqn:Hblock.
                - move: Hblock => /eqP Hblock; subst.
                  destruct (C' == C) eqn:HC1.
                  + move: HC1 => /eqP ->.
                    destruct (o == 0%Z) eqn:Ho; move: Ho => /eqP Ho; subst.
                 * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                   rewrite (Memory.load_after_store_eq _ _ _ _ H9).
                   rewrite (Memory.load_after_store_eq _ _ _ _ H); eauto.
                   unfold intcall, location; congruence.
                 * destruct (o == 1%Z) eqn:Ho'; move: Ho' => /eqP Ho'; subst.
                   -- rewrite (Memory.load_after_store_eq _ _ _ _ H10).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H).
                      rewrite -MEM. unfold intcall in INT. rewrite INT; eauto.
                      now destruct H1.
                      now destruct H1.
                      (* rewrite (Memory.load_after_store_eq _ _ _ _ MEM'''); eauto. *)
                      unfold location; congruence.
                   -- destruct (o == 2%Z) eqn:Ho''; move: Ho'' => /eqP Ho''; subst.
                      ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H).
                         rewrite MEM; eauto.
                         now destruct H1.
                         unfold location, ret; congruence.
                         unfold location, ret; congruence.
                         unfold intcall, ret; congruence.
                      ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H).
                         rewrite MEM; eauto.
                         now destruct H1.
                         unfold location; congruence.
                         unfold location; congruence.
                         unfold intcall; congruence.
               + (* move: HC1 => /eqP HC1. *)
                 rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                   rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                   rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H); eauto.

                   unfold location; move: HC1 => /eqP HC1 //=; congruence.
                   unfold location; move: HC1 => /eqP HC1 //=; congruence.
                   unfold intcall; move: HC1 => /eqP HC1 //=; congruence.
             - move: Hblock => /eqP Hblock.
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H).
               rewrite <- MEM; eauto.
               unfold location; congruence.
               unfold location; congruence.
               unfold intcall; congruence.
           }
           ++ simpl. reflexivity.
           ++ clear -H4 H5 SUBTREE.
              move=> C'.
              rewrite 2!setmE.
              case: eqP => HC2; subst.
              ** move: (SUBTREE C2).
                 case (TreeWithCallers.prog_trees p C2) => //= lsC2 SUB.
                 assert (subtrees ls' (l1' ++ node (p', XECallIn P z, n', zs') ls' :: l2')). econstructor. econstructor.
                 assert (subtrees (l1' ++ node (p', XECallIn P z, n', zs') ls' :: l2') lsC2). eapply SUB; eauto.
                 move=> ? ? [] ? [] ?; subst.
                 eapply subtrees_trans; eauto.
              ** case: eqP => HC1; subst.
                 move: (SUBTREE C).
                 case (TreeWithCallers.prog_trees p C) => //= lsC1 SUB.
                 assert (subtrees ls (l1 ++ node (p0, XECallOut P z C2 rts1, n, zs) ls :: l2)). econstructor. econstructor.
                 assert (subtrees (l1 ++ node (p0, XECallOut P z C2 rts1, n, zs) ls :: l2) lsC1). eapply SUB; eauto.
                 move=> ? ? [] ? [] ?; subst.
                 eapply subtrees_trans; eauto.
                 eapply SUBTREE.
    + (* Step return *)
      inv H0; subst.
      * inversion H.
      * simpl in *; subst.
        inv H8.
        (* loc C1 *)
        destruct (Memory.store_after_load m (location C) (Int (Z.of_nat p0)) (Int (Z.of_nat n))) as [m1 MEM1].
        unfold location; rewrite <- MEM. eauto. now destruct H1 as [? []].
        (* (* ret C2 *) *)
        assert (exists oldv, Memory.load m0 (ret C2) = Some oldv) as [oldv EQoldv].
        { clear -H9 H10.
          assert (Memory.load m' (ret C2) = Memory.load m0 (ret C2)).
          { eapply Memory.load_after_store with (ptr' := ret C2) in H9.
            move: H9; case: eqP; eauto; rewrite /location /ret; congruence. }
          rewrite <- H. clear H9 H.
          move: H10; rewrite /Memory.store /Memory.load.

          case: (m' (Pointer.component (ret C2))); last by [].
          intros mC.
          destruct (ComponentMemory.store mC (Pointer.block (ret C2)) (Pointer.offset (ret C2)) (Int z)) eqn:CONTRA; last by [].
          move=> [] ?.
          eapply ComponentMemory.invert_store. eauto. }
        destruct (Memory.store_after_load m1 (ret C2) oldv (Int z)) as [m2 MEM2].
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1); last by unfold ret, location; congruence.
        unfold ret; rewrite <- MEM.
        eauto. now destruct H1.
        (* (* loc 2 *) *)
        destruct (Memory.store_after_load m2 (location C2) (Int (Z.of_nat p')) (Int (Z.of_nat n'))) as [m3 MEM3].
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
        unfold location; rewrite <- MEM. eauto. now destruct H1.
        unfold location; destruct H1; congruence.
        unfold ret, location; congruence.
        (* (* intcall 2 *) *)
        destruct (Memory.store_after_load m3 (intcall C2) (Int 1%Z) (Int 0%Z)) as [m4 MEM4].
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
        rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
        unfold intcall; rewrite <- MEM. eapply INT.
        now destruct H1.
        now destruct H1.
        unfold location, intcall; congruence.
        unfold ret, intcall; congruence.
        unfold location, intcall; congruence.
        (* (* intcall 2 again *) *)
        destruct (Memory.store_after_load m4 (intcall C2) (Int 0%Z) (Int 1%Z)) as [m5 MEM5].
        rewrite (Memory.load_after_store_eq _ _ _ _ MEM4); eauto.
        destruct (unfold_stack ge m1 z arg STACK) as [stack1 [stack2 [arg1 [arg2 [Pid [UNF1 [UNF2 UNF3]]]]]]].
        eexists; eexists; split; simpl in *.
        -- left.
           eapply star_plus_trans.
           assert (exists v, TreeWithCallers.prog_trees p C = Some v) as [? Hv].
           { apply /dommP.
             rewrite -TreeWithCallers.wfprog_defined_trees.
             now destruct H1. eauto. }
           { eapply build_event_expression_correct with (xe := XERetOut z); simpl; eauto.
             - eapply TreeWithCallers.det_loc. eauto. eapply Hv.
             - eapply subtrees_in_all_ev with (ls := l1 ++ node (p0, XERetOut z, n, zs) ls :: l2).
               eapply in_app_iff; right; now left.
               eapply SUBTREE; eauto.
               eauto.
             - rewrite Hv. reflexivity.
             - unfold location; rewrite <- MEM. eauto. destruct H1 as [? []]; now auto.
           }
           eapply plus_star_trans. econstructor. econstructor.
           do 4 take_step. eauto. eauto.
           do 1 take_step. eapply star_refl. reflexivity.
           eapply star_trans. eapply UNF3.
           rewrite UNF1.
           eapply star_step. eapply CS.KS_ExternalReturn.
           now destruct H1.
           do 6 take_step. eauto. eauto.
           do 2 take_step.
           eapply star_trans.

           { eapply return_handling_expression_correct.
             - eauto.
             - admit.
             - eauto.
             - simpl. eauto.
             - simpl.
               rewrite (Memory.load_after_store_eq _ _ _ _ MEM2). eauto.
             - simpl.
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
               unfold location; rewrite <- MEM. eauto. now destruct H1.
               unfold location; now destruct H1; congruence.
               unfold ret, location; congruence.
             - simpl. eauto. }
           do 4 take_step. eauto. eauto.
           do 9 take_step. eauto. eauto.
           assert (exists procs, TreeWithCallers.prog_procedures p C2 = Some procs) as [? PROCS].
           { apply /dommP.
             rewrite -(TreeWithCallers.wfprog_defined_procedures Hwf).
             now destruct H1. }

           do 3 take_step. eauto.
           assert (exists v, TreeWithCallers.prog_procedures p C2 = Some v) as [v Hv].
           apply /dommP; rewrite -(TreeWithCallers.wfprog_defined_procedures Hwf) //=. now destruct H1.
           eapply find_procedure_find. eapply PROCS. admit. (* FIXME: add invariant, the current expression only contains
                                                             valid calls *)
           do 10 take_step. eauto.
           rewrite (Memory.load_after_store_eq _ _ _ _ MEM4); eauto.
           do 11 take_step. eauto. eauto.
           eapply star_refl.
           (* take_step. eapply star_refl. *)
           reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
        -- eapply match_states_6; simpl in *.
           ++ eauto.
           ++ eauto.
           ++ constructor. eauto.
           ++ intros C' b o Hintf.
              { clear -H9 H10 H11 MEM1 MEM2 MEM3 MEM4 MEM5 MEM Hintf H1 INT.
                destruct (b == Block.local) eqn:Hblock.
                - move: Hblock => /eqP Hblock; subst.
                  destruct (C' == C) eqn:HC1.
                  + move: HC1 => /eqP ->.
                    destruct (o == 0%Z) eqn:Ho; move: Ho => /eqP Ho; subst.
                    * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                      rewrite (Memory.load_after_store_eq _ _ _ _ H9).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                      rewrite (Memory.load_after_store_eq _ _ _ _ MEM1); eauto.
                      all: try (unfold intcall, ret, location; congruence).
                      unfold location; destruct H1; congruence.
                      unfold location; destruct H1; congruence.
                    * destruct (o == 1%Z) eqn:Ho'; move: Ho' => /eqP Ho'; subst.
                      -- rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
                         rewrite MEM. eauto. now destruct H1.
                         all: try (unfold intcall, ret, location; congruence).
                         unfold intcall; destruct H1; congruence.
                         unfold intcall; destruct H1; congruence.
                      -- rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
                         rewrite MEM. eauto. now destruct H1.
                         all: try (unfold intcall, ret, location; congruence).
                         unfold ret; destruct H1; congruence.
                         unfold ret; destruct H1; congruence.
                  + (* move: HC1 => /eqP HC1. *)
                    destruct (C' == C2) eqn:HC2.
                    * move: HC2 => /eqP ->.
                      destruct (o == 0%Z) eqn:Ho; move: Ho => /eqP Ho; subst.
                      -- rewrite (Memory.load_after_store_eq _ _ _ _ H11).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                         rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                         rewrite (Memory.load_after_store_eq _ _ _ _ MEM3); eauto.
                         unfold intcall; congruence.
                         unfold intcall; congruence.
                      -- destruct (o == 1%Z) eqn:Ho'; move: Ho' => /eqP Ho'; subst.
                         ++ rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                            rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                            rewrite (Memory.load_after_store_eq _ _ _ _ MEM5).
                            eapply INT. now destruct H1.
                            all: try (unfold intcall, ret, location; congruence).
                         ++ destruct (o == 2%Z) eqn:Ho''; move: Ho'' => /eqP Ho''; subst.
                            ** rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                               rewrite (Memory.load_after_store_eq _ _ _ _ H10).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                               rewrite (Memory.load_after_store_eq _ _ _ _ MEM2); eauto.
                               all: try (unfold intcall, ret, location; congruence).
                            ** rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                               rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                               rewrite <- MEM; eauto. now destruct H1.
                               all: try (unfold intcall, ret, location; congruence).
                    * rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                      rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                      rewrite <- MEM; eauto.
                      all: move: HC1 => /eqP HC1; move: HC2 => /eqP HC2; unfold intcall, ret, location; congruence.
                - move: Hblock => /eqP Hblock.
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM5).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM4).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM3).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM2).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ MEM1).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
                  rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
                  rewrite MEM. eauto. eauto.
                  all: unfold location, intcall, ret; congruence.
              }
           ++ reflexivity.
           ++ reflexivity.
           ++ move=> C0 H.
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H11).
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H10).
              rewrite (Memory.load_after_store_neq _ _ _ _ _ _ H9).
              eapply INT; eauto.
              unfold location, intcall; congruence.
              unfold ret, intcall; congruence.
              unfold location, intcall; congruence.

           ++ reflexivity.
           ++ clear -H4 H5 SUBTREE.
              move=> C'.
              rewrite 2!setmE.
              case: eqP => HC2; subst.
              ** move: (SUBTREE C2).
                 case (TreeWithCallers.prog_trees p C2) => //= lsC2 SUB.
                 assert (subtrees ls' (l1' ++ node (p', XERetIn z, n', zs') ls' :: l2')). econstructor. econstructor.
                 assert (subtrees (l1' ++ node (p', XERetIn z, n', zs') ls' :: l2') lsC2). eapply SUB; eauto.
                 move=> ? ? [] ? [] ?; subst.
                 eapply subtrees_trans; eauto.
              ** case: eqP => HC1; subst.
                 move: (SUBTREE C).
                 case (TreeWithCallers.prog_trees p C) => //= lsC1 SUB.
                 assert (subtrees ls (l1 ++ node (p0, XERetOut z, n, zs) ls :: l2)). econstructor. econstructor.
                 assert (subtrees (l1 ++ node (p0, XERetOut z, n, zs) ls :: l2) lsC1). eapply SUB; eauto.
                 move=> ? ? [] ? [] ?; subst.
                 eapply subtrees_trans; eauto.
                 eapply SUBTREE.
    + (* Step silent *)
      inv H0.
      (* We cannot be in a initial state *)
      inversion H.
      simpl in *; subst.
      (* Hence we are in a silently stepping state *)
      unfold match_cont in CONT. subst k.
      pose proof (@match_cont_step p C P ((globalenv (TreeWithCallers.sem p))) ge
                                   [CState C, stk0, m0, k0, e, arg]
                                   [CState C, stk0, m', k', exp', arg]
                                   [CState C, stk, m0, concat_event_expr p C P k0, e, arg]
                                   stk
                                   Logic.eq_refl Logic.eq_refl H3).
        eapply step_silent_mem_agree in H as [m1' [step agree]].
      eexists; eexists; split.
      * left.
        econstructor. eapply step. eapply star_refl. reflexivity.
      * simpl in *.
        destruct (update_can_silent [CState C, stk0, m', k', exp', arg]) eqn:UPDATE.
        -- eapply match_states_silent; eauto.
           ++ reflexivity.
        -- assert (k' = Kstop).
           { destruct k'; eauto;
               try (now rewrite (update_can_silent_k) in UPDATE; [inversion UPDATE | eauto]). }
           subst k'.
           eapply match_states_6; eauto. reflexivity. simpl in UPDATE.
           destruct exp'; now inversion UPDATE.
           admit.
      * eapply MEM.
Admitted.
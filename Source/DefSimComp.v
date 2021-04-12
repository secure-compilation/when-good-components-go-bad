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



Fixpoint give_nums (trs: list tree) (n: nat) :=
  match trs with
  | [] => []
  | tr :: trs' =>
    let (tr_num, n') := Tree.give_num_tree tr n in
    tr_num :: give_nums trs' (S n')
  end.

(* Admitted: this lemma states a property of the function that assigns locations to
   each node. *)
Lemma give_nums_app_comm: forall (l1 l2: list tree) (e: event) (ls: list tree) (n: nat),
    exists (n': nat) (l1' l2': list numbered_tree),
      give_nums (l1 ++ node e ls :: l2) n = l1' ++ node (e, n') (give_nums ls (S n')) :: l2'.
Proof.
  induction l1.
  - move=> l2 e ls n.
    destruct (give_num_tree_destruct (node e ls) n) as [tr [n' H1]].
    eexists; exists []; exists (give_nums l2 (S n')).
    do 2 erewrite app_nil_l.
    Arguments give_num_tree : simpl never.
    simpl.
    Arguments give_num_tree : simpl nomatch.
    rewrite H1.
    assert (exists n', give_num_tree (node e ls) n = (node (e, n) (give_nums ls (S n)), n')).
    { clear.
      revert e n.
      induction ls.
      - move=> e n.
        exists (S n). reflexivity.
      - move=> e n.
        unfold give_num_tree.
        fold (give_num_tree a (S n)).
        destruct a.
        + simpl.
          fold (give_num_tree (A := event)).
          admit.
        + simpl. admit.
    }
    destruct H as [n'' Heq].
    rewrite Heq in H1.
    now inversion H1.
  - move=> l2 e ls n.
    simpl.
    destruct (give_num_tree_destruct a n) as [a' [n' H1]].
    specialize (IHl1 l2 e ls (S n')) as [n'' [l1' [l2' H2]]].
    rewrite H1 H2.
    now exists n'', (a' :: l1'), l2'.
Admitted.

Lemma give_nums_determinate: forall ls n,
  determinate_tree_list eq ls ->
  determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) (give_nums ls n).
Proof.
  unfold determinate_tree_list; induction ls.
  - move=> n [H1 H2] //=.
    split.
    + unfold unique_list; intros; contradiction.
    + intros; contradiction.
  - move=> n [H1 H2].
    assert (UNIQ1: unique_list eq ls).
    { clear -H1.
      unfold unique_list in *. move=> t1 t2 H H0 H2.
      apply H1. right; eauto. right; eauto. eauto.
    }
    assert (UNIQ2: forall tr, In tr ls -> determinate_tree eq tr).
    { clear -H2.
      move=> tr H. eapply H2.
      right; eauto.
    }
    assert (exists a' n', give_nums (a :: ls) n = a' :: give_nums ls n' /\
                     content_of a = match (content_of a') with
                                    | None => None
                                    | Some (x, _) => Some x
                                    end)
      as [a' [n' [EQ CONT]]] by admit.
    rewrite EQ.
    specialize (IHls n' (conj UNIQ1 UNIQ2)) as [IH1 IH2].
    split.
    + admit.
    + move=> tr [H | H].
      * subst.
        clear -H2 CONT.
        specialize (H2 a (or_introl Logic.eq_refl)).
        destruct a; destruct tr as [| [] ]; simpl in *;
          try (now congruence);
          try (now constructor).
        inversion CONT; subst.
        admit.
      * eauto.
Admitted.


Definition compile_tree (p: Tree.prg): NumberedTree.prg :=
  {| NumberedTree.prog_interface := Tree.prog_interface p;
     NumberedTree.prog_trees := mapm (fun x => give_nums x 0) (Tree.prog_trees p) |}.

Fixpoint add_parent_loc (tr: numbered_tree) (n: nat): parent_aware_tree :=
  match tr with
  | leaf _ => leaf _
  | node (e, n') ls => node (n, e, n') (List.map (fun tr' => add_parent_loc tr' n') ls)
  end.

Definition compile_numbered_tree (p: NumberedTree.prg): ParentAwareTree.prg :=
  {| ParentAwareTree.prog_interface := NumberedTree.prog_interface p;
     ParentAwareTree.prog_trees := mapm (List.map (fun x => add_parent_loc x 0)) (NumberedTree.prog_trees p) |}.

Definition call_information (C: Component.id) (tr: parent_aware_tree): option (Z * nat) :=
  match tr with
  | node (_, ECall _ _ arg C', n) _ => if C == C' then Some (arg, n) else None
  | _ => None
  end.

Definition collect_callers (C: Component.id) (ls: list parent_aware_tree): list (Z * nat) :=
  List.fold_right (fun tr l => match tr with | None => l | Some x => x :: l end) [] (List.map (call_information C) ls).

Lemma collect_callers_cons: forall C t ls2, collect_callers C (t :: ls2) = collect_callers C [t] ++ collect_callers C ls2.
Proof.
  move=> C t ls2. unfold collect_callers; simpl.
  destruct (call_information C t).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma collect_callers_app: forall C ls1 ls2, collect_callers C (ls1 ++ ls2) = collect_callers C ls1 ++ collect_callers C ls2.
Proof.
  intros C ls1.
  (* unfold collect_callers. *)
  (* rewrite map_app fold_right_app. *)
  induction ls1.
  - move=> ls2. simpl. reflexivity.
  - move=> ls2. simpl.

    unfold collect_callers. simpl.
    destruct (call_information C a).
    + simpl. unfold collect_callers in IHls1.
      rewrite IHls1. reflexivity.
    + simpl. unfold collect_callers in IHls1.
      rewrite IHls1. reflexivity.
Qed.

Fixpoint add_caller (C: Component.id) (tr: parent_aware_tree): caller_aware_tree :=
  match tr with
  | leaf _ => leaf _
  | node (p, e, n) ls => node (p, e, n, collect_callers C ls) (List.map (add_caller C) ls)
  end.

Definition compile_parent_aware_tree (p: ParentAwareTree.prg): CallerAwareTree.prg :=
  {| CallerAwareTree.prog_interface := ParentAwareTree.prog_interface p;
     CallerAwareTree.prog_trees := mapim (fun C => List.map (add_caller C)) (ParentAwareTree.prog_trees p) |}.

Fixpoint get_corresp_returns_tree (stack: nat) (tr: caller_aware_tree) : list caller_aware_tree :=
  let fix get_corresp_returns_list (stack: nat) (ls : list caller_aware_tree) :=
      match ls with
      | [] => []
      | tr :: ls' => (get_corresp_returns_tree stack tr) ++ (get_corresp_returns_list stack ls')
      end
  in
  match stack, tr with
  | 1, node (_, ERet _ _ _, _, _) _ => [tr]
  | S stack', node (_, ERet _ _ _, _, _) ls => get_corresp_returns_list stack' ls
  | _, node (_, ECall _ _ _ _, _, _) ls => get_corresp_returns_list (S stack) ls
  | _, _ => []
  end.

Definition get_corresp_returns (tr : caller_aware_tree) : list (nat * Z * nat) :=
  match tr with
  | leaf _ => []
  | node (_, ECall _ _ _ _, _, _) _ => List.map (fun x => match x with
                                                   | node (lc, ERet _ v _, i, _) _ => (lc, v, i)
                                                   | _ => (0, 0%Z, 0) end)
                                            (get_corresp_returns_tree 0 tr)
  | node (_, ERet _ _ _, _, _) _ => []
  end.

Fixpoint build_call_return_tree (tr: caller_aware_tree): call_return_tree :=
  let zs := get_corresp_returns tr in
  match tr with
  | leaf _ => leaf _
  | node (n, ECall C0 P' z C', i, cls) ls =>
    node (n, XECall C0 P' z C' zs, i, cls) (List.map build_call_return_tree ls)
  | node (n, ERet C0 ret_val C', i, cls) ls =>
    node (n, XERet C0 ret_val C', i, cls) (List.map build_call_return_tree ls)
  end.

Definition compile_caller_aware_tree (p: CallerAwareTree.prg): CallReturnTree.prg :=
  {| CallReturnTree.prog_interface := CallerAwareTree.prog_interface p;
     CallReturnTree.prog_trees := mapm (List.map build_call_return_tree) (CallerAwareTree.prog_trees p) |}.

Lemma initial_callers_same: forall p,
    CallerAwareTree.initial_callers (CallerAwareTree.prog_trees p) =
    CallReturnTree.initial_callers (CallReturnTree.prog_trees (compile_caller_aware_tree p)).
Proof.
  move=> [intf p] /=.
  rewrite -eq_fmap. unfold "=1". move=> x.
  destruct (p x) eqn:Heq.
  - rewrite mapimE mapimE mapmE. rewrite Heq. simpl.
    clear.
    induction l.
    + simpl.
      rewrite /DefSimLanguages.CallerAwareTree.collect_callers_initial /DefSimLanguages.CallReturnTree.collect_callers_initial.
      reflexivity.
    + move: IHl.
      rewrite /DefSimLanguages.CallerAwareTree.collect_callers_initial /DefSimLanguages.CallReturnTree.collect_callers_initial.
      rewrite /CallerAwareTree.call_information_initial /CallReturnTree.call_information_initial.
      simpl. intros. inversion IHl. simpl. rewrite H0. simpl. clear IHl H0.
      destruct a as [| [[[a0 []] a2] a3] a4]; simpl. reflexivity.
      destruct (x == i1) eqn:Heq; rewrite Heq. reflexivity. reflexivity. reflexivity.
  - rewrite mapimE mapimE mapmE. rewrite Heq. simpl.
    reflexivity.
Qed.

Definition call_handling_info (x: (nat * xevent * nat * seq (Z * nat))) :=
  match x with
  | (_, _, n, cls) => (n, cls)
  end.

Definition get_all_handle_calls C P ots :=
  match ots with
  | None => []
  | Some ts =>
    let all_nodes := List.concat (List.map tree_to_list ts) in
    List.map call_handling_info (List.filter (node_of C P) all_nodes)
  end.

(* Definition switch_clause n e_then e_else := *)
(*     let one := E_val (Int 1%Z) in *)
(*     E_if (E_binop Eq (E_deref E_local) (E_val (Int n))) *)
(*          (E_seq (E_assign E_local (E_binop Add (E_deref E_local) one)) e_then) *)
(*          e_else. *)


Definition switch_clause_arg '(z, n) e_else :=
  E_if (E_binop Eq ARG (E_val (Int z)))
       (E_assign LOCATION_p (E_val (Int (Z.of_nat n))))
       e_else.

Definition switch_arg (cls: seq (Z * nat)): expr :=
  fold_right switch_clause_arg E_exit cls.

(* Definition switch_clause_call p e_then e_else := *)
(*   E_if (E_binop Eq LOCATION (E_val (Int (Z.of_nat p)))) *)
(*        e_then *)
(*        e_else. *)

Definition call_inner (clss: seq (nat * seq (Z * nat))): seq (nat * expr) :=
  List.map (fun '(p, cls) => (p, switch_arg cls)) clss.

Definition switch_clause_call '(p, exp) e_else :=
  E_if (E_binop Eq LOCATION (E_val (Int (Z.of_nat p))))
       exp
       e_else.

Definition switch_call (clss: seq (nat * expr)) :=
  fold_right switch_clause_call E_exit clss.

Definition callexp (clss: seq (nat * seq (Z * nat))): expr :=
    switch_call (call_inner clss).

Definition guard_call (e: expr) :=
  E_seq (E_if (E_binop Eq INTCALL (E_val (Int 1%Z)))
              e
              (E_val (Int 0%Z)))
        (E_assign (INTCALL_p) (E_val (Int 1%Z))).

Definition comp_call_handle C P trs :=
  guard_call (callexp (get_all_handle_calls C P trs)).

Definition callers (gs: trace * NMap (seq call_return_tree) * NMap nat * NMap (seq (Z * nat)) * stack): NMap (seq (Z * nat)) :=
  match gs with
  | (_, _, _, cls, _) => cls
  end.

Ltac take_step :=
  match goal with
  | |- @star _ _ _ _ _ ?t _ =>
    eapply (@star_step _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
  end.


Lemma call_handling_expression_correct: forall ge gs cs cs' C P zs zs1 z n zs2 p (trees: NMap (seq call_return_tree)) trs,
    (* unique_z zs -> *) (* zs = zs1 ++ (z, n) :: zs2 -> *)
    zs = zs1 ++ (z, n) :: zs2 ->
    forall (* (CALLERS: callers gs C = Some zs) *)
      (unique_p: unique_key (get_all_handle_calls C P (trees C)))
      (unique_z: unique_key zs)
      (TREES: trees C = Some trs)
      (INTREES: callers_in_trees C P p trs zs)
      (CUREXPR: CS.s_expr cs = guard_call (callexp (get_all_handle_calls C P (trees C))))
      (CURARG: CS.s_arg cs = Int z)
      (CURLOC: Memory.load (CS.s_memory cs) (location (CS.s_component cs)) = Some (Int (Z.of_nat p)))
      (CURINT: Memory.load (CS.s_memory cs) (intcall (CS.s_component cs)) = Some (Int 1%Z)),
      cs' = [CState (CS.s_component cs), (CS.s_stack cs), (CS.s_memory cs), Kseq (E_assign INTCALL_p (E_val (Int 1))) (CS.s_cont cs),
             E_assign LOCATION_p (E_val (Int (Z.of_nat n))), Int z] ->
      star TreeWithCallers.step ge (TreeWithCallers.Build_state gs cs (update_can_silent cs)) E0 (TreeWithCallers.Build_state gs cs' (update_can_silent cs')).
Proof.
  move=> ge gs [? ? ? ? ? ?] cs' C P zs zs1 z n zs2 p trees trs H unique_p unique_z TREES INTREES CUREXPR CURARG CURLOC CURINT H0.
  simpl in *; subst.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor. eauto. eauto.
  (* take_step; eauto. econstructor. eauto. eauto. *)
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  take_step; eauto. econstructor.
  rewrite Z.eqb_refl. simpl.
  remember (get_all_handle_calls C P (Some trs)) as ls.
  remember (zs1 ++ (z, n) :: zs2) as zs.
  subst.
  rewrite TREES.
  assert (H: exists ls1 ls2, get_all_handle_calls C P (Some trs) = ls1 ++ (p, zs1 ++ (z, n) :: zs2) :: ls2).
  { clear -INTREES.
    destruct INTREES as [tr [ls1 [ls2 [EQ INTREE]]]].
    remember (zs1 ++ (z, n) :: zs2) as zs.
    revert trs ls1 ls2 EQ Heqzs.
    induction INTREE.
    - move=> trs ls1 ls2 -> -> //=.
      rewrite map_app List.map_cons concat_app concat_cons filter_app map_app.
      move: H => //= -> //=.
      exists (List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls1)))).
      exists (List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls) ++
                                                                        concat (List.map tree_to_list ls2))%list)).
      (* exists zs1, zs2. *)
      simpl.
      reflexivity.
    - move=> trs ls1' ls2' -> EQ; move: EQ IHINTREE -> => IHINTREE.
      specialize (IHINTREE _ _ _ H Logic.eq_refl).
      move: IHINTREE.
      rewrite //= map_app List.map_cons concat_app concat_cons filter_app map_app //=.
      move=> [ls3 [ls4 EQ]].
      case: (node_of C P x) => //=.
      + rewrite filter_app map_app EQ.
        exists ((List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls1'))) ++
                     (call_handling_info x) :: ls3)).
        exists (ls4 ++ List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls2')))).
        (* exists zs3, zs4. *)
        set (LS1:= List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls1')))).
        set (LS2 := List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls2')))).
        rewrite -app_assoc app_comm_cons app_assoc.
        replace ((LS1 ++ (call_handling_info x :: ls3)%SEQ)%list) with (LS1 ++ (call_handling_info x :: ls3)); last reflexivity.
        replace ((((p, zs1 ++ (z, n) :: zs2) :: ls4)%SEQ ++ LS2)%list) with ((p, zs1 ++ (z, n) :: zs2) :: ls4 ++ LS2).
        reflexivity. reflexivity.
      + rewrite filter_app map_app EQ.
        exists ((List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls1'))) ++ ls3)).
        exists (ls4 ++ List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls2')))).
        (* exists zs3, zs4. *)
        set (LS1:= List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls1')))).
        set (LS2 := List.map call_handling_info (List.filter (node_of C P) (concat (List.map tree_to_list ls2')))).
        rewrite -app_assoc. simpl. rewrite app_assoc.
        replace ((p, zs1 ++ (z, n) :: zs2) :: (ls4 ++ LS2)%list)%SEQ with ((p, zs1 ++ (z, n) :: zs2) :: ls4 ++ LS2).
        reflexivity.
        eauto. }
  destruct H as [ls1 [ls2 H]].
  (* remember (get_all_handle_calls C P (Some trs)) as ls. *)
  rewrite H. rewrite TREES in unique_p. rewrite H in unique_p.
  remember (ls1 ++ (p, zs1 ++ (z, n) :: zs2) :: ls2) as ls.
  remember (zs1 ++ (z, n) :: zs2) as zs.
  clear H.
  generalize dependent ls.
  induction ls1; intros; subst.
  - rewrite /callexp /switch_call /call_inner List.map_cons //=.
    do 5 (take_step; eauto; [econstructor | eauto]). eauto. eauto.
    do 3 (take_step; eauto; [econstructor | eauto]).
    rewrite Z.eqb_refl //=.
    (* clear H. *)
    remember (zs1 ++ (z, n) :: zs2) as zs.
    (* clear H. *)
    clear TREES INTREES.
    generalize dependent zs.
    induction zs1; intros; subst.
    + simpl in *.
      (* do 1 (take_step; eauto; [econstructor | eauto]). *)
      (* rewrite Z.eqb_refl //=. *)
      do 6 (take_step; eauto; [econstructor | eauto]).
      rewrite Z.eqb_refl //=.
      eapply star_refl.
    + destruct a. simpl.
      take_step. eauto. eauto. econstructor. eauto.
      take_step. eauto. eauto. econstructor. eauto.
      take_step. eauto. eauto. econstructor. eauto.
      take_step. eauto. eauto. econstructor. eauto.
      take_step. eauto. eauto. econstructor. eauto.
      take_step. eauto. eauto. econstructor. eauto.
      (* do 6 (take_step; [eauto | reflexivity | econstructor | eauto]). *)
      assert (Hneq: z <> z0).
      { specialize (unique_z [] z0 n0 zs1 z n zs2). simpl in unique_z.
        intros Hn. eapply unique_z; eauto.
      }
      apply Z.eqb_neq in Hneq. rewrite Hneq. simpl.
      eapply IHzs1.
      reflexivity. eapply unique_key_smaller; eauto.
      simpl. simpl in unique_p.
      clear -unique_p.
      remember ((z0, n0) :: zs1 ++ (z, n) :: zs2) as x1.
      remember (zs1 ++ (z, n) :: zs2) as x2.
      clear -unique_p.
      move: unique_p; rewrite /unique_key //=.
      move=> unique_p ls1 a1 b1 ls0 a2 b2 ls3 H.
      destruct ls1.
      * simpl in H; inversion H; subst.
        eapply unique_p with (ls1 := []). reflexivity.
      * simpl in H; inversion H; subst.
        eapply unique_p with (ls2 := (p, x1) :: ls1). simpl. reflexivity.
  - destruct a. simpl.
    (* specialize (unique_p [] n0 l ls1 p (zs1' ++ (z, n) :: zs2') ls2 Logic.eq_refl). *)
    rewrite /callexp /switch_call /call_inner List.map_cons //=.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto. eauto. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    take_step. eauto. eauto. econstructor. eauto.
    (* do 5 (take_step; [eauto | reflexivity | econstructor | eauto]). eauto. eauto. *)
    (* do 3 (take_step; [eauto | reflexivity | econstructor | eauto]). *)
    (* do 5 (take_step; eauto; [econstructor | eauto]). eauto. eauto. *)
    (* do 3 (take_step; eauto; [econstructor | eauto]). *)
    assert (Hneq: Z.of_nat p <> Z.of_nat n0). apply Znat.inj_neq.
    specialize (unique_p [] n0 l ls1 p _ ls2 Logic.eq_refl). congruence.
    apply Z.eqb_neq in Hneq. rewrite Hneq. simpl.
    eapply IHls1. reflexivity.
    eapply unique_key_smaller; eauto.
Qed.


Definition compile_call_return_tree (p: CallReturnTree.prg): TreeWithCallers.prg :=
  {| TreeWithCallers.prog_interface := CallReturnTree.prog_interface p;
     TreeWithCallers.prog_procedures :=
       mapim (fun C Ciface =>
                let procs := if C == Component.main then
                   (Procedure.main |: Component.export Ciface)%fset
                 else Component.export Ciface in
                mkfmapf (fun P => comp_call_handle C P (CallReturnTree.prog_trees p C)) procs) (CallReturnTree.prog_interface p);
     TreeWithCallers.prog_trees :=  CallReturnTree.prog_trees p |}.

Lemma comp_is_well_formed (p: CallReturnTree.prg):
  CallReturnTree.wf p ->
  TreeWithCallers.wf (compile_call_return_tree p).
Proof.
  move=> [] sound_interface same_domm.
  constructor.
  - by [].
  - by [].
  - by rewrite domm_mapi.
  - by [].
  - move=> C P.
    rewrite /exported_procedure /Program.has_component /Component.is_exporting /find_procedure.
    case=> CI [C_CI P_CI] //=.
    rewrite mapimE C_CI //= mkfmapfE.
    case: ifP => //= <-.
    case: ifP => //= ?.
    by rewrite in_fsetU P_CI orbT.
  - move=> C P Pexpr.
    rewrite /find_procedure //= mapimE.
    case intf_C: (CallReturnTree.prog_interface p C)=> [CI|] //=.
    rewrite mkfmapfE; case: ifP=> //= P_CI [<-] {Pexpr}; split; last first.
    + rewrite /comp_call_handle /guard_call /callexp /switch_call /switch_clause_call /call_inner /= 2!andbT //=.
      elim: (get_all_handle_calls _ _ _) => [| [n ls] ? IH] //=.
      rewrite IH andbT /switch_arg /switch_clause_arg.
      elim: ls => [| [n' ls'] ? IH'] //=.
    + suff: (called_procedures (comp_call_handle C P (CallReturnTree.prog_trees p C)) = fset0) by move=> ->.
      rewrite //= !fset0U !fsetU0.
      rewrite /callexp /switch_call /switch_clause_call /call_inner.
      elim: (get_all_handle_calls _ _ _) => [| [n ls] ? IH] //=.
      rewrite IH !fsetU0 !fset0U.
      rewrite /switch_arg /switch_clause_arg.
      elim: ls => [| [n' ls'] ? IH'] //=.
      now rewrite !fset0U.
  -   set (valid_procedure C P :=
             C = Component.main /\ P = Procedure.main
             \/ exported_procedure (CallReturnTree.prog_interface p) C P).

      suff: (forall C P, valid_procedure C P ->
                    find_procedure (TreeWithCallers.prog_procedures (compile_call_return_tree p)) C P =
                    Some (comp_call_handle C P (CallReturnTree.prog_trees p C))).
      { move=> /(_ Component.main Procedure.main) ->.
        + split; first reflexivity.
          intros _ => //=.
          destruct (CallReturnTree.prog_interface p Component.main) as [mainP |] eqn:Hcase.
          * apply /dommP. exists mainP. assumption.
          * discriminate.
        + by left. }
      move=> C P [[-> ->] |].
      + rewrite /find_procedure /compile_call_return_tree.
        rewrite mapimE eqxx.
        case: (CallReturnTree.prog_interface p Component.main) (wf_has_main)=> [Cint|] //= _.
          by rewrite mkfmapfE in_fsetU1 eqxx.
      + move=> [CI [C_CI CI_P]].
        rewrite /find_procedure /compile_call_return_tree.
        rewrite mapimE C_CI /= mkfmapfE.
        case: eqP=> _; last by rewrite CI_P.
          by rewrite in_fsetU1 CI_P orbT.
  - eauto.
  - eauto.
Qed.

Definition concat_exp (e1 e2: expr): expr := E_seq e1 e2.

Fixpoint return_handling_expression (l: seq (nat * Z * nat)) :=
  match l with
  | [] => E_exit
  | (p, z, n) :: l' => E_if (AND (E_binop Eq LOCATION (E_val (Int (Z.of_nat p)))) (E_binop Eq RETURN (E_val (Int z))))
                          (E_assign LOCATION_p (E_val (Int (Z.of_nat n))))
                          (return_handling_expression l')
  end.

Definition unique_key_triple {A B C: Type} (ls: seq (A * B * C)) :=
  forall ls1 (a1: A) (b1: B) (c1: C) ls2 a2 b2 c2 ls3,
    ls = ls1 ++ (a1, b1, c1) :: ls2 ++ (a2, b2, c2) :: ls3 ->
    a1 <> a2.

Lemma return_handling_expression_correct: forall ge rts1 cs cs' z n p rts rts2 k,
    rts = rts1 ++ (p, z, n) :: rts2 ->
    unique_key rts ->
    CS.s_cont cs = k ->
    CS.s_expr cs = return_handling_expression rts ->
    Memory.load (CS.s_memory cs) (ret (CS.s_component cs)) = Some (Int z) ->
    Memory.load (CS.s_memory cs) (location (CS.s_component cs)) = Some (Int (Z.of_nat p)) ->
    cs' = [CState (CS.s_component cs), (CS.s_stack cs), (CS.s_memory cs), k,
           E_assign LOCATION_p (E_val (Int (Z.of_nat n))), CS.s_arg cs] ->
    star CS.kstep ge cs E0 cs'.
Proof.
  intros ge zs1.
  induction zs1.
  - move=> [C ? ? ? ? ?] cs' z n p rts rts2 k ? UNIQUE ? EXPR MEMLOAD1 MEMLOAD2 ?; subst; simpl in *.
    rewrite EXPR.
    do 20 (take_step; eauto).
    rewrite 2!Z.eqb_refl. simpl. eapply star_refl.
  - move=> [C ? ? ? ? ?] cs' z n p rts rts2 k ? UNIQUE ? EXPR MEMLOAD1 MEMLOAD2 ?; subst; simpl in *.
    destruct a as [[? ?] ?]. rewrite EXPR.
    do 20 (take_step; eauto).
    assert (H: (Util.Z.of_bool (Z.of_nat p =? Z.of_nat n0) * Util.Z.of_bool (z =? z0))%Z = 0%Z).
    { unfold unique_key in UNIQUE.
      specialize (UNIQUE [] (n0, z0) n1 zs1 (p, z) n rts2 Logic.eq_refl).
      assert (n0 <> p \/ z0 <> z).
      destruct (n0 == p) eqn:Heq. right. intros Hn. apply UNIQUE.
      rewrite Hn. move: Heq => /eqP -> //=.
      left. move: Heq => /eqP //=.
      destruct H.
      - assert (p <> n0) by congruence.
        destruct (Z.eqb_neq (Z.of_nat p) (Z.of_nat n0)) as [H1 H2].
        rewrite H2. eauto. intros Hn. apply H0. apply Nat2Z.inj. eauto.
      - assert (z <> z0) by congruence.
        rewrite <- (Z.eqb_neq z z0) in H0. rewrite H0.
        simpl.
        rewrite Z.mul_0_r. eauto.
    }
    rewrite H. simpl.
    eapply IHzs1; simpl; eauto.
    eapply unique_key_smaller; eauto.
Qed.

Definition event_expression (Pcaller: Procedure.id) (n: nat) (e: xevent) :=
  match e with
  | XECall C1 P z C2 rts => E_seq (E_assign LOCATION_p (E_val (Int (Z.of_nat n))))
                           (* (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 1)))) *)
                           (E_seq (E_assign RETURN_p (E_call C2 P (E_val (Int z)))) (* does the call and stores its value *)
                           (E_seq (return_handling_expression rts)
                           (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                  (E_call C1 Pcaller (E_val (Int (Z.of_nat 0)))))))
  | XERet C1 z C2 => E_seq (E_assign LOCATION_p (E_val (Int (Z.of_nat n))))
                    (* (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 1)))) *)
                            (E_val (Int z))
  end.

Lemma call_event_correct: forall ge C1 P Pcaller z C2 rts n cs cs' m' P_expr,
    allowed_xevent (genv_interface ge) (XECall C1 P z C2 rts) ->
    CS.s_component cs = C1 ->
    CS.s_expr cs = event_expression Pcaller n (XECall C1 P z C2 rts) ->
    find_procedure (genv_procedures ge) C2 P = Some P_expr ->
    Memory.store (CS.s_memory cs) (location (CS.s_component cs)) (Int (Z.of_nat n)) = Some m' ->
    cs' = [CState C2, CS.Frame C1 (CS.s_arg cs) (Kassign1 (RETURN_p)
                                                       (Kseq ((E_seq (return_handling_expression rts)
                                                                     (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                                            (E_call C1 Pcaller(E_val (Int (Z.of_nat 0)))))))
                                                             (CS.s_cont cs))) :: (CS.s_stack cs),
           m', Kstop, P_expr, Int z] ->
    plus CS.kstep ge cs [ECall C1 P z C2] cs'.
Proof.
  move=> ge C1 P P' z C2 rts n [? ? ? ? ? ?] cs' m' (* m'' *) P_expr ALLOWED COMP EXPR PROC MEMSTORE1 (* MEMSTORE2 *) ?; subst; simpl in *.
  rewrite EXPR.
  econstructor. econstructor.
  do 8 (take_step; eauto).
  eapply star_step. destruct ALLOWED as [[ALL0 ALL1] [ALL2 ALL3]].
  eapply CS.KS_ExternalCall. eauto. eauto. eauto.
  eapply star_refl.
  now rewrite E0_right.
  reflexivity.
Qed.

Lemma return_event_correct: forall ge n Pcaller C1 z C2 cs cs' old_arg rts old_stack m' (* m'' *),
    allowed_xevent (genv_interface ge) (XERet C1 z C2) ->
    CS.s_component cs = C1 ->
    CS.s_cont cs = Kstop ->
    CS.s_expr cs = event_expression Pcaller n (XERet C1 z C2) ->
    CS.s_stack cs = CS.Frame C2 old_arg (Kassign1 RETURN_p (Kseq ((E_seq (return_handling_expression rts)
                                                                         (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                                                (E_call C1 Procedure.main (E_val (Int (Z.of_nat 0)))))))
                                                                 Kstop)) :: old_stack ->
    Memory.store (CS.s_memory cs) (location (CS.s_component cs)) (Int (Z.of_nat n)) = Some m' ->
    (* Memory.store m' (intcall (CS.s_component cs)) (Int 1%Z) = Some m'' -> *)
    cs' = [CState C2, old_stack, m', (Kassign1 RETURN_p (Kseq ((E_seq (return_handling_expression rts)
                                                                         (E_seq (E_assign INTCALL_p (E_val (Int (Z.of_nat 0))))
                                                                                (E_call C1 Procedure.main (E_val (Int (Z.of_nat 0)))))))
                                                             Kstop)),
           E_val (Int z), old_arg] ->
    plus CS.kstep ge cs [ERet C1 z C2] cs'.
Proof.
  move=> ge n Pcaller C1 z C2 [? ? ? ? ? ?] cs' old_arg rts old_stack m' [ALL1 [ALL2 ALL3]] COMP CONT EXPR STACK MEMSTORE1 ?;
           subst; simpl in *.
  rewrite EXPR CONT.
  econstructor. econstructor.
  do 5 (take_step; eauto).
  rewrite STACK.
  eapply star_step. eapply CS.KS_ExternalReturn. eauto.
  eapply star_refl.
  now rewrite E0_right.
  reflexivity.
Qed.


Definition switch_clause_event '(p, e) e_else :=
  E_if (E_binop Eq LOCATION (E_val (Int (Z.of_nat p))))
       e
       e_else.

Definition switch_event (evs: seq (nat * expr)) :=
  fold_right switch_clause_event E_exit evs.

Definition node_of_comp C (x: nat * xevent * nat * seq (Z * nat)) :=
  match x with
  | (p, xe, n, cls) =>
    match xe with
    | XECall C0 P0 z C1 rts => C0 == C
    | XERet C0 z C1 => C0 == C
    end
  end.

Definition event_info (x: nat * xevent * nat * seq (Z * nat)) :=
  match x with
  | (p, xe, n, _) => (p, xe, n)
  end.

Definition get_all_event C ots :=
  match ots with
  | None => []
  | Some ts =>
    let all_nodes := List.concat (List.map tree_to_list ts) in
    List.map event_info (List.filter (node_of_comp C) all_nodes)
  end.

Definition build_event_expression (C: Component.id) (P: Procedure.id) ots :=
  let all_events := get_all_event C ots in
  let parent_plus_expr := List.map (fun '(p, xe, n) => (p, event_expression P n xe)) all_events in
  switch_event parent_plus_expr.


(* Admitted: this heavily relies on unicity of the location.
   It holds, because in our setting a tree that has control only has one possibility *)
Lemma build_event_expression_correct: forall ge cs cs' C P trs k trs' trs'' tr p xe n cls,
    forall (CURCONT: CS.s_cont cs = Kseq (build_event_expression C P (Some trs)) k)
      (SUBTREES: subtrees trs' trs)
      (TREES: trs' = [tr])
      (TREE: tr = node (p, xe, n, cls) trs'')
      (CURLOC: Memory.load (CS.s_memory cs) (location (CS.s_component cs)) = Some (Int (Z.of_nat p))),
      cs' = [CState (CS.s_component cs), (CS.s_stack cs), (CS.s_memory cs), k,
             event_expression P n xe, CS.s_arg cs] ->
      star CS.kstep ge cs E0 cs'.
Proof.
  Admitted.



Definition compile_tree_with_callers (p: TreeWithCallers.prg): program :=
  {| prog_interface := TreeWithCallers.prog_interface p;
     prog_procedures :=
       mapim (fun C procs => mapim (fun P call_exp => E_seq call_exp (build_event_expression C P (TreeWithCallers.prog_trees p C)))
                                procs) (TreeWithCallers.prog_procedures p);
     prog_buffers := (mapim (fun C Ciface => inr [Int 0%Z; Int 0%Z; Int 0%Z]) (TreeWithCallers.prog_interface p)) |}.

(* admitted: this is a well-formedness theorem of the source program that are generated *)
Lemma wf_compile (p: TreeWithCallers.prg) (WF: TreeWithCallers.wf p):
  well_formed_program (compile_tree_with_callers p).
Proof.
  case: WF => [] closed_intf sound_intf domm_eq domm_eq' exported_procs_ex well_formed_expr has_main.
  constructor.
  - by [].
  - by rewrite domm_mapi.
  - move=> C P //= H.
    case: (exported_procs_ex C P H); rewrite /find_procedure mapimE.
    case: (TreeWithCallers.prog_procedures p C) => //=.
    move=> a EQ; rewrite mapimE.
    by case: (a P) EQ.
  - move=> C P Pexpr.
    rewrite /find_procedure /compile_tree_with_callers mapimE.
    case procs_C: (TreeWithCallers.prog_procedures p C)=> [procs|] //=.
    rewrite mapimE.
    case expr_P: (procs P)=> [expr|] //=.
    move=> [] <-.
    move: (well_formed_expr) => /(_ C P expr).
    rewrite /find_procedure procs_C expr_P => /(_ Logic.eq_refl) [wf_expr1 wf_expr2].
    split.
    + have: (called_procedures (E_seq expr (build_event_expression C P (TreeWithCallers.prog_trees p C))) =
             called_procedures expr :|: called_procedures (build_event_expression C P (TreeWithCallers.prog_trees p C)))%fset by [].
      move=> -> //=.
      move=> C' P' /fsetUP => //=; move=> [in_called_expr | in_called].
      * (* The procedure is called in the expression generated at the previous step*)
        move: wf_expr1 => /(_ C' P' in_called_expr) //=.
        case: ifP => //=.
        rewrite /find_procedure //= mapimE => ?.
        case: (TreeWithCallers.prog_procedures p C) => //= a H; rewrite mapimE.
        by case: (a P') H.
      * (* The procedure is called is the expression generated at this step *)
        move: C' P' in_called.
        pose call_of_event (e: nat * xevent * nat) := if e is (_, XECall _ P _ C _, _) then Some (C, P) else None.
        have /fsubsetP sub :
          fsubset (called_procedures (build_event_expression C P (TreeWithCallers.prog_trees p C)))
                  ((C, P) |: fset (pmap call_of_event (get_all_event C (TreeWithCallers.prog_trees p C))))%fset.
        { rewrite /build_event_expression /switch_event /switch_clause_event /event_expression.
          move: wf_events => /(_ C).
          case: (TreeWithCallers.prog_trees p C) => //=; last by (move=> ?; apply fsub0set).
          move=> trs /(_ trs Logic.eq_refl) //=.
          assert (X: List.Forall (Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe)) trs ->
                     List.Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (concat (List.map tree_to_list trs))).
          { clear.
            induction trs.
            - simpl. econstructor.
            - simpl. move=> H.
              inversion H; subst; clear H.
              eapply List.Forall_app. split; eauto.
              eapply forall_list_forall. eauto.
          }
          move=> /X. clear X.

          assert (X: List.Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (concat (List.map tree_to_list trs)) ->
                     List.Forall (fun '(_, xe, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (List.map event_info (List.filter (node_of_comp C) (concat (List.map tree_to_list trs))))).
          { clear.
            elim: (concat (List.map tree_to_list trs)) => [|e t IH] //=.
            move=> H. inversion H; subst; clear H.
            case: (node_of_comp C e); last by eauto.
            simpl. econstructor. destruct e as [[[? ?] ?] ?]. eauto.
            eauto. }
          move=> /X; clear X.
          (* elim: (List.map event_info (List.filter (node_of_comp C) (concat (List.map tree_to_list trs)))) C'_P' Y => [|e t IH] //=. *)
          (* elim: (List.filter (node_of_comp C) (concat (List.map tree_to_list trs))) C'_P' => [|e t IH] //=. *)
          elim: (concat (List.map tree_to_list trs)) => [|e t IH] //=; first by move=> ?; apply fsub0set.
          destruct (node_of_comp C e) eqn:EQ.
          -- case: e EQ => [] [] [] p0 xe n0 cls EQ.
             case: xe EQ => [C' P' v C'' rts| C' z ?] EQ //=.
             ++ have: (called_procedures (return_handling_expression rts) = fset0).
                { rewrite /return_handling_expression. elim: rts {EQ} => [|[[p1 z] n1] rts' IH'] //=; by rewrite !fset0U. }
                move=> ->.
                rewrite !fsetU0 fset_cons !fsubUset !fsub1set !in_fsetU1 !eqxx !orbT //=.
                rewrite fsetUA [((C, P) |: fset1 (C'', P'))%fset]fsetUC -fsetUA fsubsetU //=.
                intros H. rewrite fsubsetU.
                ** simpl in EQ.
                   move: EQ => /eqP [->]; by rewrite eqxx.
                ** rewrite IH. by rewrite orbT. by inversion H.
                ** by rewrite fsub0set.
             ++ rewrite !fset0U. intros H; inversion H; subst; clear H. eauto.
          -- intros H. eapply IH. eauto.
        }

        move=> C' P' /sub/fsetU1P [[-> ->]|] {sub}.
        rewrite eqxx /find_procedure mapimE  procs_C //= mapimE expr_P //=.

        (* move: P_CI; case: eqP intf_C=> [->|_] intf_C. *)
        (*   rewrite /valid_procedure. *)
        (*   case/fsetU1P=> [->|P_CI]; eauto. *)
        (*   by right; exists CI; split. *)
        (* by move=> P_CI; right; exists CI; split. *)
        rewrite in_fset /= => C'_P'.
        suffices imp : imported_procedure (TreeWithCallers.prog_interface p) C C' P'.

        case: eqP procs_C => [<- |] //.
        move: (exported_procs_ex C' P').
        rewrite /find_procedure mapimE => ex EQ; move: ex; rewrite EQ //=.
        rewrite mapimE => H.
        assert (exported_procedure (TreeWithCallers.prog_interface p) C' P'). eapply closed_intf. eauto.
        specialize (H H0). move: H.
        by case: (procs P').

        specialize (wf_events C).
        move: C'_P' wf_events.
        case: (TreeWithCallers.prog_trees p C) => //= trs C'_P' /(_ trs Logic.eq_refl).
        assert (X: List.Forall (Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe)) trs ->
               List.Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (concat (List.map tree_to_list trs))).
        { clear.
          induction trs.
          - simpl. econstructor.
          - simpl. move=> H.
            inversion H; subst; clear H.
            eapply List.Forall_app. split; eauto.
            eapply forall_list_forall. eauto.
        }
        move=> /X. clear X.

        assert (X: List.Forall (fun '(_, xe, _, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (concat (List.map tree_to_list trs)) ->
                   List.Forall (fun '(_, xe, _) => allowed_xevent (TreeWithCallers.prog_interface p) xe) (List.map event_info (List.filter (node_of_comp C) (concat (List.map tree_to_list trs))))).
        { clear.
          elim: (concat (List.map tree_to_list trs)) => [|e t IH] //=.
          move=> H. inversion H; subst; clear H.
          case: (node_of_comp C e); last by eauto.
          simpl. econstructor. destruct e as [[[? ?] ?] ?]. eauto.
          eauto. }
        move=> /X; clear X.
        (* elim: (List.map event_info (List.filter (node_of_comp C) (concat (List.map tree_to_list trs)))) C'_P' Y => [|e t IH] //=. *)
        (* elim: (List.filter (node_of_comp C) (concat (List.map tree_to_list trs))) C'_P' => [|e t IH] //=. *)
        elim: (concat (List.map tree_to_list trs)) C'_P' => [|e t IH] //=.
        case: e => [] [] [] ? [C0 ? ? ? ?| C0 ? ?] ? ? //=.
        destruct (C0 == C) eqn:EQ.
        -- rewrite inE. case /orP.
           ++ move /eqP => [<- <-].
              move=> H'. inversion H'; subst; clear H'.
              destruct H1 as [[] ].
              by move: EQ => /eqP <-.
           ++ move=> H H'; inversion H'; now apply IH.
        -- move=> H H'; inversion H'; now apply IH.
        -- destruct (C0 == C) eqn:EQ => //=.
           move=> H H'; inversion H'; now apply IH.
    + rewrite /= wf_expr2 /=.
      rewrite /build_event_expression /switch_event /switch_clause_event.
      elim: (get_all_event C (TreeWithCallers.prog_trees p C)) => [|[[p0 e] n0] xs IH] //=.
      rewrite IH andbT.
      case: e => [? ? ? ? rts | ? ? ?] //=; rewrite andbT.
      elim: rts => [|[[p1 e] n1] rts IH'] //=.
  - by rewrite domm_mapi.
  - move=> C; rewrite -mem_domm => /dommP [CI C_CI].
    rewrite /has_required_local_buffers /= mapmE C_CI /=.
    eexists; eauto=> /=; lia.
  - move: has_main.
    rewrite /prog_main //= /find_procedure mapimE.
    case: (TreeWithCallers.prog_procedures p Component.main) => //=.
    move=> a EQ; rewrite mapimE.
    by case: (a Procedure.main) EQ.
Qed.

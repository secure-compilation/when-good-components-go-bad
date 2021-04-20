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

Definition event_in_component (C: Component.id) (e: event) :=
  (C == cur_comp_of_event e) || (C == next_comp_of_event e).

Variant loc_ev :=
(* Incoming call *)
| ECallIn: Procedure.id -> Z -> loc_ev
(* Outgoing call *)
| ECallOut: Procedure.id -> Z -> Component.id -> loc_ev
(* Incoming return *)
| ERetIn: Z -> loc_ev
(* Outgoing return *)
| ERetOut: Z -> loc_ev
.

Definition loc_ev_in_of_event (e: event) :=
  match e with
  | ECall C1 P z C2 => ECallIn P z
  | ERet C1 z C2 => ERetIn z
  end.

Definition loc_ev_out_of_event (e: event) :=
  match e with
  | ECall C1 P z C2 => ECallOut P z C2
  | ERet C1 z C2 => ERetOut z
  end.

Definition loc_is_out (e: loc_ev) :=
  match e with
  | ECallOut _ _ _ | ERetOut _ => true
  | ECallIn _ _ | ERetIn _ => false
  end.

Definition tree := Tree.t loc_ev.

Definition unique_loc_tree (ls: seq (loc_ev)) :=
  forall (p p' : nat) (par: nat) (e1 e2: loc_ev) (n1 n2: nat),
    loc_is_out e1 ->
    loc_is_out e2 ->
    nth_error ls p = Some (e1) ->
    nth_error ls p' = Some (e2) ->
    p = p'.

Definition numbered_tree := Tree.t (loc_ev * nat). (* nat: location *)
Definition unique_loc_num_tree (ls: seq (loc_ev * nat)) :=
  forall (p p' : nat) (par: nat) (e1 e2: loc_ev) (n1 n2: nat),
    loc_is_out e1 ->
    loc_is_out e2 ->
    nth_error ls p = Some (e1, n1) ->
    nth_error ls p' = Some (e2, n2) ->
    p = p'.

Definition parent_aware_tree := Tree.t (nat * loc_ev * nat). (* first nat: last time C had control *)

Definition unique_loc_par_tree (ls: seq (nat * loc_ev * nat)) :=
  forall (p p' : nat) (par: nat) (e1 e2: loc_ev) (n1 n2: nat),
    loc_is_out e1 ->
    loc_is_out e2 ->
    nth_error ls p = Some (par, e1, n1) ->
    nth_error ls p' = Some (par, e2, n2) ->
    p = p'.

Definition caller_aware_tree := Tree.t (nat * loc_ev * nat * list (Procedure.id * Z * nat)).

Definition unique_loc_cal_tree (ls: seq (nat * loc_ev * nat * list (Procedure.id * Z *nat))) :=
  forall (p p' : nat) (par: nat) (e1 e2: loc_ev) (n1 n2: nat) zs1 zs2,
    loc_is_out e1 ->
    loc_is_out e2 ->
    nth_error ls p = Some (par, e1, n1, zs1) ->
    nth_error ls p' = Some (par, e2, n2, zs2) ->
    p = p'.


Definition location (C: Component.id): Pointer.t := (C, Block.local, 0%Z).
Definition intcall (C: Component.id): Pointer.t := (C, Block.local, 1%Z).
Definition ret (C: Component.id): Pointer.t := (C, Block.local, 2%Z).

Definition unique_p {A: Type} (zs: list (nat * A)) :=
  forall p p' n a a',
    List.nth_error zs p = Some (n, a) ->
    List.nth_error zs p' = Some (n, a') ->
    p = p'.

Definition unique_p_z (zs: list (Procedure.id * Z * nat)) :=
  forall p p' P z n n',
    List.nth_error zs p = Some (P, z, n) ->
    List.nth_error zs p' = Some (P, z, n') ->
    p = p'.

Definition next_comp t :=
  match t with
  | [] => None
  | e :: t' => Some (cur_comp_of_event e)
  end.

Definition next_call_comp t :=
  match t with
  | ECall _ _ _ C2 :: t' => Some C2
  | _ => None
  end.

Definition next_call_proc t :=
  match t with
  | ECall _ P _ _ :: t' => Some P
  | _ => None
  end.

Definition next_call_arg t :=
  match t with
  | ECall _ _ z _ :: t' => Some z
  | _ => None
  end.

Definition allowed_event (intf: Program.interface) (e: event) :=
  match e with
  | ECall C1 P z C2 => C1 <> C2 /\ imported_procedure intf C1 C2 P /\ exported_procedure intf C2 P
  | ERet C1 z C2 => C1 <> C2
  end /\ cur_comp_of_event e \in domm intf /\ next_comp_of_event e \in domm intf.

Definition allowed_loc_event C (intf: Program.interface) (e: loc_ev):=
  match e with
  | ECallOut P z C2 => C <> C2 /\ imported_procedure intf C C2 P
  | ECallIn _ _ | ERetOut _ | ERetIn _ => True
  end.

Fixpoint wb_trace (st: seq Component.id) (t: trace) :=
  match t with
  | [] => true
  | ECall C1 _ _ C2 :: t' => wb_trace (C1 :: st) t'
  | ERet C1 _ C2 :: t' =>
    match st with
    | [] => false
    | C :: st' => (C == C2) && wb_trace st' t'
    end
  end.

Definition valid_trace (intf: Program.interface) (t: trace) :=
  forall e, In e t -> allowed_event intf e.

Definition events_sequence_ok (t: trace) :=
  match t with
  | [] => True
  | e :: [] => True
  | e :: t' => Some (next_comp_of_event e) = next_comp t'
  end.

Definition wf_trace (intf: Program.interface) (t: trace) :=
  wb_trace [] t /\ valid_trace intf t /\ next_comp t = Some Component.main /\ events_sequence_ok t.

Definition all_trees {A: Type} (a: A -> Prop) (trees: NMap (list (t A))): Prop :=
  forall C trs,
    trees C = Some trs ->
    List.Forall (Tree.Forall a) trs.

Inductive subtrees {A: Type}: seq (Tree.t A) -> seq (Tree.t A) -> Prop :=
| subtrees_eq: forall trs,
    subtrees trs trs
|subtrees_child: forall trs trs' trs1 trs2 x,
    subtrees trs trs' ->
    subtrees trs (trs1 ++ (node x trs') :: trs2)
.

Lemma subtrees_trans: forall (A: Type) (trs1 trs2 trs3: seq (t A)),
    subtrees trs1 trs2 ->
    subtrees trs2 trs3 ->
    subtrees trs1 trs3.
Proof.
  move=> A trs1 trs2 trs3 H1 H2.
  generalize dependent trs1.
  induction H2.
  - eauto.
  - intros.
    eapply IHsubtrees in H1.
    econstructor. eauto.
Qed.

Module Tree.
  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list tree) }.
  Definition genv := Program.interface.
  Definition state := (trace * NMap (list tree))%type.

  Record wf (p: prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
      wfprog_interface_soundness: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
      (*                                         exists ts, prog_trees p C = Some ts; *)
      determinacy: forall C ts, prog_trees p C = Some ts ->
                           determinate_tree_list eq ts;
      (* wf_events: all_trees (fun e => allowed_event (prog_interface p) e) (prog_trees p); *)
      wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun e => allowed_loc_event C (prog_interface p) e)) trs;
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
                     initial p (t, prog_trees p)
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees, final p ([], trees)
  .

  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list tree)) l1 l1' ls ls' l2 l2',
      forall (SEQOK: events_sequence_ok (e::t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node (loc_ev_out_of_event e) ls :: l2) ->
      trees C2 = Some (l1' ++ node (loc_ev_in_of_event e) ls' :: l2') ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list eq ls)
        (DET': determinate_tree_list eq ls'),
      step prog ge (e :: t, trees) [e] (t, setm (setm trees C1 ls) C2 ls' )
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.
End Tree.

Definition initial_locs (intf: Program.interface): NMap nat := mkfmapf (fun C => 0) (domm intf).
Lemma initial_locs_spec (intf: Program.interface): forall C,
    C \in (domm intf) ->
    initial_locs intf C = Some 0.
Proof.
  move=> C; by rewrite mkfmapfE => ->.
Qed.


Module NumberedTree.

  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list numbered_tree) }.
  Definition genv := Program.interface.
  Definition state := (trace * NMap (list numbered_tree) * NMap nat)%type.

  Record wf (p: prg) :=
    { wfprog_interface_soundness: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
      (*                          exists ts, prog_trees p C = Some ts; *)
      determinacy: forall C ts, prog_trees p C = Some ts ->
                           determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ts;
      (* wf_events: all_trees (fun '(e, n) => allowed_event (prog_interface p) e) (prog_trees p); *)
      wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun '(e, _) => allowed_loc_event C (prog_interface p) e)) trs;
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
                     initial p (t, prog_trees p, initial_locs (prog_interface p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees n, final p ([], trees, n)
  .

  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list numbered_tree)) (locs: NMap nat) l1 l1' ls ls' l2 l2' n n',
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node (loc_ev_out_of_event e, n) ls :: l2) ->
      trees C2 = Some (l1' ++ node (loc_ev_in_of_event e, n') ls' :: l2') ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls'),
      step prog ge (e :: t, trees, locs) [e] (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.
End NumberedTree.

Module ParentAwareTree.
  (* Here, each node contains the information of its parent node. *)

  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list parent_aware_tree) }.
  Definition genv := Program.interface.
  (* Trace * (Component.id -> trees) * (Component.id -> current loc) *)
  Definition state := (trace * NMap (list parent_aware_tree) * NMap nat)%type.

  Record wf (p: prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
      wfprog_interface_soundness: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      determinacy: forall C ts, prog_trees p C = Some ts ->
                           determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) ts;
      det_loc: forall C ts, prog_trees p C = Some ts ->
                     unique_loc_par_tree (List.concat (List.map tree_to_list ts));
      (* wf_events: all_trees (fun '(_, e, _) => allowed_event (prog_interface p) e) (prog_trees p); *)
      wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun '(_, e, _) => allowed_loc_event C (prog_interface p) e)) trs;
      wf_has_main: prog_interface p Component.main
                                  (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
                                  (*                                         exists t, prog_trees p C = Some t; *)
    }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
      forall (INIPARENT: forall C l1 p0 xe n ls l2,
            prog_trees p C = Some (l1 ++ node (p0, xe, n) ls :: l2) ->
            p0 = 0),
                     initial p (t, prog_trees p, initial_locs (prog_interface p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs, final p ([], trees, locs)
  .


  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list parent_aware_tree)) (locs: NMap nat)
                  l1 l1' ls ls' l2 l2' n n' p p',
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node (p, loc_ev_out_of_event e, n) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', loc_ev_in_of_event e, n') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _) '(_, e2, _) => e1 = e2) ls'),
      step prog ge (e :: t, trees, locs) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.
End ParentAwareTree.

Module CallerAwareTree.

  (* Here, in each node is stored the possible callers *)

  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list caller_aware_tree) }.
  Definition genv := Program.interface.
  (* Trace * (Component.id -> trees) * (Component.id -> current loc) * (Component.id -> caller_information )*)
  Definition state := (trace * NMap (list caller_aware_tree) * NMap nat * NMap (list (Procedure.id * Z * nat)))%type.

  Record wf (p: prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
      wfprog_interface_soundness: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      determinacy: forall C ts, prog_trees p C = Some ts ->
                           determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ts;
      det_loc: forall C ts, prog_trees p C = Some ts ->
                       unique_loc_cal_tree (List.concat (List.map tree_to_list ts));
      (* wf_events: all_trees (fun '(_, e, _, _) => allowed_event (prog_interface p) e) (prog_trees p); *)
      wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun '(_, e, _, _) => allowed_loc_event C (prog_interface p) e)) trs;
      wf_has_main: prog_interface p Component.main
                                  (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
                                  (*                                         exists t, prog_trees p C = Some t; *)
    }.

  Definition call_information_initial (C: Component.id) (tr: caller_aware_tree): option (Procedure.id * Z * nat) :=
    match tr with
    | node (_, ECallIn P arg, n, _) _ => Some (P, arg, n)
    | _ => None
    end.

  Local Definition collect_callers_initial (C: Component.id) (ls: list caller_aware_tree): list (Procedure.id * Z * nat) :=
    List.fold_right (fun tr l => match tr with | None => l | Some x => x :: l end)
                   [] (List.map (call_information_initial C) ls).

  Lemma collect_callers_initial_cons: forall C t ls2,
      collect_callers_initial C (t :: ls2) = collect_callers_initial C [t] ++ collect_callers_initial C ls2.
  Proof.
    move=> C t ls2. unfold collect_callers_initial; simpl.
    destruct (call_information_initial C t).
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma collect_callers_initial_app: forall C ls1 ls2,
      collect_callers_initial C (ls1 ++ ls2) = collect_callers_initial C ls1 ++ collect_callers_initial C ls2.
  Proof.
    intros C ls1.
    induction ls1.
    - move=> ls2. simpl. reflexivity.
    - move=> ls2. simpl.
      unfold collect_callers_initial. simpl.
      destruct (call_information_initial C a).
      + simpl. unfold collect_callers_initial in IHls1.
        rewrite IHls1. reflexivity.
      + simpl. unfold collect_callers_initial in IHls1.
        rewrite IHls1. reflexivity.
  Qed.

  Definition initial_callers (ls: NMap (list caller_aware_tree)): NMap (list (Procedure.id * Z * nat)) :=
    mapim (fun C => collect_callers_initial C) ls.
  Lemma initial_callers_spec (ls: NMap (list caller_aware_tree)): forall C,
      C \in (domm ls) ->
            exists cls, initial_callers ls C = Some cls.
  Proof.
    move=> C; rewrite mapimE mem_domm => H.
    destruct (ls C).
    - eexists; by [].
    - by [].
  Qed.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
      forall (INIPARENT: forall C l1 p0 xe n zs ls l2,
            prog_trees p C = Some (l1 ++ node (p0, xe, n, zs) ls :: l2) ->
            p0 = 0),
                     initial p (t, prog_trees p, initial_locs (prog_interface p), initial_callers (prog_trees p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs callers, final p ([], trees, locs, callers)
  .


  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e t (trees: NMap (list caller_aware_tree)) (locs: NMap nat) (callers: NMap (seq (Procedure.id * Z * nat)))
                  l1 l1' ls ls' l2 l2' n n' p p' zs zs' zs1 zs2 P z,
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      e = ECall C1 P z C2 ->
      trees C1 = Some (l1 ++ node (p, loc_ev_out_of_event e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', loc_ev_in_of_event e, n', zs') ls' :: l2') ->
      (* The caller information data that was collected contains all the possible calls! *)
      callers C2 = Some (zs1 ++ (P, z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      forall (UNIQ: unique_p_z (zs1 ++ (P, z, n') :: zs2)),
      step prog ge (e :: t, trees, locs, callers) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs')
  | step_ret: forall C1 C2 e t (trees: NMap (list caller_aware_tree)) (locs: NMap nat) (callers: NMap (seq (Procedure.id * Z * nat)))
                  l1 l1' ls ls' l2 l2' n n' p p' zs zs' z,
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      e = ERet C1 z C2 ->
      trees C1 = Some (l1 ++ node (p, loc_ev_out_of_event e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', loc_ev_in_of_event e, n', zs') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      step prog ge (e :: t, trees, locs, callers) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.

End CallerAwareTree.


Definition possible_returns := list (nat * Z * nat).
Definition stack := list (Component.id * possible_returns).
Inductive xevent :=
| XECallIn: Procedure.id -> Z -> xevent
| XECallOut: Procedure.id -> Z -> Component.id ->
             possible_returns -> xevent
| XERetIn: Z -> xevent
| XERetOut: Z -> xevent
.

Definition xevent_to_loc_event (xe: xevent) :=
  match xe with
  | XECallIn P z => ECallIn P z
  | XECallOut P z C rts => ECallOut P z C
  | XERetIn z => ERetIn z
  | XERetOut z => ERetOut z
  end.
Definition call_return_tree := Tree.t (nat * xevent * nat * list (Procedure.id * Z * nat)).

Definition initial_returns (intf: Program.interface): NMap (list (list (nat * Z * nat))) :=
  mkfmapf (fun _ => []) (domm intf).
Lemma initial_returns_spec (intf: Program.interface): forall C,
    C \in (domm intf) ->
    initial_returns intf C = Some [].
Proof.
  move=> C; by rewrite mkfmapfE => ->.
Qed.

Definition initial_stack: stack := [].

Definition allowed_xevent (C1: Component.id) (intf: Program.interface) (e: xevent) :=
  match e with
  | XECallOut P z C2 rts => C1 <> C2 /\ C2 \in domm intf /\ imported_procedure intf C1 C2 P
  | XECallIn _ _ | XERetIn _ | XERetOut _ => True
  end.

Definition is_out (xe: xevent) :=
  match xe with
  | XECallOut _ _ _ _ | XERetOut _ => true
  | XECallIn _ _ | XERetIn _ => false
  end.

Definition unique_loc (ls: seq (nat * xevent * nat)) :=
  forall (p p' : nat) (par: nat) (xe1 xe2: xevent) (n1 n2: nat),
    is_out xe1 ->
    is_out xe2 ->
    nth_error ls p = Some (par, xe1, n1) ->
    nth_error ls p' = Some (par, xe2, n2) ->
    p = p'.


Definition node_of_comp (x: nat * xevent * nat * seq (Procedure.id * Z * nat)) :=
  match x with
  | (p, xe, n, cls) =>
    match xe with
    | XECallOut _ _ _ _ | XERetOut _ => true
    | _ => false
    (* | XECall C0 P0 z C1 rts => C0 == C *)
    (* | XERet C0 z C1 => C0 == C *)
    end
  end.

Definition event_info (x: nat * xevent * nat * seq (Procedure.id * Z * nat)) :=
  match x with
  | (p, xe, n, _) => (p, xe, n)
  end.

Definition get_all_event ots :=
  match ots with
  | None => []
  | Some ts =>
    let all_nodes := List.concat (List.map tree_to_list ts) in
    List.map event_info (List.filter (node_of_comp) all_nodes)
  end.

Definition call_handling_info (x: (nat * xevent * nat * seq (Procedure.id * Z * nat))) :=
  match x with
  | (_, _, n, cls) => (n, cls)
  end.

Definition call_of P (x:((Procedure.id * Z * nat))) :=
  match x with
  | (P', _, _) => P == P'
  end.



Definition get_all_handle_calls (P: Procedure.id) ots :=
  match ots with
  | None => []
  | Some ts =>
    let all_nodes := List.concat (List.map tree_to_list ts) in
    List.map (fun '(n, ls) => (n, List.filter (call_of P) ls)) (List.map call_handling_info all_nodes)
  end.

Module CallReturnTree.

  (* Each call node contains information on how it can possibly be returned to *)
  (* The semantics introduce a stack per compartment that stores what the open calls are and how they may be returned to *)

  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list call_return_tree) }.
  Definition genv := Program.interface.
  (* Trace * (Component.id -> trees) * (Component.id -> current loc) * (Component.id -> caller_information )*)

  Definition state := (trace * NMap (list call_return_tree) * NMap nat * NMap (seq (Procedure.id * Z * nat)) * stack)%type.

  Record wf (p: prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
      wfprog_interface_soundness: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      determinacy: forall C ts, prog_trees p C = Some ts ->
                           determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ts;
      det_loc: forall C ts, prog_trees p C = Some ts ->
                       unique_loc (get_all_event (Some ts));
      (* wf_events: all_trees (fun '(_, xe, _, _) => allowed_xevent (prog_interface p) xe) (prog_trees p); *)
      wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun '(_, xe, _, _) => allowed_xevent C (prog_interface p) xe)) trs;
      wf_has_main: prog_interface p Component.main

                                  (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
                                  (*                                         exists t, prog_trees p C = Some t; *)
    }.


  Definition call_information_initial (C: Component.id) (tr: call_return_tree): option (Procedure.id * Z * nat) :=
    match tr with
    | node (_, XECallIn P arg, n, _) _ => Some (P, arg, n)
    | _ => None
    end.

  Local Definition collect_callers_initial (C: Component.id) (ls: list call_return_tree): seq (Procedure.id * Z * nat) :=
    List.fold_right (fun tr l => match tr with | None => l | Some x => x :: l end)
                   [] (List.map (call_information_initial C) ls).
  Lemma collect_callers_initial_cons: forall C t ls2,
      collect_callers_initial C (t :: ls2) = collect_callers_initial C [t] ++ collect_callers_initial C ls2.
  Proof.
    move=> C t ls2. unfold collect_callers_initial; simpl.
    destruct (call_information_initial C t).
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma collect_callers_initial_app: forall C ls1 ls2,
      collect_callers_initial C (ls1 ++ ls2) = collect_callers_initial C ls1 ++ collect_callers_initial C ls2.
  Proof.
    intros C ls1.
    induction ls1.
    - move=> ls2. simpl. reflexivity.
    - move=> ls2. simpl.
      unfold collect_callers_initial. simpl.
      destruct (call_information_initial C a).
      + simpl. unfold collect_callers_initial in IHls1.
        rewrite IHls1. reflexivity.
      + simpl. unfold collect_callers_initial in IHls1.
        rewrite IHls1. reflexivity.
  Qed.

  Definition initial_callers (ls: NMap (list call_return_tree)): NMap (seq (Procedure.id * Z * nat)) :=
    mapim (fun C => collect_callers_initial C) ls.
  Lemma initial_callers_spec (ls: NMap (list call_return_tree)): forall C,
      C \in (domm ls) ->
            exists cls, initial_callers ls C = Some cls.
  Proof.
    move=> C; rewrite mapimE mem_domm => H.
    destruct (ls C).
    - eexists; by [].
    - by [].
  Qed.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
      forall (INIPARENT: forall C l1 p0 xe n zs ls l2,
            prog_trees p C = Some (l1 ++ node (p0, xe, n, zs) ls :: l2) ->
            p0 = 0),
                     initial p (t, prog_trees p, initial_locs (prog_interface p),
                                initial_callers (prog_trees p), initial_stack)
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs callers st, final p ([], trees, locs, callers, st)
  .


  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                 (callers: NMap (seq (Procedure.id * Z * nat))) (st: stack)
                 l1 l1' ls ls' l2 l2' n n' p p' zs zs' zs1 zs2 P z rts1,
      forall (SEQOK: events_sequence_ok ((ECall C1 P z C2) :: t)),
      allowed_event ge (ECall C1 P z C2) ->
      e1 = XECallOut P z C2 rts1 ->
      e2 = XECallIn P z ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      callers C2 = Some (zs1 ++ (P, z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      forall (UNIQ: unique_p_z (zs1 ++ (P, z, n') :: zs2)),
      step prog ge (ECall C1 P z C2 :: t, trees, locs, callers, st) [ECall C1 P z C2]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n',
            setm (setm callers C1 zs) C2 zs',
            (C1, rts1) :: st)
  | step_ret: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                (callers: NMap (list (Procedure.id * Z * nat))) (st: stack)
                l1 l1' ls ls' l2 l2' n n' p p' zs zs' z rts rts1 rts2,
      forall (SEQOK: events_sequence_ok ((ERet C1 z C2) :: t)),
      allowed_event ge (ERet C1 z C2) ->
      e1 = XERetOut z ->
      e2 = XERetIn z ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      rts = rts1 ++ (p', z, n') :: rts2 ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      step prog ge (ERet C1 z C2 :: t, trees, locs, callers, (C2, rts) :: st) [ERet C1 z C2]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs', st)
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.

End CallReturnTree.

Definition LOCATION_p := E_local.
Definition LOCATION := E_deref E_local.
(* Definition ARG_p := E_binop Add E_local (E_val (Int 1)). *)
(* Definition ARG := E_deref ARG_p. *)
Definition INTCALL_p := E_binop Add E_local (E_val (Int 1)).
Definition INTCALL := E_deref INTCALL_p.
Definition ARG := E_arg.
Definition RETURN_p := E_binop Add E_local (E_val (Int 2)).
Definition RETURN := E_deref RETURN_p.

Definition AND (e1 e2: expr) := E_binop Mul e1 e2.

Definition unique_key {A B: Type} (ls: seq (A * B)) :=
  forall ls1 a1 b1 ls2 a2 b2 ls3,
    ls = ls1 ++ (a1, b1) :: ls2 ++ (a2, b2) :: ls3 ->
    a1 <> a2.

Lemma unique_key_smaller: forall {A B: Type} (a: A) (b: B) ls,
    unique_key ((a, b) :: ls) ->
    unique_key ls.
Proof.
  move=> A B a b ls.
  rewrite /unique_key => H.
  move=> ls1 a1 b1 ls2 a2 b2 ls3 H0.
  rewrite H0 in H.
  eapply (H ((a, b) :: ls1)). simpl. reflexivity.
Qed.

Definition update_can_silent (cs: CS.state): bool :=
  match CS.s_expr cs, CS.s_cont cs with
  | E_val _, Kstop => false
  (* | E_exit, Kstop => false *)
  | _, _ => true
  end.

Lemma update_can_silent_k: forall C stk m k e arg,
          k <> Kstop ->
          update_can_silent [CState C, stk, m, k, e, arg] = true.
Proof.
  move=> C stk m k e arg H.
  destruct e, k; eauto.
Qed.

Lemma update_can_silent_e: forall C stk m k e arg,
    (forall v, e <> E_val v) ->
    e <> E_exit ->
    update_can_silent [CState C, stk, m, k, e, arg] = true.
Proof.
  move=> C stk m k e arg H H0.
  destruct e, k; eauto.
  specialize (H v). contradiction.
Qed.

(* Sadly need to put that here *)

Definition switch_clause n e_then e_else :=
    let one := E_val (Int 1%Z) in
    E_if (E_binop Eq (E_deref E_local) (E_val (Int n)))
         (E_seq (E_assign E_local (E_binop Add (E_deref E_local) one)) e_then)
         e_else.


Definition switch_clause_arg (cl: Procedure.id * Z * nat) e_else :=
  let '(P, z, n) := cl in
  E_if (E_binop Eq ARG (E_val (Int z)))
       (E_assign LOCATION_p (E_val (Int (Z.of_nat n))))
       e_else.

Definition switch_arg (cls: seq (Procedure.id * Z * nat)): expr :=
  fold_right switch_clause_arg E_exit cls.

(* Definition switch_clause_call p e_then e_else := *)
(*   E_if (E_binop Eq LOCATION (E_val (Int (Z.of_nat p)))) *)
(*        e_then *)
(*        e_else. *)

Definition call_inner (clss: seq (nat * seq (Procedure.id * Z * nat))): seq (nat * expr) :=
  List.map (fun '(p, cls) => (p, switch_arg cls)) clss.

Definition switch_clause_call '(p, exp) e_else :=
  E_if (E_binop Eq LOCATION (E_val (Int (Z.of_nat p))))
       exp
       e_else.

Definition switch_call (clss: seq (nat * expr)) :=
  fold_right switch_clause_call E_exit clss.

Definition callexp (clss: seq (nat * seq (Procedure.id * Z * nat))): expr :=
    switch_call (call_inner clss).

Definition guard_call (e: expr) :=
  E_seq (E_if (E_binop Eq INTCALL (E_val (Int 1%Z)))
              e
              (E_val (Int 0%Z)))
        (E_assign (INTCALL_p) (E_val (Int 1%Z))).

Definition comp_call_handle P trs :=
  guard_call (callexp (get_all_handle_calls P trs)).





Module TreeWithCallers.

  Record prg := { prog_interface: Program.interface;
                  prog_procedures: NMap (NMap expr);
                  prog_trees: NMap (list call_return_tree) }.
  Definition genv := global_env.

  (* Boolean: whether we are doing call handling or not *)
  Record state := { ghost_state: (trace * NMap (list call_return_tree) * NMap nat * NMap (seq (Procedure.id * Z * nat)) * stack)%type;
                    concrete_state: CS.state;
                    can_silent: bool }.

  Record wf (p: prg) := {
    wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_procedures p);
    wfprog_defined_trees: domm (prog_interface p) = domm (prog_trees p);
    wfprog_exported_procedures_existence: forall C P,
        exported_procedure (prog_interface p) C P ->
        find_procedure (prog_procedures p) C P;
    wfprog_well_formed_procedures : forall (C : Component.id) (P : Procedure.id) (Pexpr : expr),
        find_procedure (prog_procedures p) C P = Some Pexpr ->
        valid_calls (prog_procedures p) (prog_interface p) C (called_procedures Pexpr)
        /\ values_are_integers Pexpr;
    wfprog_main_existence : Component.main \in domm (prog_interface p) <->
                                               find_procedure (prog_procedures p) Component.main Procedure.main;
    wf_events: forall C trs, prog_trees p C = Some trs ->
                    List.Forall (Forall (fun '(_, xe, _, _) => allowed_xevent C (prog_interface p) xe)) trs;
    det_loc: forall C ts, prog_trees p C = Some ts ->
                     unique_loc (get_all_event (Some ts));
    (* wf_events: all_trees (fun '(_, xe, _, _) => allowed_xevent (prog_interface p) xe) (prog_trees p); *)
    wf_has_main: prog_interface p Component.main
   }.

  Definition initial_callers := CallReturnTree.initial_callers.

  Definition initial_memory (intf: Program.interface) :=
    mkfmapf (fun C => ComponentMemory.prealloc [fmap (0, inr [Int 0; Int 1; Int 0])]) (domm intf).

  Definition initial_machine_state (intf: Program.interface) :=
    [CState Component.main, [::], initial_memory intf, Kstop, E_val (Int 0), Int 0].

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t,
      wf_trace (prog_interface p) t ->
      forall (INIPARENT: forall C l1 p0 xe n zs ls l2,
            prog_trees p C = Some (l1 ++ node (p0, xe, n, zs) ls :: l2) ->
            p0 = 0),
        initial p {| ghost_state := (t, prog_trees p, initial_locs (prog_interface p),
                                    initial_callers (prog_trees p), initial_stack);
                     concrete_state := initial_machine_state (prog_interface p);
                     can_silent := false |}
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs callers st cs b,
      final p {| ghost_state := ([], trees, locs, callers, st);
                 concrete_state := cs;
                 can_silent := b |}
  .


  Variant step (prog: prg) (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                 (callers: NMap (list (Procedure.id * Z * nat))) (st: stack)
          l1 l1' ls ls' l2 l2' n n' p p' zs zs' exp zs1 zs2 P z rts1
                 call_exp
                 gs gs' cs cs'
                 stk m m' m''
                 (* k  *)old_call_arg,
      forall (SEQOK: events_sequence_ok ((ECall C1 P z C2) :: t)),
      allowed_event (genv_interface ge) (ECall C1 P z C2) ->
      e1 = XECallOut P z C2 rts1 ->
      e2 = XECallIn P z ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      callers C2 = Some (zs1 ++ (P, z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      forall (LOC1: Memory.load m (location C1) = Some (Int (Z.of_nat p)))
        (LOC2: Memory.load m (location C2) = Some (Int (Z.of_nat p'))),
      (* Memory operations *)
      Memory.store m (location C1) (Int (Z.of_nat n)) = Some m' ->
      Memory.store m' (intcall C1) (Int 1%Z) = Some m'' ->
      find_procedure (genv_procedures ge) C2 P = Some call_exp ->
      forall (CALLEXP: call_exp = comp_call_handle P (prog_trees prog C2)),
      gs = (ECall C1 P z C2 :: t, trees, locs, callers, st) ->
      gs' = (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n',
             setm (setm callers C1 zs) C2 zs',
             (C1, rts1) :: st) ->
      cs = [CState C1, stk, m, Kstop, exp, old_call_arg] ->
      cs' = [CState C2, {| CS.f_component := C1; CS.f_arg := old_call_arg; CS.f_cont := Kstop |} :: stk,
             m'',
             Kstop,
             call_exp,
             Int z] ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      forall (UNIQ: unique_p_z (zs1 ++ (P, z, n') :: zs2)),
      step prog ge {| ghost_state := gs; concrete_state := cs; can_silent := false |} [ECall C1 P z C2]
           {| ghost_state := gs'; concrete_state := cs'; can_silent := true |}
  | step_ret: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                (callers: NMap (seq (Procedure.id * Z * nat))) (st: stack)
                l1 l1' ls ls' l2 l2' n n' p p' zs zs' z rts rts1 rts2
                gs gs' cs cs'
                stk m m' m'' m''' old_call_arg arg exp k,
      forall (SEQOK: events_sequence_ok (ERet C1 z C2 :: t)),
      allowed_event (genv_interface ge) (ERet C1 z C2) ->
      e1 = XERetOut z ->
      e2 = XERetIn z ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      rts = rts1 ++ (p', z, n') :: rts2 ->
      forall (LOC1: Memory.load m (location C1) = Some (Int (Z.of_nat p)))
        (LOC2: Memory.load m (location C2) = Some (Int (Z.of_nat p'))),
      Memory.store m (location C1) (Int (Z.of_nat n)) = Some m' ->
      Memory.store m' (ret C2) (Int z) = Some m'' ->
      Memory.store m'' (location C2) (Int (Z.of_nat n')) = Some m''' ->
      gs = (ERet C1 z C2 :: t, trees, locs, callers, (C2, rts) :: st) ->
      gs' = (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n',
             setm (setm callers C1 zs) C2 zs',
             st) ->
      cs = [CState C1, {| CS.f_component := C2; CS.f_arg := old_call_arg; CS.f_cont := k |} :: stk, m, Kstop, exp, arg] ->
      cs' = [CState C2, stk, m''', Kstop, E_val (Int (Z.of_nat n')), Int 0%Z] ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(_, e1, _, _) '(_, e2, _, _) => e1 = e2) ls'),
      step prog ge {| ghost_state := gs; concrete_state := cs; can_silent := false |} [ERet C1 z C2]
           {| ghost_state := gs'; concrete_state := cs'; can_silent := false |}
  | step_silent: forall C1 stk m m' k k' exp exp' arg
                   gs cs cs' b,
      cs = [CState C1, stk, m, k, exp, arg] ->
      cs' = [CState C1, stk, m', k', exp', arg] ->
      CS.kstep ge cs E0 cs' ->
      update_can_silent cs' = b ->
      step prog ge {| ghost_state := gs; concrete_state := cs; can_silent := true |} E0
           {| ghost_state := gs; concrete_state := cs'; can_silent := b |}
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := {| genv_interface := prog_interface p; genv_procedures := prog_procedures p |} |}.

End TreeWithCallers.

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

Definition tree := Tree.t event.
Definition numbered_tree := Tree.t (event * nat). (* nat: location *)
Definition parent_aware_tree := Tree.t (nat * event * nat). (* first nat: last time C had control *)
Definition caller_aware_tree := Tree.t (nat * event * nat * list (Z * nat)).


Definition location (C: Component.id): Pointer.t := (C, Block.local, 0%Z).
Definition intcall (C: Component.id): Pointer.t := (C, Block.local, 1%Z).
Definition ret (C: Component.id): Pointer.t := (C, Block.local, 2%Z).

Definition unique_z (zs: list (Z * nat)) :=
  forall p p' z n n',
    List.nth_error zs p = Some (z, n) ->
    List.nth_error zs p' = Some (z, n') ->
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
  | ECall C1 P z C2 => C1 <> C2 /\ imported_procedure intf C1 C2 P
  | ERet C1 z C2 => C1 <> C2
  end /\ cur_comp_of_event e \in domm intf /\ next_comp_of_event e \in domm intf.

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

Module Tree.
  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list tree) }.
  Definition genv := Program.interface.
  Definition state := (trace * NMap (list tree))%type.

  Record wf (p: prg) := {
    wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
    (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
    (*                                         exists ts, prog_trees p C = Some ts; *)
    determinacy: forall C ts, prog_trees p C = Some ts ->
                         determinate_tree_list eq ts;
    wf_events: all_trees (fun e => allowed_event (prog_interface p) e) (prog_trees p);
    wf_has_main: prog_interface p Component.main }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
                     initial p (t, prog_trees p)
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees, final p ([], trees)
  .

  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list tree)) l1 l1' ls ls' l2 l2',
      forall (SEQOK: events_sequence_ok (e::t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node e ls :: l2) ->
      trees C2 = Some (l1' ++ node e ls' :: l2') ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list eq ls)
        (DET': determinate_tree_list eq ls'),
      step ge (e :: t, trees) [e] (t, setm (setm trees C1 ls) C2 ls' )
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
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

  Record wf (p: prg) := {
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
    (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
    (*                          exists ts, prog_trees p C = Some ts; *)
    determinacy: forall C ts, prog_trees p C = Some ts ->
                         determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ts;
    wf_events: all_trees (fun '(e, n) => allowed_event (prog_interface p) e) (prog_trees p);
    wf_has_main: prog_interface p Component.main
                       }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
                     initial p (t, prog_trees p, initial_locs (prog_interface p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees n, final p ([], trees, n)
  .

  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list numbered_tree)) (locs: NMap nat) l1 l1' ls ls' l2 l2' n n',
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node (e, n) ls :: l2) ->
      trees C2 = Some (l1' ++ node (e, n') ls' :: l2') ->
      (* Determinacy and unicity *)
      forall (DET: determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls)
        (DET': determinate_tree_list (fun '(e1, _) '(e2, _) => e1 = e2) ls'),
      step ge (e :: t, trees, locs) [e] (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
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

  Record wf (p: prg) := {
    wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
    wf_events: all_trees (fun '(_, e, _) => allowed_event (prog_interface p) e) (prog_trees p);
    wf_has_main: prog_interface p Component.main
    (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
    (*                                         exists t, prog_trees p C = Some t; *)
                        }.

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
                     initial p (t, prog_trees p, initial_locs (prog_interface p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs, final p ([], trees, locs)
  .


  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_trace: forall C1 C2 e t (trees: NMap (list parent_aware_tree)) (locs: NMap nat)
                  l1 l1' ls ls' l2 l2' n n' p p',
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      C1 = cur_comp_of_event e ->
      C2 = next_comp_of_event e ->
      trees C1 = Some (l1 ++ node (p, e, n) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e, n') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      step ge (e :: t, trees, locs) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
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
  Definition state := (trace * NMap (list caller_aware_tree) * NMap nat * NMap (list (Z * nat)))%type.

  Record wf (p: prg) := {
    wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
    wf_events: all_trees (fun '(_, e, _, _) => allowed_event (prog_interface p) e) (prog_trees p);
    wf_has_main: prog_interface p Component.main
    (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
    (*                                         exists t, prog_trees p C = Some t; *)
                        }.

  Definition call_information_initial (C: Component.id) (tr: caller_aware_tree): option (Z * nat) :=
    match tr with
    | node (_, ECall _ _ arg C', n, _) _ => if C == C' then Some (arg, n) else None
    | _ => None
    end.

  Local Definition collect_callers_initial (C: Component.id) (ls: list caller_aware_tree): list (Z * nat) :=
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

  Definition initial_callers (ls: NMap (list caller_aware_tree)): NMap (list (Z * nat)) :=
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
                     initial p (t, prog_trees p, initial_locs (prog_interface p), initial_callers (prog_trees p))
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs callers, final p ([], trees, locs, callers)
  .


  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e t (trees: NMap (list caller_aware_tree)) (locs: NMap nat) (callers: NMap (list (Z * nat)))
                  l1 l1' ls ls' l2 l2' n n' p p' zs zs' zs1 zs2 P z,
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      e = ECall C1 P z C2 ->
      trees C1 = Some (l1 ++ node (p, e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e, n', zs') ls' :: l2') ->
      (* The caller information data that was collected contains all the possible calls! *)
      callers C2 = Some (zs1 ++ (z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      step ge (e :: t, trees, locs, callers) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs')
  | step_ret: forall C1 C2 e t (trees: NMap (list caller_aware_tree)) (locs: NMap nat) (callers: NMap (list (Z * nat)))
                  l1 l1' ls ls' l2 l2' n n' p p' zs zs' z,
      forall (SEQOK: events_sequence_ok (e :: t)),
      allowed_event ge e ->
      e = ERet C1 z C2 ->
      trees C1 = Some (l1 ++ node (p, e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e, n', zs') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      step ge (e :: t, trees, locs, callers) [e]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs')
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.

End CallerAwareTree.


Definition possible_returns := list (nat * Z * nat).
Definition stack := list (Component.id * possible_returns).
Inductive xevent :=
| XECall : Component.id -> Procedure.id -> Z -> Component.id ->
           possible_returns -> (* last time C had control * return value * next location *)
           xevent
| XERet : Component.id -> Z -> Component.id ->
          xevent.
Definition call_return_tree := Tree.t (nat * xevent * nat * list (Z * nat)).

Definition initial_returns (intf: Program.interface): NMap (list (list (nat * Z * nat))) :=
  mkfmapf (fun _ => []) (domm intf).
Lemma initial_returns_spec (intf: Program.interface): forall C,
    C \in (domm intf) ->
    initial_returns intf C = Some [].
Proof.
  move=> C; by rewrite mkfmapfE => ->.
Qed.

Definition initial_stack: stack := [].

Definition cur_comp_of_xevent (e: xevent) :=
  match e with
  | XECall C _ _ _ _ => C
  | XERet C _ _ => C
  end.

Definition next_comp_of_xevent (e: xevent) :=
  match e with
  | XECall _ _ _ C _ => C
  | XERet _ _ C => C
  end.

Definition allowed_xevent (intf: Program.interface) (e: xevent) :=
  match e with
  | XECall C1 P z C2 rts => C1 <> C2 /\ imported_procedure intf C1 C2 P
  | XERet C1 _ C2 => C1 <> C2
  end /\ cur_comp_of_xevent e \in domm intf /\ next_comp_of_xevent e \in domm intf.

Lemma allowed_event_allowed_xevent (intf: Program.interface):
  forall (e: xevent),
    match e with
    | XECall C1 P z C2 rts => allowed_event intf (ECall C1 P z C2)
    | XERet C1 z C2 => allowed_event intf (ERet C1 z C2)
    end ->
    allowed_xevent intf e.
Proof.
  intros []; eauto.
Qed.

Definition node_of C P (x:(nat * xevent * nat * seq (Z * nat))) :=
  match x with
  | (p, xe, n, cls) =>
    match xe with
    | XECall C0 P0 z C1 rts => (C0 == C) && (P0 == P)
    | XERet C0 z C1 => C0 == C
    end
  end.

Inductive callers_in_tree: Component.id -> Procedure.id -> nat -> call_return_tree -> seq (Z * nat) -> Prop :=
| callers_in_node: forall C P p e n zs ls,
    node_of C P (p, e, n, zs) ->
    callers_in_tree C P n (node (p, e, n, zs) ls) zs
| callers_in_child: forall C P p ls ls1 tr ls2 zs x,
    ls = ls1 ++ tr :: ls2 ->
    callers_in_tree C P p tr zs ->
    callers_in_tree C P p (node x ls) zs.

Definition callers_in_trees (C: Component.id) (P: Procedure.id) (p: nat) (ls: seq call_return_tree) (callers: seq (Z * nat)) :=
  exists tr ls1 ls2,
    ls = ls1 ++ tr :: ls2 /\ callers_in_tree C P p tr callers.

Inductive subtrees {A: Type}: seq (Tree.t A) -> seq (Tree.t A) -> Prop :=
| subtrees_eq: forall trs,
    subtrees trs trs
|subtrees_child: forall trs trs' trs1 trs2 x,
    subtrees trs trs' ->
    subtrees trs (trs1 ++ (node x trs') :: trs2)
.

Lemma callers_in_subtrees: forall C P p trs trs' zs,
    subtrees trs trs' ->
    callers_in_trees C P p trs zs ->
    callers_in_trees C P p trs' zs.
Proof.
  move=> C P p trs trs' zs H.
  induction H.
  - eauto.
  - move=> H0.
    specialize (IHsubtrees H0).
    unfold callers_in_trees.
    destruct IHsubtrees as [tr [ls1 [ls2 [IH1 IH2]]]].
    rewrite IH1.
    eexists; eexists; eexists. split. eauto.
    econstructor. eauto. eauto.
Qed.

Module CallReturnTree.

  (* Each call node contains information on how it can possibly be returned to *)
  (* The semantics introduce a stack per compartment that stores what the open calls are and how they may be returned to *)

  Record prg := { prog_interface: Program.interface;
                  prog_trees: NMap (list call_return_tree) }.
  Definition genv := Program.interface.
  (* Trace * (Component.id -> trees) * (Component.id -> current loc) * (Component.id -> caller_information )*)

  Definition state := (trace * NMap (list call_return_tree) * NMap nat * NMap (seq (Z * nat)) * stack)%type.

  Record wf (p: prg) := {
    wfprog_interface_closed: closed_interface (prog_interface p); (* NOTE: closed_interface implies sound_interface *)
    wfprog_interface_soundness: sound_interface (prog_interface p);
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
    wf_events: all_trees (fun '(_, xe, _, _) => allowed_xevent (prog_interface p) xe) (prog_trees p);
    wf_has_main: prog_interface p Component.main

    (* wf_has_trees: forall C, C \in domm (prog_interface p) -> *)
    (*                                         exists t, prog_trees p C = Some t; *)
                        }.


  Definition call_information_initial (C: Component.id) (tr: call_return_tree): option (Z * nat) :=
    match tr with
    | node (_, XECall _ _ arg C' _, n, _) _ => if C == C' then Some (arg, n) else None
    | _ => None
    end.

  Local Definition collect_callers_initial (C: Component.id) (ls: list call_return_tree): list (Z * nat) :=
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

  Definition initial_callers (ls: NMap (list call_return_tree)): NMap (list (Z * nat)) :=
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
                     initial p (t, prog_trees p, initial_locs (prog_interface p),
                                initial_callers (prog_trees p), initial_stack)
  .

  Variant final (p: prg): state -> Prop :=
  | final_nil: forall trees locs callers st, final p ([], trees, locs, callers, st)
  .


  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                 (callers: NMap (list (Z * nat))) (st: stack)
                 l1 l1' ls ls' l2 l2' n n' p p' zs zs' zs1 zs2 P z rts1 rts2,
      forall (SEQOK: events_sequence_ok ((ECall C1 P z C2) :: t)),
      allowed_xevent ge e1 ->
      e1 = XECall C1 P z C2 rts1 ->
      e2 = XECall C1 P z C2 rts2 ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      callers C2 = Some (zs1 ++ (z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      step ge (ECall C1 P z C2 :: t, trees, locs, callers, st) [ECall C1 P z C2]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n',
            setm (setm callers C1 zs) C2 zs',
            (C1, rts1) :: st)
  | step_ret: forall C1 C2 e t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                (callers: NMap (list (Z * nat))) (st: stack)
                l1 l1' ls ls' l2 l2' n n' p p' zs zs' z rts rts1 rts2,
      forall (SEQOK: events_sequence_ok ((ERet C1 z C2) :: t)),
      allowed_xevent ge e ->
      e = XERet C1 z C2 ->
      trees C1 = Some (l1 ++ node (p, e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e, n', zs') ls' :: l2') ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      rts = rts1 ++ (p', z, n') :: rts2 ->
      step ge (ERet C1 z C2 :: t, trees, locs, callers, (C2, rts) :: st) [ERet C1 z C2]
           (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n', setm (setm callers C1 zs) C2 zs', st)
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
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
  | E_exit, Kstop => false
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

Module TreeWithCallers.

  Record prg := { prog_interface: Program.interface;
                  prog_procedures: NMap (NMap expr);
                  prog_trees: NMap (list call_return_tree) }.
  Definition genv := global_env.

  (* Boolean: whether we are doing call handling or not *)
  Record state := { ghost_state: (trace * NMap (list call_return_tree) * NMap nat * NMap (seq (Z * nat)) * stack)%type;
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
    wf_events: all_trees (fun '(_, xe, _, _) => allowed_xevent (prog_interface p) xe) (prog_trees p);
    wf_has_main: prog_interface p Component.main
   }.

  Definition initial_callers := CallReturnTree.initial_callers.

  Definition initial_memory (intf: Program.interface) :=
    mkfmapf (fun C => ComponentMemory.prealloc [fmap (0, inr [Int 0; Int 1; Int 0])]) (domm intf).

  Definition initial_machine_state (intf: Program.interface) :=
    [CState Component.main, [::], initial_memory intf, Kstop, E_val (Int 0), Int 0].

  Variant initial (p: prg): state -> Prop :=
  | initial_st: forall t, wf_trace (prog_interface p) t ->
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


  Variant step (ge: genv): state -> trace -> state -> Prop :=
  | step_call: forall C1 C2 e1 e2 t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                 (callers: NMap (list (Z * nat))) (st: stack)
          l1 l1' ls ls' l2 l2' n n' p p' zs zs' exp zs1 zs2 P z rts1 rts2
                 call_exp
                 gs gs' cs cs'
                 stk m m'
                 (* k  *)old_call_arg,
      forall (SEQOK: events_sequence_ok ((ECall C1 P z C2) :: t)),
      allowed_xevent (genv_interface ge) e1 ->
      e1 = XECall C1 P z C2 rts1 ->
      e2 = XECall C1 P z C2 rts2 ->
      trees C1 = Some (l1 ++ node (p, e1, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e2, n', zs') ls' :: l2') ->
      callers C2 = Some (zs1 ++ (z, n') :: zs2) ->
      locs C1 = Some p ->
      locs C2 = Some p' ->
      forall (LOC1: Memory.load m (location C1) = Some (Int (Z.of_nat p)))
        (LOC2: Memory.load m (location C2) = Some (Int (Z.of_nat p'))),
      Memory.store m (location C1) (Int (Z.of_nat n)) = Some m' ->
      find_procedure (genv_procedures ge) C2 P = Some call_exp ->
      gs = (ECall C1 P z C2 :: t, trees, locs, callers, st) ->
      gs' = (t, setm (setm trees C1 ls) C2 ls', setm (setm locs C1 n) C2 n',
             setm (setm callers C1 zs) C2 zs',
             (C1, rts1) :: st) ->
      cs = [CState C1, stk, m, Kstop, exp, old_call_arg] ->
      cs' = [CState C2, {| CS.f_component := C1; CS.f_arg := old_call_arg; CS.f_cont := Kstop |} :: stk,
             m',
             Kstop,
             call_exp,
             Int z] ->
      step ge {| ghost_state := gs; concrete_state := cs; can_silent := false |} [ECall C1 P z C2]
           {| ghost_state := gs'; concrete_state := cs'; can_silent := true |}
  | step_ret: forall C1 C2 e t (trees: NMap (list call_return_tree)) (locs: NMap nat)
                (callers: NMap (list (Z * nat))) (st: stack)
                l1 l1' ls ls' l2 l2' n n' p p' zs zs' z rts rts1 rts2
                gs gs' cs cs'
                stk m m' m'' m''' old_call_arg arg exp k,
      forall (SEQOK: events_sequence_ok (ERet C1 z C2 :: t)),
      allowed_xevent (genv_interface ge) e ->
      e = XERet C1 z C2 ->
      trees C1 = Some (l1 ++ node (p, e, n, zs) ls :: l2) ->
      trees C2 = Some (l1' ++ node (p', e, n', zs') ls' :: l2') ->
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
      cs' = [CState C2, stk, m''', Kstop, E_val (Int (Z.of_nat n')), old_call_arg] ->
      step ge {| ghost_state := gs; concrete_state := cs; can_silent := false |} [ERet C1 z C2]
           {| ghost_state := gs'; concrete_state := cs'; can_silent := false |}
  | step_silent: forall C1 stk m m' k k' exp exp' arg
                   gs cs cs' b,
      cs = [CState C1, stk, m, k, exp, arg] ->
      cs' = [CState C1, stk, m', k', exp', arg] ->
      CS.kstep ge cs E0 cs' ->
      update_can_silent cs' = b ->
      step ge {| ghost_state := gs; concrete_state := cs; can_silent := true |} E0
           {| ghost_state := gs; concrete_state := cs'; can_silent := b |}
  .

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step;
       initial_state := initial p;
       final_state := final p;
       globalenv := {| genv_interface := prog_interface p; genv_procedures := prog_procedures p |} |}.

End TreeWithCallers.


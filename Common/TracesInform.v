Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Values.
Require Import Common.Traces.
Require Import Common.Memory.

From mathcomp
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Eregister : Type :=
  E_R_ONE | E_R_COM | E_R_AUX1 | E_R_AUX2 | E_R_RA | E_R_SP | E_R_ARG.

Inductive Ebinop : Set :=
  E_Add : Ebinop | E_Minus : Ebinop | E_Mul : Ebinop | E_Eq : Ebinop | E_Leq : Ebinop.

Inductive event_inform :=
| ECall : Component.id -> Procedure.id -> value -> Memory.t -> Component.id -> event_inform
| ERet : Component.id -> value -> Memory.t -> Component.id -> event_inform
| EConst : Component.id -> value -> Eregister -> event_inform
| EMov : Component.id -> Eregister -> Eregister -> event_inform
| EBinop : Component.id -> Ebinop -> Eregister -> Eregister -> Eregister -> event_inform
| ELoad : Component.id -> Eregister -> Eregister -> event_inform
| EStore : Component.id -> Eregister -> Eregister -> event_inform
| EAlloc : Component.id -> Eregister -> Eregister -> event_inform
| EInvalidateRA : Component.id -> event_inform.

Inductive match_event : event_inform -> event_inform -> Prop :=
| match_events_ECall: forall C P arg mem C',
    match_event (ECall C P arg mem C')
                (ECall C P arg mem C')
| match_events_ERet: forall C retval mem C',
    match_event (ERet C retval mem C')
                (ERet C retval mem C')
| match_events_EConst: forall C v r,
    match_event (EConst C v r)
                (EConst C v r)
| match_events_EMov: forall C r1 r2,
    match_event (EMov C r1 r2)
                (EMov C r1 r2)
| match_events_EBinop: forall C op r1 r2 r3,
    match_event (EBinop C op r1 r2 r3)
                (EBinop C op r1 r2 r3)
| match_events_ELoad: forall C r1 r2,
    match_event (ELoad C r1 r2)
                (ELoad C r1 r2)
| match_events_EStore: forall C r1 r2,
    match_event (EStore C r1 r2)
                (EStore C r1 r2)
| match_events_EAlloc: forall C r1 r2,
    match_event (EAlloc C r1 r2)
                (EAlloc C r1 r2)
| match_events_EInvalidateRA: forall C,
    match_event (EInvalidateRA C)
                (EInvalidateRA C).

Lemma match_event_equal:
  forall e e', match_event e e' -> e = e'.
Proof. intros e e' Hmatch. inversion Hmatch; auto.
Qed.

Lemma equal_match_event:
  forall e e', e = e' -> match_event e e'.
Proof. intros e e' Heq. rewrite Heq. destruct e'.
       - apply match_events_ECall.
       - apply match_events_ERet.
       - apply match_events_EConst.
       - apply match_events_EMov.
       - apply match_events_EBinop.
       - apply match_events_ELoad.
       - apply match_events_EStore.
       - apply match_events_EAlloc.
       - apply match_events_EInvalidateRA.
Qed.

Instance event_inform_EventClass : EventClass event_inform :=
  {
    cur_comp_of_event e :=
      match e with
      | ECall   C _ _ _ _ => C
      | ERet    C _ _ _  => C
      | EConst  C _ _ => C
      | EMov    C _ _ => C
      | EBinop  C _ _ _ _ => C
      | ELoad   C _ _ => C
      | EStore  C _ _ => C
      | EAlloc  C _ _ => C
      | EInvalidateRA C => C
      end;
    next_comp_of_event e :=
      match e with
      (* Calls and returns yield control. *)
      | ECall  _ _ _ _ C => C
      | ERet   _ _ _  C => C
      (* All the other events retain control. *)
      | EConst  C _ _ => C
      | EMov    C _ _ => C
      | EBinop  C _ _ _ _ => C
      | ELoad   C _ _ => C
      | EStore  C _ _ => C
      | EAlloc  C _ _ => C
      | EInvalidateRA C => C
      end;
    event_equal := match_event;
    event_equal_equal := match_event_equal;
    equal_event_equal := equal_match_event
  }.

Section Traces.

Inductive stack_state := StackState {
  (* The current running component.  *)
  cur_comp : Component.id;

  (* Other running components further down the stack. *)
  callers  : list Component.id
}.

Definition stack_state0 := StackState Component.main [::].

Implicit Types (t : trace event_inform)
         (C : Component.id) (s : stack_state) (intf : Program.interface).

Fixpoint well_bracketed_trace s t : bool :=
  match t with
  | [::] => true
  | e :: t' =>
    (cur_comp s == cur_comp_of_event e) &&
    match e with
    | ECall C _ _ _ C' =>
      well_bracketed_trace (StackState C' (C :: callers s)) t'
    | ERet C _ _ C' =>
      match callers s with
      | [] => false
      | head :: tail =>
        (head == C') && well_bracketed_trace (StackState C' tail) t'
      end
    | _ => well_bracketed_trace s t'
    end
  end.

Definition run_event s e :=
  match e with
  | ECall C _ _ _ C' => StackState C' (C :: callers s)
  | ERet  C _ _  C' => StackState C' (tail (callers s))
  | _ => s
  end.

Definition run_trace s t := foldl run_event s t.

Lemma run_trace1 s t e : run_trace s (rcons t e) = run_event (run_trace s t) e.
Proof. by rewrite -cats1 /run_trace foldl_cat. Qed.

Lemma well_bracketed_trace_cat s t1 t2 :
  well_bracketed_trace s (t1 ++ t2) =
  well_bracketed_trace s t1 &&
  well_bracketed_trace (run_trace s t1) t2.
Proof.
  elim: t1 s=> [//|[C ? ? ? C'|C ? ? C'|? ? ?|? ? ?|? ? ? ? ?|? ? ?|? ? ?|? ? ?|?] t1 IH]
                 [Ccur callers] /=;
  try by rewrite IH andbA.
case: eqP callers => [_ {Ccur}|_] //= [|top callers] //=;
  by rewrite IH andbA.                
Qed.

Definition seq_of_stack_state s := cur_comp s :: callers s.

Coercion seq_of_stack_state : stack_state >-> seq.

Lemma seq_of_stack_state_inj : injective seq_of_stack_state.
Proof. by case=> [??] [??] [-> ->]. Qed.

Lemma well_bracketed_trace_suffix t C C' Cs :
  well_bracketed_trace stack_state0 t ->
  suffix [:: C, C' & Cs] (run_trace stack_state0 t) ->
  exists t1 P arg mem t2, t = t1 ++ ECall C' P arg mem C :: t2.
Proof.
  set s0 := stack_state0.
  elim/last_ind: t=> [|t e IH] //=.
    by rewrite suffix_cons suffix_nil /= orbF => _ /eqP.
    have -> : well_bracketed_trace s0 (rcons t e) =
              well_bracketed_trace s0 t &&
                                   well_bracketed_trace (run_trace s0 t) [:: e].
      by rewrite -cats1 well_bracketed_trace_cat andbC.
      rewrite run_trace1;
        case: e => [C1 P arg mem C2|C1 ? ? C2|C1 ? ?|C1 ? ?|C1 ? ? ? ?|C1 ? ?|C1 ? ?|C1 ? ?|C1]
                     /=;
                     try rewrite andbT;
                     try (case/andP=> wb_t /eqP <- {C1} /=;
                                           move => Hsuff;
                                                   case/(_ wb_t Hsuff):
                                                     IH=> [t1 [P' [arg' [mem' [t2 ->]]]]];
                                                            by eexists
                                                                 t1, P', arg', mem', (rcons t2 _);
                                                            rewrite rcons_cat; split; eauto).
  - case/andP=> wb_t /eqP <- {C1} /=.
    rewrite -[_ :: callers _]/(run_trace s0 t : seq _) suffix_cons /=.
    case/orP=> [/eqP|Hsuff].
    + case: (run_trace _ _)=> [? ?] [<- <- <-] /=.
        by eexists t, _, _, _, [::]; rewrite cats1.
    + case/(_ wb_t Hsuff): IH=> [t1 [P' [arg' [mem' [t2 ->]]]]].
        by eexists t1, P', arg', mem', (rcons t2 _); rewrite rcons_cat; split; eauto.
  - case/and3P=> wb_t /eqP e1 e2.
    have -> : StackState C2 (tl (callers (run_trace s0 t))) =
              callers (run_trace s0 t) :> seq _.
      by case: (callers _) e2=> [|e cs] //= /andP [/eqP ->].
      move=> Hsuff; have {Hsuff} Hsuff: suffix [:: C, C' & Cs] (run_trace s0 t).
        by rewrite suffix_cons Hsuff orbT.
        case/(_ wb_t Hsuff): IH=> [t1 [P [arg [mem [t2 ->]]]]].
          by eexists t1, P, arg, mem, (rcons _ _); rewrite rcons_cat.
Qed.

Lemma well_bracketed_trace_inv t C res mem C' :
  well_bracketed_trace stack_state0 (t ++ [:: ERet C res mem C']) ->
  exists t1 P arg mem' t2, t = t1 ++ ECall C' P arg mem' C :: t2.
Proof.
rewrite -[t]cat0s.
elim: t {1 3}nil=> [|e t IH] pre //=; last first.
  rewrite -cat1s [pre ++ _]catA; exact: IH.
rewrite cats0 well_bracketed_trace_cat /=.
case/and3P=> wb_t /eqP e_C e_C'.
have : suffix [:: C, C' & tail (callers (run_trace stack_state0 pre))]
              (run_trace stack_state0 pre).
  case: run_trace e_C e_C'=> [? [|??]] //=; rewrite andbT.
  by move=> -> /eqP ->; rewrite suffix_refl.
exact: well_bracketed_trace_suffix=> //.
Qed.

(* TODO: Here, this is an important definition.
   Need as an extra argument the status of the (shared?) memory at the program state in which
   the event was emitted.
   Only then can we use reachability to compute the views of each component.
   Based on the view of a component memory, we can judge whether an ERead/EWrite that it
   performs is a possible read/write.  *)
Definition well_formed_event intf (e: event_inform) : bool :=
  match e with
  | ECall C P _ _ C' => (C != C') && imported_procedure_b intf C C' P
  | ERet  C _ _  C' => (C != C')
  | _ => true
  end.

Definition well_formed_trace intf (t: trace event_inform) : bool :=
  well_bracketed_trace stack_state0 t &&
  all (well_formed_event intf) t.

Definition declared_event_comps intf e :=
  [&& cur_comp_of_event e \in domm intf &
      next_comp_of_event e \in domm intf].

Lemma well_formed_trace_int intf t :
  well_formed_trace intf t ->
  closed_interface intf ->
  all (declared_event_comps intf) t.
Proof.
Admitted.
(*
  case/andP=> wb wf clos; rewrite /declared_event_comps.
  Check allP.
  Check pred_sort.
  assert (forall x, x \in t -> (cur_comp_of_event x \in domm intf)
                                 && (next_comp_of_event x \in domm intf) x) as asrt.
  case=> [C P v C'|C v C'] /=; rewrite !mem_domm.
  - move/(allP wf)=> /andP [_ imp].
    move: (imp); rewrite /imported_procedure_b; case: getm => //= _ _.
      by case/imported_procedure_iff/clos: imp=> ? [->].
  - move=> in_p; case/path.splitP: in_p wb wf => {t} t1 t2.
    rewrite -cats1 /= well_bracketed_trace_cat.
    case/andP=> /well_bracketed_trace_inv [t11 [P [v' [t12 ->]]]] _ wf.
    have : well_formed_event intf (ECall C' P v' C).
      by move/allP: wf; apply; rewrite !mem_cat inE eqxx /= orbT.
      case/andP=> _ imp.
      case/imported_procedure_iff/clos: (imp)=> ? [-> _] /=.
        by move: imp; rewrite /imported_procedure_b; case: getm.
Qed.
*)
End Traces.

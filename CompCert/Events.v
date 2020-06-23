Require Import Common.Definitions.
Require Import Common.Values.
Require Import CompCert.Coqlib.


Class EventClass (A : Type) :=
  { next_comp_of_event : A -> Component.id;
    cur_comp_of_event : A -> Component.id
  }.


(* RB: TODO: RW: Allowing arbitrary values to appear in events does not preclude
   the possibility of nonsensical values appearing in traces, notably Undef
   values. We have two basic alternatives:
    1. Rule out Undef values in the semantics.
    2. Refine the definition of defined and undefined values at the type level.
*)
Inductive event :=
| ECall : Component.id -> Procedure.id -> Z (* value *) -> Component.id -> event
| ERet : Component.id -> Z (* value *) -> Component.id -> event
| ERead : Component.id -> Pointer.t -> value -> event
| EWrite : Component.id -> Pointer.t -> value -> event.

Instance event_EventClass : EventClass event :=
  {
    cur_comp_of_event e :=
      match e with
      | ECall  C _ _ _ => C
      | ERet   C _ _   => C
      | ERead  C _ _   => C
      | EWrite C _ _   => C
      end;
    next_comp_of_event e :=
      match e with
      (* Calls and returns yield control. *)
      | ECall  _ _ _ C => C
      | ERet   _ _   C => C
      (* Reads and writes retain control. *)
      | ERead  C _ _   => C
      | EWrite C _ _   => C
      end
  }.

Definition trace (A : Type) := list A.

Definition E0 {A : Type} : trace A := nil.

Definition Eapp {A : Type} (t1 t2: trace A) : trace A := t1 ++ t2.

CoInductive traceinf (A : Type) : Type :=
| Econsinf: A -> traceinf A -> traceinf A.

Fixpoint Eappinf {A : Type} (t: trace A) (T: traceinf A) {struct t} : traceinf A :=
  match t with
  | nil => T
  | ev :: t' => Econsinf _ ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
      or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall A (t: trace A), E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall A (t: trace A) , t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall A (t1: trace A) t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall A (t1: trace A) t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof.
  intros. apply app_eq_nil. auto.
Qed.

Lemma E0_left_inf: forall A (T : @traceinf A) , E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall A (t1: trace A) t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
     E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq (trace _) ?x ?y) |- _ ] =>
    subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
    apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
    auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim {A : Type} : traceinf A -> traceinf A -> Prop :=
| traceinf_sim_cons: forall e T1 T2,
    traceinf_sim T1 T2 ->
    traceinf_sim (Econsinf _ e T1) (Econsinf _ e T2).

Lemma traceinf_sim_refl:
  forall A (T : traceinf A), traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall A (T1 : traceinf A) T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall A (T1 : traceinf A) T2 T3,
    traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim' {A : Type} : traceinf A -> traceinf A -> Prop :=
| traceinf_sim'_cons: forall t T1 T2,
    t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall A (T1 : traceinf A) T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t. elim H0; auto.
  Transparent Eappinf.
  Transparent E0.
  simpl.
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf' (A : Type) : Type :=
| Econsinf': forall (t: trace A) (T: traceinf' A), t <> E0 -> traceinf' A.

Program Definition split_traceinf' {A : Type} (t: trace A) (T: traceinf' A) (NE: t <> E0)
  : A * traceinf' A :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' _ t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto.
Qed.

CoFixpoint traceinf_of_traceinf' {A : Type} (T': traceinf' A) : traceinf A :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
    let (e, tl) := split_traceinf' t T'' NOTEMPTY in
    Econsinf _ e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall A (T : traceinf' A), T = match T with Econsinf' t T' NE => Econsinf' _ t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall {A} (T: traceinf A), T = match T with Econsinf t T' => Econsinf _ t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall {A} (t: trace A) T NE,
    traceinf_of_traceinf' (Econsinf' _ t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' _ (a :: t) T NE))).
  simpl. destruct t. auto.
  Transparent Eappinf.
  simpl. f_equal. apply IHt.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix {A : Type} (t1 t2: trace A) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix {A : Type} (t1: trace A) (T2: traceinf A) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall {A} (t1 : trace A) t2 t,
    trace_prefix t1 t2 ->
    trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall {A} (t1: trace A) T2 t,
    traceinf_prefix t1 T2 ->
    traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

Set Implicit Arguments.

(* TODO: What does match_traces mean? How should it be updated now
   that we have ERead and EWrite?
 *)
(*
  The name "match_traces" should be changed.
  Maybe it should be "check_both_nil_or_singleton" or similar.
*)
Inductive match_traces: (@trace event) -> (@trace event) -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_call: forall C P arg C',
      match_traces (ECall C P arg C' :: nil)
                   (ECall C P arg C' :: nil)
  | match_traces_ret: forall C retval C',
      match_traces (ERet C retval C' :: nil)
                   (ERet C retval C' :: nil)
  | match_traces_read: forall C ptr v,
      match_traces (ERead C ptr v :: nil)
                   (ERead C ptr v :: nil)
  | match_traces_write: forall C ptr v,
      match_traces (EWrite C ptr v :: nil)
                   (EWrite C ptr v :: nil).

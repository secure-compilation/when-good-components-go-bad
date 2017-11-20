Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Module PS.

Import Source.

Definition stack : Type := list (Component.id * option (value * CS.cont)).

Definition program_state : Type := Component.id * stack * Memory.t * CS.cont * expr.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state.

Ltac unfold_state :=
  match goal with
  | H: state |- _ =>
    let C := fresh "C" in
    let pgps := fresh "pgps" in
    let pmem := fresh "pmem" in
    let k := fresh "k" in
    let e := fresh "e" in
    destruct H as [[[[[C pgps] pmem] k] e] | [[C pgps] pmem] []]
  end.

Inductive state_eq: state -> state -> Prop :=
| program_states_eq: forall C1 pgps1 pmem1 k1 e1 C2 pgps2 pmem2 k2 e2,
    C1 = C2 ->
    pgps1 = pgps2 ->
    PMap.Equal pmem1 pmem2 ->
    k1 = k2 ->
    e1 = e2 ->
    state_eq (PC (C1, pgps1, pmem1, k1, e1)) (PC (C2, pgps2, pmem2, k2, e2))
| context_state_eq: forall C1 pgps1 pmem1 C2 pgps2 pmem2,
    C1 = C2 ->
    pgps1 = pgps2 ->
    PMap.Equal pmem1 pmem2 ->
    state_eq (CC (C1, pgps1, pmem1) Normal) (CC (C2, pgps2, pmem2) Normal).

Lemma state_eq_refl:
  forall s,
    state_eq s s.
Proof.
  intros; unfold_state; constructor; reflexivity.
Qed.

Lemma state_eq_sym:
  forall s1 s2,
    state_eq s1 s2 -> state_eq s2 s1.
Proof.
  intros s1 s2 H.
  inversion H; subst;
    constructor;
    try reflexivity;
    try symmetry; assumption.
Qed.

Lemma state_eq_trans:
  forall s1 s2 s3,
    state_eq s1 s2 -> state_eq s2 s3 -> state_eq s1 s3.
Proof.
  intros s1 s2 s3 H1 H2.
  inversion H1; subst; inversion H2; subst;
    constructor;
    try reflexivity;
    try etransitivity; eauto.
Qed.

Add Parametric Relation: (state) (state_eq)
    reflexivity proved by (state_eq_refl)
    symmetry proved by (state_eq_sym)
    transitivity proved by (state_eq_trans)
      as state_eq_rel.

Definition component_of_state (sps: state) : Component.id :=
  match sps with
  | PC (C, _, _, _, _) => C
  | CC (C, _, _) _     => C
  end.

Instance state_turn : HasTurn state := {
  turn_of s iface := PMap.In (component_of_state s) iface
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := ~ is_context_component ps ctx.

Ltac simplify_turn :=
  unfold PS.is_program_component, PS.is_context_component in *;
  unfold turn_of, PS.state_turn in *;
  simpl in *.

(* stack partialization *)

Definition to_partial_frame ctx frame : Component.id * option (value * CS.cont) :=
  let '(C, v, k) := frame in
  if Util.Lists.mem C ctx then
    (C, None)
  else
    (C, Some (v, k)).

Definition to_partial_stack (s : CS.stack) (pc : list Component.id) :=
  map (to_partial_frame pc) s.

(* might be useful in the future
Lemma push_by_context_preserves_partial_stack:
  forall s ps ctx C v k,
    Util.Lists.mem C ctx = true ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,v,k)::s) ctx = (C,None) :: ps.
Proof.
  intros s ctx pc C v k Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_prog_preserves_partial_stack:
  forall s ps ctx C v k,
    ~ (In C ctx) ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,v,k)::s) ctx = (C,Some (v,k)) :: ps.
Proof.
  intros s ps ctx C v k Hprogturn Hpstack.
  simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.
*)

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall C gps pgps mem pmem k e,
    (* program has control *)
    is_program_component (PC (C, pgps, pmem, k, e)) ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx (C, gps, mem, k, e) (PC (C, pgps, pmem, k, e))

| ContextControl_Normal: forall C gps pgps mem pmem k e,
    (* context has control *)
    is_context_component (CC (C, pgps, pmem) Normal) ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx (C, gps, mem, k, e) (CC (C, pgps, pmem) Normal).

Definition partialize (ctx: Program.interface) (scs: CS.state) : PS.state :=
  let '(C, gps, mem, k, e) := scs in
  let pgps := to_partial_stack gps (map fst (PMap.elements ctx)) in
  let pmem := PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem in
  if PMapFacts.In_dec ctx C then CC (C, pgps, pmem) Normal
  else PC (C, pgps, pmem, k, e).

Lemma partial_state_partialize ctx scs sps :
  partial_state ctx scs sps <-> state_eq sps (partialize ctx scs).
Proof.
  (*
  split.
  - intros H.
    destruct H as [C gps pgps mem pmem k e ? ? Hcomp Hmem ?
                  |C gps pgps mem pmem k e ? ? Hcomp Hmem];
    subst scs sps pgps;
    unfold is_program_component, is_context_component in Hcomp;
    simpl in *;
    destruct (PMapFacts.In_dec ctx C) as [?|?]; try easy.
    + now apply PCE.
    + now apply CCE.
  - intros H.
    inversion H as [C gps mem1 mem2 k e Hmem Hsps Hpart
                   |C gps mem1 mem2 Hmem Hsps Hpart]; subst sps; clear H;
    destruct scs as [[[[C' gps'] mem'] k'] e']; simpl in Hpart;
    destruct (PMapFacts.In_dec ctx C') as [Hin|Hnin]; try easy.
    + inversion Hpart; subst C' gps mem2 k' e'.
      now econstructor; eauto.
    + inversion Hpart; subst C' gps mem2.
      now econstructor; eauto.
Qed.
   *)
Admitted.

Theorem partial_state_preserves_turn_of:
  forall psi cs ps,
    partial_state psi cs ps -> (turn_of ps psi <-> turn_of cs psi).
Proof.
  (*
  intros psi scs sps H. simpl.
  apply partial_state_partialize in H.
  destruct scs as [[[[C gps] mem] k] e].
  rewrite H. simpl.
  now destruct (PMapFacts.In_dec _ _).
Qed.
   *)
Admitted.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall scs sps,
    partial_state ctx scs sps ->
    CS.initial_state p scs ->
    initial_state p ctx sps.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_intro: forall scs sps,
    ~ turn_of sps ctx ->
    partial_state ctx scs sps ->
    CS.final_state scs->
    final_state p ctx sps
| final_state_context: forall sps,
    turn_of sps ctx ->
    final_state p ctx sps.

Inductive kstep (ctx: Program.interface) (G: global_env)
  : state -> trace -> state -> Prop :=
| partial_step:
    forall sps t sps' scs scs',
      CS.kstep G scs t scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->
      kstep ctx G sps t sps'.

(* partial semantics *)

Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Let G := init_genv p.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  (* the context is part of p *)
  Hypothesis valid_context:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (prog_interface p).

  Definition sem :=
    @Semantics_gen state global_env (kstep ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.

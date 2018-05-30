Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

Record global_env := mkGlobalEnv {
  genv_interface: Program.interface;
  genv_procedures: NMap (NMap code);
  genv_entrypoints: EntryPoint.t;
}.

Definition executing G (pc : Pointer.t) (i : instr) : Prop :=
  exists C_procs P_code,
    getm (genv_procedures G) (Pointer.component pc) = Some C_procs /\
    getm C_procs (Pointer.block pc) = Some P_code /\
    (Pointer.offset pc >= 0) % Z /\
    nth_error P_code (Z.to_nat (Pointer.offset pc)) = Some i.

Definition prepare_global_env (p: program) : global_env :=
  let mem := prepare_initial_memory p in
  let '(_, procs, entrypoints) := prepare_procedures p mem in
  {| genv_interface := prog_interface p;
     genv_procedures := procs;
     genv_entrypoints := entrypoints |}.

Definition empty_global_env := {|
  genv_interface := emptym;
  genv_procedures := emptym;
  genv_entrypoints := emptym
|}.

Lemma prepare_global_env_empty_prog:
  prepare_global_env empty_prog = empty_global_env.
Proof.
  reflexivity.
Qed.

Lemma domm_genv_procedures : forall p,
  domm (genv_procedures (prepare_global_env p)) = domm (prog_interface p).
Admitted. (* Grade 2. Spec. *)

Lemma domm_genv_entrypoints : forall p,
  domm (genv_entrypoints (prepare_global_env p)) = domm (prog_interface p).
Admitted. (* Grade 2. Spec. *)

Definition global_env_union (genv1 genv2 : global_env) : global_env := {|
  genv_interface   := unionm (genv_interface   genv1) (genv_interface   genv2);
  genv_procedures  := unionm (genv_procedures  genv1) (genv_procedures  genv2);
  genv_entrypoints := unionm (genv_entrypoints genv1) (genv_entrypoints genv2)
|}.

Lemma prepare_global_env_link : forall {p c},
  linkable (prog_interface p) (prog_interface c) ->
  prepare_global_env (program_link p c) =
  global_env_union (prepare_global_env p) (prepare_global_env c).
Admitted. (* Grade 2. Spec. *)

Lemma genv_procedures_program_link_left_notin :
  forall {c Cid},
    Cid \notin domm (prog_interface c) ->
  forall {p},
    linkable (prog_interface p) (prog_interface c) ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros c Cid Hnotin p Hlinkable.
  rewrite (prepare_global_env_link Hlinkable).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) Cid = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  setoid_rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) Cid) eqn:Hcase;
    by setoid_rewrite Hcase.
Qed.

Lemma genv_procedures_program_link_left_in :
  forall {p Cid},
    Cid \in domm (prog_interface p) ->
  forall {c},
    linkable (prog_interface p) (prog_interface c) ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros p Cid Hin c Hlinkable.
  rewrite (prepare_global_env_link Hlinkable).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert
    (exists procs, (genv_procedures (prepare_global_env p)) Cid = Some procs)
    as [procs Hprocs]
    by (apply /dommP; rewrite domm_genv_procedures; assumption).
  setoid_rewrite Hprocs.
  assumption.
Qed.

Lemma genv_entrypoints_program_link_left :
  forall {c C},
    C \notin domm (prog_interface c) ->
  forall {p},
    linkable (prog_interface p) (prog_interface c) ->
  forall {P},
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c))) =
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)).
Proof.
  intros c C Hnotin p Hlinkable P.
  rewrite (prepare_global_env_link Hlinkable).
  unfold EntryPoint.get, global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_entrypoints (prepare_global_env c)) C = None)
    by (apply /dommPn; rewrite domm_genv_entrypoints; done).
  rewrite HNone.
  destruct ((genv_entrypoints (prepare_global_env p)) C) eqn:Hcase;
    by rewrite Hcase.
Qed.

Fixpoint find_label (c : code) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | ILabel l' :: c' =>
        if Nat.eqb l l' then
          Some o
        else
          aux c' (1 + o)%Z
      | _ :: c' =>
        aux c' (1 + o)%Z
      end
  in aux c 0%Z.

Definition find_label_in_procedure G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    match getm C_procs (Pointer.block pc) with
    | Some P_code =>
      match find_label P_code l with
      | Some offset => Some (Pointer.component pc, Pointer.block pc, offset)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Fixpoint find_label_in_component_helper
         G (procs: list (Block.id * code))
         (pc: Pointer.t) (l: label) : option Pointer.t :=
  match procs with
  | [] => None
  | (p_block,p_code) :: procs' =>
    match find_label_in_procedure G (Pointer.component pc, p_block, 0%Z) l with
    | None => find_label_in_component_helper G procs' pc l
    | Some ptr => Some ptr
    end
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    find_label_in_component_helper G (elementsm C_procs) pc l
  | None => None
  end.

Lemma find_label_in_procedure_guarantees:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc' /\
    Pointer.block pc = Pointer.block pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_procedure in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  destruct (getm procs (Pointer.block pc)) as [code|];
    try discriminate.
  destruct (find_label code l) as [offset|];
    try discriminate.
  destruct pc'. destruct p.
  inversion Hfind. subst.
  split; reflexivity.
Qed.

Lemma find_label_in_procedure_1:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_2:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.block pc = Pointer.block pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    linkable (prog_interface p) (prog_interface c) ->
  forall {l},
    find_label_in_procedure (prepare_global_env (program_link p c)) pc l =
    find_label_in_procedure (prepare_global_env p) pc l.
Proof.
  (* RB: Note the proof strategy for all these lemmas is remarkably similar.
     It may be worthwhile to refactor it and/or its intermediate steps. *)
  intros c pc Hnotin p Hlinkable l.
  rewrite (prepare_global_env_link Hlinkable).
  unfold find_label_in_procedure, global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) (Pointer.component pc) = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc)) eqn:Hcase;
    by rewrite Hcase.
Qed.

Lemma find_label_in_component_helper_guarantees:
  forall G procs pc pc' l,
    find_label_in_component_helper G procs pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G procs pc pc' l Hfind.
  induction procs.
  - discriminate.
  - simpl in *.
    destruct a.
    destruct (find_label_in_procedure
                G (Pointer.component pc, i, 0%Z) l)
             eqn:Hfind'.
    + apply find_label_in_procedure_1 in Hfind'.
      simpl in *. inversion Hfind. subst. auto.
    + apply IHprocs; auto.
Qed.

Lemma find_label_in_component_1:
  forall G pc pc' l,
    find_label_in_component G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_component in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  eapply find_label_in_component_helper_guarantees in Hfind; auto.
Qed.

Lemma find_label_in_component_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    linkable (prog_interface p) (prog_interface c) ->
  forall {l},
    find_label_in_component (prepare_global_env (program_link p c)) pc l =
    find_label_in_component (prepare_global_env p) pc l.
Proof.
  intros c pc Hnotin p Hlinkable l.
  rewrite (prepare_global_env_link Hlinkable).
  unfold find_label_in_component. unfold global_env_union at 1. simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) (Pointer.component pc) = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc))
    as [procs |] eqn:Hcase;
    rewrite Hcase.
  - simpl.
    (* Inlined is the corresponding lemma on find_label_in_component_helper. *)
    induction (elementsm procs) as [| [p_block code] elts IHelts];
      first reflexivity.
    unfold find_label_in_component_helper; simpl.
    assert (Hnotin' : Pointer.component (Pointer.component pc, p_block, 0%Z)
                      \notin domm (prog_interface c)).
      by done.
    rewrite <- (prepare_global_env_link Hlinkable).
    rewrite (find_label_in_procedure_program_link_left Hnotin' Hlinkable).
    fold find_label_in_component_helper.
    rewrite <- IHelts.
    rewrite <- (prepare_global_env_link Hlinkable).
    reflexivity.
  - reflexivity.
Qed.

(* Lemma placeholder: execution_invariant_to_linking *)

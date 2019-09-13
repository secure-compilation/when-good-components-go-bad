Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.
Require Import Intermediate.GlobalEnv.
Require Import Old.Intermediate.MachineExtra.

Import Intermediate.
Import Machine.Intermediate.
Import MachineExtra.Intermediate.

From mathcomp Require Import ssreflect ssrfun.

Set Bullet Behavior "Strict Subproofs".

Definition empty_global_env := {|
  genv_interface := emptym;
  genv_procedures := emptym;
  genv_entrypoints := emptym
|}.

Lemma prepare_global_env_empty_prog:
  prepare_global_env empty_prog = empty_global_env.
Proof.
  unfold prepare_global_env.
  rewrite prepare_procedures_initial_memory_empty_program.
  reflexivity.
Qed.

Lemma genv_procedures_program_link_left_in :
  forall {p Cid},
    Cid \in domm (prog_interface p) ->
  forall {c},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros p Cid Hin c Hwfp Hwfc Hlinkable Hmains.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert
    (exists procs, (genv_procedures (prepare_global_env p)) Cid = Some procs)
    as [procs Hprocs]
    by (apply /dommP; rewrite domm_genv_procedures; assumption).
  setoid_rewrite Hprocs.
  assumption.
Qed.

Lemma find_label_in_procedure_2:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.block pc = Pointer.block pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

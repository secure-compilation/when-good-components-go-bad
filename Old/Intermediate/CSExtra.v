Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Traces.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Lib.Extra.
Require Import Lib.Monads.
Require Import Intermediate.CS.
Import CS.

From mathcomp Require ssreflect ssrfun ssrbool eqtype.

Set Bullet Behavior "Strict Subproofs".

Module CS.

Import Intermediate.

(* A similar result is used above. Here is a weaker formulation. *)
Lemma initial_state_stack_state0 p s :
  initial_state p s ->
  stack_state_of s = Traces.stack_state0.
Proof.
  intros Hini.
  unfold initial_state, initial_machine_state in Hini.
  destruct (prog_main p) as [mainP |]; simpl in Hini.
  - destruct (prepare_procedures p (prepare_initial_memory p))
      as [[mem dummy] entrypoints].
    destruct (EntryPoint.get Component.main mainP entrypoints).
    + subst. reflexivity.
    + subst. reflexivity.
  - subst. reflexivity.
Qed.

Lemma comes_from_initial_state_mergeable_sym :
  forall s iface1 iface2,
    Linking.mergeable_interfaces iface1 iface2 ->
    comes_from_initial_state s (unionm iface1 iface2) ->
    comes_from_initial_state s (unionm iface2 iface1).
Proof.
  intros s iface1 iface2 [[_ Hdisjoint] _] Hfrom_initial.
  rewrite <- (unionmC Hdisjoint).
  exact Hfrom_initial.
Qed.

(* RB: NOTE: Consider possible alternatives on [CS.comes_from_initial_state]
   complemented instead by, say, [PS.step] based on what we usually have in
   the context, making for more direct routes. *)
Lemma comes_from_initial_state_step_trans p s t s' :
  CS.comes_from_initial_state s (prog_interface p) ->
  CS.step (prepare_global_env p) s t s' ->
  CS.comes_from_initial_state s' (prog_interface p).
Admitted. (* Grade 2. *)

(* RB: TODO: These domain lemmas should now be renamed to reflect their
   operation on linked programs. *)
Section ProgramLink.
  Variables p c : program.
  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).
  Hypothesis Hprog_is_closed  : closed_program (program_link p c).

  Import ssreflect.

  (* RB: NOTE: Check with existing results (though currently unused). *)
  Lemma star_stack_cons_domm {s frame gps mem regs pc t} :
    initial_state (program_link p c) s ->
    Star (sem (program_link p c)) s t (frame :: gps, mem, regs, pc) ->
    Pointer.component frame \in domm (prog_interface p) \/
    Pointer.component frame \in domm (prog_interface c).
  Proof.
    intros Hini Hstar.
    assert (H : Pointer.component frame \in domm (prog_interface (program_link p c))).
    { eapply CS.comes_from_initial_state_stack_cons_domm.
      destruct (cprog_main_existence Hprog_is_closed) as [i [_ [? _]]].
      exists (program_link p c), i, s, t.
      split; first (destruct Hmergeable_ifaces; now apply linking_well_formedness).
      repeat split; eauto. }
    move: H. simpl. rewrite domm_union. now apply /fsetUP.
  Qed.
End ProgramLink.

End CS.

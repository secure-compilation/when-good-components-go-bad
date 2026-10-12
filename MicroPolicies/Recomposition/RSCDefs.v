Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.

Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

Section ProgramSemantics.

  Variable NC : nat.
  Variable W : program.

  (* trace-shaped step wrappers, mirroring Definitions.v's [step1]/[step2] *)
  Definition prog_step_me := (fun (ge: unit) (s: state) t (s': state) =>
                                match t with
                                | [::] => step_me s s' None (NC := NC)
                                | e :: [::] => step_me s s' (Some e) (NC := NC)
                                | _ => False
                                end).

  Definition prog_step_mp := (fun (ge: unit) (s: state) t (s': state) =>
                                match t with
                                | [::] => step_mp s s' None (NC := NC)
                                | e :: [::] => step_mp s s' (Some e) (NC := NC)
                                | _ => False
                                end).

  Definition prog_initial : state -> Prop :=
    fun s => s = initial_state (code W) (prog_buffers W) (prog_interface W).

  Definition final_halt : state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc _) _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) => (Types.decode_instr i) = Some (Types.Halt _)
      end.

  (* overlay final states: [Halt] on a code cell *)
  Definition final_halt_code : state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc _) _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) =>
          ((Types.decode_instr i) = Some (Types.Halt _)) /\ (is_code tag = true)
      end.

  (* THE micro-policy machine semantics of a whole MP-level program *)
  Definition mp_sem : semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := unit;
       Smallstep.step := prog_step_mp;
       Smallstep.initial_state := prog_initial;
       Smallstep.final_state := final_halt;
       Smallstep.globalenv := tt |}.

  (* the overlay (Merged) semantics of a whole MP-level program *)
  Definition me_sem : semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := unit;
       Smallstep.step := prog_step_me;
       Smallstep.initial_state := prog_initial;
       Smallstep.final_state := final_halt_code;
       Smallstep.globalenv := tt |}.

  Lemma det_mp_sem : determinate mp_sem.
  Proof.
    econstructor; intros; unfold mp_sem in *.
    - simpl in *. unfold prog_step_mp, step_mp in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold prog_initial in *. subst. done.
    - simpl in *. intros t s' step. unfold prog_step_mp, step_mp in step.
      destruct t; try destruct t; try contradiction;
        setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step;
        destruct s, pc0; unfold final_halt in H; destruct (mem0 vala); try auto; destruct a;
        rewrite H in step; simpl in step; inversion step.
  Qed.

  Lemma det_me_sem : determinate me_sem.
  Proof.
    econstructor; intros; unfold me_sem in *.
    - simpl in *. unfold prog_step_me, step_me in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold prog_initial in *. subst. done.
    - simpl in *. intros t s' step. unfold prog_step_me, step_me in step.
      destruct t; try destruct t; try contradiction;
        setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step;
        destruct s, pc0; unfold final_halt_code in H; destruct (mem0 vala); try auto; destruct a;
        destruct H as [eq ?]; rewrite eq in step; simpl in step; inversion step.
  Qed.

End ProgramSemantics.

(* the running colour of a state (standalone copy of Definitions.v's
   functor-internal [color_of]; definitionally equal) *)
Definition rsc_color_of : state -> Component.id :=
  fun '(Symbolic.State m r (Types.Atom _ tpc) _) =>
    match (tpc) with
    | Level _ c => c
    end.

Section RUBSemantics.

  Variable NC : nat.
  (* the partial-program / context interfaces (the [I] of [UB(I)]) *)
  Variables pI cI : Program.interface.
  Variable W : program.

  Definition rub_allowed : state -> Prop :=
    fun s => (rsc_color_of s) \in (domm cI).

  Definition rub_final : state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc tpc) _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) =>
          ((Types.decode_instr i) = Some (Types.Halt _))
          /\ ((color tag) \in (domm pI) -> (is_code tag = true))
      end.

  (* the UB-restricting semantics [⇝_{UB(C)}]: the context side may take raw
     machine steps (refining overlay-level undefined behaviour), the program
     side must stay within the overlay *)
  Definition rub_sem : semantics :=
    L_restricted_UB (prog_step_me NC) (prog_step_mp NC)
                    (prog_initial W) rub_final tt rub_allowed.

End RUBSemantics.

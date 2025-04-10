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
Require Import Coq.micromega.Lia.

Record program :=
  { prog_interface: Program.interface;
    code: @Merged.code concrete_int_32_mt;
    prog_buffers: NMap {fmap Block.id -> (nat + seq value)};
    prog_main: bool;
  }.

Definition program_link p c :=
  {| prog_interface := unionm (prog_interface p) (prog_interface c);
    code := code p ++ code c;
    prog_buffers := unionm (prog_buffers p) (prog_buffers c);
    prog_main := prog_main p || prog_main c;
  |}.

(* Main simulation theorem. *)
Section Recombination.
  Variables p c p' c' : program.

  (* Hypothesis Hwfp  : well_formed_program p. *)
  (* Hypothesis Hwfc  : well_formed_program c. *)
  (* Hypothesis Hwfp' : well_formed_program p'. *)
  (* Hypothesis Hwfc' : well_formed_program c'. *)

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* Hypothesis Hprog_is_closed  : closed_program (program_link p  c ). *)
  (* Hypothesis Hprog_is_closed' : closed_program (program_link p' c'). *)

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.

  Let state := @Symbolic.state mt LRC.lrc_tags [eqType of unit].
  Let genvtype := unit.
  Let step1 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_me s s' None
                                       | e :: [::] => step_me s s' (Some e)
                                       | _ => False
                                       end).
  Let step2 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_mp s s' None
                                       | e :: [::] => step_mp s s' (Some e)
                                       | _ => False
                                       end).
   Definition initial_state1: state -> Prop :=
     fun s => s = initial_state (code prog  ) (prog_buffers prog  ) (prog_interface prog  ). 

   Definition initial_state2: state -> Prop :=
     fun s => s = initial_state (code prog' ) (prog_buffers prog' ) (prog_interface prog' ). 

   Definition initial_state3: state -> Prop :=
     fun s => s = initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'').
   
  Variable final_state: state -> Prop. (*might be different between semantics*)

  Variable allowed_UB: state -> Prop.

  Let sem   :=
        L_restricted_UB step1 step2 initial_state1 final_state tt allowed_UB.

  Let sem'  :=
        {| Smallstep.state := state;
          Smallstep.genvtype := genvtype;
          Smallstep.step := step1;
          Smallstep.initial_state := initial_state2;
          Smallstep.final_state := final_state;
          Smallstep.globalenv := tt |}.
  Let sem'' :=

        {| Smallstep.state := state;
          Smallstep.genvtype := genvtype;
          Smallstep.step := step1;
          Smallstep.initial_state := initial_state3;
          Smallstep.final_state := final_state;
          Smallstep.globalenv := tt |}.
  
  Lemma det_L2 : determinate sem'.
  Proof.
    econstructor; intros; unfold sem'  in *.
    - simpl in *. unfold step1, step_me in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold initial_state2 in *. subst. done.
    - admit.
  Admitted.
  
  Lemma det_L3 : determinate sem''.
  Proof.
    econstructor; intros; unfold sem'  in *.
    - simpl in *. unfold step1, step_me in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold initial_state3 in *. subst. done.
    - admit.
  Admitted.

  
  Ltac left_subst :=
    match goal with
    | H : ?a = ?b, H0 : ?a = ?c |- _  =>
        try (rewrite H0 in H; inv H)
    end.
  
  Lemma det_L1 : determinate sem.
  Proof.
    econstructor; intros; unfold sem'  in *.
    - simpl in *. (*unfold step1, step2, step_mp, step_me in *. *)
      destruct H, H0 ; [|clear H0| clear H| clear H1 H2];
        unfold step1, step2, step_mp, step_me in *;
        destruct t, t0; try destruct t; try destruct t0; try contradiction;
        (do 2 (match goal with | H : step _ _ _ _ |- _ => setoid_rewrite <- Exec.stepP in H end));
        left_subst; try (split; [try destruct e; try econstructor|try done]).
    - unfold single_events. intros.
      destruct H; unfold step1, step2, step_mp, step_me in *;
        destruct t; try destruct t; try contradiction;
        (match goal with | H : step _ _ _ _ |- _ => setoid_rewrite <- Exec.stepP in H end); simpl; lia.
    - simpl in *. unfold initial_state1 in *. subst. done.
    - admit.
  Admitted.
  
  Lemma single_L1: single_events sem.
  Proof. eapply sd_traces. exact det_L1. Qed. 

  Lemma single_L2: single_events sem'.
  Proof. eapply sd_traces. exact det_L2. Qed. 

  Lemma single_L3: single_events sem''.
  Proof. eapply sd_traces. exact det_L3. Qed. 

  Theorem simulation:
    @threeway_simulation sem sem' sem'' single_L1 single_L2 single_L3.
  Proof.
    eapply threeway_simulation_diagram.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Corollary recomposition_blame:
    forall m,
      does_prefix sem   m ->
      does_prefix sem'  m ->
      does_prefix sem'' m.
  Proof.
  Admitted.

  Corollary recomposition_blame':
    forall m,
      does_prefix sem   (FGoes_wrong m) ->
      does_prefix sem'  (FTbc m) ->
      does_prefix sem'' (FGoes_wrong m).
  Proof.
  Admitted.


End Recombination.

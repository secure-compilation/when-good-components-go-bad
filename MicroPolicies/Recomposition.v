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
  Variable initial_state1: state -> Prop.
  (* Definition initial_state1: state -> Prop := *)
  (*   fun s => *)
  (*     s = initialize prog. *)
  Variable initial_state2: state -> Prop.
  (* Definition initial_state2: state -> Prop := *)
  (*   fun s => *)
  (*     s = initialize prog'. *)
  Variable initial_state3: state -> Prop.
  Variable final_state: state -> Prop.

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

  Lemma single_L1: single_events sem.
  Proof.
  Admitted.

  Lemma single_L2: single_events sem'.
  Proof.
  Admitted.

  Lemma single_L3: single_events sem''.
  Proof.
  Admitted.

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

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
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.PreservationLemmas.

Require Import MicroPolicies.Recomposition.StepSilentStrong.
Require Import MicroPolicies.Recomposition.StepSilentStrong2.
Require Import MicroPolicies.Recomposition.StepSilentWeak2.
Require Import MicroPolicies.Recomposition.StepEventReturn.
Require Import MicroPolicies.Recomposition.RecompositionInit.
Require Import MicroPolicies.Recomposition.PcColor.
Require Import MicroPolicies.Recomposition.RecBackward.

Module RecTop (S: RecompositionContext) (A: AlignmentFacts S).

  Module P0 := Preservation S.
  Module PCM := RecBackward S A P0.
  Include PCM.

  Module SS1 := StepStrong S P0.
  Module SS2 := StepStrong2 S P0.
  Module SW := StepWeak2 S P0.
  Module SE := StepEventReturn S P0.

  Notation lrc_silent_gmc := SW.lrc_silent_gmc.

  Theorem tsim_properties_match_states:
    @tsim_properties sem sem' sem'' (sd_traces det_sem) (sd_traces det_sem') (sd_traces det_sem'')
      (fun s1 s2 s3 => exists M, match_states M s1 s2 s3).
  Proof.
    eapply threeway_simulation_properties.
    - exact match_initial_states.
    - exact SS1.step_silent_strong1.
    - exact SS2.step_silent_strong2.
    - exact SW.step_silent_weak1.
    - exact SW.step_silent_weak2.
    -
      intros s1 e s1' Hs1 s2 s2' Hs2 s3 M Hms.
      destruct e as [comp proc z comp' | comp z comp'].
      + eapply SE.step_event_call; eassumption.
      + eapply SE.step_event_return; eassumption.
  Qed.

  Local Opaque Merged.initial_state Merged.encode_code Merged.initial_memory.

  Lemma relevant_of_side : forall i c,
    side_of c = i -> (c \in domm ip) || (c \in domm ic) -> is_relevant_comp i c.
  Proof.
    move=> i c; rewrite /side_of /is_relevant_comp => <- Hval.
    case Hip: (c \in domm ip) => //=.
    rewrite Hip /= in Hval; exact Hval.
  Qed.

  Lemma common_pcc1 : forall m s1 s2 s3, common_equiv m s1 s2 s3 -> pc_code_color s1.
  Proof. move=> m s1 s2 s3 H; destruct H; assumption. Qed.
  Lemma common_pcc2 : forall m s1 s2 s3, common_equiv m s1 s2 s3 -> pc_code_color s2.
  Proof. move=> m s1 s2 s3 H; destruct H; assumption. Qed.
  Lemma final_rUB_cell : forall s,
    final_state_rUB s ->
    exists d, mem s (vala (pc s)) = Some d /\ decode_instr (vala d) = Some (Halt _) /\
              (color (taga d) \in domm ip -> is_code (taga d)).
  Proof.
    move=> [m r [pcv tp] int]; rewrite /final_state_rUB /=.
    case E: (m pcv) => [[v t]|] // [Hd Hc]. by exists (v @ t).
  Qed.

  Lemma final_me_transfer_strong : forall (i : side) (s s3 : state) (d : atom (mword mt) mem_tag),
    same_pc i s s3 ->
    combined_codes i s s3 ->
    pc_code_color s ->
    is_relevant_comp i (color_of s) ->
    mem s (vala (pc s)) = Some d ->
    is_code (taga d) ->
    decode_instr (vala d) = Some (Halt _) ->
    final_state_me s3.
  Proof.
    move=> i s s3 [va ta] Hsp Hcc Hpcc Hrel Hmem Hcode Hdec.
    have Hct : color ta = color_of s by apply: (Hpcc _ Hmem Hcode).
    inversion Hsp as [u u' Hpe Hnone | u u' vv off Hcell Hoff Hpc3]; subst.
    - case: Hnone => Hn1 _; rewrite Hmem in Hn1; discriminate Hn1.
    - have Hrel' : is_relevant_comp i (color ta) by rewrite Hct.
      have Hoff' : get_offset i (color ta) = Some off by rewrite Hct.
      have [Hfwd _] := Hcc (vala (pc s)) va ta off (color ta) Hrel' Hoff' Hcode (erefl (color ta)).
      have [v' [Hdm Hmem3]] := Hfwd Hmem.
      have Hvv : va = v'.
      { inversion Hdm; subst;
          try (match goal with K : decode_instr va = Some (Jal _) |- _ =>
                 rewrite Hdec in K; discriminate end); reflexivity. }
      subst v'.
      have Hfin : mem s3 (vala (pc s3)) = Some (va @ ta) by rewrite Hpc3.
      exact: (final_me_intro Hfin Hdec Hcode).
  Qed.

  Corollary recomposition_blame:
    forall m,
      does_prefix sem   m ->
      does_prefix sem'  m ->
      does_prefix sem'' m.
  Proof.
    pose proof tsim_properties_match_states as props.
    pose proof (tsim_match_initial_states props) as MINIT.
    assert (HI_sem  : Smallstep.initial_state sem
                        (initial_state (code prog)  (prog_buffers prog)  (prog_interface prog)))  by reflexivity.
    assert (HI_sem' : Smallstep.initial_state sem'
                        (initial_state (code prog') (prog_buffers prog') (prog_interface prog'))) by reflexivity.
    intros m dp_sem dp_sem'.
    apply (does_prefix_equiv det_sem) in dp_sem.
    apply (does_prefix_equiv det_sem') in dp_sem'.
    apply (does_prefix_equiv det_sem'').
    inversion dp_sem; subst; inversion dp_sem'; subst;
      try (exfalso; match goal with
             | H : (forall s, ~ Smallstep.initial_state sem  s) |- _ => exact (H _ HI_sem)
             | H : (forall s, ~ Smallstep.initial_state sem' s) |- _ => exact (H _ HI_sem')
           end);
      match goal with
      | Hi  : Smallstep.initial_state sem  ?s1, Hi' : Smallstep.initial_state sem' ?s2,
        Hst : Star sem ?s1 ?t ?s1', Hst' : Star sem' ?s2 ?t ?s2' |- _ =>
          destruct (MINIT _ _ Hi Hi') as [s3 [Hi3 Hmatch]];
          destruct (tsimulation_star props Hst Hst' s3 Hmatch) as [s3' [Hst3 Hmatch3]]
      end.
    -
      apply (does_FTbc Hi3 Hst3).
    -
      destruct Hmatch3 as [M Hms].
      have Hpc3 := reachable_pc_color'' Hi3 Hst3.
      match goal with Hii : Smallstep.initial_state sem ?ss, Hss : Star sem ?ss _ ?se |- _ =>
        have Hpc1 : pc_color_inv se by exact: (reachable_pc_color Hii Hss) end.
      match goal with Hii' : Smallstep.initial_state sem' ?ss', Hss' : Star sem' ?ss' _ ?se' |- _ =>
        have Hpc2 : pc_color_inv se' by exact: (reachable_pc_color' Hii' Hss') end.
      apply (does_FGoes_wrong Hi3 Hst3).
      + match goal with
        | Hn1 : Nostep sem ?a, Hn2 : Nostep sem' ?b |- _ =>
            exact: (nostep_reflect Hms Hpc3 Hpc1 Hpc2 Hn1 Hn2) end.
      + match goal with
        | Hf1 : ~ final_state sem ?a, Hf2 : ~ final_state sem' ?b |- _ =>
            exact: (notfinal_reflect Hms Hpc3 Hf1 Hf2) end.
    -
      apply (does_FTerminates Hi3 Hst3).
      destruct Hmatch3 as [M Hms].
      inversion Hms as [M0 sa sb sc Hcom HstrL HwkR | M0 sa sb sc Hcom HwkL HstrR]; subst.
      +
        have Hsp   := strong_same_pc HstrL.
        have Hside := strong_side HstrL.
        have Hrel1 : is_relevant_comp Left (color_of s')
          by apply: relevant_of_side; [ exact Hside | exact: (common_color_valid1 Hcom) ].
        have [d1 [Hcell1 [Hdec1 Himpl1]]] := final_rUB_cell H1.
        case Ecode: (is_code (taga d1)).
        * apply: (final_me_transfer_strong (i := Left) (s := s') (d := d1));
            [ exact Hsp | exact: (common_combined_left Hcom) | exact: (common_pcc1 Hcom)
            | exact Hrel1 | exact Hcell1 | exact Ecode | exact Hdec1 ].
        *
          exfalso.
          have Hpci : pc_color_inv s'.
          { match goal with
            | Hii : Smallstep.initial_state sem ?ss, Hss : Star sem ?ss _ s' |- _ =>
                exact: (reachable_pc_color Hii Hss) end. }
          have Hc := Hpci d1 Hcell1.
          have Hip : color (taga d1) \in domm ip by rewrite Hc; exact: Hrel1.
          by move: (Himpl1 Hip); rewrite Ecode.
      +
        have Hsp   := strong_same_pc HstrR.
        have Hside := strong_side HstrR.
        have Hrel2 : is_relevant_comp Right (color_of s'0)
          by apply: relevant_of_side; [ exact Hside | exact: (common_color_valid2 Hcom) ].
        have [d2 [Hcell2 [Hdec2 Hcode2]]] := final_me_cell H5.
        apply: (final_me_transfer_strong (i := Right) (s := s'0) (d := d2));
          [ exact Hsp | exact: (common_combined_right Hcom) | exact: (common_pcc2 Hcom)
          | exact Hrel2 | exact Hcell2 | exact Hcode2 | exact Hdec2 ].
  Qed.

  Corollary recomposition_blame':
    forall m,
      does_prefix sem   (FGoes_wrong m) ->
      does_prefix sem'  (FTbc m) ->
      Common.Blame.undef_in m ip ->
      does_prefix sem'' (FGoes_wrong m).
  Proof.
    pose proof tsim_properties_match_states as props.
    pose proof (tsim_match_initial_states props) as MINIT.
    assert (HI_sem  : Smallstep.initial_state sem
                        (initial_state (code prog)  (prog_buffers prog)  (prog_interface prog)))  by reflexivity.
    assert (HI_sem' : Smallstep.initial_state sem'
                        (initial_state (code prog') (prog_buffers prog') (prog_interface prog'))) by reflexivity.
    intros m dp_sem dp_sem' undef_m.
    apply (does_prefix_equiv det_sem) in dp_sem.
    apply (does_prefix_equiv det_sem') in dp_sem'.
    apply (does_prefix_equiv det_sem'').
    inversion dp_sem; subst; inversion dp_sem'; subst;
      try (exfalso; match goal with
             | H : (forall s, ~ Smallstep.initial_state sem  s) |- _ => exact (H _ HI_sem)
             | H : (forall s, ~ Smallstep.initial_state sem' s) |- _ => exact (H _ HI_sem')
           end);
      match goal with
      | Hi  : Smallstep.initial_state sem  ?s1, Hi' : Smallstep.initial_state sem' ?s2,
        Hst : Star sem ?s1 ?t ?s1', Hst' : Star sem' ?s2 ?t ?s2' |- _ =>
          destruct (MINIT _ _ Hi Hi') as [s3 [Hi3 Hmatch]];
          destruct (tsimulation_star props Hst Hst' s3 Hmatch) as [s3' [Hst3 Hmatch3]]
      end.
    destruct Hmatch3 as [M Hms].
    have Hpc3 := reachable_pc_color'' Hi3 Hst3.
    match goal with
    | Hii : Smallstep.initial_state sem ?ss, Hss : Star sem ?ss _ ?se |- _ =>
        have Hpc1 : pc_color_inv se by exact: (reachable_pc_color Hii Hss)
    end.
    inversion Hms as [M0 sa sb sc Hcom HstrL HwkR | M0 sa sb sc Hcom HwkL HstrR]; subst.
    -
      apply (does_FGoes_wrong Hi3 Hst3).
      + match goal with Hn1 : Nostep sem ?a |- _ =>
          exact: (nostep_reflect_left Hcom HstrL Hpc3 Hpc1 Hn1) end.
      + match goal with Hf1 : ~ final_state sem ?a |- _ =>
          exact: (notfinal_reflect_left Hcom HstrL Hpc3 Hf1) end.
    -
      exfalso.
      match goal with Hi : Smallstep.initial_state sem ?ss, Hst : Star sem ?ss m ?e |- _ =>
        have Hip := undef_running_left Hi Hst undef_m end.
      have Hic := relevant_of_side (strong_side HstrR) (common_color_valid2 Hcom).
      have Heq := common_color_eq12 Hcom.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have Hnotic := fdisjointP Hdis _ Hip. rewrite Heq in Hnotic. by rewrite Hic in Hnotic.
  Qed.


End RecTop.

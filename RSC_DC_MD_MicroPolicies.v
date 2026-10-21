Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RecompositionTop.
Require Import MicroPolicies.Recomposition.RSC_ME_MP.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.
Require Import BackTranslationMeMP.Backtranslation_ME_MP_Inst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type MicroPoliciesInput.

  Parameter p c : program.
  Parameter L P C NC : nat.

  Axiom Hwfmp_p : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) p.
  Axiom Hwfmp_c : wf_mp L P C (unionm (prog_interface p) (prog_interface c)) c.

  Axiom Hmergeable : mergeable_interfaces (prog_interface p) (prog_interface c).
  Axiom Hclosed : closed_program (program_link p c).

  Axiom comps_bounded : forall x,
    (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) ->
    1 + x < 2 ^ NC.
  Axiom NC_lt_word : NC < word_size mt.
  Axiom alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
  Axiom memory_size_pc :
    size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c)))
      + size (code p ++ code c) < alloc_label.

  Parameter fm : finpref_behavior.
  Axiom observed : does_prefix (mp_sem NC (program_link p c)) fm.
  Axiom safe : not_wrong_finpref fm.

  Axiom fits : bt_fits L P C p c (finpref_trace fm).

End MicroPoliciesInput.

Module RSC_DC_MD_MicroPolicies (In : MicroPoliciesInput).

  Module Lft <: MEtoMP_Left.
    Definition p := In.p.
    Definition c := In.c.
    Definition L := In.L.
    Definition P := In.P.
    Definition C := In.C.
    Definition NC := In.NC.
    Definition Hwfmp_p := In.Hwfmp_p.
    Definition Hwfmp_c := In.Hwfmp_c.
    Definition Hmergeable := In.Hmergeable.
    Definition Hclosed := In.Hclosed.
    Definition comps_bounded := In.comps_bounded.
    Definition NC_lt_word := In.NC_lt_word.
    Definition alloc_label_lt_word_NC := In.alloc_label_lt_word_NC.
    Definition memory_size_pc := In.memory_size_pc.
  End Lft.

  Module BT := BT_ME Lft.

  Module Obs <: ObservedRun Lft BT.
    Definition fm := In.fm.
    Definition observed := In.observed.
    Definition safe := In.safe.
    Definition fits := In.fits.
  End Obs.

  Module M := RSC_ME_MP_Faithful Lft BT Obs.

  Theorem RSC_DC_MD_MicroPolicies :
    does_prefix M.Trec.sem'' In.fm
    \/ (exists m',
          does_prefix M.Trec.sem'' (FGoes_wrong m')
          /\ trace_finpref_prefix m' In.fm
          /\ undef_in m' (prog_interface In.p)).
  Proof. exact: M.rsc_dc_md_me_mp_faithful. Qed.
  (* Print Assumptions RSC_DC_MD_MicroPolicies. *)

End RSC_DC_MD_MicroPolicies.

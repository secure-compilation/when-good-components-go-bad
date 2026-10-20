Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TDrain.
Require Import S2T.TSim.
Require Import S2T.TStatic.
Require Import S2T.TStart.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.

Module TFull.


Theorem s2t_forward_simulation (p : Source.program)
                               (tp : Intermediate.program) :
  Source.well_formed_program p ->
  Source.closed_program p ->
  compile_program p = Some tp ->
  forward_simulation
    (S.CS.sem p)
    (TSim.t_sem (Transitional.intermediate_to_transitional tp) tp).
Proof.
  move=> Hwf Hclosed Hcomp.
  have Huniq := TStatic.labels_uniq_compiled Hcomp.
  have Hee : TSim.entry_ext (Transitional.intermediate_to_transitional tp)
               (Source.prog_interface p) (labelsP p) p.
  { move=> C Cf P P_expr HneC Him Hfind.
    case: (TStatic.entry_ext_whole_any Hwf Hclosed Hcomp Him Hfind)
      => [Hdom [pcW [tniW [plmf [pl [pcE [cbody [sA [sB
         [[Hfd Hex Hchk Hplm] Hwrap EcE Hce HcodeE]]]]]]]]]].
    split; first exact: Hdom.
    by exists pcW, tniW, plmf, pl, pcE, sA, sB, cbody; split=> //; split. }
  apply: (TSim.t_forward_simulation (iface := Source.prog_interface p) _ Hee).
  -
    move=> C P P_expr plm tl Hfind Hplm Htl.
    case: (TStatic.entry_int_whole_any Hwf Hcomp Hfind Hplm Htl)
      => [pcE [cbody [sA [sB [EcE Hce Hcode]]]]].
    by exists pcE, sA, sB, cbody.
  -
    move=> C0 plm0 Hg. exact: (TStatic.labelsP_domm Hwf Hg).
  -
    apply: (TStart.start_ok_proof Hwf Hclosed Hcomp _ Huniq).
    by rewrite (compilation_preserves_interface _ _ Hcomp).
Qed.

End TFull.

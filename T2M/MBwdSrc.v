Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Common.Linking.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.

Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import S2T.TSem.
Require Import S2T.TSim.
Require Import S2T.TFull.

Require Import T2M.MStatic.
Require Import T2M.MInj.
Require Import T2M.MSig.
Require Import T2M.MSync.
Require Import T2M.MFlip.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Theorem t2me_H_bwd_src :
  forall (L P C : nat) (sa sb : Source.program)
         (a b : Intermediate.program) (m : finpref_behavior),
  Source.well_formed_program sa ->
  Source.well_formed_program sb ->
  Source.closed_program (Source.program_link sa sb) ->
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  MDefs.t2m_ok L P C a ->
  MDefs.t2m_ok L P C b ->
  MDefs.link_fits L P C a b ->
  forall (MM : Component.id -> seq sv),
  (forall c S, getm (MDefs.cde a b) c = Some S ->
     comp_ok (c, 1, Z0) S (MM c)) ->
  (forall pc iv r tg c p,
     Transitional.executing (MDefs.cde a b) pc (TrConst iv r) tg c ->
     iv = IPtr p ->
     p = (c, 0, Z0) \/
     ((p = (c, 1, Z0) \/ p = (c, 1, BinInt.Z.one)) /\
      (r = R_AUX1 \/ r = R_AUX2))) ->
  (forall (c : Component.id) (S : TS.tcode) (l : label)
      (m0 m0' : nat) (t1 t2 : mem_tag),
     getm (MDefs.cde a b) c = Some S ->
     nth_error S m0 = Some (TrLabel (inl l), t1) ->
     nth_error S m0' = Some (TrLabel (inl l), t2) -> m0 = m0') ->
  (MDefs.run_fits (MDefs.cde a b) (Intermediate.program_link a b)
     (finpref_trace m) ->
   forall ts0,
     TSim.t_initial_base (MDefs.cde a b)
       (Intermediate.program_link a b) ts0 ->
     mm_dsync L P C a b (MDefs.PBw a b) (MDefs.PIw a b) MM
       (MDefs.cde a b) (amap0 (MDefs.PBw a b)) ts0
       (Merged.initial_state
          (Definitions.code (MDefs.Wme L P C a b))
          (Definitions.prog_buffers (MDefs.Wme L P C a b))
          (Definitions.prog_interface (MDefs.Wme L P C a b)))) ->
  does_prefix (MDefs.mesem L P C a b) m ->
  MDefs.run_fits (MDefs.cde a b) (Intermediate.program_link a b)
    (finpref_trace m) ->
  exists beh,
    program_behaves (S.CS.sem (Source.program_link sa sb)) beh /\
    (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).
Proof.
move=> L P C sa sb a b m Hwsa Hwsb HclS Hca Hcb Hlink Hcl Hoka Hokb
       Hfits MM0 HMM0 Hcst0 Huniq0 Hdsy0 Hdp Hrf.
have HlinkS : linkable (Source.prog_interface sa) (Source.prog_interface sb).
{ move: Hlink.
  by rewrite (compilation_preserves_interface _ _ Hca)
             (compilation_preserves_interface _ _ Hcb). }
have HwfS : Source.well_formed_program (Source.program_link sa sb)
  := Source.linking_well_formedness Hwsa Hwsb HlinkS.
have [pc Hcpc] := well_formed_compilable _ HwfS.
have Epc : pc = Intermediate.program_link a b
  := separate_compilation _ _ _ _ _ Hwsa Hwsb HlinkS Hca Hcb Hcpc.
subst pc.
have FS := TFull.s2t_forward_simulation HwfS HclS Hcpc.
have [behS HbehS] :=
  @program_behaves_exists (S.CS.sem (Source.program_link sa sb)).
have [bT [HbT Himpr]] := forward_simulation_behavior_improves FS HbehS.
exists behS. split; first exact: HbehS.
apply: (improves_prefix_transfer Himpr).
have Hprem : MDefs.t2me_premises L P C a b.
{ split; last split.
  - split.
    + by exists sa; split.
    + by exists sb; split.
    + exact: (compilation_preserves_well_formedness Hwsa Hca).
    + exact: (compilation_preserves_well_formedness Hwsb Hcb).
    + exact: Hlink.
  - exact: Hcl.
  - by split. }
exact: (t2me_bwd_assembled_for Hprem HMM0 Hcst0 Huniq0 Hdsy0 Hdp Hrf HbT).
Qed.

Theorem t2me_bt_run :
  forall (L P C : nat) (sa sb : Source.program)
         (a b : Intermediate.program) (m : finpref_behavior),
  Source.well_formed_program sa ->
  Source.well_formed_program sb ->
  Source.closed_program (Source.program_link sa sb) ->
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  MDefs.t2m_ok L P C a ->
  MDefs.t2m_ok L P C b ->
  MDefs.link_fits L P C a b ->
  forall (MM : Component.id -> seq sv),
  (forall c S, getm (MDefs.cde a b) c = Some S ->
     comp_ok (c, 1, Z0) S (MM c)) ->
  (forall pc iv r tg c p,
     Transitional.executing (MDefs.cde a b) pc (TrConst iv r) tg c ->
     iv = IPtr p ->
     p = (c, 0, Z0) \/
     ((p = (c, 1, Z0) \/ p = (c, 1, BinInt.Z.one)) /\
      (r = R_AUX1 \/ r = R_AUX2))) ->
  (forall (c : Component.id) (S : TS.tcode) (l : label)
      (m0 m0' : nat) (t1 t2 : mem_tag),
     getm (MDefs.cde a b) c = Some S ->
     nth_error S m0 = Some (TrLabel (inl l), t1) ->
     nth_error S m0' = Some (TrLabel (inl l), t2) -> m0 = m0') ->
  (MDefs.run_fits (MDefs.cde a b) (Intermediate.program_link a b)
     (finpref_trace m) ->
   forall ts0,
     TSim.t_initial_base (MDefs.cde a b)
       (Intermediate.program_link a b) ts0 ->
     mm_dsync L P C a b (MDefs.PBw a b) (MDefs.PIw a b) MM
       (MDefs.cde a b) (amap0 (MDefs.PBw a b)) ts0
       (Merged.initial_state
          (Definitions.code (MDefs.Wme L P C a b))
          (Definitions.prog_buffers (MDefs.Wme L P C a b))
          (Definitions.prog_interface (MDefs.Wme L P C a b)))) ->
  does_prefix (S.CS.sem (Source.program_link sa sb)) m ->
  not_wrong_finpref m ->
  MDefs.run_fits (MDefs.cde a b) (Intermediate.program_link a b)
    (finpref_trace m) ->
  does_prefix (MDefs.mesem L P C a b) m.
Proof.
move=> L P C sa sb a b m Hwsa Hwsb HclS Hca Hcb Hlink Hcl Hoka Hokb
       Hfits MM0 HMM0 Hcst0 Huniq0 Hdsy0 Hdp Hnw Hrf.
have HlinkS : linkable (Source.prog_interface sa) (Source.prog_interface sb).
{ move: Hlink.
  by rewrite (compilation_preserves_interface _ _ Hca)
             (compilation_preserves_interface _ _ Hcb). }
have HwfS : Source.well_formed_program (Source.program_link sa sb)
  := Source.linking_well_formedness Hwsa Hwsb HlinkS.
have [pc Hcpc] := well_formed_compilable _ HwfS.
have Epc : pc = Intermediate.program_link a b
  := separate_compilation _ _ _ _ _ Hwsa Hwsb HlinkS Hca Hcb Hcpc.
subst pc.
have FS := TFull.s2t_forward_simulation HwfS HclS Hcpc.
have HdpT : does_prefix (MDefs.tsem a b) m
  := fsim_does_prefix FS Hdp Hnw.
have Hprem : MDefs.t2me_premises L P C a b.
{ split; last split.
  - split.
    + by exists sa; split.
    + by exists sb; split.
    + exact: (compilation_preserves_well_formedness Hwsa Hca).
    + exact: (compilation_preserves_well_formedness Hwsb Hcb).
    + exact: Hlink.
  - exact: Hcl.
  - by split. }
exact: (t2me_fwd_assembled Hprem HMM0 Hcst0 Huniq0 Hdsy0 HdpT Hnw Hrf).
Qed.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimCode.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TStack.
Require Import S2T.TInject.
Require Import S2T.TLabel.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.
Require Import S2T.TMatch.
Require Import S2T.TDrain.
Require Import S2T.TLeaf.
Require Import S2T.TProlog.
Require Import S2T.TDiagram.
Require Import S2T.TSim.
Require Import S2T.TStatic.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import zify.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TStart.

Section WithProgram.

Variable p : Source.program.
Variable tp : Intermediate.program.
Variable iface : Program.interface.

Local Notation cde := (Transitional.intermediate_to_transitional tp).
Local Notation m0 :=
  (Transitional.Memory.prepare_procedures_initial_memory tp).

Hypothesis Hwf : Source.well_formed_program p.
Hypothesis Hclosed : Source.closed_program p.
Hypothesis Hcomp : compile_program p = Some tp.
Hypothesis Hiface : domm iface = domm (Intermediate.prog_interface tp).
Hypothesis Huniq : forall C0, TDrain.labels_uniq cde C0.


Lemma buf_shape C ib :
  getm (Source.prog_buffers p) C = Some ib ->
  getm (Intermediate.prog_buffers tp) C
  = Some (mkfmap [:: (0, ib); (1, inr [:: Undef; Int 0])]).
Proof.
  move=> Hg.
  by rewrite (compilation_preserves_buffers Hcomp) /gen_buffers mapmE Hg.
Qed.

Lemma buf_domm :
  domm (Source.prog_buffers p) = domm (Intermediate.prog_interface tp).
Proof.
  by rewrite (compilation_preserves_interface _ _ Hcomp)
             -(Source.wfprog_defined_buffers Hwf).
Qed.

Lemma minj0 : TInject.minj init_renaming (Source.prepare_buffers p) m0.
Proof.
  apply: TStatic.initial_minj.
  - move=> C ib Hg. exact: (Source.wfprog_buffer_values Hwf Hg).
  - exact: buf_shape.
  - exact: buf_domm.
Qed.

Lemma main_dom : Component.main \in domm (Intermediate.prog_interface tp).
Proof.
  have [mexpr Hmain] : exists mexpr, Source.prog_main p = Some mexpr.
  { case E: (Source.prog_main p) => [m|]; first by exists m.
    by move: (Source.cprog_main_existence Hclosed); rewrite E. }
  rewrite (compilation_preserves_interface _ _ Hcomp).
  apply/(proj2 (Source.wfprog_main_existence Hwf)). by rewrite Hmain.
Qed.

Lemma main_buf_shape :
  exists ib, getm (Intermediate.prog_buffers tp) Component.main
             = Some (mkfmap [:: (0, ib); (1, inr [:: Undef; Int 0])]).
Proof.
  have Hin : Component.main \in domm (Source.prog_buffers p)
    by rewrite buf_domm; exact: main_dom.
  case/dommP: Hin => [ib Hib]. exists ib. exact: buf_shape Hib.
Qed.

Lemma main_cells :
  Transitional.Memory.load m0 (Component.main, 1, 0%Z)
  = Some (MVal Other Undef, def_mem_tag Component.main false)
  /\ Transitional.Memory.load m0 (Component.main, 1, 1%Z)
     = Some (MVal Other (Int 0), def_mem_tag Component.main false).
Proof.
  case: main_buf_shape => [ib Hib].
  exact: (TStatic.initial_cells Hib main_dom).
Qed.


Lemma main_code :
  exists mexpr CprocsT cd plmf plf pre post s s',
    [/\ Source.prog_main p = Some mexpr,
        getm (labelsP p) Component.main = Some plmf,
        getm plmf Procedure.main = Some plf,
        compile_proc Component.main (lbp Component.main) (scr Component.main)
          plmf Procedure.main mexpr s = Some (cd, s')
      & [/\ getm (Intermediate.prog_procedures tp) Component.main
            = Some CprocsT,
            getm CprocsT Procedure.main = Some cd,
            Transitional.linearize_component tp Component.main
            = pre ++ (Transitional.TrLabel (inr (Component.main,
                                                 Procedure.main)),
                      Transitional.head_tag tp Component.main Procedure.main)
                    :: [seq Transitional.instr_to_transitional Component.main i
                       | i <- cd] ++ post
          & Transitional.find_plabel_in_code cde Component.main Procedure.main
            = Some (Component.main, 0, Z.of_nat (size pre))]].
Proof.
  have [mexpr Hmain] : exists mexpr, Source.prog_main p = Some mexpr.
  { case E: (Source.prog_main p) => [m|]; first by exists m.
    by move: (Source.cprog_main_existence Hclosed); rewrite E. }
  have [CprocsM [HgCm HgPm]] :
    exists CprocsM,
      getm (Source.prog_procedures p) Component.main = Some CprocsM
      /\ getm CprocsM Procedure.main = Some mexpr.
  { move: Hmain. rewrite /Source.prog_main /Source.find_procedure.
    case E: (getm (Source.prog_procedures p) Component.main) => [Cp|] //= H.
    by exists Cp. }
  case: (compile_prog_procedures_spec Hwf Hcomp)
    => [labels [cenv1 [Egen HSPEC]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  case: (HSPEC _ _ _ _ HgCm HgPm)
    => [plmf [CprocsT [cd [sx1 [sx2 [Hplmf HgT HgTP Hcp]]]]]].
  have [plf Hplf] : exists plf, getm plmf Procedure.main = Some plf.
  { move: Hcp. rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
    case: (getm plmf Procedure.main) => [x|] //=. by exists x. }
  case: (TStatic.find_plabel_in_code_at HgT HgTP) => [pre [post [Elin _ Hfind]]].
  exists mexpr, CprocsT, cd, plmf, plf, pre, post, sx1, sx2.
  split.
  - exact: Hmain.
  - by rewrite Elab.
  - exact: Hplf.
  - exact: Hcp.
  - by split.
Qed.

Lemma scratch_cells C' :
  C' \in domm (Intermediate.prog_interface tp) ->
  Transitional.Memory.load m0 (C', 1, 0%Z)
  = Some (MVal Other Undef, def_mem_tag C' false).
Proof.
  move=> HC'.
  have Hin : C' \in domm (Source.prog_buffers p) by rewrite buf_domm.
  case/dommP: Hin => [ib Hib].
  by case: (TStatic.initial_cells (buf_shape Hib) HC').
Qed.

Lemma main_guard :
  Component.eqb Component.main Component.main
  && Procedure.eqb Procedure.main Procedure.main = true.
Proof. by rewrite /Component.eqb /Procedure.eqb !PeanoNat.Nat.eqb_refl. Qed.


Theorem start_ok_proof : TSim.start_ok cde iface (labelsP p) p tp.
Proof.
  move=> s1 Hini.
  case: main_code => [mexpr [CprocsT [cd [plmf [plf [pre [post [sx1 [sx2
    [Hmain Hplmf Hplf Hcp [HgT HgTP Elin Hfind]]]]]]]]]]].
  rewrite Hini /S.CS.initial_machine_state Hmain.
  set pcW := ((Component.main, 0, Z.of_nat (size pre)) : Pointer.t).
  have Hbase : TSim.t_initial_base cde tp
                 (m0, Transitional.Register.init, pcW, Level 0)
    by exists pcW.
  have Hexec := TStatic.executing_header HgT HgTP Elin.
  case Hfin: (immediately_final mexpr).
  -
    case: (compile_proc_shape_main_final _ _ _ _ _ _ _ _ Hcp Hplf main_guard
             Hfin) => [restH EcdH].
    have Hc1 : TMacros.code_at_I cde Component.main (Pointer.inc pcW)
                 (IHalt :: restH).
    { apply: (TStatic.code_at_I_after_header (B := IHalt :: restH) (D := [::])
                HgT HgTP Elin). by rewrite EcdH cats0. }
    have S1 : TS.step cde (m0, Transitional.Register.init, pcW, Level 0) E0
              (m0, Transitional.Register.init, Pointer.inc pcW, Level 0).
    { eapply TS.Label; first exact: Hexec.
      apply: PcFall. exact: (TMacros.code_at_I_head Hc1). }
    exists (m0, Transitional.Register.init, Pointer.inc pcW, Level 0). split.
    + exists (m0, Transitional.Register.init, pcW, Level 0).
      split; first exact: Hbase. exact: star_one S1.
    + apply: TSim.MS_halted;
        [exact: minj0 | exact: (TMacros.code_at_I_head Hc1) | by [] | by []].
  -
    case: (TStatic.entry_main_of_compiled HgT HgTP Hcp Hplf main_guard Hfin)
      => [pcW' [pcE [cbody [sA [sB [lmain [lreturn
         [Hfind' HcodeW EcE Hce HcodeE]]]]]]]].
    have EpcW : pcW' = pcW.
    { move: Hfind'. rewrite Hfind. by move=> [<-]. }
    rewrite EpcW in HcodeW.
    have S1 : TS.step cde (m0, Transitional.Register.init, pcW, Level 0) E0
              (m0, Transitional.Register.init, Pointer.inc pcW, Level 0).
    { eapply TS.Label; first exact: Hexec.
      apply: PcFall. exact: (TMacros.code_at_I_head HcodeW). }
    have [Hscr0 Hflag0] := main_cells.
    have HcompW : Pointer.component (Pointer.inc pcW) = Component.main
      by rewrite Pointer.inc_preserves_component.
    case: (TProlog.ef_main_entry_run (L := [::]) HcodeW HcompW
             (TStatic.init_regs_tag R_RA) Hscr0 (erefl _) Hflag0 (erefl _)
             (erefl _) (TStatic.initial_memory_component main_dom)
             (ltac:(by []) : ~ List.In TInv.CReg (TInv.sites [::]))
             (ltac:(by []) : ~ List.In
                (TInv.CMem ((Component.main, 1, 0%Z) : Pointer.t))
                (TInv.sites [::]))
             (ltac:(by []) : ~ List.In
                (TInv.CMem ((Component.main, 1, 1%Z) : Pointer.t))
                (TInv.sites [::]))
             (ltac:(by move=> b0; rewrite /init_renaming; case: ifP)
                : forall b0, init_renaming Component.main b0 <> Some 1)
             minj0 (TStatic.initial_tag_inv tp))
      => [m1 [rs1 [fbE [pcF1
         [Pl [Hfresh1 Havoid1 HfbE1 Hmj1 Hcap1]
             [Hw0 Ht0 Hw1 Ht1 [Hw2 Ht2 Hw3 Ht3]]
             [Hpv Hpt EcF1 HcF1 [HONE1 HSP1 HCOM1]]
             [Htag1 Hflagv1 Hflagt1]]]]]].
    have Hb1E : forall (C' : Component.id) (o : Z),
        Pointer.component ((C', 1, o) : Pointer.t) <> Component.main
        \/ Pointer.block ((C', 1, o) : Pointer.t) <> fbE
      by move=> C' o; right => /= E; apply: HfbE1; rewrite -E.
    have Hne01 : forall C' : Component.id,
        ((C', 1, 0%Z) : Pointer.t) <> (Component.main, 1, 1%Z)
      by move=> C' E; move: (f_equal Pointer.offset E) => /=; lia.
    have Lv1 : forall C' : Component.id,
        TMem.vload m1 (C', 1, 0%Z) = TMem.vload m0 (C', 1, 0%Z)
      by move=> C'; exact: (Hpv _ (Hb1E C' 0%Z) (Hne01 C')).
    have Lt1 : forall C' : Component.id,
        TMem.tload m1 (C', 1, 0%Z) = TMem.tload m0 (C', 1, 0%Z)
      by move=> C'; exact: (Hpt _ (Hb1E C' 0%Z) (Hne01 C')).
    have HcE0 : TMacros.code_at_I cde Component.main pcE
        ([::] ++ ILabel plf
         :: ([:: IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need mexpr))) R_SP;
                 IAlloc R_SP R_SP]
             ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
             ++ (cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])))
      by move: HcodeE; by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    case: (TMacros.code_at_I_label_find HcE0 EcE (@Huniq Component.main))
      => [pcL [HfindL EcL HcL]].
    have SJ : TS.step cde (m1, rs1, pcF1, Level 0) E0
              (m1, Transitional.Register.set R_RA (Ptr (Pointer.inc pcF1))
                     InternalJump rs1, pcL, Level 0).
    { eapply TS.Jal.
      - exact: (TMacros.code_at_I_head HcF1).
      - by rewrite EcF1; exact: HfindL.
      - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
        by rewrite EcL EcF1. }
    set rs2 := Transitional.Register.set R_RA (Ptr (Pointer.inc pcF1))
                 InternalJump rs1 in SJ *.
    have Htag2 : TInv.tag_inv [:: (TInv.CReg, InternalJump)] m1 rs2 (Level 0)
      by apply: (TInv.tag_inv_jal (Pointer.inc pcF1) _ Htag1); by [].
    have Hnn : cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump] <> [::]
      by apply: TDrain.cat_nonempty.
    have [nxtB [restB EB]] := TDrain.nonempty_cons Hnn.
    have HcL' : TMacros.code_at_I cde Component.main pcL
        ([:: ILabel plf; IMov R_SP R_AUX1;
             IConst (IInt (Z.of_nat (4 + stack_need mexpr))) R_SP;
             IAlloc R_SP R_SP]
         ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
         ++ nxtB :: restB) by rewrite -EB; exact: HcL.
    have HONE2 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
      by rewrite /rs2 TInv.get_set_neq //.
    have [wsc Hwsc] : exists w,
        Transitional.Memory.load m1 (Component.main, 1, 0%Z) = Some w.
    { have Hv : TMem.vload m1 (Component.main, 1, 0%Z) = Some Undef
        by rewrite (Lv1 Component.main) /TMem.vload Hscr0.
      case: (TMem.vload_load Hv) => [w Hw]. by exists w. }
    have HcmF : exists cm, getm m1 Component.main = Some cm.
    { case Hg: (getm m1 Component.main) => [cm|]; first by exists cm.
      by move: Hwsc; rewrite /Transitional.Memory.load /= Hg. }
    case: (TProlog.prologue_run HcL' EcL HONE2 HcmF Hmj1 Htag2)
      => [m2 [rs3 [fbN [pcF2
         [Sp [Hfresh2 Havoid2 Hmj2 Hcap2 Hpres2] [Hsl0 Hsl1]
              [HONE3 HSP3 HARG3 HCOM3 HRA3] [Htag3 EcF2 HcF2]]]]]].
    have HfbN1 : Component.main = Component.main -> fbN <> 1
      by move=> _ E; apply: (Hfresh2 0%Z wsc); rewrite E.
    have HfbN1' : fbN <> 1 by exact: HfbN1.
    have [wE HwE] : exists w,
        Transitional.Memory.load m1 (Component.main, fbE, 0%Z) = Some w
      by case: (TMem.vload_load Hw0) => [w Hw]; exists w.
    have HneNE : fbN <> fbE
      by move=> E; apply: (Hfresh2 0%Z wE); rewrite E.
    have Lv2 : forall q, Pointer.block q <> fbN ->
        TMem.vload m2 q = TMem.vload m1 q
      by move=> q Hq; rewrite /TMem.vload (Hpres2 q (or_intror _ Hq)).
    have Lt2 : forall q, Pointer.block q <> fbN ->
        TMem.tload m2 q = TMem.tload m1 q
      by move=> q Hq; rewrite /TMem.tload (Hpres2 q (or_intror _ Hq)).
    have Hb1N : forall (C' : Component.id) (o : Z),
        Pointer.block ((C', 1, o) : Pointer.t) <> fbN
      by move=> C' o /= E; apply: HfbN1'; rewrite -E.
    have HbEN : forall o : Z,
        Pointer.block ((Component.main, fbE, o) : Pointer.t) <> fbN
      by move=> o /= E; apply: HneNE; rewrite E.
    exists (m2, rs3, pcF2, Level 0). split.
    + exists (m0, Transitional.Register.init, pcW, Level 0).
      split; first exact: Hbase.
      eapply star_step with (t1 := E0) (t2 := E0); [exact: S1 | | by []].
      eapply star_trans with (t1 := E0) (t2 := E0);
        [exact: (plus_star Pl) | | by []].
      eapply star_step with (t1 := E0) (t2 := E0); [exact: SJ | | by []].
      exact: Sp.
    + apply: (TSim.MS_expr (a := init_renaming) (scrs := emptym)
                (ret := Pointer.inc pcF1) (Sl := [::]) (fb := fbN)
                (prot := [:: (Component.main, fbE)]) (temps := [::])
                (plm := plmf) (c := cbody)
                (rest := pop R_ARG ++ pop R_SP ++ [:: IJump])
                (s1 := sA) (s2 := sB) (cap := 4 + stack_need mexpr)); last first.
      { by move=> v Ev; move: Hfin; rewrite Ev. }
      apply: TMatch.ExprInv.
      * exact: Hplmf.
      * by rewrite Hiface; exact: main_dom.
      * exact: Hmj2.
      *
        split.
        -- by move=> C' v; rewrite emptymE.
        -- split.
           ++ rewrite (Lv2 _ (Hb1N Component.main 1%Z)). exact: Hflagv1.
           ++ rewrite (Lt2 _ (Hb1N Component.main 1%Z)). exact: Hflagt1.
        -- move=> C' HC'. exists Undef.
           rewrite (Lv2 _ (Hb1N C' 0%Z)) (Lv1 C') /TMem.vload.
           by rewrite (scratch_cells _); last by rewrite -Hiface.
        -- move=> C' HC'.
           rewrite (Lt2 _ (Hb1N C' 0%Z)) (Lt1 C') /TMem.tload.
           by rewrite (scratch_cells _); last by rewrite -Hiface.
      * exact: HONE3.
      * by rewrite HSP3.
      * rewrite HARG3 /rs2 TInv.get_set_neq // HCOM1. exact: VI_int.
      * by rewrite HRA3 /rs2 TInv.get_set_eq.
      * by [].
      * exact: EcF2.
      * exact: Hce.
      * by rewrite EB.
      * apply: CMJ_base. exact: CM_stop.
      * exact: (fun C0 => @Huniq C0).
      * by split; [exact: HfbN1' | exact: Havoid2].
      * exact: init_scratch_priv.
      * by move=> ix; rewrite ltn0.
      * exact: Hcap2.
      * rewrite /= maxn0 add0n. by lia.
      * apply/negP => /orP [/eqP Ex|] //.
        by apply: HneNE; move: (f_equal snd Ex) => /= ->.
      *
        apply: TSM.SM_init.
        -- rewrite /TMem.vload Hsl0 /= /rs2 TInv.get_set_neq //.
           by rewrite HSP1.
        -- by rewrite /TMem.vload Hsl1.
        -- by rewrite /TMem.tload Hsl0.
        -- rewrite /TMem.tload Hsl1 /=.
           by rewrite (TInv.ti_regs Htag2 (r := R_ARG) (ltac:(by []))).
        -- by rewrite (Lv2 _ (HbEN 0%Z)); exact: Hw0.
        -- by rewrite (Lv2 _ (HbEN 1%Z)); exact: Hw1.
        -- by rewrite (Lt2 _ (HbEN 0%Z)); exact: Ht0.
        -- by rewrite (Lt2 _ (HbEN 1%Z)); exact: Ht1.
        -- by rewrite (Lv2 _ (HbEN 2%Z)); exact: Hw2.
        -- by rewrite (Lv2 _ (HbEN 3%Z)); exact: Hw3.
        -- by rewrite (Lt2 _ (HbEN 3%Z)); exact: Ht3.
        -- by split; [exact: HfbE1 | exact: Havoid1].
        -- by rewrite Pointer.inc_preserves_component.
        -- exact: (TMacros.code_at_I_tail HcF1).
        -- exact: HneNE.
      * by rewrite /TMatch.ledger_at /=; exact: Htag3.
      *
        by exists pcW; eexists; split; [exact: Hfind | exact: HcodeW].
Qed.

End WithProgram.

End TStart.

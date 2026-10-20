Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import S2T.TSem.
Require Import S2T.TSim.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require Import T2M.MSig.
Require T2M.MDisc.
Require Import T2M.MSync.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Lemma domm_head_zero (T' : Type) (m : NMap T') :
  0 \in domm m ->
  exists t, domm m = 0 :: t :> seq nat.
Proof.
move=> H0.
have Hs : sorted Ord.lt (\val (domm m)) := valP (domm m).
have Hval : (0 \in domm m) = (0 \in \val (domm m)) by [].
case E: (\val (domm m)) => [|h t].
- by move: H0; rewrite Hval E.
- exists t.
  have H0' : (0 \in h :: t).
  { by move: H0; rewrite Hval E. }
  case Eh: (h == 0); first by move/eqP: Eh => ->.
  exfalso.
  move: H0'; rewrite inE eq_sym Eh /= => H0t.
  move: Hs; rewrite E /= => Hpath.
  have Hall := order_path_min (@Ord.lt_trans _) Hpath.
  have := allP Hall _ H0t.
  by rewrite Ord_lt_nat ltn0.
Qed.


Section InitialMatch.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Local Notation tp := (Intermediate.program_link pra prb).
Local Notation cdeW :=
  (Transitional.intermediate_to_transitional_gen PI
     (Intermediate.program_link pra prb)).
Local Notation codeW :=
  (compiler_code L P C PB PI pra ++ compiler_code L P C PB PI prb).
Local Notation pc0 := (size (initial_memory (mt := mt) PB)).
Local Notation Wme :=
  (Definitions.program_link (compiler L P C PB PI pra)
                            (compiler L P C PB PI prb)).

Hypothesis HPI :
  PI = Intermediate.prog_interface (Intermediate.program_link pra prb).
Hypothesis HPB :
  PB = Intermediate.prog_buffers (Intermediate.program_link pra prb).

Hypothesis Hbound : size (linearize_bufs PB) + size codeW < 2 ^ word_size mt.
Hypothesis Hsmall :
  size (linearize_bufs PB) + size codeW < Merged.alloc_label.

Variable Cmain : NMap Machine.code.
Hypothesis Hmain_procs :
  Intermediate.prog_procedures (Intermediate.program_link pra prb)
    Component.main = Some Cmain.
Hypothesis Hmain_proc : Procedure.main \in domm Cmain.

Hypothesis Hwfa : Intermediate.well_formed_program pra.
Hypothesis Hwfb : Intermediate.well_formed_program prb.
Hypothesis Hlinkable :
  linkable (Intermediate.prog_interface pra) (Intermediate.prog_interface prb).

Lemma find_plabel_main (pr : Intermediate.program)
    (Cp : NMap Machine.code) :
  Intermediate.prog_procedures pr Component.main = Some Cp ->
  Procedure.main \in domm Cp ->
  Transitional.find_plabel
    (Transitional.linearize_component_gen PI pr Component.main)
    Component.main Procedure.main
  = Some BinNums.Z0.
Proof.
move=> Hg H0.
have [t Et] := domm_head_zero H0.
rewrite /Transitional.linearize_component_gen Hg /= Et /=.
by [].
Qed.

Lemma find_plabel_in_code_main :
  Transitional.find_plabel_in_code cdeW Component.main Procedure.main
  = Some (Component.main, 0, BinNums.Z0).
Proof.
rewrite /Transitional.find_plabel_in_code i2t_getm Hmain_procs /=.
by rewrite (find_plabel_main Hmain_procs Hmain_proc).
Qed.

Let colp : (@Merged.instr mt * mem_tag) -> bool :=
  fun cell => color cell.2 == Component.main.

Lemma find_color_pred_eq (cde0 : @Merged.code mt) :
  find (fun '(_, tag) => color tag == Component.main) cde0 = find colp cde0.
Proof.
apply: eq_find => cell.
by case: cell.
Qed.

Lemma init_tregs_get r :
  Transitional.Register.get r Transitional.Register.init
  = Transitional.tUndef.
Proof. by case: r. Qed.

Lemma reg0_sysregs : sysregs_ok (reg0 (mt := mt)).
Proof.
move=> k.
rewrite !inE => /orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]]];
  rewrite /reg0 mkfmapE /=;
  rewrite !(won_eqE (small_lt_reg _) (small_lt_reg _)) //=;
  by eexists.
Qed.

Theorem match_initial (ts : TS.state) :
  TSim.t_initial_base
    (Transitional.intermediate_to_transitional
       (Intermediate.program_link pra prb))
    (Intermediate.program_link pra prb) ts ->
  (forall c cm b blk o cell,
      Transitional.Memory.prepare_procedures_initial_memory
        (Intermediate.program_link pra prb) c = Some cm ->
      getm (Transitional.Memory.content cm) b = Some blk ->
      List.nth_error blk o = Some cell ->
      MDefs.value_fits
        (Transitional.Memory.prepare_procedures_initial_memory
           (Intermediate.program_link pra prb))
        (Transitional.val cell.1)) ->
  match_st L P C pra prb PB PI (amap0 PB) ts
    (Merged.initial_state (Definitions.code Wme)
       (Definitions.prog_buffers Wme) (Definitions.prog_interface Wme)).
Proof.
move=> Hbase Hfit.
have HcdeE : Transitional.intermediate_to_transitional
               (Intermediate.program_link pra prb) = cdeW
  by rewrite /Transitional.intermediate_to_transitional -HPI.
have EB : unionm (Intermediate.prog_buffers pra) (Intermediate.prog_buffers prb)
          = PB
  by rewrite HPB.
case: Hbase => pcM [HpcM Ets].
rewrite HcdeE find_plabel_in_code_main in HpcM.
case: HpcM => EpcM.
subst ts; rewrite -{}EpcM.
set ms := Merged.initial_state _ _ _.
have Hms_mem :
  Symbolic.mem ms
  = unionm (encode_code codeW pc0) (initial_memory (mt := mt) PB).
{ by rewrite /ms /Merged.initial_state /= EB. }
have Hms_regs : Symbolic.regs ms = reg0 (mt := mt).
{ by rewrite /ms /Merged.initial_state. }
have Hms_pcv :
  Symbolic.pcv ms = word_of_nat (pc0 + find colp codeW).
{ by rewrite /ms /Merged.initial_state /Symbolic.pcv /= EB
             find_color_pred_eq. }
have Hms_pct : Symbolic.pct ms = LRC.Level 0 Component.main.
{ by rewrite /ms /Merged.initial_state. }
rewrite /match_st.
constructor.
-
  rewrite Hms_pcv.
  case Hside: (Component.main \in domm (Intermediate.prog_procedures pra)).
  +
    have [Cp HCp] : exists Cp,
        Intermediate.prog_procedures pra Component.main = Some Cp
      by apply/dommP.
    have ECp : Cp = Cmain.
    { move: Hmain_procs. rewrite /= unionmE HCp /=. by move=> [->]. }
    subst Cp.
    have Hseg : Transitional.intermediate_to_transitional_gen PI pra
                  Component.main
                = Some (Transitional.linearize_component_gen PI pra
                          Component.main)
      by rewrite i2t_getm HCp.
    apply: (@PCLeft _ _ _ _ _ _ _ _ _
              (Transitional.linearize_component_gen PI pra Component.main)).
    * by rewrite /= mem_domm HCp.
    * exact: Hseg.
    * by [].
    * rewrite /colp (find_color_link L P C prb PB PI HCp Hmain_proc).
      rewrite /tpos /= take0 /tseg_size /= addn0.
      congr word_of_nat. by lia.
  +
    have HnotA : Component.main \notin domm (Intermediate.prog_interface pra).
    { by rewrite (Intermediate.wfprog_defined_procedures Hwfa) Hside. }
    have HCp : Intermediate.prog_procedures prb Component.main = Some Cmain.
    { move: Hmain_procs. rewrite /= unionmE.
      by move: Hside; rewrite mem_domm; case: (Intermediate.prog_procedures
                                                 pra Component.main). }
    have Hseg : Transitional.intermediate_to_transitional_gen PI prb
                  Component.main
                = Some (Transitional.linearize_component_gen PI prb
                          Component.main)
      by rewrite i2t_getm HCp.
    apply: (@PCRight _ _ _ _ _ _ _ _ _
              (Transitional.linearize_component_gen PI prb Component.main)).
    * by rewrite /= Hside.
    * exact: Hseg.
    * by [].
    * rewrite /colp (find_color_link_r L P C PB PI Hwfa HnotA HCp Hmain_proc).
      rewrite /tpos /= take0 /tseg_size /= addn0.
      congr word_of_nat. by lia.
-
  by rewrite Hms_pct.
-
  rewrite Hms_regs => r.
  left.
  have [w Hw] := reg0_get r.
  exists (Atom w Other).
  split.
  + exact: Hw.
  + by rewrite init_tregs_get; exact: VRUndef.
  + by rewrite init_tregs_get.
-
  rewrite Hms_mem.
  have Hwftp : Intermediate.well_formed_program
                 (Intermediate.program_link pra prb)
    := Intermediate.linking_well_formedness Hwfa Hwfb Hlinkable.
  by apply: minj_init => //.
-
  move=> w v Hv.
  by rewrite Hms_mem unionmE Hv.
-
  rewrite Hms_regs.
  exact: reg0_sysregs.
-
  rewrite Hms_mem unionmE.
  have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
  { rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
  have Hal32 : Merged.alloc_label < 2 ^ word_size mt.
  { have H1532 : (2 : nat) ^ imm_size mt < 2 ^ word_size mt
      by rewrite imm_size_mt word_size_mt ltn_exp2l.
    by lia. }
  have Hsz : size (initial_memory (mt := mt) PB) = size (linearize_bufs PB).
  { apply: initial_memory_size_eq. by lia. }
  have Hcode0 : encode_code codeW (size (initial_memory (mt := mt) PB))
                  (@word_of_nat (word_size mt) Merged.alloc_label) = None.
  { case E: (encode_code _ _ _) => [v|]; last by [].
    exfalso.
    have [n [Hw [Hn _]]] := encode_code_nth_inv E.
    have Hn32 : n + size (initial_memory (mt := mt) PB) < 2 ^ word_size mt
      by lia.
    have := won_inj Hal32 Hn32 Hw.
    by lia. }
  have Hge : size (linearize_bufs PB) <= Merged.alloc_label
    := leq_trans (leq_addr (size codeW) _) (ltnW Hsmall).
  have Hdata0 : initial_memory (mt := mt) PB
                  (@word_of_nat (word_size mt) Merged.alloc_label) = None.
  { apply: initial_memory_above.
    - exact: Hge.
    - exact: Hal32. }
  by rewrite Hcode0 Hdata0.
Qed.


Theorem sync_initial (MM : Component.id -> seq sv) (pcM : Pointer.t) :
  (forall c S, getm cdeW c = Some S -> comp_ok (c, 1, Z0) S (MM c)) ->
  Transitional.find_plabel_in_code cdeW Component.main Procedure.main
    = Some pcM ->
  (forall c cm b blk o cell,
      Transitional.Memory.prepare_procedures_initial_memory
        (Intermediate.program_link pra prb) c = Some cm ->
      getm (Transitional.Memory.content cm) b = Some blk ->
      List.nth_error blk o = Some cell ->
      MDefs.value_fits
        (Transitional.Memory.prepare_procedures_initial_memory
           (Intermediate.program_link pra prb))
        (Transitional.val cell.1)) ->
  sync_claims L P C pra prb PB PI MM (amap0 PB)
    (Transitional.Memory.prepare_procedures_initial_memory
       (Intermediate.program_link pra prb))
    Transitional.Register.init
    (Symbolic.regs (Merged.initial_state (Definitions.code Wme)
       (Definitions.prog_buffers Wme) (Definitions.prog_interface Wme)))
    (Symbolic.mem (Merged.initial_state (Definitions.code Wme)
       (Definitions.prog_buffers Wme) (Definitions.prog_interface Wme)))
    pcM None [::] (fun _ => [::]).
Proof.
move=> HMM HpcM Hfit.
have [EcM EvT] := MDisc.plabel_target HMM HpcM.
have EB : unionm (Intermediate.prog_buffers pra)
            (Intermediate.prog_buffers prb) = PB
  by rewrite HPB.
have Hms_regs : Symbolic.regs (Merged.initial_state
    (Definitions.code Wme) (Definitions.prog_buffers Wme)
    (Definitions.prog_interface Wme)) = Merged.reg0 (mt := mt).
{ by []. }
have Hms_mem : Symbolic.mem (Merged.initial_state
    (Definitions.code Wme) (Definitions.prog_buffers Wme)
    (Definitions.prog_interface Wme))
  = unionm (encode_code codeW pc0) (initial_memory (mt := mt) PB).
{ by rewrite /Merged.initial_state /= EB. }
rewrite Hms_regs Hms_mem.
have Hwftp : Intermediate.well_formed_program
               (Intermediate.program_link pra prb)
  := Intermediate.linking_well_formedness Hwfa Hwfb Hlinkable.
constructor.
-
  have [w Hw] := reg0_get R_COM.
  exists (Atom w Other). split.
  + exact: Hw.
  + rewrite init_tregs_get /tvrel /=. exact: VRUndef.
  + by rewrite init_tregs_get.
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> v0. rewrite EvT => -[<-]. by [].
-
  move=> c b j _.
  move=> cm blk cell a mc Hcm Hblk Hnth Ha Hmc.
  have Hmj : minj PB (cmapW L P C pra prb PB PI) (amap0 PB)
               (Transitional.Memory.prepare_procedures_initial_memory
                  (Intermediate.program_link pra prb))
               (unionm (encode_code codeW pc0)
                       (initial_memory (mt := mt) PB)).
  { by apply: minj_init => //. }
  have [mc' [Hmc' Hrelw]] := mj_cell Hmj Hcm Hblk Hnth Ha.
  have Emc : mc' = mc by move: Hmc; rewrite Hmc' => -[].
  subst mc'.
  case: Hrelw => [Hrel|Hclob]; first exact: Hrel.
  exfalso.
  have [v [Hcellv Hlin]] := t_init_cell (esym HPB) Hcm Hblk Hnth.
  have Ea : a = bl_base PB c b.
  { have [bm [bf [_ _ Eab]]] := amap0_dom Ha. exact: Eab. }
  have Hmceq : mc = {| vala := me_encode_val PB v;
                       taga := def_mem_tag c false |}.
  { have Hme := me_init_cell Hbound Hlin.
    move: Hmc.
    rewrite Ea.
    have -> : bl_base PB c b + j = nat_addr PB (c, b, j)
      by rewrite /nat_addr addnC.
    rewrite Hme. by move=> [<-]. }
  case: Hclob => [[_ _ Hti] _].
  move: Hti. rewrite Hmceq /=. by [].
-
  move=> v0 b j k _ Hb. by [].
-
  move=> v0 b k _ Hb. by [].
-
  move=> i A j k. by case: i.
Qed.

End InitialMatch.

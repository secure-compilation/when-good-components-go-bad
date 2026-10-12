(** * T2M match relation: relates a stackless T state (memory, registers,
    pc pointer, level tag) of the linked program to an me machine state of
    the linked compiled pair.  Says nothing about fit — fit premises enter
    the diagrams from [run_fits] (MDefs), not from the relation. *)

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
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import S2T.TSem.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MInj.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section MatchDef.

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

(* ================================================================== *)
(* 1. The linked T code decomposes per side.                          *)
(* ================================================================== *)

Lemma lin_comp_gen_eqproc (pr1 pr2 : Intermediate.program) c :
  Intermediate.prog_procedures pr1 c = Intermediate.prog_procedures pr2 c ->
  Transitional.linearize_component_gen PI pr1 c
  = Transitional.linearize_component_gen PI pr2 c.
Proof.
move=> E.
rewrite /Transitional.linearize_component_gen
        /Transitional.linearize_proc_gen E.
by [].
Qed.

Lemma cdeW_left c :
  c \in domm (Intermediate.prog_procedures pra) ->
  cdeW c = Transitional.intermediate_to_transitional_gen PI pra c.
Proof.
move=> /dommP [v Hv].
rewrite !i2t_getm /= unionmE Hv /=.
congr Some.
apply: lin_comp_gen_eqproc.
by rewrite /= unionmE Hv.
Qed.

Lemma cdeW_right c :
  c \notin domm (Intermediate.prog_procedures pra) ->
  cdeW c = Transitional.intermediate_to_transitional_gen PI prb c.
Proof.
move=> Hc.
have Hv : Intermediate.prog_procedures pra c = None
  by apply/dommPn.
rewrite !i2t_getm /= unionmE Hv /=.
case Hb: (Intermediate.prog_procedures prb c) => [w|] //=.
congr Some.
apply: lin_comp_gen_eqproc.
by rewrite /= unionmE Hv Hb.
Qed.

(* ================================================================== *)
(* 2. The pc relation.                                                *)
(* ================================================================== *)

(* the me flat position of the T pc (start of its expansion), by side —
   the address orientation ([pos + pc0]) matches [link_tfetch_l/r] *)
Variant pc_rel (tpc : Pointer.t) (w : mword mt) : Prop :=
| PCLeft cseg :
    Pointer.component tpc \in domm (Intermediate.prog_procedures pra) ->
    Transitional.intermediate_to_transitional_gen PI pra
      (Pointer.component tpc) = Some cseg ->
    BinInt.Z.le 0 (Pointer.offset tpc) ->
    w = word_of_nat
          (tpos PI pra (Pointer.component tpc) cseg
             (BinInt.Z.to_nat (Pointer.offset tpc)) + pc0) ->
    pc_rel tpc w
| PCRight cseg :
    Pointer.component tpc \notin domm (Intermediate.prog_procedures pra) ->
    Transitional.intermediate_to_transitional_gen PI prb
      (Pointer.component tpc) = Some cseg ->
    BinInt.Z.le 0 (Pointer.offset tpc) ->
    w = word_of_nat
          ((size (compiler_code L P C PB PI pra)
            + tpos PI prb (Pointer.component tpc) cseg
                (BinInt.Z.to_nat (Pointer.offset tpc))) + pc0) ->
    pc_rel tpc w.

(* ================================================================== *)
(* 3. The CODE-address map, and the register relation.                *)
(* ================================================================== *)

(* the linked layout's code-position function: component × T-array
   index ↦ flat me address (pc0 included) — [cmap_t]'s instantiation *)
Definition cmapW (c : Component.id) (q : nat) : option nat :=
  if c \in domm (Intermediate.prog_procedures pra)
  then omap (fun cseg => tpos PI pra c cseg q + pc0)
            (Transitional.intermediate_to_transitional_gen PI pra c)
  else omap (fun cseg => (size (compiler_code L P C PB PI pra)
                          + tpos PI prb c cseg q) + pc0)
            (Transitional.intermediate_to_transitional_gen PI prb c).

(* the STRONG per-register fact: value related through the address maps
   ([tvrel]: the value TAG picks the data/code interpretation), me tag =
   T value tag on the nose *)
Definition reg_synced (amap : amap_t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) : Prop :=
  exists ra,
    [/\ mregs (word_of_nat (Intermediate.Register.to_nat r)) = Some ra,
        tvrel cmapW amap (Transitional.Register.get r tregs) (vala ra)
      & taga ra = Transitional.tvtag (Transitional.Register.get r tregs)].

(* Every register is either synced or EVENT-CLOBBERED: on Call/Return
   T writes [tUndef] (tag OTHER) while me re-tags the old value
   INVALIDATED, a representation mismatch the relation must allow;
   diagrams take [reg_synced] premises for the registers they READ. *)
Definition mregs_rel (amap : amap_t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall r : register,
    reg_synced amap tregs mregs r
    \/ (exists ra,
          [/\ mregs (word_of_nat (Intermediate.Register.to_nat r)) = Some ra,
              Transitional.Register.get r tregs = Transitional.tUndef
            & taga ra = Invalidated]).

Lemma mregs_rel_lookup (amap : amap_t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) :
  mregs_rel amap tregs mregs ->
  exists ra,
    mregs (word_of_nat (Intermediate.Register.to_nat r)) = Some ra.
Proof.
move=> /(_ r) [[ra [Hra _ _]]|[ra [Hra _ _]]]; by exists ra.
Qed.

(* the me machine's [reg_clear_list] (Jal/Jump/Call/Return) reads the
   SYSTEM registers 7 and 16-19 too — their PRESENCE is part of the
   relation (their contents are policy-internal, unconstrained) *)
Definition sysregs_ok (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall k : nat, k \in [:: 7; 16; 17; 18; 19] ->
    exists ra, mregs (@word_of_nat (reg_field_size mt) k) = Some ra.

Lemma sysregs_ok_setm (mregs : {fmap reg mt -> @ratom mt})
    (k' : reg mt) (a : @ratom mt) :
  sysregs_ok mregs -> sysregs_ok (setm mregs k' a).
Proof.
move=> H k Hk.
rewrite setmE.
case: ifP => _; first by eexists.
exact: H Hk.
Qed.

(* ================================================================== *)
(* 4. The match relation.                                             *)
(* ================================================================== *)

Record match_states (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit) : Prop := {
  mm_pc    : pc_rel tpc (Symbolic.pcv ms);
  mm_pctag : Symbolic.pct ms
             = LRC.Level (Transitional.level tpct) (Pointer.component tpc);
  mm_regs  : mregs_rel amap tregs (Symbolic.regs ms);
  mm_mem   : minj PB cmapW amap tmem (Symbolic.mem ms);
  mm_code  : forall w v,
      encode_code codeW pc0 w = Some v -> Symbolic.mem ms w = Some v;
  mm_sys   : sysregs_ok (Symbolic.regs ms);
  mm_gap   : Symbolic.mem ms
               (@word_of_nat (word_size mt) Merged.alloc_label) = None
}.

Definition match_st (amap : amap_t) (ts : TS.state)
    (ms : @Symbolic.state mt lrc_tags unit) : Prop :=
  let '(tmem, tregs, tpc, tpct) := ts in
  match_states amap tmem tregs tpc tpct ms.

(* ================================================================== *)
(* 5. The fetch master lemma — the entry point of every diagram.      *)
(* ================================================================== *)

(* the diagram entry point: from T [executing] and the pc relation, the
   me memory at the me pc holds the FIRST expansion cell of the T
   instruction: same tag, decoding to the merged instruction. *)
Lemma match_fetch (mmem : {fmap mword mt -> matom})
    (tpc : Pointer.t) (w : mword mt)
    (i : Transitional.instr) (tg : mem_tag) cell :
  pc0 + size codeW < 2 ^ word_size mt ->
  (forall w' v, encode_code codeW pc0 w' = Some v -> mmem w' = Some v) ->
  Transitional.executing cdeW tpc i tg (Pointer.component tpc) ->
  pc_rel tpc w ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i, tg)) 0
  = Some cell ->
  exists (pos : nat) (v : matom),
    [/\ w = word_of_nat (pos + pc0),
        mmem w = Some v,
        taga v = cell.2,
        Types.decode_instr (vala v)
        = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                  (pc0 + pos))
      & cmapW (Pointer.component tpc)
          (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (pos + pc0)].
Proof.
move=> Hbound Hcode Hex Hpc Hcell.
have Hk : 0 < texp_size i by case: i {Hex Hcell}.
case: Hex => C_code [HcompE [Hcde [Hoff Hnth]]].
case: Hpc => cseg Hside Hseg Hle Hw.
-
  have Hcseg : C_code = cseg.
  { move: Hcde. rewrite (cdeW_left Hside) Hseg. by move=> [->]. }
  subst C_code.
  have [v [Hv [Htag Hdec]]] :=
    link_tfetch_l (pc0 := pc0) Hbound Hseg Hnth Hk Hcell.
  rewrite addn0 in Hv Hdec.
  exists (tpos PI pra (Pointer.component tpc) cseg
            (BinInt.Z.to_nat (Pointer.offset tpc))), v.
  split=> //.
  + by rewrite Hw; exact: (Hcode _ _ Hv).
  + by rewrite /cmapW Hside Hseg /=.
-
  have Hcseg : C_code = cseg.
  { move: Hcde. rewrite (cdeW_right Hside) Hseg. by move=> [->]. }
  subst C_code.
  have [v [Hv [Htag Hdec]]] :=
    link_tfetch_r (pc0 := pc0) Hbound Hseg Hnth Hk Hcell.
  rewrite addn0 in Hv Hdec.
  exists (size (compiler_code L P C PB PI pra)
          + tpos PI prb (Pointer.component tpc) cseg
              (BinInt.Z.to_nat (Pointer.offset tpc))), v.
  split=> //.
  + by rewrite Hw; exact: (Hcode _ _ Hv).
  + by rewrite /cmapW (negbTE Hside) Hseg /=.
Qed.

(* the k-th expansion cell of the executing instruction (the ALLOC
   stub spans FIVE cells; [match_fetch] is the k = 0 face) *)
Lemma match_fetch_k (mmem : {fmap mword mt -> matom})
    (tpc : Pointer.t) (w : mword mt)
    (i : Transitional.instr) (tg : mem_tag) (k : nat) cell :
  pc0 + size codeW < 2 ^ word_size mt ->
  (forall w' v, encode_code codeW pc0 w' = Some v -> mmem w' = Some v) ->
  Transitional.executing cdeW tpc i tg (Pointer.component tpc) ->
  pc_rel tpc w ->
  k < texp_size i ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i, tg)) k
  = Some cell ->
  exists (pos : nat) (v : matom),
    [/\ w = word_of_nat (pos + pc0),
        mmem (word_of_nat ((pos + k) + pc0)) = Some v,
        taga v = cell.2,
        Types.decode_instr (vala v)
        = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                  (pc0 + (pos + k)))
      & cmapW (Pointer.component tpc)
          (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (pos + pc0)].
Proof.
move=> Hbound Hcode Hex Hpc Hk Hcell.
case: Hex => C_code [HcompE [Hcde [Hoff Hnth]]].
case: Hpc => cseg Hside Hseg Hle Hw.
-
  have Hcseg : C_code = cseg.
  { move: Hcde. rewrite (cdeW_left Hside) Hseg. by move=> [->]. }
  subst C_code.
  have [v [Hv [Htag Hdec]]] :=
    link_tfetch_l (pc0 := pc0) Hbound Hseg Hnth Hk Hcell.
  exists (tpos PI pra (Pointer.component tpc) cseg
            (BinInt.Z.to_nat (Pointer.offset tpc))), v.
  split=> //.
  + exact: (Hcode _ _ Hv).
  + by rewrite /cmapW Hside Hseg /=.
-
  have Hcseg : C_code = cseg.
  { move: Hcde. rewrite (cdeW_right Hside) Hseg. by move=> [->]. }
  subst C_code.
  have [v [Hv [Htag Hdec]]] :=
    link_tfetch_r (pc0 := pc0) Hbound Hseg Hnth Hk Hcell.
  exists (size (compiler_code L P C PB PI pra)
          + tpos PI prb (Pointer.component tpc) cseg
              (BinInt.Z.to_nat (Pointer.offset tpc))), v.
  have Ea : (size (compiler_code L P C PB PI pra)
             + tpos PI prb (Pointer.component tpc) cseg
                 (BinInt.Z.to_nat (Pointer.offset tpc))) + k
            = size (compiler_code L P C PB PI pra)
              + (tpos PI prb (Pointer.component tpc) cseg
                   (BinInt.Z.to_nat (Pointer.offset tpc)) + k)
    by rewrite -addnA.
  split.
  + exact: Hw.
  + rewrite Ea. exact: (Hcode _ _ Hv).
  + exact: Htag.
  + by rewrite Ea.
  + by rewrite /cmapW (negbTE Hside) Hseg /=.
Qed.

(* ================================================================== *)
(* 6. [pc_rel] IS [cmapW] at the pc's coordinates — the glue the      *)
(*    control-flow diagrams invert through ([code_rel] uses cmapW).   *)
(* ================================================================== *)

Lemma pc_rel_cmap (tpc : Pointer.t) (w : mword mt) :
  pc_rel tpc w ->
  exists pos,
    [/\ cmapW (Pointer.component tpc)
          (BinInt.Z.to_nat (Pointer.offset tpc)) = Some pos,
        BinInt.Z.le 0 (Pointer.offset tpc)
      & w = @word_of_nat (word_size mt) pos].
Proof.
case=> cseg Hside Hseg Hle Hw.
- exists (tpos PI pra (Pointer.component tpc) cseg
            (BinInt.Z.to_nat (Pointer.offset tpc)) + pc0).
  split.
  + by rewrite /cmapW Hside Hseg /=.
  + exact: Hle.
  + exact: Hw.
- exists ((size (compiler_code L P C PB PI pra)
           + tpos PI prb (Pointer.component tpc) cseg
               (BinInt.Z.to_nat (Pointer.offset tpc))) + pc0).
  split.
  + by rewrite /cmapW (negbTE Hside) Hseg /=.
  + exact: Hle.
  + exact: Hw.
Qed.

Lemma cmap_pc_rel (tpc : Pointer.t) (w : mword mt) (pos : nat) :
  cmapW (Pointer.component tpc)
    (BinInt.Z.to_nat (Pointer.offset tpc)) = Some pos ->
  BinInt.Z.le 0 (Pointer.offset tpc) ->
  w = @word_of_nat (word_size mt) pos ->
  pc_rel tpc w.
Proof.
rewrite /cmapW.
case Hside: (Pointer.component tpc
             \in domm (Intermediate.prog_procedures pra)).
- case Hseg: (Transitional.intermediate_to_transitional_gen PI pra
                (Pointer.component tpc)) => [cseg|] //= [Epos] Hle Hw.
  apply: (@PCLeft _ _ cseg).
  + exact: Hside.
  + exact: Hseg.
  + exact: Hle.
  + by rewrite Hw Epos.
- case Hseg: (Transitional.intermediate_to_transitional_gen PI prb
                (Pointer.component tpc)) => [cseg|] //= [Epos] Hle Hw.
  apply: (@PCRight _ _ cseg).
  + by rewrite Hside.
  + exact: Hseg.
  + exact: Hle.
  + by rewrite Hw Epos.
Qed.

End MatchDef.

(** * The T-keyed position layer: re-keys [MPos.v]'s fetch chain by
    [tpos c cseg q] (component base + expanded size of the first [q] T cells)
    down to the encoded memory (the T pc is a (component, array-offset) pair),
    plus the label-resolution bridges keyed the same way. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.
Require Import MicroPolicies.Recomposition.OffsetWord.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.

Require Import T2M.MPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ================================================================== *)
(* 1. The T-keyed flat position.                                      *)
(* ================================================================== *)

(* flat position (within one side's [compiler_gen]) of the [q]-th T cell
   of component [c], whose array is [cseg] *)
Definition tpos (PI : Program.interface) (pr : Intermediate.program)
    (c : Component.id)
    (cseg : seq (Transitional.instr * mem_tag)) (q : nat) : nat :=
  comp_base (intermediate_to_transitional_gen PI pr) c
  + tseg_size (take q cseg).

Lemma tseg_take_lt (cseg : seq (Transitional.instr * mem_tag)) q x k :
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  tseg_size (take q cseg) + k < tseg_size cseg.
Proof.
move=> Hq Hk.
have Hm : List.nth_error [seq texp_size y.1 | y <- cseg] q
          = Some (texp_size x.1).
{ exact: (map_nth_error_seq (fun y => texp_size y.1) Hq). }
have Hle := sumn_take_le Hm.
have He : tseg_size (take q cseg)
          = sumn (take q [seq texp_size y.1 | y <- cseg]).
{ by rewrite /tseg_size map_take. }
rewrite /tseg_size in He Hle *.
by lia.
Qed.

(* ================================================================== *)
(* 2. Per-side: T cell ↦ merged cells, through gen and code.          *)
(* ================================================================== *)

Section TKeyed.

Variables L P C : nat.
Variable pr : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Let can_msz := memory_lengths PB.

Lemma compiler_gen_tnth (c : Component.id) cseg q x k :
  intermediate_to_transitional_gen PI pr c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error (compiler_gen pr (can_make L P C) (can_upd L) PB PI)
                 (tpos PI pr c cseg q + k)
  = List.nth_error (cell_exp (can_make L P C) (can_upd L) can_msz x) k.
Proof.
move=> Hc Hq Hk.
have Hlt := tseg_take_lt Hq Hk.
have Hseg := compiler_gen_seg (can_make L P C) (can_upd L)
               (erefl (memory_lengths PB))
               Hc Hlt.
rewrite /tpos -addnA Hseg.
exact: (t2m_flat_nth _ _ _ Hq Hk).
Qed.

Lemma compiler_code_tnth (c : Component.id) cseg q x k :
  intermediate_to_transitional_gen PI pr c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error (compiler_code L P C PB PI pr) (tpos PI pr c cseg q + k)
  = List.nth_error (cell_exp (can_make L P C) (can_upd L) can_msz x) k.
Proof.
move=> Hc Hq Hk.
have Hg := compiler_gen_tnth Hc Hq Hk.
have Hg' : List.nth_error (compiler_body L P C PB PI pr) (tpos PI pr c cseg q + k)
           = List.nth_error
               (cell_exp (can_make L P C) (can_upd L) can_msz x) k
  by exact: Hg.
have Hcs : exists cell,
    List.nth_error (cell_exp (can_make L P C) (can_upd L) can_msz x) k
    = Some cell.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. exact: Hk. }
case: Hcs => cell Hcell.
rewrite /compiler_code.
case E: (compiler_body L P C PB PI pr) => [|hd rest].
- exfalso.
  rewrite E Hcell in Hg'.
  by case: (tpos PI pr c cseg q + k) Hg'.
- rewrite E in Hg'.
  rewrite -cats1 nth_error_cat1; first exact: Hg'.
  rewrite Hcell in Hg'.
  exact: (nth_error_size Hg').
Qed.

End TKeyed.

(* ================================================================== *)
(* 3. Across the link, down to the encoded me memory.                 *)
(* ================================================================== *)

Section TLinked.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Let msz_a := memory_lengths PB.
Let msz_b := memory_lengths PB.

Let codeW := compiler_code L P C PB PI pra ++ compiler_code L P C PB PI prb.

Lemma link_tnth_l (c : Component.id) cseg q x k :
  intermediate_to_transitional_gen PI pra c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error codeW (tpos PI pra c cseg q + k)
  = List.nth_error (cell_exp (can_make L P C) (can_upd L) msz_a x) k.
Proof.
move=> Hc Hq Hk.
have Hn := compiler_code_tnth L P C PB Hc Hq Hk.
have Hcs : exists cell,
    List.nth_error (cell_exp (can_make L P C) (can_upd L) msz_a x) k
    = Some cell.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. exact: Hk. }
case: Hcs => cell Hcell.
rewrite /codeW nth_error_cat1; first exact: Hn.
apply: (@nth_error_size _ _ _ cell).
by rewrite Hn.
Qed.

Lemma link_tnth_r (c : Component.id) cseg q x k :
  intermediate_to_transitional_gen PI prb c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error codeW
    (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + k))
  = List.nth_error (cell_exp (can_make L P C) (can_upd L) msz_b x) k.
Proof.
move=> Hc Hq Hk.
have Hn := compiler_code_tnth L P C PB Hc Hq Hk.
by rewrite /codeW nth_error_cat2.
Qed.

(* the me-machine fetch, LEFT side: at address pc0 + tpos + k the encoded
   memory holds the k-th expansion cell's tag, and decodes to its
   instruction with labels resolved by [code_label_pos codeW pc0] *)
Lemma link_tfetch_l (c : Component.id) cseg q x k
    (pc0 : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  intermediate_to_transitional_gen PI pra c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error (cell_exp (can_make L P C) (can_upd L) msz_a x) k
  = Some cell ->
  exists v : matom,
    encode_code codeW pc0 (word_of_nat ((tpos PI pra c cseg q + k) + pc0))
    = Some v
    /\ taga v = cell.2
    /\ Types.decode_instr (vala v)
       = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                 (pc0 + (tpos PI pra c cseg q + k))).
Proof.
move=> Hbound Hc Hq Hk Hcell.
have Hnth : List.nth_error codeW (tpos PI pra c cseg q + k) = Some cell.
{ by rewrite (link_tnth_l Hc Hq Hk). }
case: cell Hnth Hcell => mi tg Hnth Hcell.
have [v [Hv [Htag Hval]]] := encode_code_fetch Hbound Hnth.
exists v.
split; first exact: Hv.
split; first exact: Htag.
rewrite Hval /encode_instr_mp.
by rewrite encodeK.
Qed.

Lemma link_tfetch_r (c : Component.id) cseg q x k
    (pc0 : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  intermediate_to_transitional_gen PI prb c = Some cseg ->
  List.nth_error cseg q = Some x ->
  k < texp_size x.1 ->
  List.nth_error (cell_exp (can_make L P C) (can_upd L) msz_b x) k
  = Some cell ->
  exists v : matom,
    encode_code codeW pc0
      (word_of_nat ((size (compiler_code L P C PB PI pra)
                     + (tpos PI prb c cseg q + k)) + pc0))
    = Some v
    /\ taga v = cell.2
    /\ Types.decode_instr (vala v)
       = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                 (pc0 + (size (compiler_code L P C PB PI pra)
                         + (tpos PI prb c cseg q + k)))).
Proof.
move=> Hbound Hc Hq Hk Hcell.
have Hnth : List.nth_error codeW
              (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + k))
            = Some cell.
{ by rewrite (link_tnth_r Hc Hq Hk). }
case: cell Hnth Hcell => mi tg Hnth Hcell.
have [v [Hv [Htag Hval]]] := encode_code_fetch Hbound Hnth.
exists v.
split; first exact: Hv.
split; first exact: Htag.
rewrite Hval /encode_instr_mp.
by rewrite encodeK.
Qed.

End TLinked.

(* ================================================================== *)
(* 4. Label resolution keyed by the T-array position of the defining  *)
(*    [TrLabel] cell.  Mirrors MPos's Link{Body,Entry} sections but   *)
(*    takes the T-side fact ("the label cell sits at array offset q") *)
(*    instead of Intermediate procedure coordinates.                  *)
(* ================================================================== *)

Section TLabelBridges.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.

Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).

Let codeW := compiler_code L P C PB PI pra ++ compiler_code L P C PB PI prb.

Let Hdisj' : fdisjoint (domm (Intermediate.prog_procedures prb))
                       (domm (Intermediate.prog_procedures pra)).
Proof. by rewrite fdisjointC. Qed.

(* ---- BODY label defined on the LEFT ---- *)

Section TBodyLeft.

Variables (c : Component.id) (l : nat).
Variable cseg : seq (Transitional.instr * mem_tag).
Variables (q : nat) (xt : mem_tag).
Hypothesis Hc : intermediate_to_transitional_gen PI pra c = Some cseg.
Hypothesis Hq : List.nth_error cseg q = Some (TrLabel (inl l), xt).
Hypothesis Hcol : color xt = c.
Hypothesis HlL : l < L.
Hypothesis Huniq_a : forall Cprocs0,
  Intermediate.prog_procedures pra c = Some Cprocs0 ->
  sumn [seq count (ilab l) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.

Let lab := mk_body L c l.

Let Hina : c \in domm (Intermediate.prog_procedures pra).
Proof.
move: Hc; rewrite i2t_getm.
by case E: (Intermediate.prog_procedures pra c) => [?|] //= _;
   rewrite mem_domm E.
Qed.

Let HcC : c < C.
Proof. exact: Hcomp_a Hina. Qed.

Let Hcb : c \notin domm (Intermediate.prog_procedures prb).
Proof. exact: (fdisjointP Hdisj _ Hina). Qed.

Lemma tlink_count_body_l : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := count_body_compiler_code P PB PI Hlab_a HcC HlL Huniq_a.
have Hb := count_body_compiler_code_absent P PB PI HcC HlL Hlab_b Hcb.
rewrite /lab; by lia.
Qed.

Lemma tlink_body_nth_l :
  List.nth_error codeW (tpos PI pra c cseg q + 0)
  = Some (MrLabel (can_upd L c l), xt).
Proof.
have Hk : 0 < texp_size (TrLabel (inl l) : Transitional.instr) by [].
have Hn := link_tnth_l L P C prb PB Hc Hq Hk.
by rewrite Hn /cell_exp /= Hcol.
Qed.

Lemma tlink_body_findopt_l :
  findopt (is_label_def lab) codeW = Some (tpos PI pra c cseg q + 0).
Proof.
apply: (findopt_unique_pos tlink_count_body_l tlink_body_nth_l).
by rewrite /is_label_def /= /lab /can_upd eqxx.
Qed.

Lemma tlink_label_pos_body_l (pc0 default : nat) :
  code_label_pos codeW pc0 lab default = pc0 + (tpos PI pra c cseg q + 0).
Proof. by rewrite /code_label_pos tlink_body_findopt_l. Qed.

End TBodyLeft.

(* ---- BODY label defined on the RIGHT ---- *)

Section TBodyRight.

Variables (c : Component.id) (l : nat).
Variable cseg : seq (Transitional.instr * mem_tag).
Variables (q : nat) (xt : mem_tag).
Hypothesis Hc : intermediate_to_transitional_gen PI prb c = Some cseg.
Hypothesis Hq : List.nth_error cseg q = Some (TrLabel (inl l), xt).
Hypothesis Hcol : color xt = c.
Hypothesis HlL : l < L.
Hypothesis Huniq_b : forall Cprocs0,
  Intermediate.prog_procedures prb c = Some Cprocs0 ->
  sumn [seq count (ilab l) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.

Let lab := mk_body L c l.

Let Hinb : c \in domm (Intermediate.prog_procedures prb).
Proof.
move: Hc; rewrite i2t_getm.
by case E: (Intermediate.prog_procedures prb c) => [?|] //= _;
   rewrite mem_domm E.
Qed.

Let HcC : c < C.
Proof. exact: Hcomp_b Hinb. Qed.

Let Hca : c \notin domm (Intermediate.prog_procedures pra).
Proof. exact: (fdisjointP Hdisj' _ Hinb). Qed.

Lemma tlink_count_body_r : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := count_body_compiler_code_absent P PB PI HcC HlL Hlab_a Hca.
have Hb := count_body_compiler_code P PB PI Hlab_b HcC HlL Huniq_b.
rewrite /lab; by lia.
Qed.

Lemma tlink_body_nth_r :
  List.nth_error codeW
    (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0))
  = Some (MrLabel (can_upd L c l), xt).
Proof.
have Hk : 0 < texp_size (TrLabel (inl l) : Transitional.instr) by [].
have Hn := link_tnth_r L P C pra PB Hc Hq Hk.
by rewrite Hn /cell_exp /= Hcol.
Qed.

Lemma tlink_body_findopt_r :
  findopt (is_label_def lab) codeW
  = Some (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0)).
Proof.
apply: (findopt_unique_pos tlink_count_body_r tlink_body_nth_r).
by rewrite /is_label_def /= /lab /can_upd eqxx.
Qed.

Lemma tlink_label_pos_body_r (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0)).
Proof. by rewrite /code_label_pos tlink_body_findopt_r. Qed.

End TBodyRight.

(* ---- ENTRY label defined on the LEFT ---- *)

Section TEntryLeft.

Variables (c : Component.id) (p : Procedure.id).
Variable cseg : seq (Transitional.instr * mem_tag).
Variables (q : nat) (xt : mem_tag).
Hypothesis Hc : intermediate_to_transitional_gen PI pra c = Some cseg.
Hypothesis Hq : List.nth_error cseg q = Some (TrLabel (inr (c, p)), xt).
Hypothesis HpP : p < P.

Let lab := mk_entry L P C c p.

Let Hina : c \in domm (Intermediate.prog_procedures pra).
Proof.
move: Hc; rewrite i2t_getm.
by case E: (Intermediate.prog_procedures pra c) => [?|] //= _;
   rewrite mem_domm E.
Qed.

Let Hcb : c \notin domm (Intermediate.prog_procedures prb).
Proof. exact: (fdisjointP Hdisj _ Hina). Qed.

Lemma tlink_count_entry_l : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := count_entry_compiler_code PB PI Hlab_a Hproc_a Hcomp_a c HpP.
have Hb := count_entry_compiler_code_absent PB PI Hlab_b Hproc_b Hcomp_b HpP Hcb.
rewrite /lab; by lia.
Qed.

Lemma tlink_entry_nth_l :
  List.nth_error codeW (tpos PI pra c cseg q + 0)
  = Some (MrLabel (can_make L P C (c, p)), xt).
Proof.
have Hk : 0 < texp_size (TrLabel (inr (c, p)) : Transitional.instr) by [].
have Hn := link_tnth_l L P C prb PB Hc Hq Hk.
by rewrite Hn /cell_exp /=.
Qed.

Lemma tlink_entry_findopt_l :
  findopt (is_label_def lab) codeW = Some (tpos PI pra c cseg q + 0).
Proof.
apply: (findopt_unique_pos tlink_count_entry_l tlink_entry_nth_l).
by rewrite /is_label_def /= /lab /can_make /= eqxx.
Qed.

Lemma tlink_label_pos_entry_l (pc0 default : nat) :
  code_label_pos codeW pc0 lab default = pc0 + (tpos PI pra c cseg q + 0).
Proof. by rewrite /code_label_pos tlink_entry_findopt_l. Qed.

End TEntryLeft.

(* ---- ENTRY label defined on the RIGHT ---- *)

Section TEntryRight.

Variables (c : Component.id) (p : Procedure.id).
Variable cseg : seq (Transitional.instr * mem_tag).
Variables (q : nat) (xt : mem_tag).
Hypothesis Hc : intermediate_to_transitional_gen PI prb c = Some cseg.
Hypothesis Hq : List.nth_error cseg q = Some (TrLabel (inr (c, p)), xt).
Hypothesis HpP : p < P.

Let lab := mk_entry L P C c p.

Let Hinb : c \in domm (Intermediate.prog_procedures prb).
Proof.
move: Hc; rewrite i2t_getm.
by case E: (Intermediate.prog_procedures prb c) => [?|] //= _;
   rewrite mem_domm E.
Qed.

Let Hca : c \notin domm (Intermediate.prog_procedures pra).
Proof. exact: (fdisjointP Hdisj' _ Hinb). Qed.

Lemma tlink_count_entry_r : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := count_entry_compiler_code_absent PB PI Hlab_a Hproc_a Hcomp_a HpP Hca.
have Hb := count_entry_compiler_code PB PI Hlab_b Hproc_b Hcomp_b c HpP.
rewrite /lab; by lia.
Qed.

Lemma tlink_entry_nth_r :
  List.nth_error codeW
    (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0))
  = Some (MrLabel (can_make L P C (c, p)), xt).
Proof.
have Hk : 0 < texp_size (TrLabel (inr (c, p)) : Transitional.instr) by [].
have Hn := link_tnth_r L P C pra PB Hc Hq Hk.
by rewrite Hn /cell_exp /=.
Qed.

Lemma tlink_entry_findopt_r :
  findopt (is_label_def lab) codeW
  = Some (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0)).
Proof.
apply: (findopt_unique_pos tlink_count_entry_r tlink_entry_nth_r).
by rewrite /is_label_def /= /lab /can_make /= eqxx.
Qed.

Lemma tlink_label_pos_entry_r (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (size (compiler_code L P C PB PI pra) + (tpos PI prb c cseg q + 0)).
Proof. by rewrite /code_label_pos tlink_entry_findopt_r. Qed.

End TEntryRight.

End TLabelBridges.

(* ================================================================== *)
(* 5. Word arithmetic for Bnz/Jal targets.  [mt] is opaque, so the    *)
(*    immediate-width bounds are carried as premises, discharged at    *)
(*    instantiation from [link_fits].                                  *)
(* ================================================================== *)

(* a small immediate survives the unsigned imm->word cast *)
Lemma swcast_word_of_nat_small (x : nat) :
  x < 2 ^ imm_size mt ->
  @swcast _ (word_size mt) (@word_of_nat (imm_size mt) x)
  = @word_of_nat (word_size mt) x.
Proof.
move=> Hx.
by rewrite /swcast /word_of_nat (as_wordK Hx).
Qed.


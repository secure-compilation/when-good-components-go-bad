Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Layout.
Require Import Backtranslation_ME_MP_Wf.
Require Import Backtranslation_ME_MP_Pkg.

Notation minstr := (@Merged.instr mt).

Lemma size_load N r tmp : size (rp_load N r tmp) = if N < rp_small then 1 else 17.
Proof. rewrite /rp_load. by case: ifP. Qed.

Lemma size_load_mono N1 N2 r tmp : N1 <= N2 -> size (rp_load N1 r tmp) <= size (rp_load N2 r tmp).
Proof.
move=> HN. rewrite !size_load.
case: ifP => H1; case: ifP => H2 //.
exfalso. move: H1 => /negbT. rewrite -leqNgt => H1.
have := leq_ltn_trans (leq_trans H1 HN) H2. by rewrite ltnn.
Qed.

Lemma size_init_mono L t1 s cid A j :
  size (rp_init L t1 cid A j) <= size (rp_init L (t1 ++ s) cid A j).
Proof.
rewrite /rp_init !size_cat leq_add2l leq_add2r. apply: size_load_mono.
by rewrite /rp_blocks size_cat leq_add2r leq_addr.
Qed.

Lemma size_disp_mono L cid A n1 n2 :
  n1 <= n2 -> size (rp_disp L cid A n1) <= size (rp_disp L cid A n2).
Proof.
move=> Hn. rewrite /rp_disp !size_cat leq_add2l leq_add2r.
rewrite -(subnKC Hn) iotaD map_cat flatten_cat size_cat. exact: leq_addr.
Qed.

Lemma size_flat_mono (A T : Type) (f g : A -> seq T) (s : seq A) :
  (forall x, size (f x) <= size (g x)) ->
  size (flatten (map f s)) <= size (flatten (map g s)).
Proof.
move=> H. elim: s => [//|x s IH] /=. rewrite !size_cat. exact: leq_add (H x) IH.
Qed.

Section Mono.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}).

Lemma rp_events_cat t1 s X : rp_events (t1 ++ s) X = rp_events t1 X ++ rp_events s X.
Proof. by rewrite /rp_events filter_cat. Qed.

Lemma size_cc_mono t1 s X :
  size (rp_comp_code L P C PI PB t1 X) <= size (rp_comp_code L P C PI PB (t1 ++ s) X).
Proof.
have E3 : forall a b c : @Merged.code mt, size (a ++ b ++ c) = size a + (size b + size c).
{ move=> a b c. by rewrite !size_cat. }
rewrite /rp_comp_code !E3.
apply: leq_add.
{ case: (X == Component.main); last exact: leqnn.
  rewrite !size_tagged [size (rp_init _ _ _ _ _ ++ _)]size_cat
          [size (rp_init _ _ _ _ _ ++ _)]size_cat leq_add2r.
  exact: size_init_mono. }
rewrite leq_add2l !size_tagged.
have Ecs : forall x (l : seq minstr), size (x :: l) = (size l).+1 by [].
rewrite [size (MrLabel _ :: _)]Ecs [size (MrLabel _ :: _)]Ecs ltnS.
rewrite [size (rp_init _ _ _ _ _ ++ _)]size_cat [size (rp_init _ _ _ _ _ ++ _)]size_cat.
apply: leq_add; first exact: size_init_mono.
rewrite [size (rp_push ++ _)]size_cat [size (rp_push ++ _)]size_cat leq_add2l.
rewrite [size (rp_goto _ _ _ ++ _)]size_cat [size (rp_goto _ _ _ ++ _)]size_cat leq_add2l.
rewrite [size (rp_disp _ _ _ _ ++ _)]size_cat [size (rp_disp _ _ _ _ ++ _)]size_cat.
rewrite rp_events_cat [size (rp_events _ _ ++ _)]size_cat.
apply: leq_add; first exact: size_disp_mono (leq_addr _ _).
rewrite [size (flatten _ ++ _)]size_cat [size (flatten _ ++ _)]size_cat leq_add2r.
rewrite iotaD zip_cat ?size_iota // map_cat flatten_cat size_cat.
exact: leq_addr.
Qed.

Lemma size_code_mono t1 s (I : Program.interface) (B : NMap {fmap Block.id -> nat + seq value}) :
  size (code (rp_program L P C PI PB t1 I B)) <= size (code (rp_program L P C PI PB (t1 ++ s) I B)).
Proof. apply: size_flat_mono => X. exact: size_cc_mono. Qed.

End Mono.

Section Fits.

Variables (L P C : nat) (p c : program).

Local Notation Ip := (prog_interface p).
Local Notation Ic := (prog_interface c).
Local Notation PI := (unionm Ip Ic).
Local Notation PB := (unionm (prog_buffers p) (prog_buffers c)).

Definition bt_fits (t : trace) : Prop :=
  [/\ forall X, (X \in domm Ip) || (X \in domm Ic) -> 4 + size (rp_events t X) <= L,
      (size t).+4 < 2 ^ 14,
      size (linearize_bufs (unionm (prog_buffers (rp_program L P C PI PB t Ip (prog_buffers p)))
                                   (prog_buffers (rp_program L P C PI PB t Ic (prog_buffers c)))))
        + size (code (rp_program L P C PI PB t Ip (prog_buffers p))
                ++ code (rp_program L P C PI PB t Ic (prog_buffers c))) < alloc_label
    & size (linearize_bufs (unionm (prog_buffers p)
                                   (prog_buffers (rp_program L P C PI PB t Ic (prog_buffers c)))))
        + size (code p ++ code (rp_program L P C PI PB t Ic (prog_buffers c))) < alloc_label].

Lemma bt_fits_prefix t1 t2 : trace_prefix t1 t2 -> bt_fits t2 -> bt_fits t1.
Proof.
case=> s ->. case=> H1 H2 H3 H4.
have Es : t1 ** s = t1 ++ s by [].
rewrite Es in H1 H2 H3 H4.
split.
- move=> X HX. apply: leq_trans (H1 X HX). by rewrite rp_events_cat size_cat leq_add2l leq_addr.
- apply: leq_ltn_trans _ H2. by rewrite size_cat !ltnS leq_addr.
- apply: leq_ltn_trans _ H3. rewrite leq_add2l !size_cat.
  apply: leq_add; exact: size_code_mono.
- apply: leq_ltn_trans _ H4. rewrite leq_add2l !size_cat leq_add2l.
  exact: size_code_mono.
Qed.

End Fits.

Module BT_ME (Lft : MEtoMP_Left) <: H_bt_me Lft.

  Definition bt_fits := bt_fits Lft.L Lft.P Lft.C Lft.p Lft.c.

  Lemma bt_fits_prefix : forall t1 t2, trace_prefix t1 t2 -> bt_fits t2 -> bt_fits t1.
  Proof. exact: bt_fits_prefix. Qed.

  Definition back (m0 : finpref_behavior)
      (Hdp : does_prefix (rub_sem Lft.NC (prog_interface Lft.p) (prog_interface Lft.c)
                            (program_link Lft.p Lft.c)) m0)
      (Hnw : not_wrong_finpref m0)
      (Hf : bt_fits (finpref_trace m0)) :
      bt_me_package Lft.L Lft.P Lft.C Lft.NC Lft.p Lft.c m0 :=
    let '(And4 Hfl Hft Hfc Hfc2) := Hf in
    bt_pack Lft.Hwfmp_p Lft.Hwfmp_c Lft.Hmergeable Lft.Hclosed Lft.comps_bounded
            Lft.NC_lt_word Lft.alloc_label_lt_word_NC Lft.memory_size_pc Hdp Hnw
            Hfl Hft Hfc Hfc2.

End BT_ME.

(* Phase 5, tier 3a (part 4): initial-state discharge for trace
   well-formedness.

   [star_well_formed_trace] (TraceBracket.v) needs two facts about the run's
   initial state: its memory's entry tags are sanctioned by the interface
   ([entry_sound]) and it realizes the empty call stack ([bracket_inv
   stack_state0]).  This file proves both:
     - generically, for [Merged.initial_state cde pb pi] under syntactic
       conditions on the code's tags (no Ret value-tags; interface-sound
       entry tags) — buffer cells and [reg0] are unconditionally benign;
     - concretely, for the linked linearizer output
       [program_link (compiler a) (compiler b)], via LinearizeMerged's
       cell characterization (every cell is a [head_tag] entry cell or a
       [def_mem_tag] body cell).

   The [encode_code]/[initial_memory] inversion lemmas are reproduced from
   RecompositionInit.v (functor-internal there), on top of the functor-free
   EncodeCode.v (re-added to the build). *)

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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Intermediate.Machine.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import Common.Traces.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.
Import Symbolic.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

(* ==================== initial-memory tag shapes (copies) ==================== *)

Lemma linearize_buf_tag: forall (pb : NMap {fmap Block.id -> nat + seq value}) c b n vt,
  List.nth_error (linearize_buf pb c b) n = Some vt ->
  snd vt = def_mem_tag c false.
Proof.
  intros pb c0 b n vt.
  unfold linearize_buf.
  destruct (getm pb c0) as [map |] eqn:Hc; simpl; [| destruct n; discriminate].
  destruct (getm map b) as [block |] eqn:Hb; simpl; [| destruct n; discriminate].
  destruct block as [sz | vals].
  - move=> Hnth.
    have := List.nth_error_In _ _ Hnth.
    intros H. eapply List.repeat_spec in H. subst. simpl. reflexivity.
  - move=> Hnth.
    have := List.nth_error_In _ _ Hnth.
    rewrite List.in_map_iff. move=> [x [<- _]]. reflexivity.
Qed.

Lemma linearize_bufs_tag: forall (pb : NMap {fmap Block.id -> nat + seq value}) k val_tag,
  linearize_bufs pb k = Some val_tag ->
  exists c, snd val_tag = def_mem_tag c false.
Proof.
  intros pb k val_tag.
  unfold linearize_bufs.
  intros H. apply mapk_Some in H.
  destruct H as [k0 [? Hk0]].
  move: Hk0. rewrite uncurrymE mapmE.
  destruct k0 as [k1 k2].
  simpl.
  destruct (mapim (fun c map =>
    mapim (fun b _ => fmap_of_seq (linearize_buf pb c b)) map) pb k1)
    as [inner_map |] eqn:Hinner; simpl; [| try discriminate].
  - rewrite mapimE in Hinner.
    destruct k2 as [k2 k3]. subst k.
    destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in Hinner; [| try discriminate].
    + rewrite Hpb in Hinner. simpl in Hinner.
      inversion Hinner. simpl in *.
      rewrite mapimE. rewrite Hpb. simpl. rewrite H0.
      rewrite uncurrymE. simpl.
      rewrite <- H0.
      destruct (mapim (fun b _ => fmap_of_seq (linearize_buf pb k1 b)) pb_map k2)
        as [inner2 |] eqn:Hinner2; simpl; [| try discriminate].
      * rewrite mapimE in Hinner2.
        destruct (pb_map k2) as [block |] eqn:Hblock; simpl in Hinner2; [| discriminate].
        inversion Hinner2. rewrite mapimE. rewrite Hblock. simpl.
        rewrite fmap_of_seqE.
        intros G.
        exists k1.
        eapply nth_map_Some_nth_error in G.
        apply linearize_buf_tag in G. eauto.
      * simpl in *. rewrite mapimE in Hinner2.
        rewrite mapimE.
        destruct (pb_map k2) as [block |]; simpl in *; try congruence.
    + simpl in *.
      rewrite mapimE. rewrite Hpb. simpl. congruence.
  - simpl in *.
    rewrite mapimE. rewrite mapimE in Hinner.
    destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in *.
    rewrite Hpb in Hinner; simpl in Hinner; try congruence.
    rewrite Hpb. simpl. congruence.
Qed.

Lemma initial_memory_tag: forall (pb : NMap {fmap Block.id -> nat + seq value}) w v,
  @initial_memory mt pb w = Some v ->
  exists c, taga v = def_mem_tag c false.
Proof.
  intros pb w v Hmem.
  unfold initial_memory in Hmem.
  apply mapk_Some in Hmem. destruct Hmem as [k [_ Hmem]].
  rewrite mapmE in Hmem.
  destruct (linearize_bufs pb k) as [val_tag |] eqn:Hbufs; simpl in Hmem; [| discriminate].
  injection Hmem => <-. simpl.
  exact (linearize_bufs_tag Hbufs).
Qed.

Lemma encode_code_foldr_tag: forall (cde : @Merged.code mt) lp offset n v,
  List.nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 n = Some v ->
  exists i t, List.In (i, t) cde /\ taga v = t.
Proof.
  intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset n v Hnth.
  - simpl in Hnth. destruct n; discriminate.
  - simpl in Hnth.
    set acc := (foldr _ _ cde') in Hnth.
    destruct n as [| n'].
    + simpl in Hnth. injection Hnth => <-.
      exists i0, t0. split.
      * left. reflexivity.
      * unfold encode_instr_atom. simpl. reflexivity.
    + simpl in Hnth.
      destruct (IH lp offset n' v Hnth) as [i' [t' [Hin' Htag']]].
      exists i', t'. split.
      * right. exact Hin'.
      * exact Htag'.
Qed.

Lemma encode_code_tag: forall (cde : @Merged.code mt) pc0 w v,
  encode_code cde pc0 w = Some v ->
  exists i t,
    List.In (i, t) cde /\
    taga v = t.
Proof.
  intros cde pc0 w v Henc.
  unfold encode_code in Henc.
  apply mapk_Some in Henc. destruct Henc as [k [_ Hk]].
  rewrite fmap_of_seqE in Hk.
  apply nth_map_Some_nth_error in Hk.
  destruct (encode_code_foldr_tag Hk) as [i [t [Hin Htag]]].
  exists i, t. split; [exact Hin | exact Htag].
Qed.

(* ==================== the initial register file ==================== *)

Lemma reg0_no_caps : forall (r0 : reg mt) v n,
  Merged.reg0 r0 = Some (v @ (Ret n)) -> False.
Proof.
  move=> r0 v n. rewrite /Merged.reg0 mkfmapE /=.
  do 12 (case: ifP => [_|_]; first by move=> [= _ Hc]).
  by [].
Qed.

Lemma reg0_domm : forall (r0 : reg mt), r0 \in domm Merged.reg0 ->
  (r0 == ra) || (r0 \in [seq (as_word (ssrint.Posz n) : reg mt) | n <- reg_list]).
Proof.
  move=> r0. rewrite mem_domm /Merged.reg0 mkfmapE /=.
  do 12 (case: ifP => [/eqP -> _|_]; first by vm_compute).
  by [].
Qed.

(* ==================== generic initial-state facts ==================== *)

Section InitGeneric.

  Variables (cde : @Merged.code mt) (pb : NMap {fmap Block.id -> nat + seq value}) (pi : Program.interface).

  Let s0 := Merged.initial_state cde pb pi.

  Lemma initial_mem_shape :
    mem s0 = unionm (encode_code cde (size (@initial_memory mt pb)))
                    (@initial_memory mt pb).
  Proof. by []. Qed.

  Lemma initial_regs_shape : regs s0 = Merged.reg0.
  Proof. by []. Qed.

  Lemma initial_pc_tag : taga (pc s0) = build_tpc 0 Component.main.
  Proof. by []. Qed.

  (* every cell of the initial memory: from the code (with its listed tag)
     or a buffer cell (def_mem_tag) *)
  Lemma initial_cell_inv : forall w d,
    mem s0 w = Some d ->
    (exists i t, List.In (i, t) cde /\ taga d = t)
    \/ (exists c, taga d = def_mem_tag c false).
  Proof.
    move=> w d. rewrite initial_mem_shape unionmE.
    case E: (encode_code cde (size (@initial_memory mt pb)) w) => [d0|] /=.
    - move=> [= <-]. left. exact: (encode_code_tag E).
    - move=> Hbuf. right. exact: (initial_memory_tag Hbuf).
  Qed.

  Lemma initial_entry_sound : forall intf,
    (forall i t p lc c, List.In (i, t) cde -> entry t = Some (p, lc) ->
       c \in lc -> imported_procedure_b intf c (color t) p) ->
    entry_sound intf (mem s0).
  Proof.
    move=> intf Hcde w iv tn p lc c Hw Hent Hc.
    case: (initial_cell_inv Hw) => [[i [t [Hin Htag]]] | [c0 Htag]].
    - move: Htag => /= Htag. subst t.
      exact: (Hcde _ _ _ _ _ Hin Hent Hc).
    - move: Htag => /= Htag. by rewrite Htag /= in Hent.
  Qed.

  Lemma initial_bracket_inv :
    (forall i t, List.In (i, t) cde -> forall n, vtag t <> Ret n) ->
    bracket_inv stack_state0 s0.
  Proof.
    move=> Hnoret. exists [::]. split.
    - by rewrite initial_pc_tag.
    - by [].
    - by move=> e; rewrite in_nil.
    - move=> v n p Hp. exfalso.
      case: p Hp => [r0|w] Hp.
      + exact: (reg0_no_caps Hp).
      + case: Hp => t [Hw Hvt].
        case: (initial_cell_inv Hw) => [[i [t' [Hin Htag]]] | [c0 Htag]].
        * move: Htag => /= Htag. subst t'.
          exact: (Hnoret _ _ Hin n Hvt).
        * move: Htag => /= Htag. by rewrite Htag /= in Hvt.
    - move=> r0 Hd. apply: reg0_domm. exact: Hd.
  Qed.

End InitGeneric.

(* ==================== rub-run glue ==================== *)

(* every step of the UB-restricted semantics contains a machine step *)
Lemma rub_step_mp : forall (NCv : nat) pI cI (W : program) s t s',
  Step (rub_sem NCv pI cI W) s t s' -> prog_step_mp NCv tt s t s'.
Proof. move=> NCv pI cI W s t s' Hstep. by inversion Hstep. Qed.

Lemma rub_star_mp : forall (NCv : nat) pI cI (W : program) s tw s',
  Star (rub_sem NCv pI cI W) s tw s' -> Star (mp_sem NCv W) s tw s'.
Proof.
  move=> NCv pI cI W s tw s' Hstar.
  elim: Hstar => [s0|s1 t1 s2 t2 s3 tw0 Hstep Hstar IH Etw].
  - exact: star_refl.
  - eapply star_step; [exact: (rub_step_mp Hstep) | exact: IH | exact: Etw].
Qed.

(* ==================== discharge for linked linearizer output ==================== *)

Section LinDischarge.

  Variables (L0 P0 C0 : nat) (a b : Intermediate.program).
  Hypothesis Hwa : Intermediate.well_formed_program a.
  Hypothesis Hwb : Intermediate.well_formed_program b.
  Hypothesis Hdisj : fdisjoint (domm (Intermediate.prog_interface a))
                               (domm (Intermediate.prog_interface b)).

  Let PBW := unionm (Intermediate.prog_buffers a) (Intermediate.prog_buffers b).
  Let intf := unionm (Intermediate.prog_interface a)
                     (Intermediate.prog_interface b).
  Let W := program_link (compiler L0 P0 C0 PBW intf a)
                        (compiler L0 P0 C0 PBW intf b).

  Lemma lin_link_cell : forall i t,
    List.In (i, t) (code W) ->
    List.In (i, t) (compiler_code L0 P0 C0 PBW intf a)
    \/ List.In (i, t) (compiler_code L0 P0 C0 PBW intf b).
  Proof. move=> i t HIn. exact: (List.in_app_or _ _ _ HIn). Qed.

  Lemma lin_link_noret : forall i t,
    List.In (i, t) (code W) -> forall n, vtag t <> Ret n.
  Proof.
    move=> i t /lin_link_cell [HIn|HIn] n;
      by have [_ Hv] := lin_low_tags HIn; rewrite Hv.
  Qed.

  (* a head_tag entry list only sanctions importers declared in the
     (now JOINT, §3.8) interface it was computed against *)
  Lemma head_tag_entry_sound : forall (PI : Program.interface) c0 p0 p lc c,
    entry (head_tag_gen PI c0 p0) = Some (p, lc) ->
    c \in lc ->
    exists i', getm PI c = Some i'
          /\ (c0, p) \in Component.import i'
          /\ c \in domm PI.
  Proof.
    move=> PI c0 p0 p lc c. rewrite /head_tag_gen /=.
    move=> [= Ep Elc]. subst p0.
    rewrite -Elc mem_filter => /andP [Hallow HcI].
    move: Hallow.
    case E1: (getm PI c0) => [i1|] //=.
    case E2: (getm PI c) => [i2|] //=.
    move=> /andP [Hexp Himp].
    exists i2. split; first by [].
    split; first exact: Himp.
    exact: HcI.
  Qed.

  Lemma lin_link_entry_sound : forall i t p lc c,
    List.In (i, t) (code W) -> entry t = Some (p, lc) -> c \in lc ->
    imported_procedure_b intf c (color t) p.
  Proof.
    move=> i t p lc c /lin_link_cell [HIn|HIn] Hent Hc;
      have Ht := lin_entry_head HIn Hent;
      rewrite Ht in Hent;
      have [i' [Hgi [Himp HcI]]] := head_tag_entry_sound Hent Hc;
      rewrite /imported_procedure_b Hgi /=;
      exact: Himp.
  Qed.

  (* THE initial-state trace well-formedness theorem for linked linearizer
     output: any machine run from the loaded initial state has a
     well-formed trace for the link interface. *)
  Theorem lin_link_initial_trace_wf : forall (NCv : nat) (s : state) tw (s' : state),
    s = Merged.initial_state (code W) (prog_buffers W) (prog_interface W) ->
    Star (mp_sem NCv W) s tw s' ->
    well_formed_trace intf tw.
  Proof.
    move=> NCv s tw s' Hs Hstar.
    apply: (star_well_formed_trace Hstar).
    - rewrite Hs. apply: initial_entry_sound.
      move=> i t p lc c. exact: lin_link_entry_sound.
    - rewrite Hs. apply: initial_bracket_inv.
      move=> i t Hin n. exact: (lin_link_noret Hin).
  Qed.

  (* the same, for runs of the UB-restricted semantics (any interface split) *)
  Corollary lin_link_rub_trace_wf : forall (NCv : nat) pI cI (s : state) tw (s' : state),
    s = Merged.initial_state (code W) (prog_buffers W) (prog_interface W) ->
    Star (rub_sem NCv pI cI W) s tw s' ->
    well_formed_trace intf tw.
  Proof.
    move=> NCv pI cI s tw s' Hs Hstar.
    exact: (lin_link_initial_trace_wf Hs (rub_star_mp Hstar)).
  Qed.

End LinDischarge.

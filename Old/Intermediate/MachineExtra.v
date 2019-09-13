Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.
Require Import Lib.Extra.
Require Intermediate.Machine.
Import Machine.Intermediate.

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Intermediate.

Module Register.

  Let get  := Machine.Intermediate.Register.get.
  Let init := Machine.Intermediate.Register.init.

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.

End Register.

Theorem linkability_disjoint_procedures :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2
    [_ Hdisjoint_interface].
  inversion Hwell_formed1 as [_ Hwell_formed_procs1 _ _ _ _].
  inversion Hwell_formed2 as [_ Hwell_formed_procs2 _ _ _ _].
  by rewrite -Hwell_formed_procs1 -Hwell_formed_procs2.
Qed.

Theorem linkability_disjoint_buffers :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2 [_ Hdisjoint_interface].
  inversion Hwell_formed1 as [_ _ _ _ Hwell_formed_buffers1 _].
  inversion Hwell_formed2 as [_ _ _ _ Hwell_formed_buffers2 _].
  by rewrite -Hwell_formed_buffers1 -Hwell_formed_buffers2.
Qed.

(*
Theorem linkability_disjoint_mains :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    linkable_mains (prog_main prog1) (prog_main prog2).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2 [Hsound_interface Hdisjoint_interface].
  inversion Hwell_formed1 as [_ _ _ _ _ Hmain_existence1].
  inversion Hwell_formed2 as [_ _ _ _ _ Hmain_existence2].
  (* All cases except one, which leads to contradiction, are trivial. *)
  unfold linkable_mains.
  destruct (prog_main prog1) as [(cid1, pid1) |];
    destruct (prog_main prog2) as [(cid2, pid2) |];
    try (apply I; fail).
  (* The interesting case remains. *)
  specialize (Hmain_existence1 cid1 pid1).
  specialize (Hmain_existence2 cid2 pid2).
  (* RB: Short story, there is a main in prog_procedures for each prog1 and
     prog2, which are however disjoint, and main is unique (may need to
     shuffle things a bit). *)
  admit.
*)

(* RB: NOTE: Does this properly belong in machine? *)
Definition partialize_program (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_interface p);
     prog_procedures :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_procedures p);
     prog_buffers :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_buffers p);
     prog_main := prog_main p |}.

Definition empty_prog := {| prog_interface := emptym;
                            prog_procedures := emptym;
                            prog_buffers := emptym;
                            prog_main := None |}.

Theorem empty_interface_implies_empty_program:
  forall p,
    well_formed_program p ->
    prog_interface p = emptym ->
    p = empty_prog.
Proof.
  move=> [intf procs bufs main] [/= _ e_procs _ _ e_bufs Hmain _] e_intf.
  subst intf; congr mkProg.
  - apply/eq_fmap=> ?; rewrite emptymE; apply/dommPn.
    by rewrite -e_procs mem_domm emptymE.
  - apply/eq_fmap=> ?; rewrite emptymE; apply/dommPn.
    by rewrite -e_bufs mem_domm emptymE.
  - case e: main Hmain=> [mainP|] //= /(_ _ erefl) [main_procs].
    by move/eqP: e_procs; rewrite domm0 eq_sym => /emptymP -> [].
Qed.

Lemma empty_prog_is_well_formed:
  well_formed_program empty_prog.
Proof.
  constructor; try by [].
  - by rewrite domm0.
Qed.

Theorem linking_empty_program:
  forall p,
    program_link p empty_prog = p.
Proof.
  intros p.
  destruct p. unfold program_link. simpl.
  repeat rewrite unionm0.
  by case: prog_main0.
Qed.

Lemma linkable_mains_empty_prog:
  forall p,
    linkable_mains p empty_prog.
Proof.
  intros p.
  destruct p. unfold linkable_mains.
  now rewrite andb_comm.
Qed.

Lemma prog_main_link_none_left: forall p1 p2,
  prog_main (program_link p1 p2) = None ->
  prog_main p1 = None.
Proof.
  intros p1 p2 Hprog_main.
  unfold program_link in Hprog_main. simpl in Hprog_main.
  destruct (prog_main p1);
    destruct (prog_main p2);
    easy.
Qed.

Lemma prog_main_link_none_right: forall p1 p2,
  prog_main (program_link p1 p2) = None ->
  prog_main p2 = None.
Proof.
  intros p1 p2 Hprog_main.
  unfold program_link in Hprog_main. simpl in Hprog_main.
  destruct (prog_main p1);
    destruct (prog_main p2);
    easy.
Qed.

(* initialization of the empty program *)

Lemma prepare_procedures_initial_memory_aux_empty_program:
  prepare_procedures_initial_memory_aux empty_prog = emptym.
Proof.
  unfold prepare_procedures_initial_memory_aux.
  rewrite domm0.
  reflexivity.
Qed.

Theorem prepare_procedures_empty_program:
  prepare_procedures empty_prog emptym = (emptym, emptym, emptym).
Proof.
  unfold prepare_procedures.
  reflexivity.
Qed.

Theorem prepare_initial_memory_empty_program:
  prepare_initial_memory empty_prog = emptym.
Proof.
  unfold prepare_initial_memory.
  simpl. rewrite domm0.
  reflexivity.
Qed.

Theorem prepare_procedures_initial_memory_empty_program:
  prepare_procedures_initial_memory empty_prog = (emptym, emptym, emptym).
Proof.
  unfold prepare_procedures_initial_memory.
  rewrite prepare_procedures_initial_memory_aux_empty_program.
  rewrite !mapm_empty.
  reflexivity.
Qed.

(* The following two lemmas are quick conveniences for the proper
   result of the partition lemma that follows.*)
Lemma prog_buffers_in_domm :
  forall p Cid,
    well_formed_program p ->
    Cid \in domm (prog_interface p) ->
  exists bufs,
    (prog_buffers p) Cid = Some bufs.
Proof.
  intros p Cid [_ _ _ _ Hbufs _] Hin.
  apply /dommP.
  congruence.
Qed.

Lemma prog_buffers_notin_domm :
  forall p Cid,
    well_formed_program p ->
    Cid \notin domm (prog_interface p) ->
    (prog_buffers p) Cid = None.
Proof.
  intros p Cid [_ _ _ _ Hbufs _] Hin.
  apply /dommPn.
  congruence.
Qed.

(* TODO: Refactor proof (easy). Inline or relocate auxiliary lemmas. *)
Lemma alloc_static_buffers_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    alloc_static_buffers (program_link p c)
                         (domm (prog_interface (program_link p c))) =
    unionm (alloc_static_buffers p (domm (prog_interface p)))
           (alloc_static_buffers c (domm (prog_interface c))).
Proof.
  intros p c Hwfp Hwfc [Hsound Hdisjoint].
  unfold alloc_static_buffers.
  rewrite <- eq_fmap. (* Operate from extensional equality. *)
  unfold eqfun. simpl. intros Cid.
  rewrite !(mkfmapfE, unionmE).
  destruct (Cid \in domm (prog_interface p)) eqn:Hintp;
    destruct (Cid \in domm (prog_interface c)) eqn:Hintc.
  - (* Contra.
       However, note this case works out with the current definition. *)
    pose proof prog_buffers_in_domm Hwfp Hintp as [bufsp Hbufsp].
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - pose proof prog_buffers_in_domm Hwfp Hintp as [bufsp Hbufsp].
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - apply negb_true_iff in Hintp.
    pose proof prog_buffers_notin_domm Hwfp Hintp as Hbufsp.
    apply negb_true_iff in Hintp.
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - (* Trivial case. *)
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite Hintp.
    rewrite mem_domm in Hintc. rewrite Hintc.
    reflexivity.
Qed.

Theorem prepare_initial_memory_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_initial_memory (program_link p c) =
    unionm (prepare_initial_memory p) (prepare_initial_memory c).
Proof.
  intros p c Hwf1 Hwf2 Hlinkable.
  unfold prepare_initial_memory.
  apply alloc_static_buffers_after_linking; auto.
Qed.

Remark prepare_procedures_initial_memory_decompose:
  forall p,
    prepare_procedures_initial_memory p =
    (prepare_procedures_memory p,
     prepare_procedures_procs p,
     prepare_procedures_entrypoints p).
Proof.
  reflexivity.
Qed.

(* A more lightweight variation on the above lemma.
   RB: NOTE: is_true_true replaces eq_refl on specializations, as eqtype is
   imported. *)
Lemma interface_preserves_closedness_r' :
  forall p1 p2 p2',
    well_formed_program p1 ->
    well_formed_program p2 ->
    closed_program (program_link p1 p2) ->
    linkable (prog_interface p1) (prog_interface p2) ->
    linkable_mains p1 p2 ->
    well_formed_program p2' ->
    prog_interface p2 = prog_interface p2' ->
    closed_program (program_link p1 p2').
Proof.
  intros p c c' Hwfp Hwfc Hclosed Hlinkable Hmains Hwfc' Hifaces.
  apply interface_preserves_closedness_r with (p2 := c);
    try assumption.
  - (* RB: TODO: Extract lemma from here. The stronger relation between
       interfaces and main procedures essentially renders matching_mains
       superfluous, trivially derivable. *)
    inversion Hwfc as [_ _ _ _ _ _ [Hmainc Hmainc']].
    inversion Hwfc' as [_ _ _ _ _ _ [Hmainc1 Hmainc1']].
    rewrite <- Hifaces in Hmainc1, Hmainc1'.
    destruct (Component.main \in domm (prog_interface c)) eqn:Hcase1.
    + specialize (Hmainc is_true_true). specialize (Hmainc1 is_true_true).
      unfold matching_mains.
      destruct (prog_main c) as [mainc |] eqn:Hcase2;
        destruct (prog_main c') as [mainc' |] eqn:Hcase3;
        done.
    + destruct (prog_main c) as [mainc |] eqn:Hcase2.
      * now specialize (Hmainc' is_true_true).
      * destruct (prog_main c') as [mainc' |] eqn:Hcase3;
          last done.
        now specialize (Hmainc1' is_true_true).
Qed.

Lemma closed_program_link_sym p1 p2 :
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p1) (prog_interface p2) ->
  closed_program (program_link p1 p2) = closed_program (program_link p2 p1).
Proof.
  intros Hwf1 Hwf2 Hlinkable.
  rewrite (program_linkC Hwf1 Hwf2 Hlinkable).
  reflexivity.
Qed.

Remark prog_main_none_same_interface :
  forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    prog_interface p1 = prog_interface p2 ->
    prog_main p1 = None ->
    prog_main p2 = None.
Proof.
  intros p1 p2 Hwf1 Hwf2 Hiface Hnone.
  inversion Hwf1 as [_ _ _ _ _ _ [Hmain1 Hmain1']].
  inversion Hwf2 as [_ _ _ _ _ _ [Hmain2 Hmain2']].
  destruct p1 as [iface1 procs1 bufs1 main1];
    destruct p2 as [iface2 procs2 bufs2 main2];
    simpl in *.
  destruct main2 as [main2P |] eqn:Hcase1;
    last reflexivity.
  subst.
  specialize (Hmain1 (Hmain2' isT)).
  discriminate.
Qed.

End Intermediate.

Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

From mathcomp Require Import ssreflect ssrfun seq.

Set Bullet Behavior "Strict Subproofs".

Record global_env := mkGlobalEnv {
  genv_interface: Program.interface;
  genv_procedures: NMap (NMap code);
  genv_entrypoints: EntryPoint.t;
}.

Definition executing G (pc : Pointer.t) (i : instr) : Prop :=
  exists C_procs P_code,
    getm (genv_procedures G) (Pointer.component pc) = Some C_procs /\
    getm C_procs (Pointer.block pc) = Some P_code /\
    (Pointer.offset pc >= 0) % Z /\
    nth_error P_code (Z.to_nat (Pointer.offset pc)) = Some i.

Definition prepare_global_env (p: program) : global_env :=
  let '(_, procs, entrypoints) := prepare_procedures_initial_memory p in
  {| genv_interface := prog_interface p;
     genv_procedures := procs;
     genv_entrypoints := entrypoints |}.

Definition empty_global_env := {|
  genv_interface := emptym;
  genv_procedures := emptym;
  genv_entrypoints := emptym
|}.

Lemma prepare_global_env_empty_prog:
  prepare_global_env empty_prog = empty_global_env.
Proof.
  unfold prepare_global_env.
  rewrite prepare_procedures_initial_memory_empty_program.
  reflexivity.
Qed.

(* global environments are computational and pure: deterministic.
   what else do I need? some kind of per-component isolation stated
   in a way that's easy to reuse *)
Lemma domm_genv_procedures : forall p,
  domm (genv_procedures (prepare_global_env p)) = domm (prog_interface p).
Proof.
  intros p.
  unfold genv_procedures, prepare_global_env.
  rewrite Extra.domm_map. (* RB: Should be domm_mapm! *)
  rewrite domm_prepare_procedures_initial_memory_aux.
  reflexivity.
Qed.

Lemma domm_genv_entrypoints : forall p,
  domm (genv_entrypoints (prepare_global_env p)) = domm (prog_interface p).
Proof.
  intros p.
  unfold genv_procedures, prepare_global_env.
  rewrite Extra.domm_map domm_prepare_procedures_initial_memory_aux.
  reflexivity.
Qed.

Definition global_env_union (genv1 genv2 : global_env) : global_env := {|
  genv_interface   := unionm (genv_interface   genv1) (genv_interface   genv2);
  genv_procedures  := unionm (genv_procedures  genv1) (genv_procedures  genv2);
  genv_entrypoints := unionm (genv_entrypoints genv1) (genv_entrypoints genv2)
|}.

Lemma prepare_global_env_link : forall {p c},
  well_formed_program p ->
  well_formed_program c ->
  linkable (prog_interface p) (prog_interface c) ->
  linkable_mains p c ->
  prepare_global_env (program_link p c) =
  global_env_union (prepare_global_env p) (prepare_global_env c).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hmains.
  unfold prepare_global_env, prepare_procedures_initial_memory.
  rewrite (prepare_procedures_initial_memory_aux_after_linking
           Hwfp Hwfc Hlinkable Hmains).
  unfold global_env_union. simpl.
  rewrite !mapm_unionm.
  reflexivity.
Qed.

(* RB: NOTE: This kind of lemma is usually the composition of two unions, one
   of which is generally extant. Compare with "after_linking" lemmas. *)
Lemma imported_procedure_recombination {p c c' Cid C P} :
  Cid \notin domm (prog_interface c) ->
  imported_procedure (genv_interface (prepare_global_env (program_link p c ))) Cid C P ->
  imported_procedure (genv_interface (prepare_global_env (program_link p c'))) Cid C P.
Proof.
  intros Hdomm Himp.
  rewrite (imported_procedure_unionm_left Hdomm) in Himp.
  destruct Himp as [CI [Hcomp Himp]]. exists CI. split; [| assumption].
  unfold Program.has_component. rewrite unionmE. now rewrite Hcomp.
Qed.

Lemma genv_procedures_program_link_left_notin :
  forall {c Cid},
    Cid \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros c Cid Hnotin p Hwfp Hwfc Hlinkable Hmains.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) Cid = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  setoid_rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) Cid) eqn:Hcase;
    by setoid_rewrite Hcase.
Qed.

Lemma genv_procedures_program_link_left_in :
  forall {p Cid},
    Cid \in domm (prog_interface p) ->
  forall {c},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros p Cid Hin c Hwfp Hwfc Hlinkable Hmains.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert
    (exists procs, (genv_procedures (prepare_global_env p)) Cid = Some procs)
    as [procs Hprocs]
    by (apply /dommP; rewrite domm_genv_procedures; assumption).
  setoid_rewrite Hprocs.
  assumption.
Qed.

Lemma genv_entrypoints_program_link_left :
  forall {c C},
    C \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
  forall {P},
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c))) =
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)).
Proof.
  intros c C Hnotin p Hwfp Hwfc Hlinkable Hmains P.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold EntryPoint.get, global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_entrypoints (prepare_global_env c)) C = None)
    by (apply /dommPn; rewrite domm_genv_entrypoints; done).
  rewrite HNone.
  destruct ((genv_entrypoints (prepare_global_env p)) C) eqn:Hcase;
    by rewrite Hcase.
Qed.

  Lemma genv_entrypoints_interface_some p p' C P b pc :
    (* Pointer.component pc \in domm (prog_interface p) -> *)
    (* imported_procedure (genv_interface (globalenv sem')) (Pointer.component pc) C P -> *)
    Pointer.component pc <> C ->
    imported_procedure (genv_interface (prepare_global_env p')) (Pointer.component pc) C P ->
    well_formed_program p ->
    well_formed_program p' ->
    closed_program p ->
    closed_program p' ->
    prog_interface p = prog_interface p' ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p )) = Some b ->
  exists b',
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'.
  Proof.
    move=> Hpc Himported Hwf Hwf' Hclosed Hclosed' Hiface.

    destruct Hclosed' as [? _].
    unfold closed_interface in cprog_closed_interface0.
    apply cprog_closed_interface0 in Himported.
    unfold exported_procedure in Himported.
    destruct Himported as [CI [H1 H2]].
    assert (H4 := H2).
    apply wfprog_exported_procedures_existence with (C := C) (p := p) in H2.
    destruct H2 as [Cprocs [Pcode [H2 H3]]].
    apply wfprog_exported_procedures_existence with (C := C) (p := p') in H4.
    destruct H4 as [Cprocs' [Pcode' [H2' H3']]].

    (* destruct Himported as [[exp imp] [Himp1 Himp2]]. *)
    (* destruct pc as [[cid bid] off]. *)
    (* simpl in *. *)
    (* unfold Component.is_importing in Himp2. simpl in Himp2. *)
    (* unfold Program.has_component in Himp1. *)
    (* pose proof (has_component_in_domm_prog_interface Himp1) as Hhas_comp. *)
    (* assert (prog_interface p cid = prog_interface p' cid) by congruence. *)
    (* rewrite Himp1 in H. *)

    unfold EntryPoint.get, prepare_global_env, genv_entrypoints; simpl.
    (* move=> H; exists b; rewrite -H; clear H. *)
    unfold prepare_procedures_initial_memory_aux.
    unfold elementsm, odflt, oapp.
    rewrite 2!mapmE.
    unfold omap, obind, oapp; simpl.
    rewrite 2!mkfmapfE.
    rewrite -Hiface.
    destruct (C \in domm (prog_interface p)) eqn:HC.
    - rewrite HC.
      assert (HC': (C \in domm (prog_interface p')) = true) by now rewrite -Hiface.
      inversion Hwf as [_ Hproc _ _ Hbuf _ _].
      inversion Hwf' as [_ Hproc' _ _ Hbuf' _ _].
      assert (Heq1: prog_buffers p C <-> prog_buffers p' C).
      {
        rewrite -2!mem_domm.
        now rewrite -Hbuf Hiface Hbuf'.
      }
      destruct (prog_buffers p C) eqn:H8.
      + assert (H1': prog_buffers p' C) by now apply Heq1.
        destruct (prog_buffers p' C) eqn:H8''; try now auto.
        rewrite H2. rewrite H2'. simpl.
          move=> Hreserve.
          apply /dommP.
          unfold reserve_component_blocks in Hreserve.
          erewrite reserve_component_blocks_lemma with (p' := p); eauto.
          apply /dommP. eexists; eauto.
      + assert (H1': prog_buffers p' C = None).
        {
          destruct (prog_buffers p' C); simpl in *.
          clear -Heq1 H1.
          inversion Heq1; try (exfalso; firstorder).
          eauto.
        }
        rewrite H1'; simpl in *.
        assert (Heq2: prog_procedures p C <-> prog_procedures p' C).
        {
          rewrite -2!mem_domm.
          now rewrite -Hproc Hiface Hproc'.
        }
        destruct (prog_procedures p C) eqn:H2.
        * assert (H2': prog_procedures p' C) by now apply Heq2.
          destruct (prog_procedures p' C); try now auto.
          simpl in *.
          move=> Hreserve.
          apply /dommP.
          erewrite reserve_component_blocks_lemma with (p' := p); eauto.
          apply /dommP. eexists; eauto.
        * move=> ?. by [].
    - now rewrite HC.
  Qed.

(* (* RB: NOTE: Add program well-formedness if needed. *) *)
(* Lemma genv_entrypoints_interface_some p p' C P b (* pc *) : *)
(*   (* Pointer.component pc \in domm (prog_interface p) -> *) *)
(*   (* imported_procedure (genv_interface (globalenv sem')) (Pointer.component pc) C P -> *) *)
(*   prog_interface p = prog_interface p' -> *)
(*   EntryPoint.get C P (genv_entrypoints (prepare_global_env p )) = Some b -> *)
(* exists b', *)
(*   EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'. *)
(* Proof. *)
(*   move=> Hiface. *)
(*   unfold EntryPoint.get, prepare_global_env, genv_entrypoints; simpl. *)
(*   (* move=> H; exists b; rewrite -H; clear H. *) *)
(*   unfold prepare_procedures_initial_memory_aux. *)
(*   unfold elementsm, odflt, oapp. *)
(*   rewrite 2!mapmE. *)
(*   unfold omap, obind, oapp; simpl. *)
(*   rewrite 2!mkfmapfE. *)
(*   rewrite -Hiface. *)
(*   destruct (C \in domm (prog_interface p)) eqn:HC. *)
(*   - rewrite HC. *)
(*     admit. *)
(*   - now rewrite HC. *)
(* Admitted. *)

(* RB: NOTE: The two EntryPoint lemmas can be phrased as a more general one
   operating on an explicit program link, one then being the exact symmetric of
   the other, i.e., its application after communativity of linking. There is a
   choice of encoding of component membership in both cases. *)

(* RB: TODO: Rephrase goal as simple equality? *)
(* Search _ EntryPoint.get. *)
Lemma genv_entrypoints_recombination_left :
  forall p c c',
    well_formed_program p ->
    well_formed_program c ->
    well_formed_program c' ->
    mergeable_interfaces (prog_interface p) (prog_interface c) ->
    prog_interface c = prog_interface c' ->
  forall C P b,
    C \in domm (prog_interface p) ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c ))) = Some b ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c'))) = Some b.
Proof.
  intros p c c' Hwfp Hwfc Hwfc' Hmergeable_ifaces Hifacec C P b Hdomm Hentry.
  pose proof proj1 Hmergeable_ifaces as Hlinkable.
  eapply (domm_partition_notin _ _ (mergeable_interfaces_sym _ _ Hmergeable_ifaces)) in Hdomm.
  rewrite genv_entrypoints_program_link_left in Hentry; try assumption;
    [| now apply linkable_implies_linkable_mains].
  rewrite Hifacec in Hlinkable, Hdomm.
  rewrite genv_entrypoints_program_link_left; try assumption.
  now apply linkable_implies_linkable_mains.
Qed.

Lemma genv_entrypoints_recombination_right :
  forall p c p' c',
    well_formed_program p ->
    well_formed_program p' ->
    well_formed_program c' ->
    mergeable_interfaces (prog_interface p) (prog_interface c) ->
    prog_interface p = prog_interface p' ->
    prog_interface c = prog_interface c' ->
  forall C P b,
    C \in domm (prog_interface c) ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p' c'))) = Some b ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p  c'))) = Some b.
Proof.
  intros p c p' c' Hwfp Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec C P b Hdomm Hentry.
  pose proof proj1 Hmergeable_ifaces as Hlinkable.
  rewrite program_linkC in Hentry; try congruence.
  rewrite program_linkC; try congruence.
  eapply genv_entrypoints_recombination_left with (c := p'); try assumption; try congruence.
  rewrite -Hifacec -Hifacep. now apply mergeable_interfaces_sym.
Qed.

Fixpoint find_label (c : code) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | ILabel l' :: c' =>
        if Nat.eqb l l' then
          Some o
        else
          aux c' (1 + o)%Z
      | _ :: c' =>
        aux c' (1 + o)%Z
      end
  in aux c 0%Z.

Definition find_label_in_procedure G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    match getm C_procs (Pointer.block pc) with
    | Some P_code =>
      match find_label P_code l with
      | Some offset => Some (Pointer.component pc, Pointer.block pc, offset)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Fixpoint find_label_in_component_helper
         G (procs: list (Block.id * code))
         (pc: Pointer.t) (l: label) : option Pointer.t :=
  match procs with
  | [] => None
  | (p_block,p_code) :: procs' =>
    match find_label_in_procedure G (Pointer.component pc, p_block, 0%Z) l with
    | None => find_label_in_component_helper G procs' pc l
    | Some ptr => Some ptr
    end
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    find_label_in_component_helper G (elementsm C_procs) pc l
  | None => None
  end.

Lemma find_label_in_procedure_guarantees:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc' /\
    Pointer.block pc = Pointer.block pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_procedure in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  destruct (getm procs (Pointer.block pc)) as [code|];
    try discriminate.
  destruct (find_label code l) as [offset|];
    try discriminate.
  destruct pc'. destruct p.
  inversion Hfind. subst.
  split; reflexivity.
Qed.

Lemma find_label_in_procedure_1:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_2:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.block pc = Pointer.block pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
  forall {l},
    find_label_in_procedure (prepare_global_env (program_link p c)) pc l =
    find_label_in_procedure (prepare_global_env p) pc l.
Proof.
  (* RB: Note the proof strategy for all these lemmas is remarkably similar.
     It may be worthwhile to refactor it and/or its intermediate steps. *)
  intros c pc Hnotin p Hwfp Hwfc Hlinkable Hmains l.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold find_label_in_procedure, global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) (Pointer.component pc) = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc)) eqn:Hcase;
    by rewrite Hcase.
Qed.

Lemma find_label_in_component_helper_guarantees:
  forall G procs pc pc' l,
    find_label_in_component_helper G procs pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G procs pc pc' l Hfind.
  induction procs.
  - discriminate.
  - simpl in *.
    destruct a.
    destruct (find_label_in_procedure
                G (Pointer.component pc, i, 0%Z) l)
             eqn:Hfind'.
    + apply find_label_in_procedure_1 in Hfind'.
      simpl in *. inversion Hfind. subst. auto.
    + apply IHprocs; auto.
Qed.

Lemma find_label_in_component_1:
  forall G pc pc' l,
    find_label_in_component G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_component in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  eapply find_label_in_component_helper_guarantees in Hfind; auto.
Qed.

Lemma find_label_in_component_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
  forall {l},
    find_label_in_component (prepare_global_env (program_link p c)) pc l =
    find_label_in_component (prepare_global_env p) pc l.
Proof.
  intros c pc Hnotin p Hwfp Hwfc Hlinkable Hmains l.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
  unfold find_label_in_component. unfold global_env_union at 1. simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) (Pointer.component pc) = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc))
    as [procs |] eqn:Hcase;
    rewrite Hcase.
  - simpl.
    (* Inlined is the corresponding lemma on find_label_in_component_helper. *)
    induction (elementsm procs) as [| [p_block code] elts IHelts];
      first reflexivity.
    unfold find_label_in_component_helper; simpl.
    assert (Hnotin' : Pointer.component (Pointer.component pc, p_block, 0%Z)
                      \notin domm (prog_interface c)).
      by done.
    rewrite <- (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
    rewrite (find_label_in_procedure_program_link_left Hnotin' Hwfp Hwfc Hlinkable Hmains).
    fold find_label_in_component_helper.
    rewrite <- IHelts.
    rewrite <- (prepare_global_env_link Hwfp Hwfc Hlinkable Hmains).
    reflexivity.
  - reflexivity.
Qed.

(* RB: Unified presentation of linkable + linkable_mains, to be used as needed
   around the development? *)
Lemma execution_invariant_to_linking:
  forall p c1 c2 pc instr,
    linkable (prog_interface p) (prog_interface c1) ->
    linkable (prog_interface p) (prog_interface c2) ->
    linkable_mains p c1 ->
    linkable_mains p c2 ->
    well_formed_program p ->
    well_formed_program c1 ->
    well_formed_program c2 ->
    Pointer.component pc \in domm (prog_interface p) ->
    executing (prepare_global_env (program_link p c1)) pc instr ->
    executing (prepare_global_env (program_link p c2)) pc instr.
Proof.
  intros p c1 c2 pc instr Hlinkable1 Hlinkable2 Hmains1 Hmains2 Hwf Hwf1 Hwf2 Hpc Hexec.
  inversion Hexec as [procs [proc [Hgenv_procs [Hprocs_proc [Hoffset Hproc_instr]]]]].
  exists procs, proc.
  split; [| split; [| split]];
    [| assumption | assumption | assumption].
  assert (Pointer.component pc \notin domm (prog_interface c1)) as Hcc1.
  {
    inversion Hlinkable1 as [_ Hdisjoint]. apply /fdisjointP. apply Hdisjoint. assumption.
  }
  assert (Pointer.component pc \notin domm (prog_interface c2)) as Hcc2.
  {
    inversion Hlinkable2 as [_ Hdisjoint]. apply /fdisjointP. apply Hdisjoint. assumption.
  }
  rewrite (genv_procedures_program_link_left_notin Hcc1 Hwf Hwf1 Hlinkable1 Hmains1) in Hgenv_procs.
  rewrite (genv_procedures_program_link_left_notin Hcc2 Hwf Hwf2 Hlinkable2 Hmains2).
  assumption.
Qed.

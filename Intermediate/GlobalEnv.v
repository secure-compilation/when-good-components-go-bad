Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

From mathcomp Require Import ssreflect ssrfun.

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

Lemma executing_deterministic:
  forall G pc i i',
    executing G pc i -> executing G pc i' -> i = i'.
Proof.
  unfold executing. intros G pc i i'
                           [C_procs [P_code [memCprocs [memPcode [offsetCond memi]]]]]
                           [C_procs' [P_code' [memCprocs' [memPcode' [offsetCond' memi']]]]].
  rewrite memCprocs in memCprocs'.
  inversion memCprocs'.
  subst C_procs.
  rewrite memPcode in memPcode'.
  inversion memPcode'.
  subst P_code.
  rewrite memi in memi'.
  inversion memi'.
  auto.
Qed.

Definition prepare_global_env (p: program) : global_env :=
  let '(_, procs, entrypoints) := prepare_procedures_initial_memory p in
  {| genv_interface := prog_interface p;
     genv_procedures := procs;
     genv_entrypoints := entrypoints |}.

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

(* RB: NOTE: Add program well-formedness if needed. *)
Lemma genv_entrypoints_interface_some p p' C P b (* pc *) :
  (* Pointer.component pc \in domm (prog_interface p) -> *)
  (* imported_procedure (genv_interface (globalenv sem')) (Pointer.component pc) C P -> *)
  well_formed_program p ->
  well_formed_program p' ->
  prog_interface p = prog_interface p' ->
  EntryPoint.get C P (genv_entrypoints (prepare_global_env p )) = Some b ->
exists b',
  EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'.
Proof.
  move=> Hwf Hwf' Hiface.
  unfold EntryPoint.get (*, prepare_global_env *) (*, genv_entrypoints *); simpl.
  (* move=> H; exists b; rewrite -H; clear H. *)
  unfold prepare_procedures_initial_memory_aux.
  unfold elementsm, odflt, oapp.
  rewrite 2!mapmE.
  unfold omap, obind, oapp; simpl.
  rewrite 2!mkfmapfE.
  rewrite -Hiface.
  destruct (C \in domm (prog_interface p)) eqn:HC.
  - rewrite HC.
    intro HSome.
    destruct ((prog_procedures p) C) as [procs |] eqn:Hcase1;
      last discriminate.
    assert (exists procs', (prog_procedures p') C = Some procs') as [procs' Hcase1'].
    { apply /dommP.
      rewrite -(wfprog_defined_procedures Hwf') -Hiface (wfprog_defined_procedures Hwf).
      apply /dommP. now exists procs. }
    (* JT: TODO: Clean up this step *)
    assert (Hbufs: prog_buffers p C <> None).
    { intros Hn.
      have: (exists procs, prog_procedures p C = Some procs) by (now exists procs).
      move=> /dommP[H].
      move: Hn => /dommPn[H'].
      move: H H'.
      rewrite -(wfprog_defined_buffers Hwf) -(wfprog_defined_procedures Hwf) => H1 H2.
      exfalso. move: H2 => /negP. by []. }
    destruct ((prog_buffers p) C) as [bufs |] eqn:Hcase2;
      last contradiction.
    assert (exists bufs', (prog_buffers p') C = Some bufs') as [bufs' Hcase2'].
    { apply /dommP.
      rewrite -(wfprog_defined_buffers Hwf') -Hiface (wfprog_defined_buffers Hwf).
      apply /dommP. now exists bufs. }
    rewrite -> Hcase1', Hcase2'.
    (* RB: NOTE: For now, phrase in terms of domains. *)
    assert (P \in domm (reserve_component_blocks p C (ComponentMemory.prealloc bufs) procs).2) as Hdomm.
    {
      apply /dommP. eauto. (* RB: TODO: Clean up this step. *)
    }
    apply /dommP.
    (* Continue to case analyze both machines in sync. *)
    unfold reserve_component_blocks. unfold reserve_component_blocks in Hdomm.
    destruct (ComponentMemoryExtra.reserve_blocks (ComponentMemory.prealloc bufs) (length procs))
      as [Cmem bs] eqn:Hblocks.
    destruct (ComponentMemoryExtra.reserve_blocks (ComponentMemory.prealloc bufs') (length procs'))
      as [Cmem' bs'] eqn:Hblocks'.
    rewrite domm_mkfmap. rewrite domm_mkfmap in Hdomm.
    rewrite <- Hiface.
    assert (Hmain : matching_mains p p') by now apply interface_implies_matching_mains.
    destruct (prog_main p) as [|] eqn:Hcase3;
      destruct (prog_main p') as [|] eqn:Hcase4.
    + match goal with
      | |- is_true (P \in seq.unzip1 (seq.pmap ?F ?L)) => remember F as fmap eqn:Hfmap
      end.
      simpl in Hfmap.
      rewrite -domm_mkfmap. rewrite -domm_mkfmap in Hdomm.
      remember (seq.zip (seq.unzip1 procs') bs') as l' eqn:Hl'.
      remember (seq.zip (seq.unzip1 procs) bs) as l eqn:Hl.
      destruct (prog_interface p C) as [iface |] eqn:Hiface_eq.
      * assert (Hin: forall l,
                   P \in domm (mkfmap (seq.pmap fmap l)) <->
                         (P \in Component.export iface \/ (P = 0 /\ C = 0)) /\ P \in domm (mkfmap l)).
        {
          clear -Hfmap.
          intros l; subst; split.
          - intros H; induction l.
            + move: H => /dommP [v Hv]; by [].
            + simpl in H; unfold oapp in H.
              destruct a as [P' b']; destruct (P' \in Component.export iface) eqn:HP';
                rewrite HP' in H; simpl in H.
              * move: H; rewrite domm_set => /fsetU1P.
                move=> [Heq | Hdomm]; subst.
                -- split; first now left.
                   rewrite domm_set; simpl.
                   apply /fsetU1P; now left.
                -- specialize (IHl Hdomm) as [IH1 IH2].
                   split; try assumption.
                   rewrite domm_set; apply /fsetU1P; now right.
              * destruct C eqn:HeqC; destruct P' eqn:HeqP'; simpl in *;
                  try (specialize (IHl H) as [IH1 IH2]; split; first assumption;
                       rewrite domm_set in_fsetU; apply /orP; now right).
                move: H; rewrite domm_set => /fsetU1P [Heq | Hdomm]; subst.
                -- split; first now right.
                   rewrite domm_set; simpl. apply /fsetU1P; now left.
                -- specialize (IHl Hdomm) as [IH1 IH2].
                   split; first assumption.
                   rewrite domm_set in_fsetU. apply /orP; now right.
          - move=> [H1 H2].
            induction l.
            + case: H2. by [].
            + simpl; unfold oapp.
              destruct a as [P' b']; destruct (P' \in Component.export iface) eqn:HP';
                rewrite HP'; simpl.
              * simpl in *.
                move: H2. rewrite domm_set in_fsetU => /orP. move => [H2 | H2].
                move: H2 => /fset1P Heq; subst.
                rewrite domm_set; apply /fsetU1P; now left.
                rewrite domm_set; apply /fsetU1P; right.
                now apply IHl.
              * destruct C eqn:HeqC; destruct P' eqn:HeqP'; simpl in *;
                  try (apply IHl;
                       move: H2; rewrite domm_set in_fsetU => /orP [H2 | H2]; last assumption;
                                                             move: H2; rewrite in_fset1; rewrite eqtype.eqE; simpl;
                                                             intros H; assert (Heq: P = S s) by (now apply /ssrnat.eqnP); subst P;
                                                             rewrite HP' in H1; destruct H1 as [? | [? ?]]; congruence).
                -- rewrite domm_set in_fsetU; apply /orP.
                   destruct P; first now left.
                   right. apply IHl.
                   move: H2; rewrite domm_set in_fsetU => /orP [H2 | H2]; last assumption.
                   inversion H2.
                -- apply IHl.
                   destruct P. destruct H1. rewrite HP' in H. congruence.
                   destruct H. congruence.
                   move: H2; rewrite domm_set in_fsetU => /orP [H2 | H2]; last assumption.
                   inversion H2.
        }
        apply Hin in Hdomm as [Hdomm1 Hdomm2].
        apply Hin; split; try assumption. simpl in *.
        (* now we are left to prove that domm (mkfmap l') ⊆ domm (mkfmap l) *)
        subst l l'.
        rewrite domm_map_zip_unzip_same_length_is_equal;
          last (symmetry; apply (ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Hblocks')).
        rewrite domm_map_zip_unzip_same_length_is_equal in Hdomm2;
          last (symmetry; apply (ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Hblocks)).
        
        (* Now we can conclude by well-formedness of p' *)
        clear -Hiface_eq Hdomm2 Hdomm1 Hiface Hcase1 Hcase1' Hwf Hwf'.
        assert (Hiface_eq': prog_interface p' C = Some iface) by now rewrite -Hiface.
        destruct Hdomm1 as [Hdomm1 | Hdomm1].
        -- assert (His_exporting': Component.is_exporting iface P) by assumption.
           pose proof wfprog_exported_procedures_existence Hwf' Hiface_eq' His_exporting'
             as [procs'' [? [? ?]]].
           assert (procs' = procs'') by congruence; subst procs''.
           apply /dommP. exists x.
           rewrite mkfmapE. assumption.
        -- destruct Hdomm1; subst.
           pose proof (wfprog_main_existence Hwf').
           destruct H as [main_procs [H1 H2]]. apply (wfprog_main_component Hwf').
           apply /dommP; exists iface; unfold Component.main; auto.
           unfold Component.main in *; unfold Procedure.main in *.
           assert (main_procs = procs') by congruence.
           subst; auto. rewrite domm_mkfmap.
           unfold domm in *. (* ... *)
           rewrite in_fset in H2. assumption.
      * assert (H: seq.pmap fmap l = []).
        {
          clear -Hfmap.
          subst.
          induction l. by [].
          rewrite //= /oapp; now destruct a.
        }
        rewrite H in Hdomm; clear -Hdomm; exfalso.
        move: Hdomm => //=. apply /negP.
        now rewrite domm0.
    + now rewrite -> (proj1 Hmain Hcase3) in Hcase4. (* Contra. *)
    + now rewrite -> (proj2 Hmain Hcase4) in Hcase3. (* Contra. *)
    + (* Finish synchronizing both runs. Refer to first case as needed. Since
         there are no main procedures, the complications of that case are
         avoided here. *)
      match goal with
      | |- is_true (P \in seq.unzip1 (seq.pmap ?F ?L)) => remember F as fmap eqn:Hfmap
      end.

      (* First attempt *)
      rewrite -domm_mkfmap. rewrite -domm_mkfmap in Hdomm.
      remember (seq.zip (seq.unzip1 procs') bs') as l' eqn:Hl'.
      remember (seq.zip (seq.unzip1 procs) bs) as l eqn:Hl.
      destruct (prog_interface p C) as [iface |] eqn:Hiface_eq.
      * (* this assert helps simplify the expression *)
        assert (Hin : forall l,
                   P \in domm (mkfmap (seq.pmap fmap l)) <->
                         (P \in Component.export iface /\ P \in domm (mkfmap l))).
        { clear -Hfmap.
          intros l.
          subst.
          split.
          - intros H.
            induction l.
            + move: H => /dommP [v Hv]; case: Hv. by [].
            + simpl in H; unfold oapp in H.
              destruct a as [P' b']; destruct (P' \in Component.export iface) eqn:HP';
                rewrite HP' in H; simpl in H.
              * move: H; rewrite domm_set => /fsetU1P.
                move=> [Heq | Hdomm]; subst.
                -- split; first assumption.
                   rewrite domm_set.
                   simpl; apply /fsetU1P; now left.
                -- specialize (IHl Hdomm) as [IH1 IH2].
                   split; try assumption.
                   rewrite domm_set; apply /fsetU1P; now right.
              * simpl in *.
                specialize (IHl H) as [IH1 IH2].
                split; first assumption.
                rewrite domm_set. rewrite in_fsetU.
                apply /orP. now right.
          - move=> [H1 H2].
            induction l.
            + case: H2. by [].
            + simpl; unfold oapp.
              destruct a as [P' b']; destruct (P' \in Component.export iface) eqn:HP';
                rewrite HP'; simpl.
              * simpl in *.
                move: H2. rewrite domm_set in_fsetU => /orP. move => [H2 | H2].
                move: H2 => /fset1P Heq; subst.
                rewrite domm_set; apply /fsetU1P; now left.
                rewrite domm_set; apply /fsetU1P; right.
                now apply IHl.
              * simpl in *.
                apply IHl.
                move: H2. rewrite domm_set in_fsetU => /orP. move=> [H2 | H3]; last assumption.
                move: H2; rewrite in_fset1.
                rewrite eqtype.eqE. simpl.
                intros H. assert (Heq: P = P') by now apply /ssrnat.eqnP.
                rewrite Heq in H1. rewrite HP' in H1. inversion H1.
        }
        apply Hin in Hdomm as [Hdomm1 Hdomm2].
        apply Hin; split; try assumption. simpl in *.
        (* now we are left to prove that domm (mkfmap l') ⊆ domm (mkfmap l) *)
        subst l l'.
        rewrite domm_map_zip_unzip_same_length_is_equal;
          last (symmetry; apply (ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Hblocks')).
        rewrite domm_map_zip_unzip_same_length_is_equal in Hdomm2;
          last (symmetry; apply (ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Hblocks)).

        (* Now we can conclude by well-formedness of p' *)
        clear -Hiface_eq Hdomm2 Hdomm1 Hiface Hcase1 Hcase1' Hwf Hwf'.
        assert (Hiface_eq': prog_interface p' C = Some iface) by now rewrite -Hiface.
        assert (His_exporting': Component.is_exporting iface P) by assumption.
        pose proof wfprog_exported_procedures_existence Hwf' Hiface_eq' His_exporting'
          as [procs'' [? [? ?]]].
        assert (procs' = procs'') by congruence; subst procs''.
        apply /dommP. exists x.
        rewrite mkfmapE. assumption.
      * assert (H: seq.pmap fmap l = []).
        {
          clear -Hfmap.
          subst.
          induction l. by [].
          rewrite //= /oapp; now destruct a.
        }
        rewrite H in Hdomm; clear -Hdomm; exfalso.
        move: Hdomm => //=. apply /negP.
        now rewrite domm0.
  - now rewrite HC.
Qed.

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
      | Some offset => Some (Pointer.permission pc,
                             Pointer.component pc, Pointer.block pc, offset)
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
    match find_label_in_procedure G (Pointer.permission pc,
                                     Pointer.component pc, p_block, 0%Z) l with
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
    Pointer.permission pc = Pointer.permission pc' /\
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
  destruct pc' as [[[pc'p pc'c] pc'b] pc'o].
  inversion Hfind. subst.
  split; auto; split; auto.
Qed.

Lemma find_label_in_procedure_1:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
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
                G (Pointer.permission pc, Pointer.component pc, i, 0%Z) l)
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
    assert (Hnotin' : Pointer.component
                        (Pointer.permission pc, Pointer.component pc, p_block, 0%Z)
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

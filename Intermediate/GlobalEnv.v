Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Common.Util.
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
    Pointer.permission pc = Permission.code /\
    nth_error P_code (Z.to_nat (Pointer.offset pc)) = Some i.

Lemma executing_deterministic:
  forall G pc i i',
    executing G pc i -> executing G pc i' -> i = i'.
Proof.
  unfold executing. intros G pc i i'
                           [C_procs [P_code [memCprocs [memPcode
                                                          [offsetCond
                                                             [permCond memi]]]]]]
                           [C_procs' [P_code' [memCprocs' [memPcode'
                                                             [offsetCond'
                                                                [permCond'
                                                                   memi']]]]]].
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

Lemma genv_procedures_prog_procedures_eq : forall p c x,
    well_formed_program p ->
    prog_procedures p c = Some x ->
    genv_procedures (prepare_global_env p) c =
    prog_procedures p c.
Proof.
  intros ? ? ? Hwf HSome.
  simpl. rewrite mapmE. unfold omap, obind, oapp.
  destruct (prepare_procedures_initial_memory_aux p c) as [someRes|] eqn:ec;
    rewrite ec; unfold prepare_procedures_initial_memory_aux in *;
      rewrite mkfmapfE in ec;
      destruct (c \in domm (prog_interface p)) eqn:ecintf; rewrite ecintf in ec;
        inversion ec; clear ec; simpl.
  - unfold odflt, oapp. by rewrite HSome.
  - assert (c \in domm (prog_interface p)).
    {
      rewrite wfprog_defined_procedures; auto. apply/dommP. by eauto.
    }
    congruence.
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
  prepare_global_env (program_link p c) =
  global_env_union (prepare_global_env p) (prepare_global_env c).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  unfold prepare_global_env, prepare_procedures_initial_memory.
  rewrite (prepare_procedures_initial_memory_aux_after_linking
           Hwfp Hwfc Hlinkable).
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
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Proof.
  intros c Cid Hnotin p Hwfp Hwfc Hlinkable.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) Cid = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  setoid_rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) Cid) eqn:Hcase;
    by setoid_rewrite Hcase.
Qed.

Lemma genv_procedures_program_link_right_in :
  forall {c Cid},
    Cid \in domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env c)) Cid.
Proof.
  intros c Cid Hnotin p Hwfp Hwfc Hlinkable.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable).
  unfold global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env p)) Cid = None).
  {
    apply/dommPn; rewrite domm_genv_procedures.
    destruct Hlinkable as [_ Hdisj].
    rewrite fdisjointC in Hdisj.
    move : Hdisj => /fdisjointP => Hdisj.
    apply Hdisj; by auto.
  }
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
  forall {P},
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c))) =
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)).
Proof.
  intros c C Hnotin p Hwfp Hwfc Hlinkable P.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable).
  unfold EntryPoint.get, global_env_union; simpl.
  rewrite unionmE.
  assert (HNone : (genv_entrypoints (prepare_global_env c)) C = None)
    by (apply /dommPn; rewrite domm_genv_entrypoints; done).
  rewrite HNone.
  destruct ((genv_entrypoints (prepare_global_env p)) C) eqn:Hcase;
    by rewrite Hcase.
Qed.

Lemma genv_entrypoints_interface_some p p' C P b :
  well_formed_program p ->
  well_formed_program p' ->
  prog_interface p = prog_interface p' ->
  EntryPoint.get C P (genv_entrypoints (prepare_global_env p )) = Some b ->
exists b',
  EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'.
Proof.
  move=> Hwf Hwf' Hiface. unfold EntryPoint.get; simpl.
  unfold prepare_procedures_initial_memory_aux. intros. eexists. revert H.
  rewrite !mapmE. unfold omap, obind, oapp; simpl. rewrite 2!mkfmapfE -Hiface.
  intros Hb.
  destruct (C \in domm (prog_interface p)) eqn:eC;
    rewrite eC in Hb; last discriminate; rewrite eC.
  simpl in *. find_if_inside_hyp Hb; last discriminate. inversion Hb. subst.
  setoid_rewrite mem_filter in e. setoid_rewrite mem_filter.
  move : e => /andP => [[Hentry Hbdomm]].
  unfold is_entrypoint_of_comp in *. rewrite -Hiface.
  destruct (prog_interface p C) eqn:eC2; last discriminate.
  move : Hentry => /orP => [[Hexport | Hmain]].
  - rewrite Hexport. simpl.
    assert (exists (Cprocs : NMap code) (Pcode : code),
               prog_procedures p' C = Some Cprocs /\ Cprocs b = Some Pcode)
      as [cdmap [cd [G1 G2]]].
    { eapply wfprog_exported_procedures_existence; eauto. by rewrite -Hiface. }
    rewrite G1 mem_domm G2. by simpl.
  - unfold is_main_proc in *. destruct (prog_main p) eqn:emain; last discriminate.
    rewrite Hmain.
    assert (prog_main p') as G.
    { rewrite -wfprog_main_component; auto. by rewrite -Hiface wfprog_main_component. }
    rewrite G orbT andTb. specialize (wfprog_main_existence Hwf' G) as [? [G1 G2]].
    assert (Component.main = C /\ Procedure.main = b) as [? ?]; subst.
    { move : Hmain => /andP => [[? ?]]. split; by apply beq_nat_eq. }
    by rewrite G1 G2.
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
  rewrite genv_entrypoints_program_link_left in Hentry; try assumption.
  rewrite Hifacec in Hlinkable, Hdomm.
  rewrite genv_entrypoints_program_link_left; assumption.
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


Definition find_label_in_component_helper
         G (procs: list (Block.id * code))
         (pc: Pointer.t) (l: label) : option Pointer.t :=
  match filter (fun b_c =>
                  isSome
                    (find_label_in_procedure
                       G
                       (Pointer.permission pc,
                        Pointer.component pc, b_c.1, 0%Z)
                       l
                    )
               )
               procs
  with
  | [] => None
  | (p_block,p_code) :: procs' =>
    find_label_in_procedure G (Pointer.permission pc,
                               Pointer.component pc, p_block, 0%Z) l
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
  
Lemma find_label_in_procedure_spec G pc l perm c b o:
  find_label_in_procedure G pc l = Some (perm, c, b, o) <->
  (
    exists C_procs P_code,
      getm (genv_procedures G) (Pointer.component pc) = Some C_procs /\
      getm C_procs (Pointer.block pc) = Some P_code /\
      perm = Pointer.permission pc /\
      c = Pointer.component pc /\
      b = Pointer.block pc /\
      find_label P_code l = Some o
  ).
Proof.
  unfold find_label_in_procedure.
  split; [intros Hfind | intros [? [? [HC_procs [HP_code [? [? [? Ho]]]]]]]].
  - destruct (genv_procedures G (Pointer.component pc)) as [A|] eqn:eA;
      last discriminate.
    destruct (A (Pointer.block pc)) as [B|] eqn:eB; last discriminate.
    destruct (find_label B l) as [C|] eqn:eC; last discriminate.
    inversion Hfind; subst. do 2 eexists. intuition; by eauto.
  - subst. by rewrite HC_procs HP_code Ho.
Qed.

Lemma find_label_in_procedure_1:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.


Lemma find_label_in_component_helper_Some_exists_code:
  forall p procMap l pc perm c bid o,
    genv_procedures (prepare_global_env p) (Pointer.component pc) = Some procMap ->
    find_label_in_component_helper
      (prepare_global_env p) (elementsm procMap) pc l =
    Some (perm, c, bid, o) ->
    exists cd, procMap bid = Some cd.
Proof.
  intros ? ? ? ? ? ? ? ? HprocMap HSome.
  unfold find_label_in_component_helper in *.
  destruct ([seq b_c <- elementsm procMap
            | find_label_in_procedure
                (prepare_global_env p)
                (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l])
           as [|[p_block x] t] eqn:efilter; first discriminate.
  apply find_label_in_procedure_spec in HSome as [? [? [G1 [? [? [? [? ?]]]]]]].
  rewrite HprocMap in G1. inversion G1; subst. by eauto.
Qed.

Lemma find_label_in_procedure_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
  forall {l},
    find_label_in_procedure (prepare_global_env (program_link p c)) pc l =
    find_label_in_procedure (prepare_global_env p) pc l.
Proof.
  (* RB: Note the proof strategy for all these lemmas is remarkably similar.
     It may be worthwhile to refactor it and/or its intermediate steps. *)
  intros c pc Hnotin p Hwfp Hwfc Hlinkable l.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable).
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
    Pointer.permission pc = Pointer.permission pc' /\
    Pointer.component pc = Pointer.component pc'.
Proof.
  unfold find_label_in_component_helper. intros G procs pc pc' l Hfind.
  destruct [seq b_c <- procs
           | find_label_in_procedure
               G
               (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l] eqn:efilter;
    first discriminate.
  destruct p as [? ?].
  apply find_label_in_procedure_guarantees in Hfind. by intuition.
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
  eapply find_label_in_component_helper_guarantees in Hfind; by intuition.
Qed.

Lemma find_label_in_component_perm:
  forall G pc pc' l,
    find_label_in_component G pc l = Some pc' ->
    Pointer.permission pc = Pointer.permission pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_component in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  eapply find_label_in_component_helper_guarantees in Hfind; by intuition.
Qed.  

Lemma find_label_in_component_program_link_left:
  forall {c pc},
    Pointer.component pc \notin domm (prog_interface c) ->
  forall {p},
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
  forall {l},
    find_label_in_component (prepare_global_env (program_link p c)) pc l =
    find_label_in_component (prepare_global_env p) pc l.
Proof.
  intros c pc Hnotin p Hwfp Hwfc Hlinkable l.
  rewrite (prepare_global_env_link Hwfp Hwfc Hlinkable).
  unfold find_label_in_component. unfold global_env_union at 1. simpl.
  rewrite unionmE.
  assert (HNone : (genv_procedures (prepare_global_env c)) (Pointer.component pc) = None)
    by (apply /dommPn; rewrite domm_genv_procedures; done).
  rewrite HNone.
  destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc))
    as [procs |] eqn:Hcase;
    rewrite Hcase; simpl; last by auto.
  - simpl.
    unfold find_label_in_component_helper; simpl.
    assert (Hnotin' : forall b,
               Pointer.component
                 (Pointer.permission pc, Pointer.component pc, b, 0%Z)
                 \notin domm (prog_interface c)).
      by done.

    assert (Hrewr: forall b_c: Block.id * code,
               find_label_in_procedure
                 (global_env_union (prepare_global_env p) (prepare_global_env c))
                 (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l
               =
               find_label_in_procedure
                 (prepare_global_env p)
                 (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l
           ).
    {
      rewrite <- (prepare_global_env_link Hwfp Hwfc Hlinkable).
      intros b_c.
      by rewrite
        (find_label_in_procedure_program_link_left (Hnotin' b_c.1) Hwfp Hwfc Hlinkable).
    }
    assert (Hrewr2:
               [seq b_c <- elementsm procs
               | find_label_in_procedure
                   (global_env_union (prepare_global_env p)
                                     (prepare_global_env c))
                   (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l]
               =
               [seq b_c <- elementsm procs
               | find_label_in_procedure
                   (prepare_global_env p)
                   (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l]
           ).
    {
      apply eq_filter. unfold "=1". intros. by rewrite Hrewr.
    }
    rewrite Hrewr2.
    destruct ([seq b_c <- elementsm procs
              | find_label_in_procedure
                  (prepare_global_env p)
                  (Pointer.permission pc, Pointer.component pc, b_c.1, 0%Z) l]); auto.
    destruct p0 as [b cd].
    specialize (Hrewr (b, cd)). by simpl in Hrewr.
Qed.

(* RB: Unified presentation of linkable + linkable_mains, to be used as needed
   around the development? *)
Lemma execution_invariant_to_linking:
  forall p c1 c2 pc instr,
    linkable (prog_interface p) (prog_interface c1) ->
    linkable (prog_interface p) (prog_interface c2) ->
    well_formed_program p ->
    well_formed_program c1 ->
    well_formed_program c2 ->
    Pointer.component pc \in domm (prog_interface p) ->
    executing (prepare_global_env (program_link p c1)) pc instr ->
    executing (prepare_global_env (program_link p c2)) pc instr.
Proof.
  intros p c1 c2 pc instr Hlinkable1 Hlinkable2 Hwf Hwf1 Hwf2 Hpc Hexec.
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
  rewrite (genv_procedures_program_link_left_notin Hcc1 Hwf Hwf1 Hlinkable1) in Hgenv_procs.
  rewrite (genv_procedures_program_link_left_notin Hcc2 Hwf Hwf2 Hlinkable2).
  assumption.
Qed.

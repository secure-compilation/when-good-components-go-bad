Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import Source.Language.
Require Import S2I.Compiler.
Require Import S2I.SimCode.
Require Import S2I.LabelUniq.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinPos.
Require Import MicroPolicies.Recomposition.LinMatch.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.LinGenv.
Require Import MicroPolicies.Recomposition.LinSim.
Require Import MicroPolicies.Recomposition.LinCompiled.
Require Import MicroPolicies.Recomposition.LinInv.
Require Import MicroPolicies.Recomposition.LinShape.
Require Import MicroPolicies.Recomposition.LinReach.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma me_sem_fields (NC : nat) (W1 W2 : program) :
  code W1 = code W2 ->
  prog_buffers W1 = prog_buffers W2 ->
  prog_interface W1 = prog_interface W2 ->
  me_sem NC W1 = me_sem NC W2.
Proof.
move=> H1 H2 H3.
by rewrite /me_sem /prog_initial H1 H2 H3.
Qed.

Lemma me_sem_link_Wlin (NC L P C : nat) (a b : Intermediate.program) :
  me_sem NC (program_link (lin_side L P C a) (lin_side L P C b))
  = me_sem NC (Wlin L P C a b).
Proof.
by apply: me_sem_fields.
Qed.

Lemma mem_seq_In (T : eqType) (l : seq T) (x : T) :
  x \in l -> List.In x l.
Proof.
elim: l => [|a l IH] //=.
rewrite in_cons => /orP[/eqP -> | /IH H].
- by left.
- by right.
Qed.

Lemma In_getm_def_isSome (A : Type) (l : seq (nat * A)) (k : nat) (v : A) :
  List.In (k, v) l -> exists v', getm_def l k = Some v'.
Proof.
elim: l => [|[k' v'] l IH] //= [Heq | HIn].
- case: Heq => -> _. rewrite eqxx. by exists v'.
- case Ek: (k == k'); first by exists v'.
  exact: IH HIn.
Qed.

Lemma entrypoints_main_exist (p : Intermediate.program)
    (mp : NMap Machine.code) :
  Intermediate.prog_main p = true ->
  Component.main \in domm (Intermediate.prog_interface p) ->
  getm (Intermediate.prog_procedures p) Component.main = Some mp ->
  Procedure.main \in domm mp ->
  exists bM,
    Intermediate.EntryPoint.get Component.main Procedure.main
      (Intermediate.prepare_procedures_entrypoints p) = Some bM.
Proof.
move=> Hmain Hin HC Hp0.
case Er: (ComponentMemoryExtra.reserve_blocks
            (ComponentMemory.prealloc
               (odflt emptym
                  (Intermediate.prog_buffers p Component.main)))
            (length (elementsm mp))) => [Cmem' bs].
have [Ebs En] := reserve_blocks_vals Er.
rewrite /Intermediate.EntryPoint.get
        /Intermediate.prepare_procedures_entrypoints
        /Intermediate.prepare_procedures_initial_memory
        /Intermediate.prepare_procedures_initial_memory_aux /=.
rewrite mapmE mkfmapfE Hin /= HC /=.
rewrite /Intermediate.reserve_component_blocks; cbv zeta.
rewrite Er /=.
rewrite mkfmapE.
have HmainIn : List.In Procedure.main (unzip1 (elementsm mp)).
{ apply: mem_seq_In.
  by rewrite unzip1_elementsm_domm. }
have [j Hj] := List.In_nth_error _ _ HmainIn.
have Hjlt : (j < length (unzip1 (elementsm mp)))%coq_nat.
{ apply/List.nth_error_Some. by rewrite Hj. }
have Hjlt' : (j < length (elementsm mp))%coq_nat.
{ by move: Hjlt; rewrite /unzip1 List.length_map. }
have Hbj : List.nth_error bs j
           = Some (ComponentMemory.next_block
                     (ComponentMemory.prealloc
                        (odflt emptym
                           (Intermediate.prog_buffers p Component.main)))
                   + j).
{ rewrite Ebs.
  have Hij : List.nth_error (iota 0 (length (elementsm mp))) j
             = Some (0 + j).
  { apply: nth_error_iota. by apply/ltP. }
  by rewrite (List.map_nth_error _ _ _ Hij). }
have Hzip : List.nth_error (zip (unzip1 (elementsm mp)) bs) j
            = Some (Procedure.main,
                    ComponentMemory.next_block
                      (ComponentMemory.prealloc
                         (odflt emptym
                            (Intermediate.prog_buffers p Component.main)))
                    + j).
{ exact: nth_error_zip Hj Hbj. }
have HzIn := List.nth_error_In _ _ Hzip.
set bj := (ComponentMemory.next_block _ + j) in HzIn *.
have [Ci ECi] : exists Ci,
    getm (Intermediate.prog_interface p) Component.main = Some Ci.
{ by apply/dommP. }
have HpIn : List.In (Procedure.main, bj)
    (pmap (fun '(P0, b0) =>
             match getm (Intermediate.prog_interface p) Component.main
             with
             | Some Ciface =>
                 if (P0 \in Component.export Ciface)
                    || (match Intermediate.prog_main p with
                        | true => (Component.main =? Component.main)
                                  && (Procedure.main =? P0)
                        | false => false
                        end)
                 then Some (P0, b0) else None
             | None => None
             end)
          (zip (unzip1 (elementsm mp)) bs)).
{ apply: mem_seq_In.
  rewrite mem_pmap.
  have Hmem := In_mem_seq HzIn.
  have Hf : (fun '(P0, b0) =>
               match getm (Intermediate.prog_interface p) Component.main
               with
               | Some Ciface =>
                   if (P0 \in Component.export Ciface)
                      || (match Intermediate.prog_main p with
                          | true => (Component.main =? Component.main)
                                    && (Procedure.main =? P0)
                          | false => false
                          end)
                   then Some (P0, b0) else None
               | None => None
               end) (Procedure.main, bj) = Some (Procedure.main, bj).
  { rewrite ECi Hmain /=.
    by rewrite orbT. }
  apply/mapP.
  exists (Procedure.main, bj).
  - exact: Hmem.
  - by rewrite /= Hf. }
have [bM HgM] := In_getm_def_isSome HpIn.
by exists bM; rewrite HgM.
Qed.

Lemma lin_statics_intro (L P C : nat) (a b : Intermediate.program)
    (sa sb : Source.program) :
  Intermediate.well_formed_program a ->
  Intermediate.well_formed_program b ->
  linkable (Intermediate.prog_interface a)
           (Intermediate.prog_interface b) ->
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  (forall cid Cprocs Pid Pcode l0,
     Intermediate.prog_procedures a cid = Some Cprocs ->
     getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L) ->
  (forall cid Cprocs Pid Pcode l0,
     Intermediate.prog_procedures b cid = Some Cprocs ->
     getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L) ->
  (forall cid Cprocs Pid,
     Intermediate.prog_procedures a cid = Some Cprocs ->
     Pid \in domm Cprocs -> Pid < P) ->
  (forall cid Cprocs Pid,
     Intermediate.prog_procedures b cid = Some Cprocs ->
     Pid \in domm Cprocs -> Pid < P) ->
  (forall cid,
     cid \in domm (Intermediate.prog_interface a) -> cid < C) ->
  (forall cid,
     cid \in domm (Intermediate.prog_interface b) -> cid < C) ->
  lin_statics L P C a b.
Proof.
move=> Hwfa Hwfb [Hsound Hdisj] Hca Hcb Hlab_a Hlab_b Hproc_a Hproc_b
       Hcomp_a Hcomp_b.
constructor.
- exact: Hlab_a.
- move=> cid Hin. apply: Hcomp_a.
  by rewrite (Intermediate.wfprog_defined_procedures Hwfa).
- exact: Hlab_b.
- move=> cid Hin. apply: Hcomp_b.
  by rewrite (Intermediate.wfprog_defined_procedures Hwfb).
- exact: Hproc_a.
- exact: Hproc_b.
- rewrite -(Intermediate.wfprog_defined_procedures Hwfa)
          -(Intermediate.wfprog_defined_procedures Hwfb).
  exact: Hdisj.
- move=> cid Cprocs0 l0 HC0. exact: (compiled_Huniq Hca l0 HC0).
- move=> cid Cprocs0 l0 HC0. exact: (compiled_Huniq Hcb l0 HC0).
Qed.

Section HBwdAssembly.

Variables L P C NC : nat.

Hypothesis Hres : forall a b : Intermediate.program,
  Intermediate.well_formed_program a ->
  Intermediate.well_formed_program b ->
  linkable (Intermediate.prog_interface a)
           (Intermediate.prog_interface b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  (exists sa, Source.well_formed_program sa
              /\ compile_program sa = Some a) ->
  (exists sb, Source.well_formed_program sb
              /\ compile_program sb = Some b) ->
  exists SINV, sim_residual L P C a b NC SINV.

Theorem H_bwd_from_sim :
  forall (a b : Intermediate.program) (m : finpref_behavior),
  Intermediate.well_formed_program a ->
  Intermediate.well_formed_program b ->
  linkable (Intermediate.prog_interface a)
           (Intermediate.prog_interface b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  (exists sa, Source.well_formed_program sa
              /\ compile_program sa = Some a) ->
  (exists sb, Source.well_formed_program sb
              /\ compile_program sb = Some b) ->
  does_prefix
    (me_sem NC (program_link (lin_side L P C a) (lin_side L P C b))) m ->
  exists beh,
    program_behaves (CS.sem (Intermediate.program_link a b)) beh
    /\ (CompCertExtensions.prefix m beh
        \/ behavior_improves_finpref beh m).
Proof.
move=> a b m Hwfa Hwfb Hlink Hcl Hca Hcb Hdp.
have Hwf : Intermediate.well_formed_program
             (Intermediate.program_link a b)
  := Intermediate.linking_well_formedness Hwfa Hwfb Hlink.
have Hmain : Intermediate.prog_main (Intermediate.program_link a b)
             = true.
{ have [mp [Hm _]] := Intermediate.cprog_main_existence Hcl.
  by case: (Intermediate.prog_main _) Hm. }
have Hside : (Component.main \in domm (Intermediate.prog_interface a))
          \/ (Component.main \in domm (Intermediate.prog_interface b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  have : Component.main
      \in domm (Intermediate.prog_procedures
                  (Intermediate.program_link a b))
    by rewrite mem_domm Hget.
  rewrite -(Intermediate.wfprog_defined_procedures Hwf)
          /Intermediate.program_link /= domm_union in_fsetU.
  by case/orP; [left | right]. }
have HinIlp : Component.main
    \in domm (Intermediate.prog_interface
                (Intermediate.program_link a b)).
{ rewrite /Intermediate.program_link /= domm_union in_fsetU.
  by case: Hside => -> //; rewrite orbT. }
have Hm' : Intermediate.prog_main (Intermediate.program_link a b)
  by rewrite Hmain.
have [mpI [HgetI HinI]] := Intermediate.wfprog_main_existence Hwf Hm'.
have [bM Hep] := entrypoints_main_exist Hmain HinIlp HgetI HinI.
have [SINV Hressab] := Hres Hwfa Hwfb Hlink Hcl Hca Hcb.
case: Hca => sa [Hwfsa Hcompa].
case: Hcb => sb [Hwfsb Hcompb].
have Hbufs : Intermediate.prog_buffers (Intermediate.program_link a b)
    = unionm (gen_buffers (Source.prog_buffers sa))
             (gen_buffers (Source.prog_buffers sb)).
{ rewrite /Intermediate.program_link /=.
  by rewrite (compilation_preserves_buffers Hcompa)
             (compilation_preserves_buffers Hcompb). }
have Hptr : forall (C0 : Component.id) (bk : Block.id) (off : Z)
                   (c' : Component.id) (b' : Block.id) (o' : Z),
    Memory.Memory.load
      (Intermediate.prepare_procedures_memory
         (Intermediate.program_link a b)) (C0, bk, off)
      = Some (Ptr (c', b', o')) ->
    exists bm',
      Intermediate.prog_buffers (Intermediate.program_link a b) c'
        = Some bm'
      /\ b' \in domm bm'.
{ move=> C0 bk off c' b' o' Hload.
  exact: (compiled_Hptr_union Hwfsa Hwfsb Hbufs Hload). }
have Honext : forall cid Cprocs P0 Pcode o i,
    Intermediate.prog_procedures (side_of a b cid) cid = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode o = Some i ->
    i <> IHalt -> i <> IReturn -> i <> IJump ->
    exists i', List.nth_error Pcode o.+1 = Some i'.
{ move=> cid Cprocs P0 Pcode o i.
  rewrite /side_of. case: ifP => _.
  - move=> HC HP Hn H1 H2 H3.
    exact: (compiled_proc_terminal Hcompa HC HP Hn H1 H2 H3).
  - move=> HC HP Hn H1 H2 H3.
    exact: (compiled_proc_terminal Hcompb HC HP Hn H1 H2 H3). }
have Hoenc := encode_is_code (L := L) (P := P) (C := C) Hwfa Hwfb.
rewrite (me_sem_link_Wlin NC L P C a b) in Hdp.
case: Hside => [HmainA | HmainB].
-
  have HmainL : Component.main
      \in domm (Intermediate.prog_procedures a).
  { by rewrite -(Intermediate.wfprog_defined_procedures Hwfa). }
  have [CprocsM [HmainP Hp0]] := wf_main_procs Hwf Hmain HmainL.
  have Hmain0 : forall Pcode,
      getm CprocsM Procedure.main = Some Pcode ->
      exists i0, List.nth_error Pcode 0 = Some i0.
  { move=> Pcode HPc.
    exact: (compiled_proc_nonempty Hcompa HmainP HPc). }
  exact: (bwd_improves_res Hressab Hwf Hcl Hmain HmainP Hp0 Hep Hmain0
            Hptr Honext Hoenc Hdp).
-
  have HnotA : Component.main
      \notin domm (Intermediate.prog_interface a).
  { case: Hlink => _ Hdisj.
    rewrite fdisjointC in Hdisj.
    by move/fdisjointP: Hdisj => /(_ _ HmainB). }
  have HmainNL : Component.main
      \notin domm (Intermediate.prog_procedures a).
  { by rewrite -(Intermediate.wfprog_defined_procedures Hwfa). }
  have [CprocsM [HmainP Hp0]] := wf_main_procs_r Hwf Hmain HmainNL.
  have Hmain0 : forall Pcode,
      getm CprocsM Procedure.main = Some Pcode ->
      exists i0, List.nth_error Pcode 0 = Some i0.
  { move=> Pcode HPc.
    exact: (compiled_proc_nonempty Hcompb HmainP HPc). }
  exact: (bwd_improves_res_r Hressab Hwf Hwfa HnotA Hmain HmainP Hp0
            Hep Hmain0 Hptr Honext Hoenc Hdp).
Qed.

Theorem bt_run_from_sim :
  forall (a b : Intermediate.program) (m : finpref_behavior),
  Intermediate.well_formed_program a ->
  Intermediate.well_formed_program b ->
  linkable (Intermediate.prog_interface a)
           (Intermediate.prog_interface b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  (exists sa, Source.well_formed_program sa
              /\ compile_program sa = Some a) ->
  (exists sb, Source.well_formed_program sb
              /\ compile_program sb = Some b) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem (Intermediate.program_link a b)) m ->
  does_prefix
    (me_sem NC (program_link (lin_side L P C a) (lin_side L P C b))) m.
Proof.
move=> a b m Hwfa Hwfb Hlink Hcl Hca Hcb Hnw Hdp.
have Hwf : Intermediate.well_formed_program
             (Intermediate.program_link a b)
  := Intermediate.linking_well_formedness Hwfa Hwfb Hlink.
have Hmain : Intermediate.prog_main (Intermediate.program_link a b)
             = true.
{ have [mp [Hm _]] := Intermediate.cprog_main_existence Hcl.
  by case: (Intermediate.prog_main _) Hm. }
have Hside : (Component.main \in domm (Intermediate.prog_interface a))
          \/ (Component.main \in domm (Intermediate.prog_interface b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  have : Component.main
      \in domm (Intermediate.prog_procedures
                  (Intermediate.program_link a b))
    by rewrite mem_domm Hget.
  rewrite -(Intermediate.wfprog_defined_procedures Hwf)
          /Intermediate.program_link /= domm_union in_fsetU.
  by case/orP; [left | right]. }
have HinIlp : Component.main
    \in domm (Intermediate.prog_interface
                (Intermediate.program_link a b)).
{ rewrite /Intermediate.program_link /= domm_union in_fsetU.
  by case: Hside => -> //; rewrite orbT. }
have Hm' : Intermediate.prog_main (Intermediate.program_link a b)
  by rewrite Hmain.
have [mpI [HgetI HinI]] := Intermediate.wfprog_main_existence Hwf Hm'.
have [bM Hep] := entrypoints_main_exist Hmain HinIlp HgetI HinI.
have [SINV Hressab] := Hres Hwfa Hwfb Hlink Hcl Hca Hcb.
case: Hca => sa [Hwfsa Hcompa].
case: Hcb => sb [Hwfsb Hcompb].
have Hbufs : Intermediate.prog_buffers (Intermediate.program_link a b)
    = unionm (gen_buffers (Source.prog_buffers sa))
             (gen_buffers (Source.prog_buffers sb)).
{ rewrite /Intermediate.program_link /=.
  by rewrite (compilation_preserves_buffers Hcompa)
             (compilation_preserves_buffers Hcompb). }
have Hptr : forall (C0 : Component.id) (bk : Block.id) (off : Z)
                   (c' : Component.id) (b' : Block.id) (o' : Z),
    Memory.Memory.load
      (Intermediate.prepare_procedures_memory
         (Intermediate.program_link a b)) (C0, bk, off)
      = Some (Ptr (c', b', o')) ->
    exists bm',
      Intermediate.prog_buffers (Intermediate.program_link a b) c'
        = Some bm'
      /\ b' \in domm bm'.
{ move=> C0 bk off c' b' o' Hload.
  exact: (compiled_Hptr_union Hwfsa Hwfsb Hbufs Hload). }
have Honext : forall cid Cprocs P0 Pcode o i,
    Intermediate.prog_procedures (side_of a b cid) cid = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode o = Some i ->
    i <> IHalt -> i <> IReturn -> i <> IJump ->
    exists i', List.nth_error Pcode o.+1 = Some i'.
{ move=> cid Cprocs P0 Pcode o i.
  rewrite /side_of. case: ifP => _.
  - move=> HC HP Hn H1 H2 H3.
    exact: (compiled_proc_terminal Hcompa HC HP Hn H1 H2 H3).
  - move=> HC HP Hn H1 H2 H3.
    exact: (compiled_proc_terminal Hcompb HC HP Hn H1 H2 H3). }
have Hoenc := encode_is_code (L := L) (P := P) (C := C) Hwfa Hwfb.
rewrite (me_sem_link_Wlin NC L P C a b).
case: Hside => [HmainA | HmainB].
-
  have HmainL : Component.main
      \in domm (Intermediate.prog_procedures a).
  { by rewrite -(Intermediate.wfprog_defined_procedures Hwfa). }
  have [CprocsM [HmainP Hp0]] := wf_main_procs Hwf Hmain HmainL.
  have Hmain0 : forall Pcode,
      getm CprocsM Procedure.main = Some Pcode ->
      exists i0, List.nth_error Pcode 0 = Some i0.
  { move=> Pcode HPc.
    exact: (compiled_proc_nonempty Hcompa HmainP HPc). }
  exact: (fwd_does_prefix_res Hressab Hwf Hcl Hmain HmainP Hp0 Hep
            Hmain0 Hptr Honext Hoenc Hnw Hdp).
-
  have HnotA : Component.main
      \notin domm (Intermediate.prog_interface a).
  { case: Hlink => _ Hdisj.
    rewrite fdisjointC in Hdisj.
    by move/fdisjointP: Hdisj => /(_ _ HmainB). }
  have HmainNL : Component.main
      \notin domm (Intermediate.prog_procedures a).
  { by rewrite -(Intermediate.wfprog_defined_procedures Hwfa). }
  have [CprocsM [HmainP Hp0]] := wf_main_procs_r Hwf Hmain HmainNL.
  have Hmain0 : forall Pcode,
      getm CprocsM Procedure.main = Some Pcode ->
      exists i0, List.nth_error Pcode 0 = Some i0.
  { move=> Pcode HPc.
    exact: (compiled_proc_nonempty Hcompb HmainP HPc). }
  exact: (fwd_does_prefix_res_r Hressab Hwf Hwfa HnotA Hmain HmainP
            Hp0 Hep Hmain0 Hptr Honext Hoenc Hnw Hdp).
Qed.

End HBwdAssembly.

Lemma ra_free_b_instr (i : Machine.instr) :
  ra_free_b i = true -> ra_free_instr i.
Proof.
case: i => //=.
- by move=> v r; case: r.
- by move=> r1 r2; case: r1; case: r2.
- by move=> op r1 r2 r3; case: r1; case: r2; case: r3.
- by move=> r1 r2; case: r1.
- by move=> r1 r2; case: r1.
- by move=> r1 r2; case: r1; case: r2.
- by move=> r l; case: r.
Qed.

Lemma compiled_side_ra_free (a b : Intermediate.program)
    (sa sb : Source.program) :
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  forall (side : Component.id -> Intermediate.program),
  (forall cid, side cid = a \/ side cid = b) ->
  forall cid Cprocs P0 Pcode o i,
    Intermediate.prog_procedures (side cid) cid = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode o = Some i ->
    ra_free_instr i.
Proof.
move=> Hca Hcb side Hside cid Cprocs P0 Pcode o i Hget HgetP Hnth.
apply: ra_free_b_instr.
case: (Hside cid) => Es; rewrite Es in Hget.
- exact: (compiled_ra_free Hca Hget HgetP Hnth).
- exact: (compiled_ra_free Hcb Hget HgetP Hnth).
Qed.

Lemma sr_ra_inst (a b : Intermediate.program)
    (sa sb : Source.program) :
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  forall cid Cprocs P0 Pcode o i,
    Intermediate.prog_procedures (side_of a b cid) cid = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode o = Some i ->
    ra_free_instr i.
Proof.
move=> Hca Hcb.
apply: (compiled_side_ra_free Hca Hcb).
exact: side_of_cases.
Qed.

Lemma linked_code_shape (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  forall (cid : Component.id) (Cprocs : NMap Machine.code)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    code_shape Pcode.
Proof.
move=> [pa Hca] [pb Hcb] cid Cprocs P0 Pcode.
rewrite /= unionmE.
case Ea: (Intermediate.prog_procedures a cid) => [CprocsA|] /=.
- move=> [<-] HgetP.
  exact: (compiled_code_shape Hca Ea HgetP).
- move=> Hgb HgetP.
  exact: (compiled_code_shape Hcb Hgb HgetP).
Qed.

Lemma linked_jal_target (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  forall (cid : Component.id) (Cprocs : NMap Machine.code)
         (P1 : Procedure.id) (Pcode1 : Machine.code) (o1 : nat)
         (l : label)
         (P2 : Procedure.id) (Pcode2 : Machine.code) (o2 : nat),
    Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs ->
    getm Cprocs P1 = Some Pcode1 ->
    getm Cprocs P2 = Some Pcode2 ->
    List.nth_error Pcode1 o1 = Some (IJal l) ->
    List.nth_error Pcode2 o2 = Some (ILabel l) ->
    dead_at Pcode2 o2 = false.
Proof.
move=> [pa Hca] [pb Hcb] cid Cprocs P1 Pcode1 o1 l P2 Pcode2 o2.
rewrite /= unionmE.
case Ea: (Intermediate.prog_procedures a cid) => [CprocsA|] /=.
- move=> [<-] Hg1 Hg2 Hn1 Hn2.
  exact: (compiled_jal_target Hca Ea Hg1 Hg2 Hn1 Hn2).
- move=> Hgb Hg1 Hg2 Hn1 Hn2.
  exact: (compiled_jal_target Hcb Hgb Hg1 Hg2 Hn1 Hn2).
Qed.

Lemma flat_pos_lt_lin_code (L P C : nat) (pr : Intermediate.program)
    (c : Component.id) (Cprocs : NMap Machine.code) (p : Procedure.id)
    (Pcode : Machine.code) (o : nat) (i : Machine.instr) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  flat_pos pr c p Pcode o < size (lin_code L P C pr).
Proof.
move=> HC HP Ho.
have Hk : 0 < isize i := isize_gt0 i.
have Hnth : List.nth_error (lin_gen pr (can_make L P C) (can_upd L))
              (flat_pos pr c p Pcode o + 0)
            = List.nth_error
                (cell_exp (can_make L P C) (can_upd L)
                   (memory_lengths (Intermediate.prog_buffers pr))
                   (instr_to_transitional c i)) 0
  := @lin_gen_nth (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers pr)) pr
       c Cprocs p Pcode o i 0
       (erefl (memory_lengths (Intermediate.prog_buffers pr)))
       HC HP Ho Hk.
rewrite addn0 in Hnth.
case E0: (List.nth_error
            (cell_exp (can_make L P C) (can_upd L)
               (memory_lengths (Intermediate.prog_buffers pr))
               (instr_to_transitional c i)) 0) => [cell|]; last first.
- exfalso.
  move: E0 => /List.nth_error_None.
  rewrite lin_size_length size_cell_exp texp_isize.
  by lia.
- rewrite E0 in Hnth.
  have Hlt := LinPos.nth_error_size Hnth.
  rewrite /lin_code /lin_body.
  move: Hlt Hnth.
  case: (lin_gen pr (can_make L P C) (can_upd L))
    => [|cell0 rest] Hlt Hnth.
  + by rewrite List.nth_error_nil in Hnth.
  + rewrite size_rcons.
    by lia.
Qed.

Lemma side_flat_pos_lt (L P C : nat) (a b : Intermediate.program)
    (c : Component.id) (Cprocs : NMap Machine.code) (p : Procedure.id)
    (Pcode : Machine.code) (o : nat) (i : Machine.instr) :
  Intermediate.prog_procedures (Intermediate.program_link a b) c
    = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  side_flat_pos L P C a b c p Pcode o
  < size (lin_code L P C a ++ lin_code L P C b).
Proof.
move=> HC HP Ho.
move: HC. rewrite /= unionmE.
rewrite /side_flat_pos size_cat.
case Ea: (Intermediate.prog_procedures a c) => [CprocsA|] /=.
- have -> : c \in domm (Intermediate.prog_procedures a)
    by rewrite mem_domm Ea.
  move=> [E]; subst CprocsA.
  have Hlt := @flat_pos_lt_lin_code L P C a c Cprocs p Pcode o i
                Ea HP Ho.
  by lia.
- have -> : c \in domm (Intermediate.prog_procedures a) = false
    by rewrite mem_domm Ea.
  move=> Hgb.
  have Hlt := @flat_pos_lt_lin_code L P C b c Cprocs p Pcode o i
                Hgb HP Ho.
  by lia.
Qed.

Lemma sr_jal_lab_inst (L P C : nat) (a b : Intermediate.program)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop) :
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  size (initial_memory (mt := mt)
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ imm_size mt ->
  forall bmap gps imem iregs ipc tpc ms l,
    lin_match L P C a b SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IJal l) ->
    Intermediate.GlobalEnv.find_label_in_component
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc l = Some tpc ->
    forall Cprocs,
      Intermediate.prog_procedures (Intermediate.program_link a b)
        (Pointer.component ipc) = Some Cprocs ->
      exists jt pt Ptcode,
        [/\ Pointer.block tpc
              = proc_nb0 (Intermediate.program_link a b)
                  (Pointer.component ipc) + jt,
            List.nth_error (elementsm Cprocs) jt = Some (pt, Ptcode),
            (0 <= Pointer.offset tpc)%Z,
            List.nth_error Ptcode (Z.to_nat (Pointer.offset tpc))
              = Some (ILabel l)
          & size (initial_memory (mt := mt)
                    (unionm (Intermediate.prog_buffers a)
                            (Intermediate.prog_buffers b)))
            + (side_flat_pos L P C a b (Pointer.component ipc) pt
                 Ptcode (Z.to_nat (Pointer.offset tpc)) + 0)
            < 2 ^ imm_size mt].
Proof.
move=> Hwf Hcl Hfit bmap gps imem iregs ipc tpc ms l Hm Hex HF
  Cprocs HC.
have Hdomm := wf_procs_iface Hwf.
have Hin := Hdomm _ (lm_pc_domm Hm).
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
have [Ecomp [Ptcode0 [Hrun Hofft Hlbl]]]
  := find_label_in_component_nth Hmain Hproci Hin HF.
case: Hrun => [Cprocs0 [j [P0 [HA HB HC0]]]].
move: HA. rewrite Ecomp HC. move=> [E]; subst Cprocs0.
have HgetP : getm Cprocs P0 = Some Ptcode0.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ HC0). }
exists j, P0, Ptcode0.
split.
- by rewrite HB Ecomp.
- exact: HC0.
- exact: Hofft.
- exact: Hlbl.
- have Hlt := @side_flat_pos_lt L P C a b (Pointer.component ipc)
                Cprocs P0 Ptcode0 (Z.to_nat (Pointer.offset tpc))
                (ILabel l) HC HgetP Hlbl.
  by lia.
Qed.

Lemma nth_error_lt (A : Type) (s : list A) (n : nat) :
  n < size s -> exists x, List.nth_error s n = Some x.
Proof.
move=> Hlt.
case E: (List.nth_error s n) => [x|]; first by exists x.
move: E => /List.nth_error_None.
rewrite lin_size_length. by lia.
Qed.

Lemma proc_off_le (Pcode : Machine.code) (o o' : nat)
    (i' : Machine.instr) :
  List.nth_error Pcode o' = Some i' ->
  o <= o' ->
  proc_off Pcode o <= proc_off Pcode o'.
Proof.
elim: o' i' => [|o' IH] i' Hnth Ho.
- by have -> : o = 0 by lia.
- case: (ltnP o o'.+1) => Ho2; last first.
  + have -> : o = o'.+1 by lia.
    by [].
  + have Hsz := LinPos.nth_error_size Hnth.
    have [i'' Hnth''] : exists i'',
        List.nth_error Pcode o' = Some i''.
    { apply: nth_error_lt. by lia. }
    have H1 := IH _ Hnth'' _.
    rewrite (proc_off_S Hnth'').
    have Hle : proc_off Pcode o <= proc_off Pcode o'.
    { apply: (IH _ Hnth''). by lia. }
    by lia.
Qed.

Lemma side_get (a b : Intermediate.program) (cid : Component.id)
    (Cprocs : NMap Machine.code) :
  Intermediate.prog_procedures (side_of a b cid) cid = Some Cprocs ->
  Intermediate.prog_procedures (Intermediate.program_link a b) cid
  = Some Cprocs.
Proof.
rewrite /= unionmE /side_of.
case Ea: (Intermediate.prog_procedures a cid) => [CA|] /=.
- have -> : cid \in domm (Intermediate.prog_procedures a)
    by rewrite mem_domm Ea.
  by rewrite Ea.
- have -> : (cid \in domm (Intermediate.prog_procedures a)) = false
    by rewrite mem_domm Ea.
  by [].
Qed.

Lemma sr_bnz_lab_inst (L P C : nat) (a b : Intermediate.program)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  size (initial_memory (mt := mt)
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ imm_size mt ->
  forall bmap gps imem iregs ipc tpc ms r l,
    lin_match L P C a b SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IBnz r l) ->
    Intermediate.GlobalEnv.find_label_in_procedure
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc l = Some tpc ->
    (0 <= Pointer.offset tpc)%Z /\
    (forall Cprocs (j : nat) P0 Pcode,
        Intermediate.prog_procedures
          (side_of a b (Pointer.component ipc))
          (Pointer.component ipc) = Some Cprocs ->
        getm Cprocs P0 = Some Pcode ->
        Pointer.block ipc
          = proc_nb0 (Intermediate.program_link a b)
              (Pointer.component ipc) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
          = Some (IBnz r l) ->
        [/\ List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
              = Some (ILabel l),
            side_flat_pos L P C a b (Pointer.component ipc) P0 Pcode
              (Z.to_nat (Pointer.offset ipc))
            <= side_flat_pos L P C a b (Pointer.component ipc) P0
                 Pcode (Z.to_nat (Pointer.offset tpc))
          & (size (initial_memory (mt := mt)
                     (unionm (Intermediate.prog_buffers a)
                             (Intermediate.prog_buffers b)))
             + (side_flat_pos L P C a b (Pointer.component ipc) P0
                  Pcode (Z.to_nat (Pointer.offset tpc)) + 0))
            - (size (initial_memory (mt := mt)
                       (unionm (Intermediate.prog_buffers a)
                               (Intermediate.prog_buffers b)))
               + side_flat_pos L P C a b (Pointer.component ipc) P0
                   Pcode (Z.to_nat (Pointer.offset ipc)))
            < 2 ^ imm_size mt]).
Proof.
move=> [pa Hca] [pb Hcb] Hwf Hcl Hfit
  bmap gps imem iregs ipc tpc ms r l Hm Hex HF.
have Hdomm := wf_procs_iface Hwf.
have Hin := Hdomm _ (lm_pc_domm Hm).
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
split.
-
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] [Hilp Hblk Hjnth]]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hrun : running_code a b ipc Qc by exists Cp, j0, Q0.
  have [_ Hofft _] := find_label_in_procedure_nth Hmain Hin Hrun HF.
  exact: Hofft.
- move=> Cprocs j P0 Pcode Hside HgetP Hblk Hjnth Hbnz.
  have Hilp := side_get Hside.
  have Hrun : running_code a b ipc Pcode by exists Cprocs, j, P0.
  have [HrunT Hofft Hlbl]
    := find_label_in_procedure_nth Hmain Hin Hrun HF.
  split.
  + exact: Hlbl.
  +
    have Hfwd : Z.to_nat (Pointer.offset ipc)
                < Z.to_nat (Pointer.offset tpc).
    { move: Hside. rewrite /side_of.
      case Es: (Pointer.component ipc
                \in domm (Intermediate.prog_procedures a)) => Hside'.
      - exact: (compiled_bnz_forward Hca Hside' HgetP Hbnz Hlbl).
      - exact: (compiled_bnz_forward Hcb Hside' HgetP Hbnz Hlbl). }
    rewrite /side_flat_pos /flat_pos.
    case: (Pointer.component ipc
           \in domm (Intermediate.prog_procedures a)).
    * rewrite leq_add2l leq_add2l.
      apply: (proc_off_le Hlbl). by lia.
    * rewrite leq_add2l leq_add2l leq_add2l.
      apply: (proc_off_le Hlbl). by lia.
  + have Hlt := @side_flat_pos_lt L P C a b (Pointer.component ipc)
                  Cprocs P0 Pcode (Z.to_nat (Pointer.offset tpc))
                  (ILabel l) Hilp HgetP Hlbl.
    by lia.
Qed.

Lemma sr_call_inst (L P C : nat) (a b : Intermediate.program)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.prog_interface a = Intermediate.prog_interface b ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  size (initial_memory (mt := mt)
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ imm_size mt ->
  forall bmap gps imem iregs ipc ms C' p b0,
    lin_match L P C a b SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (ICall C' p) ->
    imported_procedure
      (Intermediate.GlobalEnv.genv_interface
         (Intermediate.GlobalEnv.prepare_global_env
            (Intermediate.program_link a b)))
      (Pointer.component ipc) C' p ->
    Intermediate.EntryPoint.get C' p
      (Intermediate.GlobalEnv.genv_entrypoints
         (Intermediate.GlobalEnv.prepare_global_env
            (Intermediate.program_link a b))) = Some b0 ->
    exists cl,
      [/\ head_tag (side_of a b C') C' p
            = LRC.MTag LRC.Other C' (Some (p, cl)) true,
          mem_seq cl (Pointer.component ipc) = true,
          size (initial_memory (mt := mt)
                  (unionm (Intermediate.prog_buffers a)
                          (Intermediate.prog_buffers b)))
          + side_entry_pos L P C a b C' p < 2 ^ imm_size mt
        & exists CprocsC jc Pcode',
            [/\ Intermediate.prog_procedures
                  (Intermediate.program_link a b) C' = Some CprocsC,
                b0 = proc_nb0 (Intermediate.program_link a b) C' + jc,
                List.nth_error (elementsm CprocsC) jc
                  = Some (p, Pcode')
              & exists i0, List.nth_error Pcode' 0 = Some i0]].
Proof.
move=> [pa Hca] [pb Hcb] Hif Hwf Hfit
  bmap gps imem iregs ipc ms C' p b0 Hm Hex Himp Hep.
have Hgeq : forall x,
    getm (Intermediate.prog_interface (Intermediate.program_link a b))
      x
    = getm (Intermediate.prog_interface (side_of a b C')) x.
{ move=> x.
  have Hu : getm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) x
            = getm (Intermediate.prog_interface a) x.
  { rewrite /= unionmE.
    case Eax: (getm (Intermediate.prog_interface a) x) => [v|] //=.
    by rewrite -Hif Eax. }
  rewrite Hu /side_of.
  case: (C' \in domm (Intermediate.prog_procedures a)) => //=.
  by rewrite Hif. }
have HinC' : C' \in domm (Intermediate.prog_interface
                            (Intermediate.program_link a b)).
{ move: Hep.
  rewrite /Intermediate.EntryPoint.get /Intermediate.GlobalEnv.prepare_global_env
    /Intermediate.prepare_procedures_initial_memory
    /Intermediate.prepare_procedures_initial_memory_aux /=
    mapmE mkfmapfE.
  by case: ifP. }
have [CprocsC HgetC] : exists CprocsC,
    Intermediate.prog_procedures (Intermediate.program_link a b) C'
    = Some CprocsC.
{ move: (HinC').
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm.
  case E: (Intermediate.prog_procedures _ C') => [CprocsC|] // _.
  by exists CprocsC. }
have [jc [Pcode' [Eb0 Hjnth]]] := genv_entry_spec HinC' HgetC Hep.
have HgetP' : getm CprocsC p = Some Pcode'.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have [i0 Hi0] : exists i0, List.nth_error Pcode' 0 = Some i0.
{ move: HgetC. rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a C') => [CA|] /=.
  - move=> [E]; subst CA.
    exact: (compiled_proc_nonempty Hca Ea HgetP').
  - move=> Hgb.
    exact: (compiled_proc_nonempty Hcb Hgb HgetP'). }
case: (Himp) => CI [HhasCaller Himping].
have Hsound := Intermediate.wfprog_interface_soundness Hwf.
have [CI' HgetC'] : exists CI',
    getm (Intermediate.prog_interface (Intermediate.program_link a b))
      C' = Some CI'.
{ move: (HinC'). rewrite mem_domm.
  case E: (getm _ C') => [CI'|] // _. by exists CI'. }
have Hexp : Component.is_exporting CI' p.
{ exact: (Hsound _ _ _ Himp _ HgetC'). }
eexists. split.
- by rewrite /head_tag.
- rewrite /head_tag /=.
  have -> : forall (s : seq Component.id) (x : Component.id),
      mem_seq s x = (x \in s) by [].
  rewrite mem_filter.
  apply/andP; split.
  + rewrite -!Hgeq HgetC' HhasCaller /=.
    apply/andP; split; [exact: Hexp | exact: Himping].
  + by rewrite mem_domm -Hgeq HhasCaller.
- have Hlt := @side_flat_pos_lt L P C a b C' CprocsC p Pcode' 0 i0
                HgetC HgetP' Hi0.
  suff Hle : side_entry_pos L P C a b C' p
             <= side_flat_pos L P C a b C' p Pcode' 0 by lia.
  rewrite /side_entry_pos /side_flat_pos /flat_pos.
  case: (C' \in domm (Intermediate.prog_procedures a)); by lia.
- exists CprocsC, jc, Pcode'.
  split=> //. by exists i0.
Qed.

Lemma stub_no_label_at (a b : Intermediate.program) (pc' : Pointer.t)
    (Pcode : Machine.code) (l : label) :
  running_code a b pc' Pcode ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc'))
    = Some (ILabel l) ->
  ~ stub_pc a b pc'.
Proof.
move=> Hrun Hlbl Hstub.
case: Hstub => Cs [js [Ps [lab [HilpS HblkS HjnthS]]]].
case: Hrun => Cr [jr [Pr [HilpR HblkR HjnthR]]].
have Ecs : Cr = Cs.
{ move: HilpR. rewrite HilpS. by move=> [->]. }
subst Cr.
have Ej : jr = js by lia.
subst jr.
have EP : (Pr, Pcode)
          = (Ps, [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]).
{ move: HjnthR. rewrite HjnthS. by move=> [-> ->]. }
case: EP => _ EPc. subst Pcode.
move: Hlbl.
case E: (Z.to_nat (Pointer.offset pc')) => [|[|[|o]]] //=.
by rewrite List.nth_error_nil.
Qed.

Lemma stub_nolabel_p_inst (a b : Intermediate.program) :
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Pointer.component pc
    \in domm (Intermediate.prog_interface
                (Intermediate.program_link a b)) ->
    Intermediate.GlobalEnv.find_label_in_procedure
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc l = Some pc' ->
    ~ stub_pc a b pc'.
Proof.
move=> Hwf Hcl pc l pc' Hin HF.
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
have [Pcode [Hrun Hofft Hlbl]]
  := find_label_in_procedure_nth' Hmain Hproci Hin HF.
exact: (stub_no_label_at Hrun Hlbl).
Qed.

Lemma stub_nolabel_c_inst (a b : Intermediate.program) :
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Pointer.component pc
    \in domm (Intermediate.prog_interface
                (Intermediate.program_link a b)) ->
    Intermediate.GlobalEnv.find_label_in_component
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc l = Some pc' ->
    ~ stub_pc a b pc'.
Proof.
move=> Hwf Hcl pc l pc' Hin HF.
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
have [Ecomp [Pcode [Hrun Hofft Hlbl]]]
  := find_label_in_component_nth Hmain Hproci Hin HF.
exact: (stub_no_label_at Hrun Hlbl).
Qed.

Lemma stub_noentry_inst (a b : Intermediate.program) :
  (exists pa, Source.well_formed_program pa
              /\ compile_program pa = Some a) ->
  (exists pb, Source.well_formed_program pb
              /\ compile_program pb = Some b) ->
  Intermediate.prog_interface a = Intermediate.prog_interface b ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  forall (C0 C' : Component.id) (P : Procedure.id) (bb : Block.id),
    imported_procedure
      (Intermediate.GlobalEnv.genv_interface
         (Intermediate.GlobalEnv.prepare_global_env
            (Intermediate.program_link a b))) C0 C' P ->
    Intermediate.EntryPoint.get C' P
      (Intermediate.GlobalEnv.genv_entrypoints
         (Intermediate.GlobalEnv.prepare_global_env
            (Intermediate.program_link a b))) = Some bb ->
    ~ stub_blk a b C' bb.
Proof.
move=> [pa [Hwfa Hca]] [pb [Hwfb Hcb]] Hif Hwf C0 C' P bb Himp Hep
  Hstub.
case: Hstub => Cprocs [js [Ps [lab [HilpS HblkS HjnthS]]]].
have HinC' : C' \in domm (Intermediate.prog_interface
                            (Intermediate.program_link a b)).
{ move: Hep.
  rewrite /Intermediate.EntryPoint.get
    /Intermediate.GlobalEnv.prepare_global_env
    /Intermediate.prepare_procedures_initial_memory
    /Intermediate.prepare_procedures_initial_memory_aux /=
    mapmE mkfmapfE.
  by case: ifP. }
have [jc [Pcode' [Eb HjnthE]]] := genv_entry_spec HinC' HilpS Hep.
have Ej : jc = js by lia.
subst jc.
have EPP : (P, Pcode')
           = (Ps, [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]).
{ move: HjnthE. rewrite HjnthS. by move=> [-> ->]. }
case: EPP => E1 E2. subst Ps Pcode'.
have Hsound := Intermediate.wfprog_interface_soundness Hwf.
have [CI' HgetC'] : exists CI',
    getm (Intermediate.prog_interface (Intermediate.program_link a b))
      C' = Some CI'.
{ move: (HinC'). rewrite mem_domm.
  case E: (getm _ C') => [CI'|] // _. by exists CI'. }
have Hexp : Component.is_exporting CI' P.
{ exact: (Hsound _ _ _ Himp _ HgetC'). }
have HgetP' : getm Cprocs P
              = Some [:: IConst (IInt 1) R_ONE; IJal lab; IHalt].
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ HjnthS). }
have Hab : forall x,
    getm (Intermediate.prog_interface (Intermediate.program_link a b))
      x
    = getm (Intermediate.prog_interface a) x.
{ move=> x. rewrite /= unionmE.
  case Eax: (getm (Intermediate.prog_interface a) x) => [v|] //=.
  by rewrite -Hif Eax. }
move: HilpS. rewrite /= unionmE.
case Ea: (Intermediate.prog_procedures a C') => [CA|] /=.
- move=> [E]; subst CA.
  have HgetCIa : getm (Intermediate.prog_interface a) C' = Some CI'.
  { by rewrite -Hab. }
  exact: (compiled_stub_not_exported Hwfa Hca Ea HgetP' HgetCIa Hexp).
- move=> Hgb.
  have HgetCIb : getm (Intermediate.prog_interface b) C' = Some CI'.
  { by rewrite -Hif -Hab. }
  exact: (compiled_stub_not_exported Hwfb Hcb Hgb HgetP' HgetCIb Hexp).
Qed.

Lemma sr_jal_dead_inst (L P C : nat) (a b : Intermediate.program)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  (forall pc l pc',
     Pointer.component pc
     \in domm (Intermediate.prog_interface
                 (Intermediate.program_link a b)) ->
     Intermediate.GlobalEnv.find_label_in_component
       (Intermediate.GlobalEnv.prepare_global_env
          (Intermediate.program_link a b)) pc l = Some pc' ->
     ~ stub_pc a b pc') ->
  (forall pc l pc',
     Pointer.component pc
     \in domm (Intermediate.prog_interface
                 (Intermediate.program_link a b)) ->
     Intermediate.GlobalEnv.find_label_in_procedure
       (Intermediate.GlobalEnv.prepare_global_env
          (Intermediate.program_link a b)) pc l = Some pc' ->
     ~ stub_pc a b pc') ->
  (forall C0 C' P0 bb,
     imported_procedure
       (Intermediate.GlobalEnv.genv_interface
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b))) C0 C' P0 ->
     Intermediate.EntryPoint.get C' P0
       (Intermediate.GlobalEnv.genv_entrypoints
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b))) = Some bb ->
     ~ stub_blk a b C' bb) ->
  forall bmap gps imem iregs ipc ms l
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IJal l) ->
    Intermediate.prog_procedures (Intermediate.program_link a b)
      (Pointer.component ipc) = Some Cprocs ->
    Pointer.block ipc
      = proc_nb0 (Intermediate.program_link a b)
          (Pointer.component ipc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    (0 <= Pointer.offset ipc)%Z ->
    gps <> [::] ->
    dead_at Pcode (Z.to_nat (Pointer.offset ipc)) = true.
Proof.
move=> [pa Hca] [pb Hcb] Hwf Hnl1 Hnl2 Hne
  bmap gps imem iregs ipc ms l Cprocs j P0 Pcode
  Hreach Hm Hex Hilp Hblk Hjnth Hoff Hgps.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hdomm := wf_procs_iface Hwf.
have Hin := Hdomm _ (lm_pc_domm Hm).
have [Cp [Q0 [Qc [j0 [[Hside HgetP0 Hnth0 _ _] [Hilp0 Hblk0 Hjnth0]]]]]]
  := lm_fetch Hin (lm_pc Hm) Hex.
have Ecp : Cp = Cprocs.
{ move: Hilp0. rewrite Hilp. by move=> [->]. }
subst Cp.
have Ej : j0 = j by lia.
subst j0.
have EQ : (Q0, Qc) = (P0, Pcode).
{ move: Hjnth0. rewrite Hjnth. by move=> [-> ->]. }
case: EQ => E1 E2. subst Q0 Qc.
have [plm [nb [Hbound Hper]]] : exists plm nb,
    (forall P' l', getm plm P' = Some l' -> l' < nb)
    /\ forall Pq cd, getm Cprocs Pq = Some cd ->
        (exists e s0 s1 pl,
            [/\ compile_proc (Pointer.component ipc)
                  (Pointer.component ipc, 0, 0%Z)
                  (Pointer.component ipc, 1, 0%Z) plm Pq e s0
                  = Some (cd, s1),
                getm plm Pq = Some pl
              & nb <= nlab s0 (Pointer.component ipc)])
        \/ exists lab,
            cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]
            /\ getm plm Procedure.main = Some lab.
{ move: Hilp. rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a (Pointer.component ipc))
    => [CA|] /=.
  - move=> [E]; subst CA.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hca Ea.
    exists plm, nb. by split.
  - move=> Hgb.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hcb Hgb.
    exists plm, nb. by split. }
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd _]]].
-
  have := compile_proc_shape_facts Hcpc Hnth0.
  by move=> /=.
-
  exfalso.
  have Hstub : stub_pc a b ipc.
  { exists Cprocs, j, P0, lab.
    split=> //.
    by rewrite -Ecd. }
  have [H1 _] := ireach_sb Hnl1 Hnl2 Hne Hreach.
  exact: (Hgps (H1 Hstub)).
Qed.

Lemma cls_class_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  forall (pc : Pointer.t) (i : Machine.instr)
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures (Intermediate.program_link a b)
      (Pointer.component pc) = Some Cprocs ->
    Pointer.block pc
      = proc_nb0 (Intermediate.program_link a b)
          (Pointer.component pc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    (0 <= Pointer.offset pc)%Z ->
    List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
    match i with
    | IConst _ r =>
        r <> R_RA
        /\ (dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
            ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
              = false ->
            r <> R_SP)
    | IMov _ r2 => r2 <> R_RA /\ r2 <> R_SP
    | IBinOp op r1 r2 r3 =>
        r3 <> R_RA
        /\ (r3 = R_SP ->
            [/\ r1 = R_SP, r2 = R_ONE, op = Add \/ op = Minus
              & ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
                = false])
    | ILoad r1 r2 =>
        (r2 = R_RA ->
         [/\ r1 = R_SP,
             dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true,
             sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc)) = 0%Z
           & ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
             = false])
        /\ (r2 = R_SP ->
            dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
            r1 = R_SP
            /\ ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
               = true)
    | IStore r1 r2 =>
        (r2 = R_RA ->
         [/\ r1 = R_SP,
             dead_at Pcode (Z.to_nat (Pointer.offset pc)) = false
           & ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
             = false])
        /\ (r2 <> R_RA ->
            ph_scan Pcode false (Z.to_nat (Pointer.offset pc))
            = false)
    | IAlloc r _ =>
        r <> R_RA
        /\ dead_at Pcode (Z.to_nat (Pointer.offset pc)) = false
    | IJal _ =>
        dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
        ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false
    | ICall _ _ =>
        dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true
        /\ ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false
    | _ => True
    end.
Proof.
move=> [pa Hca] [pb Hcb] pc i Cprocs j P0 Pcode
  Hilp Hblk Hjnth Hoff Hnth.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hok : cls_ok Pcode.
{ move: Hilp. rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a (Pointer.component pc))
    => [CA|] /=.
  - move=> [E]; subst CA.
    exact: (compiled_cls Hca Ea HgetP).
  - move=> Hgb.
    exact: (compiled_cls Hcb Hgb HgetP). }
have Hcond := clso_cond Hok Hnth.
exact: (cls_condP Hcond).
Qed.

Lemma jal_target_live_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc (IJal l) ->
    Intermediate.GlobalEnv.find_label_in_component
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc l = Some pc' ->
    forall (Cprocs' : NMap Machine.code) (j' : nat)
           (P0' : Procedure.id) (Pcode' : Machine.code),
      Intermediate.prog_procedures (Intermediate.program_link a b)
        (Pointer.component pc') = Some Cprocs' ->
      Pointer.block pc'
        = proc_nb0 (Intermediate.program_link a b)
            (Pointer.component pc') + j' ->
      List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
      (0 <= Pointer.offset pc')%Z ->
      dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = false.
Proof.
move=> [pa Hca] [pb Hcb] Hwf Hcl pc l pc' Hex HF
  Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
have Hdomm := wf_procs_iface Hwf.
have Hin : Pointer.component pc
           \in domm (Intermediate.prog_interface
                       (Intermediate.program_link a b)).
{ exact: (executing_domm Hex). }
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm
    in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
have [Ecomp [Ptcode0 [Hrun Hofft Hlbl]]]
  := find_label_in_component_nth Hmain Hproci Hin HF.
case: Hrun => [Cprocs0 [j0 [P00 [HA HB HC0]]]].
have Ecp : Cprocs0 = Cprocs'.
{ move: HA. rewrite Hilp'. by move=> [->]. }
subst Cprocs0.
have Ej : j0 = j'.
{ move: HB. rewrite Hblk' => HB. by lia. }
subst j0.
have EQ : (P00, Ptcode0) = (P0', Pcode').
{ move: HC0. rewrite Hjnth'. by move=> [-> ->]. }
case: EQ => E1 E2. subst P00 Ptcode0.
have [CprocsS [jS [P0S [PcS [HilpS HblkS HjnthS HoffS HnthS]]]]]
  := executing_bundle Hwf Hex.
have EcpS : CprocsS = Cprocs'.
{ move: HilpS. rewrite -Ecomp Hilp'. by move=> [->]. }
subst CprocsS.
have HgetS : getm Cprocs' P0S = Some PcS.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ HjnthS). }
have HgetT : getm Cprocs' P0' = Some Pcode'.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth'). }
have [plm [nb [Hbound Hper]]] : exists plm nb,
    (forall P' l', getm plm P' = Some l' -> l' < nb)
    /\ forall Pq cd, getm Cprocs' Pq = Some cd ->
        (exists e s0 s1 pl,
            [/\ compile_proc (Pointer.component pc')
                  (Pointer.component pc', 0, 0%Z)
                  (Pointer.component pc', 1, 0%Z) plm Pq e s0
                  = Some (cd, s1),
                getm plm Pq = Some pl
              & nb <= nlab s0 (Pointer.component pc')])
        \/ exists lab,
            cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]
            /\ getm plm Procedure.main = Some lab.
{ move: Hilp'. rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a (Pointer.component pc'))
    => [CA|] /=.
  - move=> [E]; subst CA.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hca Ea.
    exists plm, nb. by split.
  - move=> Hgb.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hcb Hgb.
    exists plm, nb. by split. }
have Hlnb : l < nb.
{ have HinS : List.In (IJal l) PcS.
  { exact: (List.nth_error_In _ _ HnthS). }
  case: (Hper _ _ HgetS)
    => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd Hglab]]].
  - have Hjt := compile_proc_jal Hcpc.
    have [P'' HgP''] := Hjt _ HinS.
    exact: (Hbound _ _ HgP'').
  - move: HinS. rewrite Ecd /=.
    move=> [E|[E|[E|[]]]] //; case: E => El.
    subst l.
    exact: (Hbound _ _ Hglab). }
case: (Hper _ _ HgetT)
  => [[e0 [s0 [s1 [pl [Hcpc _ Hnbs]]]]] | [lab [Ecd _]]].
- have Hlt : l < nlab s0 (Pointer.component pc') by lia.
  exact: (compile_proc_label_low Hlt Hcpc Hlbl).
- exfalso.
  move: Hlbl. rewrite Ecd.
  by case: (Z.to_nat (Pointer.offset pc')) => [|[|[|n]]] //=;
    case: n.
Qed.

Lemma bnz_target_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall (pc : Pointer.t) (r : register) (l : label)
         (pc' : Pointer.t),
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc (IBnz r l) ->
    Intermediate.GlobalEnv.find_label_in_procedure
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc l = Some pc' ->
    forall (Cprocs : NMap Machine.code) (j : nat)
           (P0 : Procedure.id) (Pcode : Machine.code),
      Intermediate.prog_procedures (Intermediate.program_link a b)
        (Pointer.component pc) = Some Cprocs ->
      Pointer.block pc
        = proc_nb0 (Intermediate.program_link a b)
            (Pointer.component pc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      dead_at Pcode (Z.to_nat (Pointer.offset pc')) = false
      \/ [/\ dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true,
             sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc'))
               = sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc))
           & ph_scan Pcode false (Z.to_nat (Pointer.offset pc'))
               = ph_scan Pcode false (Z.to_nat (Pointer.offset pc))].
Proof.
move=> [pa Hca] [pb Hcb] Hwf Hcl pc r l pc' Hex HF
  Cprocs j P0 Pcode Hilp Hblk Hjnth.
have Hin : Pointer.component pc
           \in domm (Intermediate.prog_interface
                       (Intermediate.program_link a b)).
{ exact: (executing_domm Hex). }
have Hmain : Component.main
             \in domm (Intermediate.prog_interface
                         (Intermediate.program_link a b)).
{ have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget. }
have Hproci : forall cid,
    cid \in domm (Intermediate.prog_interface
                    (Intermediate.program_link a b)) ->
    exists Cprocs0,
      Intermediate.prog_procedures (Intermediate.program_link a b) cid
      = Some Cprocs0.
{ move=> cid Hin0.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm
    in Hin0.
  case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
  move=> _. by exists Cprocs0. }
have [CprocsS [jS [P0S [PcS [HilpS HblkS HjnthS HoffS HnthS]]]]]
  := executing_bundle Hwf Hex.
have EcpS : CprocsS = Cprocs.
{ move: HilpS. rewrite Hilp. by move=> [->]. }
subst CprocsS.
have EjS : jS = j by lia.
subst jS.
have EQS : (P0S, PcS) = (P0, Pcode).
{ move: HjnthS. rewrite Hjnth. by move=> [-> ->]. }
case: EQS => E1 E2. subst P0S PcS.
have [Hcm Hbk]
  := Intermediate.GlobalEnv.find_label_in_procedure_guarantees
       _ _ _ _ HF.
have [Pcode1 [Hrun1 Hoff1 Hlbl1]]
  := find_label_in_procedure_nth' Hmain Hproci Hin HF.
case: Hrun1 => [Cprocs1 [j1 [P01 [HA1 HB1 HC1]]]].
move: HA1 HB1. rewrite -Hcm -Hbk => HA1 HB1.
have Ecp1 : Cprocs1 = Cprocs.
{ move: HA1. rewrite Hilp. by move=> [->]. }
subst Cprocs1.
have Ej1 : j1 = j by lia.
subst j1.
have EQ1 : (P01, Pcode1) = (P0, Pcode).
{ move: HC1. rewrite Hjnth. by move=> [-> ->]. }
case: EQ1 => F1 F2. subst P01 Pcode1.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have [plm [nb [Hbound Hper]]] : exists plm nb,
    (forall P' l', getm plm P' = Some l' -> l' < nb)
    /\ forall Pq cd, getm Cprocs Pq = Some cd ->
        (exists e s0 s1 pl,
            [/\ compile_proc (Pointer.component pc)
                  (Pointer.component pc, 0, 0%Z)
                  (Pointer.component pc, 1, 0%Z) plm Pq e s0
                  = Some (cd, s1),
                getm plm Pq = Some pl
              & nb <= nlab s0 (Pointer.component pc)])
        \/ exists lab,
            cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]
            /\ getm plm Procedure.main = Some lab.
{ move: Hilp. rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a (Pointer.component pc))
    => [CA|] /=.
  - move=> [E]; subst CA.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hca Ea.
    exists plm, nb. by split.
  - move=> Hgb.
    have [plm [nb [Hb Hp]]] := compiled_comp_origin Hcb Hgb.
    exists plm, nb. by split. }
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc Hpl Hnbs]]]]] | [lab [Ecd _]]].
- have Hplb : pl < nlab s0 (Pointer.component pc).
  { have := Hbound _ _ Hpl. by lia. }
  exact: (compile_proc_bnztgt Hpl Hplb Hcpc HnthS Hlbl1).
- exfalso.
  move: HnthS. rewrite Ecd.
  by case: (Z.to_nat (Pointer.offset pc)) => [|[|[|n]]] //=;
    case: n.
Qed.

Lemma sr_one_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  forall gps imem iregs (pc : Pointer.t) op c bl o,
    ireach a b (gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc
      (IBinOp op R_SP R_ONE R_SP) ->
    Intermediate.Register.get R_SP iregs = Ptr (c, bl, o) ->
    eval_binop op (Ptr (c, bl, o))
      (Intermediate.Register.get R_ONE iregs)
    = Ptr (c, bl,
           (o + match op with Add => 1%Z | _ => (-1)%Z end)%Z).
Proof.
move=> Hexa Hexb Hwf gps imem iregs pc op c bl o Hreach Hex Hsp.
have Hrone' : forall (C0 : Component.id) (Cprocs : NMap Machine.code)
                     (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures (Intermediate.program_link a b) C0
      = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    rone_check Pcode false = true.
{ case: Hexa => pa Hca. case: Hexb => pb Hcb.
  move=> C0 Cprocs P0 Pcode.
  rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a C0) => [CA|] /=.
  - move=> [E]; subst CA.
    exact: (compiled_rone Hca Ea).
  - move=> Hgb.
    exact: (compiled_rone Hcb Hgb). }
have [H1 H2] := ireach_r1 Hwf Hrone' Hreach.
have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
  := executing_bundle Hwf Hex.
have HgetP : getm Cp P0 = Some Pc.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hchk := Hrone' _ _ _ _ Hilp HgetP.
have Harm := rone_check_sound Hchk Hnth.
move: Harm => /= Harm.
have Hone1 : Intermediate.Register.get R_ONE iregs = Int 1.
{ exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm). }
have Hcls := cls_class_inst Hexa Hexb Hilp Hblk Hjnth Hoff Hnth.
move: Hcls => /= [_ Hsp3].
have [_ _ Hop _] := Hsp3 erefl.
rewrite Hone1.
case: Hop => Eop; subst op => /=.
- by [].
- by have -> : (o + (-1))%Z = (o - 1)%Z by lia.
Qed.

Lemma sr_reload_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall gps imem iregs (pc : Pointer.t)
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    ireach a b (gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) pc (ILoad R_SP R_SP) ->
    Intermediate.prog_procedures (Intermediate.program_link a b)
      (Pointer.component pc) = Some Cprocs ->
    Pointer.block pc
      = proc_nb0 (Intermediate.program_link a b)
          (Pointer.component pc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
    Intermediate.Register.get R_SP iregs
      = Ptr (Pointer.component pc, 1, 0%Z).
Proof.
move=> Hexa Hexb Hwf Hcl gps imem iregs pc Cprocs j P0 Pcode
  Hreach Hex Hilp Hblk Hjnth Hph.
have Hrspt' : forall (C0 : Component.id)
                     (Cprocs0 : NMap Machine.code)
                     (P00 : Procedure.id) (Pcode0 : Machine.code),
    Intermediate.prog_procedures (Intermediate.program_link a b) C0
      = Some Cprocs0 ->
    getm Cprocs0 P00 = Some Pcode0 ->
    rspt_check (C0, 1, 0%Z) Pcode0 None false = true.
{ case: Hexa => pa Hca. case: Hexb => pb Hcb.
  move=> C0 Cprocs0 P00 Pcode0.
  rewrite /= unionmE.
  case Ea: (Intermediate.prog_procedures a C0) => [CA|] /=.
  - move=> [E]; subst CA.
    exact: (compiled_rspt Hca Ea).
  - move=> Hgb.
    exact: (compiled_rspt Hcb Hgb). }
have [H1 _] := ireach_rsp Hwf Hcl Hrspt' Hreach.
have [Cp' [j' [P0' [Pc' [Hilp' Hblk' Hjnth' Hoff' Hnth']]]]]
  := executing_bundle Hwf Hex.
have Ecp : Cp' = Cprocs.
{ move: Hilp'. rewrite Hilp. by move=> [->]. }
subst Cp'.
have Ej : j' = j by lia.
subst j'.
have EQ : (P0', Pc') = (P0, Pcode).
{ move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pc'.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hchk := Hrspt' _ _ _ _ Hilp HgetP.
have := rspt_check_sound Hchk Hnth'.
rewrite /rspt_cond Hph.
case Etr: (rsp_track Pcode None (Z.to_nat (Pointer.offset pc)))
  => [[iz|ip]|] //.
move=> /ptr_eqb_eq Eip.
subst ip.
have := H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff' Etr.
by move=> /= ->.
Qed.

Definition scr_def (C0 : Component.id) : Pointer.t := (C0, 1, 0%Z).

Lemma iinv_runs_inst (a b : Intermediate.program) :
  (exists pa, compile_program pa = Some a) ->
  (exists pb, compile_program pb = Some b) ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  forall
    (Hreload : forall gps imem iregs (pc : Pointer.t)
                      (Cprocs : NMap Machine.code) (j : nat)
                      (P0 : Procedure.id) (Pcode : Machine.code),
        ireach a b (gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc (ILoad R_SP R_SP) ->
        Intermediate.prog_procedures (Intermediate.program_link a b)
          (Pointer.component pc) = Some Cprocs ->
        Pointer.block pc
          = proc_nb0 (Intermediate.program_link a b)
              (Pointer.component pc) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
        Intermediate.Register.get R_SP iregs
        = Ptr (scr_def (Pointer.component pc)))
    (Hjumptie : forall gps imem iregs (pc pc' : Pointer.t),
        ireach a b (pc' :: gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc IJump ->
        forall (f : option (Block.id * Z))
               (fbs' : list (option (Block.id * Z)))
               (Cprocs' : NMap Machine.code) (j' : nat)
               (P0' : Procedure.id) (Pcode' : Machine.code),
          iframes imem (pc' :: gps) (f :: fbs') ->
          Intermediate.prog_procedures (Intermediate.program_link a b)
            (Pointer.component pc') = Some Cprocs' ->
          Pointer.block pc'
            = proc_nb0 (Intermediate.program_link a b)
                (Pointer.component pc') + j' ->
          List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
          (0 <= Pointer.offset pc')%Z ->
          dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
          exists fb sl,
            [/\ f = Some (fb, sl),
                ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
                  = false
              & Intermediate.Register.get R_SP iregs
                = Ptr (Pointer.component pc', fb,
                       (sl + sp_scan Pcode' 0%Z
                               (Z.to_nat (Pointer.offset pc')))%Z)])
    (Hreturntie : forall gps imem iregs (pc pc' : Pointer.t),
        ireach a b (pc' :: gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc IReturn ->
        forall (f : option (Block.id * Z))
               (fbs' : list (option (Block.id * Z)))
               (Cprocs' : NMap Machine.code) (j' : nat)
               (P0' : Procedure.id) (Pcode' : Machine.code),
          iframes imem (pc' :: gps) (f :: fbs') ->
          Intermediate.prog_procedures (Intermediate.program_link a b)
            (Pointer.component pc') = Some Cprocs' ->
          Pointer.block pc'
            = proc_nb0 (Intermediate.program_link a b)
                (Pointer.component pc') + j' ->
          List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
          (0 <= Pointer.offset pc')%Z ->
          dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
          exists fb sl,
            [/\ f = Some (fb, sl),
                ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
                  = true
              & Memory.Memory.load imem
                  (Pointer.component (scr_def (Pointer.component pc')),
                   Pointer.block (scr_def (Pointer.component pc')),
                   Pointer.offset (scr_def (Pointer.component pc')))
                = Some (Ptr (Pointer.component pc', fb,
                             (sl + sp_scan Pcode' 0%Z
                                     (Z.to_nat
                                        (Pointer.offset pc')))%Z))])
    (Hstoresep : forall gps imem iregs (pc : Pointer.t) r1 r2 bp op
                        (Cprocs : NMap Machine.code) (j : nat)
                        (P0 : Procedure.id) (Pcode : Machine.code),
        ireach a b (gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc (IStore r1 r2) ->
        Intermediate.prog_procedures (Intermediate.program_link a b)
          (Pointer.component pc) = Some Cprocs ->
        Pointer.block pc
          = proc_nb0 (Intermediate.program_link a b)
              (Pointer.component pc) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        Intermediate.Register.get r1 iregs
          = Ptr (Pointer.component pc, bp, op) ->
        (forall fb spo,
           Intermediate.Register.get R_SP iregs
             = Ptr (Pointer.component pc, fb, spo) ->
           bp <> fb
           \/ op <> (spo - sp_scan Pcode 0%Z
                             (Z.to_nat (Pointer.offset pc)))%Z)
        /\ (forall fbs, iframes imem gps fbs ->
              frames_sep gps fbs (Pointer.component pc) bp))
    ,
  forall s, ireach a b s -> iinv a b scr_def s.
Proof.
move=> Hca Hcb Hwf Hcl Hreload Hjumptie Hreturntie Hstoresep
  s Hreach.
have Hallocsep := ireach_allocsep (pra := a) (prb := b).
have Hone := sr_one_inst Hca Hcb Hwf.
have HC := cls_class_inst Hca Hcb.
have HJ := jal_target_live_inst Hca Hcb Hwf Hcl.
have HB := bnz_target_inst Hca Hcb Hwf Hcl.
exact: (ireach_iinv Hwf HC Hone Hreload HJ HB Hjumptie Hreturntie
          Hstoresep Hallocsep Hreach).
Qed.

Lemma sr_ra_undef_inst (L P C : nat) (a b : Intermediate.program)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
    (scr_of : Component.id -> Pointer.t) :
  (forall s, ireach a b s -> iinv a b scr_of s) ->
  forall bmap gps imem iregs ipc ms r1,
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IStore r1 R_RA) ->
    Intermediate.Register.get R_RA iregs = Undef.
Proof.
move=> Hii bmap gps imem iregs ipc ms r1 Hreach _ _.
have [H1 _] := Hii _ Hreach.
exact: H1.
Qed.

Theorem sim_residual_inst (L P C NC : nat)
    (a b : Intermediate.program) (sa sb : Source.program) :
  compile_program sa = Some a ->
  compile_program sb = Some b ->
  Source.well_formed_program sa ->
  Source.well_formed_program sb ->
  Intermediate.prog_interface a = Intermediate.prog_interface b ->
  Intermediate.well_formed_program (Intermediate.program_link a b) ->
  Intermediate.closed_program (Intermediate.program_link a b) ->
  size (initial_memory (mt := mt)
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ imm_size mt ->
  (forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures a cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode ->
    l0 < L) ->
  (forall cid,
    cid \in domm (Intermediate.prog_procedures a) -> cid < C) ->
  (forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures b cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode ->
    l0 < L) ->
  (forall cid,
    cid \in domm (Intermediate.prog_procedures b) -> cid < C) ->
  (forall cid Cprocs Pid,
    Intermediate.prog_procedures a cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P) ->
  (forall cid Cprocs Pid,
    Intermediate.prog_procedures b cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P) ->
  fdisjoint (domm (Intermediate.prog_procedures a))
            (domm (Intermediate.prog_procedures b)) ->
  (forall cid Cprocs0 l0,
    Intermediate.prog_procedures a cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1) ->
  (forall cid Cprocs0 l0,
    Intermediate.prog_procedures b cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1) ->
  size (initial_memory (mt := mt)
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ word_size mt ->
  size (linearize_bufs
          (unionm (Intermediate.prog_buffers a)
                  (Intermediate.prog_buffers b)))
  + size (lin_code L P C a ++ lin_code L P C b) < 2 ^ word_size mt ->
  (forall bmap gps imem iregs ipc ms r1 (bp : Block.id) (op : Z)
          (v : value) (base : nat) (w2 : mword mt)
          (cvt : LRC.value_tag)
          (ent : option (Procedure.id * seq Component.id)) mpc',
     lin_match L P C a b (sinv_inst L P C a b) bmap gps imem
       iregs ipc ms ->
     Intermediate.GlobalEnv.executing
       (Intermediate.GlobalEnv.prepare_global_env
          (Intermediate.program_link a b)) ipc (ILoad r1 R_RA) ->
     Intermediate.Register.get r1 iregs
       = Ptr (Pointer.component ipc, bp, op) ->
     Memory.Memory.load imem (Pointer.component ipc, bp, op)
       = Some v ->
     amap_get bmap (Pointer.component ipc) bp = Some base ->
     getm (Symbolic.mem ms)
       (@word_of_nat (word_size mt) (base + Z.to_nat op))
       = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
     (forall (tpc : Pointer.t) (gps' : list Pointer.t),
      gps = tpc :: gps' ->
      exists (Cprocs' : NMap Machine.code) (j' : nat)
             (P0' : Procedure.id) (Pcode' : Machine.code),
        [/\ Intermediate.prog_procedures
              (Intermediate.program_link a b)
              (Pointer.component tpc) = Some Cprocs',
            Pointer.block tpc
              = proc_nb0 (Intermediate.program_link a b)
                  (Pointer.component tpc) + j',
            List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode'),
            (0 <= Pointer.offset tpc)%Z
          & w2 = @word_of_nat (word_size mt)
                   (side_flat_pos L P C a b (Pointer.component tpc)
                      P0' Pcode' (Z.to_nat (Pointer.offset tpc))
                    + size (initial_memory (mt := mt)
                              (unionm (Intermediate.prog_buffers a)
                                 (Intermediate.prog_buffers b))))]
        /\ (exists i'',
              List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
              = Some i'')
        /\ (~~ nilp gps' ->
            dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
        /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                  then LRC.InternalJump
                  else LRC.Ret (cross_frames (Pointer.component tpc)
                                  gps'))) ->
     sinv_inst L P C a b bmap gps imem
       (Intermediate.Register.set R_RA v iregs) (Pointer.inc ipc)
       (@Symbolic.State mt lrc_tags _
          (setm (Symbolic.mem ms)
             (@word_of_nat (word_size mt) (base + Z.to_nat op))
             (w2@(LRC.MTag (if LRC.is_address cvt then LRC.Invalidated
                            else LRC.Other)
                    (Pointer.component ipc) ent false)))
          (setm (Symbolic.regs ms)
             (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA)) (w2@cvt))
          mpc' tt)) ->
  (forall bmap gps imem iregs ipc ms r1 (bp : Block.id) (op : Z)
          (v : value) (base : nat) (w2 : mword mt)
          (cvt : LRC.value_tag)
          (ent : option (Procedure.id * seq Component.id)),
     ireach a b (gps, imem, iregs, ipc) ->
     lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
       ms ->
     Intermediate.GlobalEnv.executing
       (Intermediate.GlobalEnv.prepare_global_env
          (Intermediate.program_link a b)) ipc (ILoad r1 R_RA) ->
     Intermediate.Register.get r1 iregs
       = Ptr (Pointer.component ipc, bp, op) ->
     Memory.Memory.load imem (Pointer.component ipc, bp, op)
       = Some v ->
     amap_get bmap (Pointer.component ipc) bp = Some base ->
     getm (Symbolic.mem ms)
       (@word_of_nat (word_size mt) (base + Z.to_nat op))
       = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
     forall (tpc : Pointer.t) (gps' : list Pointer.t),
       gps = tpc :: gps' ->
       exists (Cprocs' : NMap Machine.code) (j' : nat)
              (P0' : Procedure.id) (Pcode' : Machine.code),
         [/\ Intermediate.prog_procedures
               (Intermediate.program_link a b)
               (Pointer.component tpc) = Some Cprocs',
             Pointer.block tpc
               = proc_nb0 (Intermediate.program_link a b)
                   (Pointer.component tpc) + j',
             List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode'),
             (0 <= Pointer.offset tpc)%Z
           & w2 = @word_of_nat (word_size mt)
                    (side_flat_pos L P C a b (Pointer.component tpc)
                       P0' Pcode' (Z.to_nat (Pointer.offset tpc))
                     + size (initial_memory (mt := mt)
                               (unionm (Intermediate.prog_buffers a)
                                  (Intermediate.prog_buffers b))))]
         /\ (exists i'',
               List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
               = Some i'')
         /\ (~~ nilp gps' ->
             dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
         /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                   then LRC.InternalJump
                   else LRC.Ret (cross_frames (Pointer.component tpc)
                                   gps'))) ->
  (forall bmap gps imem iregs ipc ms Cprocs P0 Pcode op r1 r2 r3,
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.prog_procedures
      (side_of a b (Pointer.component ipc))
      (Pointer.component ipc) = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
      = Some (IBinOp op r1 r2 r3) ->
    (forall a0, getm (Symbolic.regs ms)
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat r1)) = Some a0 ->
       taga a0 = LRC.Other)
    /\ (forall a0, getm (Symbolic.regs ms)
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat r2)) = Some a0 ->
       taga a0 = LRC.Other)) ->
  (forall bmap gps imem iregs ipc ms v0 r,
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IConst v0 r) ->
    val_rel_b bmap (imm_to_val v0)
      (swcast (convert_value (mt := mt)
         (memory_lengths (Intermediate.prog_buffers
            (side_of a b (Pointer.component ipc)))) v0))) ->
  (forall bmap gps imem iregs ipc ms op r1 r2 r3 w1 w2,
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IBinOp op r1 r2 r3) ->
    val_rel_b bmap (Intermediate.Register.get r1 iregs) w1 ->
    val_rel_b bmap (Intermediate.Register.get r2 iregs) w2 ->
    val_rel_b bmap
      (eval_binop op (Intermediate.Register.get r1 iregs)
         (Intermediate.Register.get r2 iregs))
      (binop_denote (Merged.binop_trans op) w1 w2)) ->
  (forall bmap gps imem iregs ipc ms r l zv w,
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int zv ->
    (zv <> 0)%Z ->
    val_rel_b bmap (Int zv) w ->
    (w == 0%w) = false) ->
  (forall bmap gps imem iregs ipc ms r1 r2 bp op v,
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (ILoad r1 r2) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.load imem (Pointer.component ipc, bp, op)
      = Some v ->
    (0 <= op)%Z /\
    (r2 <> R_RA ->
     forall base a0,
        amap_get bmap (Pointer.component ipc) bp = Some base ->
        getm (Symbolic.mem ms)
          (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some a0 ->
        vtag (taga a0) = LRC.Other
        \/ (vtag (taga a0) = LRC.Invalidated /\ v = Undef))) ->
  (forall bmap gps imem imem' iregs ipc ms r1 r2 bp op,
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IStore r1 r2) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.store imem (Pointer.component ipc, bp, op)
      (Intermediate.Register.get r2 iregs) = Some imem' ->
    [/\ (0 <= op)%Z,
        (r2 <> R_RA ->
         forall base a0,
            amap_get bmap (Pointer.component ipc) bp = Some base ->
            getm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
            = Some a0 ->
            vtag (taga a0) = LRC.Other)
      & (forall base a0,
            amap_get bmap (Pointer.component ipc) bp = Some base ->
            getm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
            = Some a0 ->
            vtag (taga a0) = LRC.Other
            \/ vtag (taga a0) = LRC.Invalidated)]) ->
  (forall bmap gps imem iregs ipc ms z w t,
    ireach a b (gps, imem, iregs, ipc) ->
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.Register.get R_COM iregs = Int z ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt)
         (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
    Symbolic.convert (word.int_of_word w) = z) ->
  (forall bmap gps imem imem' iregs ipc ms rptr rsize szZ bI wsz v4
          (t4 : LRC.value_tag),
    lin_match L P C a b (sinv_inst L P C a b) bmap gps imem iregs ipc
      ms ->
    Intermediate.GlobalEnv.executing
      (Intermediate.GlobalEnv.prepare_global_env
         (Intermediate.program_link a b)) ipc (IAlloc rptr rsize) ->
    Intermediate.Register.get rsize iregs = Int szZ ->
    Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
      = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt)
         (Merged.to_nat_bis (inl rsize)))
      = Some (wsz@LRC.Other) ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt)
         (Merged.to_nat_bis (inl R_RA)))
      = Some (v4@t4) ->
    exists st4 : @Symbolic.state mt LRC.lrc_tags unit,
      [/\ getm (Symbolic.mem ms) (word_of_nat Merged.alloc_label)
            = None,
          code_region_ok L P C a b (Symbolic.mem st4),
          amap_get bmap (Pointer.component ipc) bI = None,
          (forall Cprocs P0 Pcode,
              Intermediate.prog_procedures
                (side_of a b (Pointer.component ipc))
                (Pointer.component ipc) = Some Cprocs ->
              getm Cprocs P0 = Some Pcode ->
              List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
                = Some (IAlloc rptr rsize) ->
              LRC.alloc_fun (NC := NC)
                (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                   (setm (setm (setm (setm (Symbolic.regs ms)
                      (@word_of_nat (reg_field_size mt)
                         (Merged.to_nat_bis (inr Merged.R_SC_ARG1)))
                      (wsz@LRC.Other))
                      (@word_of_nat (reg_field_size mt)
                         (Merged.to_nat_bis (inl R_RA)))
                      (v4@(if LRC.is_address t4 then LRC.Invalidated
                           else LRC.Other)))
                      (@word_of_nat (reg_field_size mt)
                         (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
                      (v4@t4))
                      (@word_of_nat (reg_field_size mt)
                         (Merged.to_nat_bis (inl R_RA)))
                      ((word_of_nat
                          ((side_flat_pos L P C a b
                              (Pointer.component ipc) P0 Pcode
                              (Z.to_nat (Pointer.offset ipc)) + 3)
                           + size (initial_memory (mt := mt)
                                     (unionm
                                        (Intermediate.prog_buffers a)
                                        (Intermediate.prog_buffers
                                           b)))))
                         @LRC.InternalJump))
                   ((word_of_nat Merged.alloc_label)
                      @(LRC.Level
                          (cross_frames (Pointer.component ipc) gps)
                          (Pointer.component ipc))) tt)
              = Some st4)
        & (forall (max : mword mt) (len : nat),
              0 < len ->
              Symbolic.mem st4
              = unionm (Symbolic.mem ms)
                  (mkfmap (mkseq (fun n =>
                     ((max + as_word (ssrint.Posz (n + 1)))%w,
                      (as_word (ssrint.Posz 0))
                        @(LRC.def_mem_tag (Pointer.component ipc)
                            false))) len)) ->
              mem_rel (amap_set bmap (Pointer.component ipc) bI
                         ((eqtype.val max).+1)) imem'
                (Symbolic.mem st4))
          /\ (forall w a0,
                getm (Symbolic.mem ms) w = Some a0 ->
                getm (Symbolic.mem st4) w = Some a0)]) ->
  forall
    (Hjumptie : forall gps imem iregs (pc pc' : Pointer.t),
        ireach a b (pc' :: gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc IJump ->
        forall (f : option (Block.id * Z))
               (fbs' : list (option (Block.id * Z)))
               (Cprocs' : NMap Machine.code) (j' : nat)
               (P0' : Procedure.id) (Pcode' : Machine.code),
          iframes imem (pc' :: gps) (f :: fbs') ->
          Intermediate.prog_procedures (Intermediate.program_link a b)
            (Pointer.component pc') = Some Cprocs' ->
          Pointer.block pc'
            = proc_nb0 (Intermediate.program_link a b)
                (Pointer.component pc') + j' ->
          List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
          (0 <= Pointer.offset pc')%Z ->
          dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
          exists fb sl,
            [/\ f = Some (fb, sl),
                ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
                  = false
              & Intermediate.Register.get R_SP iregs
                = Ptr (Pointer.component pc', fb,
                       (sl + sp_scan Pcode' 0%Z
                               (Z.to_nat (Pointer.offset pc')))%Z)])
    (Hreturntie : forall gps imem iregs (pc pc' : Pointer.t),
        ireach a b (pc' :: gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc IReturn ->
        forall (f : option (Block.id * Z))
               (fbs' : list (option (Block.id * Z)))
               (Cprocs' : NMap Machine.code) (j' : nat)
               (P0' : Procedure.id) (Pcode' : Machine.code),
          iframes imem (pc' :: gps) (f :: fbs') ->
          Intermediate.prog_procedures (Intermediate.program_link a b)
            (Pointer.component pc') = Some Cprocs' ->
          Pointer.block pc'
            = proc_nb0 (Intermediate.program_link a b)
                (Pointer.component pc') + j' ->
          List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
          (0 <= Pointer.offset pc')%Z ->
          dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
          exists fb sl,
            [/\ f = Some (fb, sl),
                ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
                  = true
              & Memory.Memory.load imem
                  (Pointer.component (scr_def (Pointer.component pc')),
                   Pointer.block (scr_def (Pointer.component pc')),
                   Pointer.offset (scr_def (Pointer.component pc')))
                = Some (Ptr (Pointer.component pc', fb,
                             (sl + sp_scan Pcode' 0%Z
                                     (Z.to_nat
                                        (Pointer.offset pc')))%Z))])
    (Hstoresep : forall gps imem iregs (pc : Pointer.t) r1 r2 bp op
                        (Cprocs : NMap Machine.code) (j : nat)
                        (P0 : Procedure.id) (Pcode : Machine.code),
        ireach a b (gps, imem, iregs, pc) ->
        Intermediate.GlobalEnv.executing
          (Intermediate.GlobalEnv.prepare_global_env
             (Intermediate.program_link a b)) pc (IStore r1 r2) ->
        Intermediate.prog_procedures (Intermediate.program_link a b)
          (Pointer.component pc) = Some Cprocs ->
        Pointer.block pc
          = proc_nb0 (Intermediate.program_link a b)
              (Pointer.component pc) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        Intermediate.Register.get r1 iregs
          = Ptr (Pointer.component pc, bp, op) ->
        (forall fb spo,
           Intermediate.Register.get R_SP iregs
             = Ptr (Pointer.component pc, fb, spo) ->
           bp <> fb
           \/ op <> (spo - sp_scan Pcode 0%Z
                             (Z.to_nat (Pointer.offset pc)))%Z)
        /\ (forall fbs, iframes imem gps fbs ->
              frames_sep gps fbs (Pointer.component pc) bp))
    ,
  sim_residual L P C a b NC (sinv_inst L P C a b).
Proof.
move=> Hca Hcb Hwfsa Hwfsb Hiface Hwf Hcl Hfiti
  Hlab_a Hcomp_a Hlab_b Hcomp_b Hproc_a Hproc_b
  Hdisj Huniq_a Huniq_b Hfitc Hfitm Hload Hloadra Hdef
  Himm Hbinop Hbnznz Hoload Hostore Hconv Hoalloc
  Hjumptie Hreturntie Hstoresep.
have Hexa : exists pa, compile_program pa = Some a by exists sa.
have Hexb : exists pb, compile_program pb = Some b by exists sb.
have Hexwa : exists pa, Source.well_formed_program pa
                        /\ compile_program pa = Some a
  by exists sa.
have Hexwb : exists pb, Source.well_formed_program pb
                        /\ compile_program pb = Some b
  by exists sb.
have Hshape := linked_code_shape Hexa Hexb.
have Hjal := linked_jal_target Hexa Hexb.
have Hreload := sr_reload_inst Hexa Hexb Hwf Hcl.
have Hraud := @sr_ra_undef_inst L P C a b (sinv_inst L P C a b)
  scr_def
  (iinv_runs_inst Hexa Hexb Hwf Hcl Hreload Hjumptie
     Hreturntie Hstoresep).
have Hbnzlab := @sr_bnz_lab_inst L P C a b (sinv_inst L P C a b)
  Hexa Hexb Hwf Hcl Hfiti.
have Hjallab := @sr_jal_lab_inst L P C a b (sinv_inst L P C a b)
  Hwf Hcl Hfiti.
have Hjaldead := @sr_jal_dead_inst L P C a b (sinv_inst L P C a b)
  Hexa Hexb Hwf
  (stub_nolabel_c_inst Hwf Hcl) (stub_nolabel_p_inst Hwf Hcl)
  (stub_noentry_inst Hexwa Hexwb Hiface Hwf).
have Hocall := @sr_call_inst L P C a b (sinv_inst L P C a b)
  Hexa Hexb Hiface Hwf Hfiti.
constructor => //.
- exact: (sinv_inst_spec_wf Hwf Hcl Hshape Hjal Hload).
- move=> bM bmap0 imem0 iregs0 ms0.
  apply: sinv_inst_init.
  have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget.
- exact: (sr_ra_inst Hca Hcb).
Qed.

Corollary sim_residual_exists_inst (L P C NC : nat)
    (a b : Intermediate.program) :
  sim_residual L P C a b NC (sinv_inst L P C a b) ->
  exists SINV, sim_residual L P C a b NC SINV.
Proof. move=> R. by exists (sinv_inst L P C a b). Qed.


Require Import MicroPolicies.Recomposition.RSCSigs.
Require Import MicroPolicies.KInstance.

Module Type SimResidualSig (B : LinBoundsSig).
  Module S := KStatics B.

  Axiom sim_residual_exists : forall a b : Intermediate.program,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    linkable (Intermediate.prog_interface a)
             (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    (exists sa, Source.well_formed_program sa
                /\ compile_program sa = Some a) ->
    (exists sb, Source.well_formed_program sb
                /\ compile_program sb = Some b) ->
    exists SINV, sim_residual B.L B.P B.C a b S.NC SINV.

  Parameter bt_fits :
    Intermediate.program -> Intermediate.program -> Events.trace -> Prop.

  Axiom H_bt : forall a b (m0 : finpref_behavior),
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    S.lin_ok a -> S.lin_ok b ->
    linkable (Intermediate.prog_interface a)
             (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (rub_sem S.NC (Intermediate.prog_interface a)
                            (Intermediate.prog_interface b)
                            (program_link (S.lin a) (S.lin b)))
                m0 ->
    not_wrong_finpref m0 ->
    bt_fits a b (finpref_trace m0) ->
    bt_package S.NC S.lin S.lin_ok a b m0.
End SimResidualSig.

Module KDynamicsFromSim (B : LinBoundsSig) (D : SimResidualSig B)
  <: KDynamicsSig B.
  Module S := KStatics B.

  Theorem H_bwd : forall a b m,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    S.lin_ok a -> S.lin_ok b ->
    linkable (Intermediate.prog_interface a)
             (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    (exists sa, Source.well_formed_program sa
                /\ compile_program sa = Some a) ->
    (exists sb, Source.well_formed_program sb
                /\ compile_program sb = Some b) ->
    does_prefix (me_sem S.NC (program_link (S.lin a) (S.lin b))) m ->
    exists beh,
      program_behaves (CS.sem (Intermediate.program_link a b)) beh
      /\ (CompCertExtensions.prefix m beh
          \/ behavior_improves_finpref beh m).
  Proof.
    move=> a b m Hwfa Hwfb _ _ Hlink Hcl Hca Hcb Hdp.
    exact: (H_bwd_from_sim D.sim_residual_exists Hwfa Hwfb Hlink Hcl
              Hca Hcb Hdp).
  Qed.

  Definition bt_fits := D.bt_fits.
  Definition H_bt := D.H_bt.
End KDynamicsFromSim.

Module KConcreteFromSim (B : LinBoundsSig) (D : SimResidualSig B)
  <: MPCompilerSig.
  Module KD := KDynamicsFromSim B D.
  Include KConcrete B KD.
End KConcreteFromSim.

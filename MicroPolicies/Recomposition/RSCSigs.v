(* The assumption layer for RSC^DC_MD at the micro-policy machine level.
   [MPCompilerSig] abstracts the Intermediate -> MP linearizer and its
   correctness; [RSC_MP_Input] packages the premises of the final theorem. *)

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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.RSCDefs.

Import DoNotation.
Import Types.

(* The back-translation package for a trace [t] of the UB-restricted run of
   [link (lin a) (lin b)]: [bt_Cs] becomes the final theorem's witness. *)
Record bt_package (NC : nat) (lin : Intermediate.program -> program)
       (lin_ok : Intermediate.program -> Prop)
       (run_ok : Intermediate.program -> Intermediate.program ->
                 Events.trace -> Prop)
       (a b : Intermediate.program) (m0 : finpref_behavior) : Type := {
  bt_Cs   : Source.program;
  bt_P'   : Source.program;
  bt_ip'  : Intermediate.program;
  bt_ic'  : Intermediate.program;

  bt_Cs_wf : Source.well_formed_program bt_Cs;
  bt_P'_wf : Source.well_formed_program bt_P';
  bt_Cs_iface : Source.prog_interface bt_Cs = Intermediate.prog_interface b;
  bt_P'_iface : Source.prog_interface bt_P' = Intermediate.prog_interface a;

  bt_compile_P' : compile_program bt_P' = Some bt_ip';
  bt_compile_Cs : compile_program bt_Cs = Some bt_ic';

  bt_ip'_ok : lin_ok bt_ip';
  bt_ic'_ok : lin_ok bt_ic';

  bt_ip'_buffers : bufs_shape (Intermediate.prog_buffers bt_ip')
                   = bufs_shape (Intermediate.prog_buffers a);
  bt_ic'_buffers : bufs_shape (Intermediate.prog_buffers bt_ic')
                   = bufs_shape (Intermediate.prog_buffers b);

  bt_Cs_mmains : matching_mains bt_Cs b;

  bt_src_closed : Source.closed_program (Source.program_link bt_P' bt_Cs);
  bt_src_run : does_prefix (S.CS.sem (Source.program_link bt_P' bt_Cs)) m0;

  bt_run : does_prefix (me_sem NC (program_link (lin bt_ip') (lin bt_ic')))
                       m0;

  bt_runok'' : run_ok a bt_ic' (finpref_trace m0);

  bt_size' :
    size (linearize_bufs (unionm (prog_buffers (lin bt_ip'))
                                 (prog_buffers (lin bt_ic'))))
      + size (code (lin bt_ip') ++ code (lin bt_ic')) < alloc_label;
  bt_size'' :
    size (linearize_bufs (unionm (prog_buffers (lin a))
                                 (prog_buffers (lin bt_ic'))))
      + size (code (lin a) ++ code (lin bt_ic')) < alloc_label;
}.

Module Type MPCompilerSig.

  Parameter NC : nat.
  Axiom NC_lt_word : NC < word_size mt.
  Axiom alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).

  (* the Intermediate → MP linearizer, abstracted *)
  Parameter lin : Intermediate.program -> program.

  Parameter lin_ok : Intermediate.program -> Prop.

  (* ---- static preservation ---- *)
  Axiom lin_interface : forall a,
    prog_interface (lin a) = Intermediate.prog_interface a.
  Axiom lin_buffers : forall a,
    prog_buffers (lin a) = Intermediate.prog_buffers a.
  Axiom lin_main : forall a,
    prog_main (lin a)
    = (Component.main \in domm (Intermediate.prog_interface a)).
  Axiom lin_wf : forall a,
    Intermediate.well_formed_program a -> lin_ok a ->
    well_formed_program (lin a).
  Axiom lin_out_wf : forall a,
    Intermediate.well_formed_program a -> lin_output_wf (lin a).

  (* label spaces of interface-disjoint programs are disjoint *)
  Axiom lin_labels_disjoint : forall a b,
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    lin_ok a -> lin_ok b ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    forall l, findopt (is_label_def l) (code (lin a)) <> None ->
              findopt (is_label_def l) (code (lin b)) = None.

  Axiom lin_jal_cross : forall a b b',
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    Intermediate.well_formed_program b' ->
    lin_ok a -> lin_ok b -> lin_ok b' ->
    fdisjoint (domm (Intermediate.prog_interface a))
              (domm (Intermediate.prog_interface b)) ->
    closed_interface (unionm (Intermediate.prog_interface a)
                             (Intermediate.prog_interface b)) ->
    Intermediate.prog_interface b = Intermediate.prog_interface b' ->
    forall n l t,
      nth_error (code (lin a)) n = Some (@MrJal mt l, t) ->
      l <> alloc_label ->
      findopt (is_label_def l) (code (lin a)) = None ->
      exists mb mb' (i i' : @Merged.instr mt) (tc : mem_tag),
        [/\ findopt (is_label_def l) (code (lin b)) = Some mb,
            findopt (is_label_def l) (code (lin b')) = Some mb',
            nth_error (code (lin b)) mb = Some (i, tc)
            /\ nth_error (code (lin b')) mb' = Some (i', tc)
          & is_code tc /\ color tc \in domm (Intermediate.prog_interface b)].

  (* ---- the pair-level run-fit ---- *)
  Parameter run_ok :
    Intermediate.program -> Intermediate.program -> Events.trace -> Prop.

  (* ---- backward compiler correctness (overlay -> Source) ---- *)
  Axiom H_bwd_src : forall (sa sb : Source.program)
      (a b : Intermediate.program) m,
    Source.well_formed_program sa ->
    Source.well_formed_program sb ->
    Source.closed_program (Source.program_link sa sb) ->
    compile_program sa = Some a ->
    compile_program sb = Some b ->
    lin_ok a -> lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (me_sem NC (program_link (lin a) (lin b))) m ->
    run_ok a b (finpref_trace m) ->
    exists beh,
      program_behaves (S.CS.sem (Source.program_link sa sb)) beh
      /\ (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).

  (* ---- the finite-machine fit ---- *)
  Parameter bt_fits :
    Intermediate.program -> Intermediate.program -> Events.trace -> Prop.

  (* ---- the back-translation package ---- *)
  Axiom H_bt : forall a b (m0 : finpref_behavior),
    Intermediate.well_formed_program a ->
    Intermediate.well_formed_program b ->
    lin_ok a -> lin_ok b ->
    linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b) ->
    Intermediate.closed_program (Intermediate.program_link a b) ->
    does_prefix (rub_sem NC (Intermediate.prog_interface a)
                            (Intermediate.prog_interface b)
                            (program_link (lin a) (lin b)))
                m0 ->
    not_wrong_finpref m0 ->
    bt_fits a b (finpref_trace m0) ->
    bt_package NC lin lin_ok run_ok a b m0.

End MPCompilerSig.

Module Type RSC_MP_Input (K : MPCompilerSig).

  Parameter p : Source.program.
  Parameter p_compiled : Intermediate.program.
  Parameter Ct : Intermediate.program.
  Parameter fm : finpref_behavior.

  (* the reasonable assumptions of RSC_DC_MD, one level down *)
  Axiom well_formed_p : Source.well_formed_program p.
  Axiom successful_compilation : compile_program p = Some p_compiled.
  Axiom well_formed_Ct : Intermediate.well_formed_program Ct.
  Axiom linkability :
    linkable (Source.prog_interface p) (Intermediate.prog_interface Ct).
  Axiom closedness :
    Intermediate.closed_program (Intermediate.program_link p_compiled Ct).
  Axiom mains : Intermediate.linkable_mains p_compiled Ct.
  Axiom p_ok : K.lin_ok p_compiled.
  Axiom Ct_ok : K.lin_ok Ct.

  (* static side conditions of the component-prefix memory scheme *)
  Axiom comp_bound : forall x,
    (x \in domm (Intermediate.prog_interface p_compiled))
    || (x \in domm (Intermediate.prog_interface Ct)) ->
    1 + x < 2 ^ K.NC.
  Axiom size_fit :
    size (linearize_bufs (unionm (prog_buffers (K.lin p_compiled))
                                 (prog_buffers (K.lin Ct))))
      + size (code (K.lin p_compiled) ++ code (K.lin Ct)) < alloc_label.

  (* the observed safe target prefix *)
  Axiom target_prefix :
    does_prefix (mp_sem K.NC (program_link (K.lin p_compiled) (K.lin Ct))) fm.
  Axiom safe_prefix : not_wrong_finpref fm.

  Axiom prefix_fits : forall t,
    trace_finpref_prefix t fm -> K.bt_fits p_compiled Ct t.

End RSC_MP_Input.

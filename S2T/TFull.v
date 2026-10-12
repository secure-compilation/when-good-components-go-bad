(** * The S → T forward simulation, stated in full.

    See plan-i2t-redo.md.

    This file exists to say, in one theorem and with no abstract section
    variables left standing, exactly what the campaign has proved:

      a well-formed closed source program `p` that compiles to `tp` is
      forward-simulated by the Transitional machine running the linearized
      compiled code.

    Everything the statement mentions is CONCRETE:

    - the target code is `Transitional.intermediate_to_transitional tp` — the
      actual linearizer applied to the actual compiler output, not a parameter;
    - the interface is `Source.prog_interface p`;
    - the label map is `S2I/Simulation.v`'s own `labelsP p`;
    - the target semantics is `TSim.t_sem`, whose initial states are the real
      `Transitional.Memory.prepare_procedures_initial_memory tp` and
      `Transitional.Register.init` at main's resolved procedure header, closed
      under silent setup steps.

    There are NO residual premises: well-formed + closed + compiles is the
    whole hypothesis list. What it took to get there is at the bottom of the
    file. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TDrain.
Require Import S2T.TSim.
Require Import S2T.TStatic.
Require Import S2T.TStart.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.

Module TFull.

(* ================================================================== *)
(* ★ The theorem                                                       *)
(* ================================================================== *)

Theorem s2t_forward_simulation (p : Source.program)
                               (tp : Intermediate.program) :
  (* --- the program is a real, closed, well-formed source program that the
         S2I compiler accepts --- *)
  Source.well_formed_program p ->
  Source.closed_program p ->
  compile_program p = Some tp ->
  (* --- …and the source program is simulated by the T machine running the
         linearized compiled code --- *)
  forward_simulation
    (S.CS.sem p)
    (TSim.t_sem (Transitional.intermediate_to_transitional tp) tp).
Proof.
  move=> Hwf Hclosed Hcomp.
  have Huniq := TStatic.labels_uniq_compiled Hcomp.
  have Hee : TSim.entry_ext (Transitional.intermediate_to_transitional tp)
               (Source.prog_interface p) (labelsP p) p.
  { move=> C Cf P P_expr HneC Him Hfind.
    case: (TStatic.entry_ext_whole_any Hwf Hclosed Hcomp Him Hfind)
      => [Hdom [pcW [tniW [plmf [pl [pcE [cbody [sA [sB
         [[Hfd Hex Hchk Hplm] Hwrap EcE Hce HcodeE]]]]]]]]]].
    split; first exact: Hdom.
    by exists pcW, tniW, plmf, pl, pcE, sA, sB, cbody; split=> //; split. }
  apply: (TSim.t_forward_simulation (iface := Source.prog_interface p) _ Hee).
  - (* [entry_int] — Stage 3, DISCHARGED for EVERY callee, [(main, main)]
       included (`entry_int_whole_any`) *)
    move=> C P P_expr plm tl Hfind Hplm Htl.
    case: (TStatic.entry_int_whole_any Hwf Hcomp Hfind Hplm Htl)
      => [pcE [cbody [sA [sB [EcE Hce Hcode]]]]].
    by exists pcE, sA, sB, cbody.
  - (* the [labelsP]-domain fact — Stage 3, DISCHARGED *)
    move=> C0 plm0 Hg. exact: (TStatic.labelsP_domm Hwf Hg).
  - (* the initial bridge — Stage 3/5, DISCHARGED *)
    apply: (TStart.start_ok_proof Hwf Hclosed Hcomp _ Huniq).
    by rewrite (compilation_preserves_interface _ _ Hcomp).
Qed.

(** ** No residual premises

    The three that used to be here are all discharged:

    - **`labels_uniq`** — `TStatic.labels_uniq_compiled`, from
      `S2I/LabelUniq.v:834`'s `compiled_labels_unique` through `count_flatten`.
      Procedure HEADERS are `TrLabel (inr _)` and are not counted, which is
      what makes flattening a component's procedures into one array safe.

    - **`entry_int`** — `TStatic.entry_int_whole_any`, every callee including
      `(main, main)`. `compile_proc_shape_main_gen` keeps the halt pad symbolic
      instead of assuming it away.

    - **`entry_ext`** — `TStatic.entry_ext_whole_any`. Three things had to
      change, and each was a genuine defect rather than plumbing:

      1. It was stated too weakly to be provable: its conclusion carries the
         LRC `check_pc_call`, which needs the CALLER's import fact.
         `imported_procedure` is now a premise — `Source/CS.v`'s
         `KS_ExternalCall` carries it, so it is available at every use — and
         `closed_interface` turns it into the callee's export half.

      2. It was FALSE at `(main, main)`: `compile_proc` gives that procedure a
         DUAL entry (the flag protocol), not the standard wrapper, and nothing
         forbids importing it. The wrapper clause is now a disjunction;
         `TProlog.flag_protocol_taken_run` runs the branch-TAKEN path,
         `ef_main_cross_entry_run` composes it onto `ef_entry_run`'s shared
         prefix, and `ef_call_entry_run` gives `diagram_call_ext` ONE interface
         over both — abstract `spE`, and it exports the `ext_frame_match`
         CONSTRUCTION rather than the two epilogue shapes.

      3. It was false a SECOND way at `(main, main)`: with an immediately-final
         main, `compile_proc` puts the HALT PAD first, so neither wrapper is
         the cell past the header. There is a third disjunct for that, and the
         diagram kills it from `TMatch.main_anchored` — a new invariant field
         saying main's wrapper sits one cell past main's header. That is a
         reachability fact in disguise (an immediately-final main means the
         source's initial state is already final, so no other component ever
         runs), and being in a state satisfying the invariant at all is exactly
         the evidence that the machine got past the pad.

    Two invariant strengthenings fell out and are worth naming: `TSM.scrs_ok`'s
    flag clause now carries the cell's TAG as well as its value (main's `ILoad`
    feeds that tag to an `IBnz`, which MP refuses unless it is `Other`), and
    `expr_inv`/`val_inv` carry `main_anchored`. *)

End TFull.

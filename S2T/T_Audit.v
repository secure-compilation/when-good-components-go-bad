(** * Stage 0 — falsification gate for the S→T tag invariant.

    Standalone harness — NOT in [_CoqProject]. It runs the REAL pipeline
    ([Source.program] --S2I--> Intermediate --> Transitional) on sample source
    programs, executes the Transitional machine with [eval_step], and evaluates
    a boolean form of the proposed [tag_inv] at EVERY step.

    Compile with:
      timeout 600 coqc -R . RobustImp S2T/T_Audit.v

    The point (see plan-i2t-redo.md §4, Stage 0): the previous Pass-1 design had
    7 of 81 assumed facts turn out FALSE only after they had shaped the
    invariant. Here the invariant is tested by execution before any proof is
    written. A [Violation] result names the first offending step and dumps the
    evidence; [Clean] means the invariant survived the whole run.

    What is checked, per state (plan §2.3):

      T4-regs  every register EXCEPT R_RA carries tag [Other]
      T4-mem   the cells carrying a non-[Other] tag are reported (they should be
               exactly the live return-address spill slots)
      T1       a non-[Other] tag always sits on a [Ptr] (a capability is an
               address)
      T3       the live [Ret k] capabilities are pairwise distinct, and those in
               MEMORY satisfy [k < level pct]

    Registers are exempted from the [k < level] bound on purpose: [JumpRet]
    calls [Register.invalidate], which KEEPS [R_RA] — so a just-consumed
    [Ret n] husk survives in the register file at [Level n]. Whether that is
    benign is one of the things this harness is here to show.

    Also reported: cells where the tvalue's [tvtag] and the mem_tag's [vtag]
    disagree. They are kept in sync by [eval_step], so a nonempty list here
    would be a genuine surprise — and it measures the blast radius of defect
    §3.1 (the relational [Load] rule stores [tvtag := Other] where [eval_step]
    stores [ts']). *)

Require Import Common.Definitions.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Set Implicit Arguments.

(* ================================================================== *)
(* 1. Sample source programs                                          *)
(* ================================================================== *)

(* Interfaces shared by the samples: [main] exports {2} and imports (2,1);
   component 2 exports {1} and imports (main,2). Mutual recursion across the
   boundary is therefore available, which is what makes re-entrancy reachable. *)
Definition iface : Program.interface :=
  mkfmap [:: (Component.main,
              {| Component.export := fset [:: 2];
                 Component.import := fset [:: (2, 1)] |});
             (2, {| Component.export := fset [:: 1];
                    Component.import := fset [:: (Component.main, 2)] |})].

Definition bufs : NMap (nat + list value) :=
  mkfmap [:: (Component.main, inl 4); (2, inl 4)].

(** Sample 1 — nested / re-entrant calls: main → 2 → 2 → main → …
    This is [Source/Examples/NestedCalls.v]'s program. It is the sample that
    exercises A → B → A re-entrancy, i.e. a second activation of a component
    beginning while an earlier one is suspended. *)
Definition p_nested : Source.program :=
  Source.mkProg iface
    (mkfmap [:: (Component.main,
                 mkfmap [:: (Procedure.main,
                             E_binop Add (E_val (Int 1))
                                     (E_call 2 1 (E_val (Int 1))));
                            (2, E_arg)]);
                (2, mkfmap [:: (1, E_binop Add E_arg
                                       (E_call 2 2 (E_arg)));
                               (2, E_binop Add E_arg
                                       (E_call Component.main 2 (E_arg)))])])
    bufs.

(** Sample 2 — mixed constructs: assign, deref, if, binop, cross-call. *)
Definition p_mixed : Source.program :=
  Source.mkProg iface
    (mkfmap [:: (Component.main,
                 mkfmap [:: (Procedure.main,
                             E_seq (E_assign E_local (E_val (Int 7)))
                                   (E_binop Add (E_deref E_local)
                                            (E_call 2 1 (E_val (Int 1)))));
                            (2, E_binop Mul E_arg (E_val (Int 2)))]);
                (2, mkfmap [:: (1, E_if E_arg
                                     (E_call Component.main 2 E_arg)
                                     (E_val (Int 0)))])])
    bufs.

(** Sample 3 — heap allocation, and an INTRA-component call (the [IJal] /
    [push R_RA] / [pop R_RA] bracket, which is the case Pass 1 turns on). *)
Definition p_alloc : Source.program :=
  Source.mkProg iface
    (mkfmap [:: (Component.main,
                 mkfmap [:: (Procedure.main,
                             E_seq (E_assign (E_alloc (E_val (Int 2)))
                                             (E_val (Int 5)))
                                   (E_call Component.main 2 (E_val (Int 3))));
                            (2, E_binop Add E_arg
                                    (E_call 2 1 (E_val (Int 1))))]);
                (2, mkfmap [:: (1, E_arg)])])
    bufs.

(* ================================================================== *)
(* 2. The boolean invariant                                           *)
(* ================================================================== *)

Definition is_other_b (t : value_tag) : bool :=
  match t with Other => true | _ => false end.

(** REVISED 2026-07-29 to match [S2T/TInv.v]'s [tag_inv] after the
    capsite redesign: the ledger tracks LIVE capabilities, and [Invalidated] is
    the DEAD marker, not a capability. *)
Definition is_live_b (t : value_tag) : bool :=
  match t with Ret _ | InternalJump => true | _ => false end.

Definition ret_of (t : value_tag) : option nat :=
  match t with Ret n => Some n | _ => None end.

Definition is_ptr_b (v : value) : bool :=
  match v with Ptr _ => true | _ => false end.

Notation addr := (nat * nat * nat)%type.

Definition cells_of_block (C b : nat) (blk : Transitional.Memory.block)
  : seq (addr * (tvalue * mem_tag)) :=
  zip [seq (C, b, i) | i <- iota 0 (size blk)] blk.

Definition all_cells (m : Transitional.Memory.t)
  : seq (addr * (tvalue * mem_tag)) :=
  flatten [seq
             flatten [seq cells_of_block Ccm.1 bbl.1 bbl.2
                     | bbl <- elementsm (Transitional.Memory.content Ccm.2)]
          | Ccm <- elementsm m].

(** [ti_regs]: registers other than R_RA (index 4) must be tagged [Other]. *)
Definition bad_regs (regs : Transitional.Register.t) : seq nat :=
  [seq kv.1 | kv <- elementsm regs
            & (kv.1 != Transitional.Register.to_nat R_RA)
              && ~~ is_other_b (tvtag kv.2)].

(** the ledger's memory sites: cells holding a LIVE capability *)
Definition live_cells (m : Transitional.Memory.t) : seq (addr * value_tag) :=
  [seq (c.1, tvtag c.2.1) | c <- all_cells m & is_live_b (tvtag c.2.1)].

Definition ra_tag (regs : Transitional.Register.t) : value_tag :=
  tvtag (Transitional.Register.get R_RA regs).

(** [ti_addr]: a live capability sits on a [Ptr]. *)
Definition cap_not_ptr (m : Transitional.Memory.t) : seq addr :=
  [seq c.1 | c <- all_cells m
           & is_live_b (tvtag c.2.1)
             && ~~ is_ptr_b (Transitional.val c.2.1)].

(** cells whose two tags disagree (diagnostic for plan §3.1) *)
Definition tag_desync (m : Transitional.Memory.t) : seq addr :=
  [seq c.1 | c <- all_cells m
           & ~~ (is_other_b (tvtag c.2.1) == is_other_b (vtag c.2.2))].

(** ★ [ti_lvl], the clause the capsite redesign introduced: the live [Ret]
    levels across BOTH memory and [R_RA] are exactly [0 .. level pct - 1].

    This is what a memory-only ledger could not express, and it is the check
    that decides whether the post-cross-return [R_RA] husk is a problem:
    [Register.invalidate] KEEPS [R_RA]'s tvalue, so a spent [Ret n] may survive
    at [Level n] — and [Ret _] is [is_live]. If that happens, this fails. *)
Definition live_rets (m : Transitional.Memory.t)
                     (regs : Transitional.Register.t) : seq nat :=
  pmap (fun c => ret_of c.2) (live_cells m)
  ++ (if is_live_b (ra_tag regs) then
        (if ret_of (ra_tag regs) is Some n then [:: n] else [::])
      else [::]).

Definition ok (s : Transitional.stackless) : bool :=
  let '(mem, regs, pc, pct) := s in
  [&& bad_regs regs == [::],
      cap_not_ptr mem == [::]
    & perm_eq (live_rets mem regs) (iota 0 (level pct))].

(* ================================================================== *)
(* 3. The instrumented run                                            *)
(* ================================================================== *)

Inductive audit_result :=
| NoCompile
| NoMain
(* survived [n] steps; [halted] says the run ended by [eval_step = None]
   (halt or stuck) rather than by running out of fuel *)
(* [maxlvl] / [maxtag] make the result NON-VACUOUS: they say the invariant was
   actually exercised (cross-component depth reached, capabilities live in
   memory), not merely never contradicted. *)
| Clean (steps : nat) (halted : bool) (maxlvl : nat) (maxtag : nat)
| Violation (step : nat)
            (badregs : seq nat)
            (capnotptr_mem : seq addr)
            (liverets : seq nat) (lvl : nat)
            (ratag_is_ret : bool) (ratag_lvl : nat)
            (livesites : seq addr) (desync : seq addr).

Definition report (i : nat) (s : Transitional.stackless) : audit_result :=
  let '(mem, regs, pc, pct) := s in
  Violation i (bad_regs regs) (cap_not_ptr mem)
              (live_rets mem regs) (level pct)
              (if ret_of (ra_tag regs) is Some _ then true else false)
              (if ret_of (ra_tag regs) is Some n then n else 0)
              [seq c.1 | c <- live_cells mem] (tag_desync mem).

Fixpoint runchk (n : nat) (cde : Transitional.code)
                (s : Transitional.stackless) (i : nat)
                (mlvl mtag : nat) : audit_result :=
  if ~~ ok s then report i s else
  let '(mem, _, _, pct) := s in
  let mlvl' := maxn mlvl (level pct) in
  let mtag' := maxn mtag (size (live_cells mem)) in
  match n with
  | 0 => Clean i false mlvl' mtag'
  | S n' =>
    match TS.eval_step cde s with   (* the RESHAPED semantics (Stage 1) *)
    | None => Clean i true mlvl' mtag'
    | Some (_, s') => runchk n' cde s' (S i) mlvl' mtag'
    end
  end.

Definition audit (p : Source.program) (fuel : nat) : audit_result :=
  match compile_program p with
  | None => NoCompile
  | Some ip =>
    let cde := Transitional.intermediate_to_transitional ip in
    let mem := Transitional.Memory.prepare_procedures_initial_memory ip in
    match Transitional.find_plabel_in_code cde Component.main Procedure.main with
    | Some pc =>
      runchk fuel cde (mem, Transitional.Register.init, pc, Level 0) 0 0 0
    | None => NoMain
    end
  end.

(* size of the initial memory, and whether the entry label resolves *)
Definition init_of (p : Source.program)
  : option (Transitional.code * Transitional.stackless) :=
  match compile_program p with
  | None => None
  | Some ip =>
    let cde := Transitional.intermediate_to_transitional ip in
    match Transitional.find_plabel_in_code cde Component.main Procedure.main with
    | Some pc =>
      Some (cde, (Transitional.Memory.prepare_procedures_initial_memory ip,
                  Transitional.Register.init, pc, Level 0))
    | None => None
    end
  end.

Definition ncells (p : Source.program) : option nat :=
  match init_of p with
  | Some (_, (m, _, _, _)) => Some (size (all_cells m))
  | None => None
  end.

(* ================================================================== *)
(* 4. Running it                                                      *)
(* ================================================================== *)

(* [vm_compute] CANNOT run this pipeline: [linearize_component] and
   [prepare_procedures_initial_memory] both go through [domm], whose result is
   an [fset], and extructures locks [fset] behind the opaque [fset_key].
   ([elementsm]-based probes do reduce; [domm]-based ones do not.) Unlocking it
   would need [Transparent fset_key], which is off-limits here.

   So the harness runs the way the rest of this project runs executable code:
   by extraction. *)

Definition FUEL := 3000.

(* End-to-end sanity: the value the run actually produces. A harness that
   reports [Clean] because the machine got STUCK at step 3 would be worthless,
   so we check the run computes the right answer.
   [p_nested]: main = 1 + (2.1 1); 2.1 a = a + (2.2 a); 2.2 a = a + (main.2 a);
   main.2 = a. So 2.2 1 = 2, 2.1 1 = 3, main = 4. *)
Definition value_of (p : Source.program) : option Z + nat :=
  match compile_program p with
  | Some ip => Transitional.compile_run FUEL ip
  | None => inr 9
  end.

Definition v_nested := value_of p_nested.
Definition v_mixed  := value_of p_mixed.
Definition v_alloc  := value_of p_alloc.

Definition r_nested := audit p_nested FUEL.
Definition r_mixed  := audit p_mixed  FUEL.
Definition r_alloc  := audit p_alloc  FUEL.

Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_taudit.ml" r_nested r_mixed r_alloc v_nested v_mixed v_alloc.

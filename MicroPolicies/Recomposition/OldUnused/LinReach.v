(* I-side reachability invariants for the linked compiled program.

   Phase 1: the stub-bottom invariant — the wrap-main stub only ever
   runs at the bottom of the call stack, discharging the naked-jal
   window oracle [sr_jal_dead].  Two interface Hypotheses isolate the
   entry/label exclusion facts (verified true of the compiled layout;
   discharged by a later increment). *)

Require Import Common.Definitions.
Require Import Common.Memory.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.

Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Source.Language.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import MicroPolicies.Recomposition.LinPos.
Require Import MicroPolicies.Recomposition.LinGenv.
Require Import MicroPolicies.Recomposition.LinSim.
Require Import MicroPolicies.Recomposition.LinInv.
Require Import MicroPolicies.Recomposition.LinShape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section LinReach.

Variables pra prb : Intermediate.program.

Local Notation ilp := (Intermediate.program_link pra prb).
Local Notation G := (Intermediate.GlobalEnv.prepare_global_env ilp).

(* a stub block: its procedure body is the wrap-main literal *)
Definition stub_blk (cid : Component.id) (b : Block.id) : Prop :=
  exists (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id)
         (lab : label),
    [/\ Intermediate.prog_procedures ilp cid = Some Cprocs,
        b = proc_nb0 ilp cid + j
      & List.nth_error (elementsm Cprocs) j
        = Some (P0, [:: IConst (IInt 1) R_ONE; IJal lab; IHalt])].

Definition stub_pc (pc : Pointer.t) : Prop :=
  stub_blk (Pointer.component pc) (Pointer.block pc).

Lemma stub_pc_inc (pc : Pointer.t) :
  stub_pc (Pointer.inc pc) <-> stub_pc pc.
Proof. by case: pc => [[c b] o]. Qed.

(* the invariant: the stub only runs, and only sits framed, at the
   bottom of the stack *)
Definition sb_inv (s : CS.state) : Prop :=
  match s with
  | (gps, _, _, pc) =>
      (stub_pc pc -> gps = [::])
      /\ (forall (gps1 : list Pointer.t) (f : Pointer.t)
                 (gps2 : list Pointer.t),
            gps = gps1 ++ f :: gps2 -> stub_pc f -> gps2 = [::])
  end.

Lemma sb_inv_nilstack (mem : Memory.Memory.t)
    (regs : Intermediate.Register.t) (pc : Pointer.t) :
  sb_inv ([::], mem, regs, pc).
Proof.
split; first by [].
by move=> [|x gps1] f gps2.
Qed.

(* silent pc-increment steps preserve the invariant *)
Lemma sb_inv_inc (gps : CS.stack)
    (mem mem' : Memory.Memory.t)
    (regs regs' : Intermediate.Register.t) (pc : Pointer.t) :
  sb_inv (gps, mem, regs, pc) ->
  sb_inv (gps, mem', regs', Pointer.inc pc).
Proof.
move=> [H1 H2].
split; last exact: H2.
move=> /stub_pc_inc Hs. exact: H1.
Qed.

(* label targets are never in the stub (it has no labels) *)
Hypothesis Hstub_nolabel_c :
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Pointer.component pc \in domm (Intermediate.prog_interface ilp) ->
    Intermediate.GlobalEnv.find_label_in_component G pc l = Some pc' ->
    ~ stub_pc pc'.

Hypothesis Hstub_nolabel_p :
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Pointer.component pc \in domm (Intermediate.prog_interface ilp) ->
    Intermediate.GlobalEnv.find_label_in_procedure G pc l = Some pc' ->
    ~ stub_pc pc'.

(* an executing pc's component is interfaced *)
Lemma executing_domm (pc : Pointer.t) (i : Machine.instr) :
  Intermediate.GlobalEnv.executing G pc i ->
  Pointer.component pc \in domm (Intermediate.prog_interface ilp).
Proof.
case=> Cp [Pc [HgC _]].
rewrite -(Intermediate.GlobalEnv.domm_genv_procedures ilp).
by rewrite mem_domm HgC.
Qed.

(* cross-component calls never enter the stub (its fresh procedure id
   is not exported) *)
Hypothesis Hstub_noentry :
  forall (C0 : Component.id) (C' : Component.id) (P : Procedure.id)
         (b : Block.id),
    imported_procedure
      (Intermediate.GlobalEnv.genv_interface G) C0 C' P ->
    Intermediate.EntryPoint.get C' P
      (Intermediate.GlobalEnv.genv_entrypoints G) = Some b ->
    ~ stub_blk C' b.

Lemma sb_step (s : CS.state) (t : Events.trace) (s' : CS.state) :
  CS.step G s t s' -> sb_inv s -> sb_inv s'.
Proof.
case=> {s t s'}.
- (* Nop *)
  move=> gps mem regs pc _.
  exact: sb_inv_inc.
- (* Label *)
  move=> gps mem regs pc l _.
  exact: sb_inv_inc.
- (* Const *)
  move=> gps mem regs regs' pc r v _ _.
  exact: sb_inv_inc.
- (* Mov *)
  move=> gps mem regs regs' pc r1 r2 _ _.
  exact: sb_inv_inc.
- (* BinOp *)
  move=> gps mem regs regs' pc r1 r2 r3 op _.
  cbv zeta. move=> _ [H1 H2].
  split; last exact: H2.
  move=> /stub_pc_inc Hs. exact: H1.
- (* Load *)
  move=> gps mem regs regs' pc r1 r2 ptr v _ _ _ _ _.
  exact: sb_inv_inc.
- (* Store *)
  move=> gps mem mem' regs pc ptr r1 r2 _ _ _ _.
  exact: sb_inv_inc.
- (* Jal *)
  move=> gps mem regs regs' pc pc' l Hex HF _ [H1 H2].
  split.
  + move=> Hs'. exfalso.
    exact: (Hstub_nolabel_c (executing_domm Hex) HF Hs').
  + move=> [|x gps1] f gps2 /= Edec Hf.
    * case: Edec => Ef Eg.
      rewrite -Eg.
      apply: H1.
      apply/stub_pc_inc.
      by rewrite Ef.
    * case: Edec => _ Eg. exact: (H2 _ _ _ Eg Hf).
- (* Jump *)
  move=> gps mem regs pc pc' _ _ [H1 H2].
  split.
  + move=> Hs'. exact: (H2 [::] pc' gps erefl Hs').
  + move=> gps1 f gps2 Eg Hf.
    apply: (H2 (pc' :: gps1) f gps2 _ Hf).
    by rewrite /= Eg.
- (* BnzNZ *)
  move=> gps mem regs pc pc' r l val Hex _ _ HFp [H1 H2].
  split; last exact: H2.
  move=> Hs'. exfalso.
  exact: (Hstub_nolabel_p (executing_domm Hex) HFp Hs').
- (* BnzZ *)
  move=> gps mem regs pc r l _ _.
  exact: sb_inv_inc.
- (* Alloc *)
  move=> gps mem mem' regs regs' pc rsize rptr size ptr _ _ _ _ _.
  exact: sb_inv_inc.
- (* Call *)
  move=> gps mem regs pc b C' P call_arg _ _ Himp Hep _ [H1 H2].
  split.
  + move=> Hs'. exfalso. exact: (Hstub_noentry Himp Hep Hs').
  + move=> [|x gps1] f gps2 /= Edec Hf.
    * case: Edec => Ef Eg.
      rewrite -Eg.
      apply: H1.
      apply/stub_pc_inc.
      by rewrite Ef.
    * case: Edec => _ Eg. exact: (H2 _ _ _ Eg Hf).
- (* Return *)
  move=> gps' mem regs pc pc' ret_arg _ _ _ [H1 H2].
  split.
  + move=> Hs'. exact: (H2 [::] pc' gps' erefl Hs').
  + move=> gps1 f gps2 Eg Hf.
    apply: (H2 (pc' :: gps1) f gps2 _ Hf).
    by rewrite /= Eg.
Qed.

(* the initial state has an empty stack, whatever its shape *)
Lemma sb_init : sb_inv (CS.initial_machine_state ilp).
Proof.
rewrite /CS.initial_machine_state.
case: (Intermediate.prog_main ilp).
- exact: sb_inv_nilstack.
- exact: sb_inv_nilstack.
Qed.

(* every reachable state satisfies the invariant *)
Theorem ireach_sb (s : CS.state) :
  ireach pra prb s -> sb_inv s.
Proof.
move=> [t Hst].
move: Hst (sb_init).
move: (CS.initial_machine_state ilp) => s0 Hst.
elim: Hst => [s1 Hinv | s1 t1 s2 t2 s3 tt Hstep Hstar IH Et Hinv].
- exact: Hinv.
- apply: IH. exact: (sb_step Hstep Hinv).
Qed.

(* ==================== phase 2: the slot model ==================== *)

(* The compiled stack frame is a FRESH ALLOCATED BLOCK (the prologue's
   IAlloc R_SP R_SP), so slot separation is block-level: user stores
   target the static buffers or data allocations, never a frame block,
   except through R_SP itself at the compiled push/pop sites.

   [sp_delta] mirrors [dead_at]: inside a call window it tracks the
   offset of R_SP above the window's RA slot (the push stores at the
   slot then increments; pushes/pops of other registers move it; the
   closing pop's preceding decrement returns it to 0). *)

Definition sp_step (i : Machine.instr) (d : Z) : Z :=
  match i with
  | IStore _ r2 => match r2 with R_RA => 0%Z | _ => d end
  | IBinOp Add R_SP R_ONE R_SP => (d + 1)%Z
  | IBinOp Minus R_SP R_ONE R_SP => (d - 1)%Z
  | _ => d
  end.

Fixpoint sp_scan (c : Machine.code) (d : Z) (o : nat) : Z :=
  match o, c with
  | 0, _ => d
  | _.+1, [::] => d
  | o'.+1, i :: c' => sp_scan c' (sp_step i d) o'
  end.

(* the running window's slot: R_SP sits [sp_scan] above the RA slot *)
Definition win_slot (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (cur : Component.id)
    (Pcode : Machine.code) (o : nat) : Prop :=
  exists (fb : Block.id) (spo : Z),
    [/\ Intermediate.Register.get R_SP iregs = Ptr (cur, fb, spo)
      & Memory.Memory.load imem
          (cur, fb, (spo - sp_scan Pcode 0%Z o)%Z) = Some Undef].

(* basic scan algebra *)
Lemma sp_scan0 (c : Machine.code) (d : Z) : sp_scan c d 0 = d.
Proof. by case: c. Qed.

Lemma sp_scan_S (c : Machine.code) (d : Z) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  sp_scan c d o.+1 = sp_step i (sp_scan c d o).
Proof.
elim: c d o => [|i0 c' IH] d o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite sp_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

(* the per-instruction SP-discipline condition: pushes open windows
   live, the closing pop reads at offset zero, in-window frame stores
   stay above the RA slot, and nothing else writes R_SP in-window *)
(* Note: cross-call windows legitimately rewrite R_SP in-window (it is
   parked in the scratch cell across the callee and reloaded — IConst
   (IPtr scr) R_SP; ILoad R_SP R_SP — restoring exactly the tracked
   offset), so only the push/pop discipline itself is enforced here;
   the run-level invariant carries the reload semantics. *)
Definition spd_cond (i : Machine.instr) (dead : bool) (d : Z) : bool :=
  match i with
  | IStore r1 r2 =>
      match r2 with
      | R_RA => ~~ dead
      | _ => match r1 with
             | R_SP => if dead then (0 <? d)%Z else true
             | _ => true
             end
      end
  | ILoad _ r2 =>
      match r2 with
      | R_RA => dead && (d =? 0)%Z
      | _ => true
      end
  | _ => true
  end.

Fixpoint spd_check (c : Machine.code) (dead : bool) (d : Z) : bool :=
  match c with
  | [::] => ~~ dead
  | i :: c' =>
      spd_cond i dead d
      && spd_check c' (ra_dead_step i dead) (sp_step i d)
  end.

Lemma spd_check_sound (c : Machine.code) :
  forall (dead : bool) (d : Z),
  spd_check c dead d = true ->
  forall (o : nat) (i : Machine.instr),
    List.nth_error c o = Some i ->
    spd_cond i (ra_dead_scan c dead o) (sp_scan c d o) = true.
Proof.
elim: c => [|i0 c' IH] dead d.
- by move=> _ o i; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o i.
  case: o => [|o'] /=.
  + by move=> [<-].
  + move=> Hnth. exact: (IH _ _ Hrest _ _ Hnth).
Qed.

(* inside a window the offset is canonical: the opening push resets it,
   so scans from different seeds agree at every dead position *)
Lemma sp_scan_dead_irrel (c : Machine.code) :
  forall (dead : bool) (d d' : Z) (o : nat),
  (dead -> d = d') ->
  ra_dead_scan c dead o = true ->
  sp_scan c d o = sp_scan c d' o.
Proof.
elim: c => [|i c IH] dead d d' o Hdd.
- case: o => [|o] //= Hd; by rewrite (Hdd Hd).
- case: o => [|o] /=.
  + move=> Hd. by rewrite (Hdd Hd).
  + move=> Hscan.
    apply: (IH _ _ _ _ _ Hscan).
    case: i {Hscan} => //=.
    * move=> op r1 r2 r3 Hd. by rewrite (Hdd Hd).
    * by move=> r1 r2; case: r2 => //= Hd; rewrite (Hdd Hd).
    * by move=> r1 r2; case: r2 => //= Hd; rewrite (Hdd Hd).
Qed.

Lemma sp_scan_cat_l (c1 c2 : Machine.code) (d : Z) (o : nat) :
  o <= size c1 ->
  sp_scan (c1 ++ c2) d o = sp_scan c1 d o.
Proof.
elim: c1 d o => [|i c1' IH] d o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite sp_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma sp_scan_cat_r (c1 c2 : Machine.code) (d : Z) (o : nat) :
  sp_scan (c1 ++ c2) d (size c1 + o)
  = sp_scan c2 (sp_scan c1 d (size c1)) o.
Proof. by elim: c1 d => [|i c1' IH] d //=. Qed.

(* at live positions the condition ignores the offset *)
Lemma spd_cond_live_irrel (i : Machine.instr) (d d' : Z) :
  spd_cond i false d = spd_cond i false d'.
Proof. by case: i => //=. Qed.

(* the compositional form: window-balanced, and every position obeys
   the discipline relative to a live entry with canonical offsets *)
Record spd_ok (c : Machine.code) : Prop := SpdOk {
  spdo_bal : ra_dead_scan c false (size c) = false;
  spdo_cond : forall (o : nat) (i : Machine.instr),
      List.nth_error c o = Some i ->
      spd_cond i (ra_dead_scan c false o) (sp_scan c 0%Z o) = true
}.

Lemma spd_ok_cat (c1 c2 : Machine.code) :
  spd_ok c1 -> spd_ok c2 -> spd_ok (c1 ++ c2).
Proof.
move=> [B1 F1] [B2 F2].
constructor.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  rewrite ra_dead_scan_cat_r B1.
  exact: B2.
- move=> o i Hnth.
  case: (ltnP o (size c1)) => Ho.
  + have Hn1 : List.nth_error c1 o = Some i.
    { move: Hnth. rewrite List.nth_error_app1 //. by apply/ltP. }
    rewrite (ra_dead_scan_cat_l _ _ (ltnW Ho))
            (sp_scan_cat_l _ _ (ltnW Ho)).
    exact: (F1 _ _ Hn1).
  + have Eo : o = size c1 + (o - size c1) by rewrite subnKC.
    have Hn2 : List.nth_error c2 (o - size c1) = Some i.
    { move: Hnth.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size c1)%coq_nat = o - size c1 by lia. }
    rewrite Eo ra_dead_scan_cat_r B1 sp_scan_cat_r.
    have Hcond := F2 _ _ Hn2.
    case Edead: (ra_dead_scan c2 false (o - size c1)).
    * (* dead: the offset is canonical *)
      have Eirr : sp_scan c2 (sp_scan c1 0%Z (size c1)) (o - size c1)
                  = sp_scan c2 0%Z (o - size c1).
      { by apply: (sp_scan_dead_irrel (dead := false)) => //. }
      rewrite Eirr.
      by rewrite Edead in Hcond.
    * (* live: the condition ignores the offset *)
      rewrite Edead in Hcond.
      by rewrite (spd_cond_live_irrel _ _ 0%Z).
Qed.

Lemma spd_check_bal (c : Machine.code) :
  forall (dead : bool) (d : Z),
  spd_check c dead d = true ->
  ra_dead_scan c dead (size c) = false.
Proof.
elim: c => [|i c IH] dead d /=.
- by move=> /negbTE.
- move=> /andP [_ Hrest]. exact: (IH _ _ Hrest).
Qed.

(* checked literals satisfy the compositional form *)
Lemma spd_check_okP (c : Machine.code) :
  spd_check c false 0%Z = true -> spd_ok c.
Proof.
move=> Hc.
constructor.
- exact: (spd_check_bal Hc).
- move=> o i Hnth. exact: (spd_check_sound Hc Hnth).
Qed.

(* a live, window-neutral head preserves the form *)
Lemma spd_ok_cons (i : Machine.instr) (c : Machine.code) :
  spd_cond i false 0%Z = true ->
  ra_dead_step i false = false ->
  spd_ok c ->
  spd_ok (i :: c).
Proof.
move=> Hc Hs H.
have H1 : spd_ok [:: i].
{ constructor.
  - by rewrite /= Hs.
  - move=> o i0.
    case: o => [|o] /=.
    + move=> [<-]. exact: Hc.
    + by rewrite List.nth_error_nil. }
exact: (spd_ok_cat H1 H).
Qed.

(* compiled expressions obey the SP discipline *)
Lemma compile_expr_spd (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  spd_ok c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _]; by apply: spd_check_okP.
- (* E_arg *)
  move: Hc => /= [<- _]. by apply: spd_check_okP.
- (* E_local *)
  move: Hc => /= [<- _]. by apply: spd_check_okP.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: spd_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: spd_ok_cons => //.
  apply: spd_ok_cons => //.
  apply: spd_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: spd_check_okP; case: bop.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (spd_ok_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: spd_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: spd_ok_cons => //.
  apply: spd_ok_cat; first exact: (IH3 _ _ _ E3).
  apply: spd_ok_cons => //.
  apply: spd_ok_cons => //.
  apply: spd_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: spd_check_okP.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: spd_ok_cat; first exact: (IH _ _ _ E1).
  by apply: spd_check_okP.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: spd_ok_cat; first exact: (IH _ _ _ E1).
  by apply: spd_check_okP.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: spd_ok_cat; first exact: (IH2 _ _ _ E2).
  apply: spd_ok_cons => //.
  apply: spd_ok_cons => //.
  apply: spd_ok_cat; first exact: (IH1 _ _ _ E1).
  by apply: spd_check_okP.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: spd_ok_cat; first exact: (IH _ _ _ E1).
    by apply: spd_check_okP.
  + move=> [<- _].
    apply: spd_ok_cat; first exact: (IH _ _ _ E1).
    by apply: spd_check_okP.
- (* E_exit *)
  move: Hc => /= [<- _]. by apply: spd_check_okP.
Qed.

Lemma spd_ok_at (c pre body post : Machine.code) :
  c = pre ++ body ++ post ->
  spd_ok pre -> spd_ok body -> spd_ok post -> spd_ok c.
Proof.
move=> -> H1 H2 H3.
exact: (spd_ok_cat H1 (spd_ok_cat H2 H3)).
Qed.

(* whole compiled procedures obey the SP discipline *)
Lemma compile_proc_spd (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : Machine.code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  spd_ok cd.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Fbody := compile_expr_spd E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (spd_ok_at
      (pre := [:: IHalt] ++ EEM ++ PROL)
      (body := pcode) (post := POST)) => //;
      apply: spd_check_okP.
  + by apply: (spd_ok_at
      (pre := EEM ++ PROL)
      (body := pcode) (post := POST)) => //;
      apply: spd_check_okP.
- by apply: (spd_ok_at
    (pre := EEN ++ PROL)
    (body := pcode) (post := POST)) => //;
    apply: spd_check_okP.
Qed.

(* every procedure of a compiled program obeys the SP discipline *)
Theorem compiled_spd (p : Source.program) (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    spd_ok cd.
Proof.
move=> Hcomp C Cprocs P cd Hget HgetP.
have [plm [nb [Hbound Hper]]] := compiled_comp_origin Hcomp Hget.
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd _]]].
- exact: (compile_proc_spd Hcpc).
- subst cd. by apply: spd_check_okP.
Qed.

(* frame lemmas: stores by other components or into other blocks leave
   a cell untouched (I-stores are component-local by the step relation,
   so cross-component callees can never reach a caller's frame) *)
Lemma load_store_other_comp (mem mem' : Memory.Memory.t)
    (ptr : Pointer.t) (v : value)
    (C : Component.id) (b : Block.id) (o : Z) :
  Memory.Memory.store mem ptr v = Some mem' ->
  Pointer.component ptr <> C ->
  Memory.Memory.load mem' (C, b, o) = Memory.Memory.load mem (C, b, o).
Proof.
move=> Hst Hne.
apply: (Memory.Memory.load_after_store_neq _ _ _ _ _ _ Hst).
case: ptr Hst Hne => [[cp bp] op] _ Hne E.
by case: E Hne => <- _ _.
Qed.

Lemma load_store_other_block (mem mem' : Memory.Memory.t)
    (ptr : Pointer.t) (v : value)
    (C : Component.id) (b : Block.id) (o : Z) :
  Memory.Memory.store mem ptr v = Some mem' ->
  Pointer.block ptr <> b ->
  Memory.Memory.load mem' (C, b, o) = Memory.Memory.load mem (C, b, o).
Proof.
move=> Hst Hne.
apply: (Memory.Memory.load_after_store_neq _ _ _ _ _ _ Hst).
case: ptr Hst Hne => [[cp bp] op] _ Hne E.
by case: E Hne => _ <- _.
Qed.

Lemma load_store_other_off (mem mem' : Memory.Memory.t)
    (ptr : Pointer.t) (v : value)
    (C : Component.id) (b : Block.id) (o : Z) :
  Memory.Memory.store mem ptr v = Some mem' ->
  Pointer.offset ptr <> o ->
  Memory.Memory.load mem' (C, b, o) = Memory.Memory.load mem (C, b, o).
Proof.
move=> Hst Hne.
apply: (Memory.Memory.load_after_store_neq _ _ _ _ _ _ Hst).
case: ptr Hst Hne => [[cp bp] op] _ Hne E.
by case: E Hne => _ _ <-.
Qed.

(* cross-boundary register clearing, per register *)
Lemma invalidate_get (regs : Intermediate.Register.t)
    (r : Machine.register) :
  Intermediate.Register.get r (Intermediate.Register.invalidate regs)
  = match r with
    | R_COM => Intermediate.Register.get R_COM regs
    | _ => Undef
    end.
Proof. by case: r. Qed.

(* the post-call phase: between a cross ICall and the R_SP reload the
   stack pointer is parked in the scratch cell *)
Definition ph_step (i : Machine.instr) (ph : bool) : bool :=
  match i with
  | ICall _ _ => true
  | ILoad R_SP R_SP => false
  | _ => ph
  end.

Fixpoint ph_scan (c : Machine.code) (ph : bool) (o : nat) : bool :=
  match o, c with
  | 0, _ => ph
  | _.+1, [::] => ph
  | o'.+1, i :: c' => ph_scan c' (ph_step i ph) o'
  end.

(* the running window's slot, phase-aware: in the normal phase R_SP
   itself locates the RA slot; in the post-call phase the parked R_SP
   sits in the scratch cell *)
Definition win_state (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (scr : Pointer.t)
    (cur : Component.id) (Pcode : Machine.code) (o : nat) : Prop :=
  exists (fb : Block.id) (spo : Z),
    Memory.Memory.load imem
      (cur, fb, (spo - sp_scan Pcode 0%Z o)%Z) = Some Undef
    /\ (if ph_scan Pcode false o
        then Memory.Memory.load imem
               (Pointer.component scr, Pointer.block scr,
                Pointer.offset scr) = Some (Ptr (cur, fb, spo))
        else Intermediate.Register.get R_SP iregs = Ptr (cur, fb, spo)).

(* the parked frames' RA slots all hold Undef; a [None] entry is a
   frameless push (the bottom stub's live jal — its return target is
   live, so the pop never needs a window to re-open) *)
Fixpoint iframes (imem : Memory.Memory.t) (gps : list Pointer.t)
    (fbs : list (option (Block.id * Z))) : Prop :=
  match gps, fbs with
  | [::], [::] => True
  | p :: rest, Some (fb, sl) :: fbs' =>
      Memory.Memory.load imem (Pointer.component p, fb, sl)
        = Some Undef
      /\ iframes imem rest fbs'
  | p :: rest, None :: fbs' => iframes imem rest fbs'
  | _, _ => False
  end.

Lemma ph_scan0 (c : Machine.code) (ph : bool) : ph_scan c ph 0 = ph.
Proof. by case: c. Qed.

Lemma ph_scan_S (c : Machine.code) (ph : bool) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  ph_scan c ph o.+1 = ph_step i (ph_scan c ph o).
Proof.
elim: c ph o => [|i0 c' IH] ph o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite ph_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

Lemma ph_scan_cat_l (c1 c2 : Machine.code) (p : bool) (o : nat) :
  o <= size c1 ->
  ph_scan (c1 ++ c2) p o = ph_scan c1 p o.
Proof.
elim: c1 p o => [|i c1' IH] p o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite ph_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma ph_scan_cat_r (c1 c2 : Machine.code) (p : bool) (o : nat) :
  ph_scan (c1 ++ c2) p (size c1 + o)
  = ph_scan c2 (ph_scan c1 p (size c1)) o.
Proof. by elim: c1 p => [|i c1' IH] p //=. Qed.

(* ==================== the position classifier ==================== *)

(* the joint static classification consumed by the run invariant: per
   instruction, what the R_RA window state (dead), the in-window SP
   offset (d) and the post-call phase (ph) must look like *)
Definition cls_cond (i : Machine.instr) (dead : bool) (d : Z)
    (ph : bool) : bool :=
  match i with
  | IConst _ r =>
      match r with
      | R_RA => false
      | R_SP => ~~ (dead && ~~ ph)
      | _ => true
      end
  | IMov _ r2 =>
      match r2 with R_RA | R_SP => false | _ => true end
  | IBinOp op r1 r2 r3 =>
      match r3 with
      | R_RA => false
      | R_SP =>
          match r1, r2, op with
          | R_SP, R_ONE, Add | R_SP, R_ONE, Minus => ~~ ph
          | _, _, _ => false
          end
      | _ => true
      end
  | ILoad r1 r2 =>
      match r2 with
      | R_RA =>
          match r1 with
          | R_SP => [&& dead, (d =? 0)%Z & ~~ ph]
          | _ => false
          end
      | R_SP =>
          ~~ dead || (match r1 with R_SP => ph | _ => false end)
      | _ => true
      end
  | IStore r1 r2 =>
      match r2 with
      | R_RA =>
          match r1 with
          | R_SP => ~~ dead && ~~ ph
          | _ => false
          end
      | _ => ~~ ph
      end
  | IAlloc r _ =>
      match r with R_RA => false | _ => ~~ dead end
  | IJal _ => ~~ dead || ~~ ph
  | ICall _ _ => dead && ~~ ph
  | _ => true
  end.

(* the propositional reading, matching the run invariant's uses *)
Lemma cls_condP (i : Machine.instr) (dead ph : bool) (d : Z) :
  cls_cond i dead d ph = true ->
  match i with
  | IConst _ r =>
      r <> R_RA /\ (dead = true -> ph = false -> r <> R_SP)
  | IMov _ r2 => r2 <> R_RA /\ r2 <> R_SP
  | IBinOp op r1 r2 r3 =>
      r3 <> R_RA
      /\ (r3 = R_SP ->
          [/\ r1 = R_SP, r2 = R_ONE, op = Add \/ op = Minus
            & ph = false])
  | ILoad r1 r2 =>
      (r2 = R_RA -> [/\ r1 = R_SP, dead = true, d = 0%Z & ph = false])
      /\ (r2 = R_SP -> dead = true -> r1 = R_SP /\ ph = true)
  | IStore r1 r2 =>
      (r2 = R_RA -> [/\ r1 = R_SP, dead = false & ph = false])
      /\ (r2 <> R_RA -> ph = false)
  | IAlloc r _ => r <> R_RA /\ dead = false
  | IJal _ => dead = true -> ph = false
  | ICall _ _ => dead = true /\ ph = false
  | _ => True
  end.
Proof.
case: i => //=.
- (* IConst *)
  move=> v r.
  case: r => //= H.
  split => // Ed Ep.
  by move: H; rewrite Ed Ep /=.
- (* IMov *)
  by move=> r1 r2; case: r2.
- (* IBinOp *)
  move=> op r1 r2 r3.
  case: r3 => //= H; split => // _.
  case: r1 H => //=; case: r2 => //=; case: op => //= H.
  + by split=> //; [left | exact: (negbTE H)].
  + by split=> //; [right | exact: (negbTE H)].
- (* ILoad *)
  move=> r1 r2.
  case: r2 => //=.
  + (* R_RA *)
    case: r1 => //= /and3P [Hd Hd0 Hp].
    split=> // _.
    by split;
      [ | exact: Hd | move: Hd0 => /Z.eqb_eq | exact: (negbTE Hp)].
  + (* R_SP *)
    move=> H.
    split=> // _ Ed.
    move: H; rewrite Ed /=.
    by case: r1.
- (* IStore *)
  move=> r1 r2.
  case: r2 => //=;
    try by move=> H; split=> [|_]; [ | exact: (negbTE H)].
  (* R_RA *)
  case: r1 => //= /andP [H1 H2].
  split.
  + move=> _.
    by split=> //; [exact: (negbTE H1) | exact: (negbTE H2)].
  + move=> HN. by case: (HN erefl).
- (* IAlloc *)
  move=> r sz.
  case: r => //= H; split=> //; exact: (negbTE H).
- (* IJal *)
  move=> l H Ed.
  move: H; rewrite Ed /=.
  exact: negbTE.
- (* ICall *)
  move=> C' P' /andP [H1 H2].
  by split; [ | exact: (negbTE H2)].
Qed.

Fixpoint cls_check (c : Machine.code) (dead : bool) (d : Z)
    (ph : bool) : bool :=
  match c with
  | [::] => ~~ dead && ~~ ph
  | i :: c' =>
      cls_cond i dead d ph
      && cls_check c' (ra_dead_step i dead) (sp_step i d)
           (ph_step i ph)
  end.

Lemma cls_check_sound (c : Machine.code) :
  forall (dead : bool) (d : Z) (ph : bool),
  cls_check c dead d ph = true ->
  forall (o : nat) (i : Machine.instr),
    List.nth_error c o = Some i ->
    cls_cond i (ra_dead_scan c dead o) (sp_scan c d o)
      (ph_scan c ph o) = true.
Proof.
elim: c => [|i0 c' IH] dead d ph.
- by move=> _ o i; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o i.
  case: o => [|o'] /=.
  + by move=> [<-].
  + move=> Hnth. exact: (IH _ _ _ Hrest _ _ Hnth).
Qed.

Lemma cls_check_bal (c : Machine.code) :
  forall (dead : bool) (d : Z) (ph : bool),
  cls_check c dead d ph = true ->
  ra_dead_scan c dead (size c) = false.
Proof.
elim: c => [|i c IH] dead d ph /=.
- by move=> /andP [/negbTE H _].
- move=> /andP [_ Hrest]. exact: (IH _ _ _ Hrest).
Qed.

Lemma cls_check_phbal (c : Machine.code) :
  forall (dead : bool) (d : Z) (ph : bool),
  cls_check c dead d ph = true ->
  ph_scan c ph (size c) = false.
Proof.
elim: c => [|i c IH] dead d ph /=.
- by move=> /andP [_ /negbTE H].
- move=> /andP [_ Hrest]. exact: (IH _ _ _ Hrest).
Qed.

(* at live positions the condition ignores the SP offset *)
Lemma cls_cond_live_irrel (i : Machine.instr) (d d' : Z) (ph : bool) :
  cls_cond i false d ph = cls_cond i false d' ph.
Proof.
by case: i => //= r1 r2; case: r2 => //=; case: r1.
Qed.

(* the compositional form *)
Record cls_ok (c : Machine.code) : Prop := ClsOk {
  clso_bal : ra_dead_scan c false (size c) = false;
  clso_phbal : ph_scan c false (size c) = false;
  clso_cond : forall (o : nat) (i : Machine.instr),
      List.nth_error c o = Some i ->
      cls_cond i (ra_dead_scan c false o) (sp_scan c 0%Z o)
        (ph_scan c false o) = true
}.

Lemma cls_ok_cat (c1 c2 : Machine.code) :
  cls_ok c1 -> cls_ok c2 -> cls_ok (c1 ++ c2).
Proof.
move=> [B1 PB1 F1] [B2 PB2 F2].
constructor.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  rewrite ra_dead_scan_cat_r B1.
  exact: B2.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  rewrite ph_scan_cat_r PB1.
  exact: PB2.
- move=> o i Hnth.
  case: (ltnP o (size c1)) => Ho.
  + have Hn1 : List.nth_error c1 o = Some i.
    { move: Hnth. rewrite List.nth_error_app1 //. by apply/ltP. }
    rewrite (ra_dead_scan_cat_l _ _ (ltnW Ho))
            (sp_scan_cat_l _ _ (ltnW Ho))
            (ph_scan_cat_l _ _ (ltnW Ho)).
    exact: (F1 _ _ Hn1).
  + have Eo : o = size c1 + (o - size c1) by rewrite subnKC.
    have Hn2 : List.nth_error c2 (o - size c1) = Some i.
    { move: Hnth.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size c1)%coq_nat = o - size c1 by lia. }
    rewrite Eo ra_dead_scan_cat_r B1 sp_scan_cat_r
            ph_scan_cat_r PB1.
    have Hcond := F2 _ _ Hn2.
    case Edead: (ra_dead_scan c2 false (o - size c1)).
    * (* dead: the offset is canonical *)
      have Eirr : sp_scan c2 (sp_scan c1 0%Z (size c1)) (o - size c1)
                  = sp_scan c2 0%Z (o - size c1).
      { by apply: (sp_scan_dead_irrel (dead := false)) => //. }
      rewrite Eirr.
      by rewrite Edead in Hcond.
    * (* live: the condition ignores the offset *)
      rewrite Edead in Hcond.
      by rewrite (cls_cond_live_irrel _ _ 0%Z).
Qed.

(* checked literals satisfy the compositional form *)
Lemma cls_check_okP (c : Machine.code) :
  cls_check c false 0%Z false = true -> cls_ok c.
Proof.
move=> Hc.
constructor.
- exact: (cls_check_bal Hc).
- exact: (cls_check_phbal Hc).
- move=> o i Hnth. exact: (cls_check_sound Hc Hnth).
Qed.

(* a live, window- and phase-neutral head preserves the form *)
Lemma cls_ok_cons (i : Machine.instr) (c : Machine.code) :
  cls_cond i false 0%Z false = true ->
  ra_dead_step i false = false ->
  ph_step i false = false ->
  cls_ok c ->
  cls_ok (i :: c).
Proof.
move=> Hc Hs Hp H.
have H1 : cls_ok [:: i].
{ constructor.
  - by rewrite /= Hs.
  - by rewrite /= Hp.
  - move=> o i0.
    case: o => [|o] /=.
    + move=> [<-]. exact: Hc.
    + by rewrite List.nth_error_nil. }
exact: (cls_ok_cat H1 H).
Qed.

Lemma cls_ok_at (c pre body post : Machine.code) :
  c = pre ++ body ++ post ->
  cls_ok pre -> cls_ok body -> cls_ok post -> cls_ok c.
Proof.
move=> -> H1 H2 H3.
exact: (cls_ok_cat H1 (cls_ok_cat H2 H3)).
Qed.

(* compiled expressions are classified *)
Lemma compile_expr_cls (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  cls_ok c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _]; by apply: cls_check_okP.
- (* E_arg *)
  move: Hc => /= [<- _]. by apply: cls_check_okP.
- (* E_local *)
  move: Hc => /= [<- _]. by apply: cls_check_okP.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: cls_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: cls_ok_cons => //.
  apply: cls_ok_cons => //.
  apply: cls_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: cls_check_okP; case: bop.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (cls_ok_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: cls_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: cls_ok_cons => //.
  apply: cls_ok_cat; first exact: (IH3 _ _ _ E3).
  apply: cls_ok_cons => //.
  apply: cls_ok_cons => //.
  apply: cls_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: cls_check_okP.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: cls_ok_cat; first exact: (IH _ _ _ E1).
  by apply: cls_check_okP.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: cls_ok_cat; first exact: (IH _ _ _ E1).
  by apply: cls_check_okP.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: cls_ok_cat; first exact: (IH2 _ _ _ E2).
  apply: cls_ok_cons => //.
  apply: cls_ok_cons => //.
  apply: cls_ok_cat; first exact: (IH1 _ _ _ E1).
  by apply: cls_check_okP.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: cls_ok_cat; first exact: (IH _ _ _ E1).
    by apply: cls_check_okP.
  + move=> [<- _].
    apply: cls_ok_cat; first exact: (IH _ _ _ E1).
    by apply: cls_check_okP.
- (* E_exit *)
  move: Hc => /= [<- _]. by apply: cls_check_okP.
Qed.

(* compiled procedure wrappers are classified *)
Lemma compile_proc_cls (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : Machine.code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  cls_ok cd.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Fbody := compile_expr_cls E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (cls_ok_at
      (pre := [:: IHalt] ++ EEM ++ PROL)
      (body := pcode) (post := POST)) => //;
      apply: cls_check_okP.
  + by apply: (cls_ok_at
      (pre := EEM ++ PROL)
      (body := pcode) (post := POST)) => //;
      apply: cls_check_okP.
- by apply: (cls_ok_at
    (pre := EEN ++ PROL)
    (body := pcode) (post := POST)) => //;
    apply: cls_check_okP.
Qed.

(* every procedure of a compiled program is classified — the bottom
   stub included *)
Theorem compiled_cls (p : Source.program) (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    cls_ok cd.
Proof.
move=> Hcomp C Cprocs P cd Hget HgetP.
have [plm [nb [Hbound Hper]]] := compiled_comp_origin Hcomp Hget.
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd _]]].
- exact: (compile_proc_cls Hcpc).
- subst cd. by apply: cls_check_okP.
Qed.

(* ==================== the R_ONE arming scan ==================== *)

(* R_ONE surely holds [Int 1]: armed by [IConst (IInt 1) R_ONE],
   killed by any other write to R_ONE and by cross calls (invalidate);
   the compiled ± push/pop binops only sit at armed positions *)
Definition rone_step (i : Machine.instr) (armed : bool) : bool :=
  match i with
  | IConst v r =>
      match r with
      | R_ONE => match v with
                 | IInt z => (z =? 1)%Z
                 | _ => false
                 end
      | _ => armed
      end
  | IMov _ r2 =>
      match r2 with R_ONE => false | _ => armed end
  | IBinOp _ _ _ r3 =>
      match r3 with R_ONE => false | _ => armed end
  | ILoad _ r2 =>
      match r2 with R_ONE => false | _ => armed end
  | IAlloc r _ =>
      match r with R_ONE => false | _ => armed end
  | ICall _ _ => false
  | _ => armed
  end.

Fixpoint rone_scan (c : Machine.code) (armed : bool) (o : nat)
  : bool :=
  match o, c with
  | 0, _ => armed
  | _.+1, [::] => armed
  | o'.+1, i :: c' => rone_scan c' (rone_step i armed) o'
  end.

Lemma rone_scan0 (c : Machine.code) (armed : bool) :
  rone_scan c armed 0 = armed.
Proof. by case: c. Qed.

Lemma rone_scan_S (c : Machine.code) (armed : bool) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  rone_scan c armed o.+1 = rone_step i (rone_scan c armed o).
Proof.
elim: c armed o => [|i0 c' IH] armed o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite rone_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

Lemma rone_scan_cat_l (c1 c2 : Machine.code) (s : bool) (o : nat) :
  o <= size c1 ->
  rone_scan (c1 ++ c2) s o = rone_scan c1 s o.
Proof.
elim: c1 s o => [|i c1' IH] s o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite rone_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma rone_scan_cat_r (c1 c2 : Machine.code) (s : bool) (o : nat) :
  rone_scan (c1 ++ c2) s (size c1 + o)
  = rone_scan c2 (rone_scan c1 s (size c1)) o.
Proof. by elim: c1 s => [|i c1' IH] s //=. Qed.

(* the condition: SP-adjusting binops require the armed flag, and so
   do all intra control-transfer sites (jal/jump/bnz) — making the
   run-invariant's transfer cases local (source-armed) *)
Definition rone_cond (i : Machine.instr) (armed : bool) : bool :=
  match i with
  | IBinOp _ _ _ r3 =>
      match r3 with R_SP => armed | _ => true end
  | IJal _ => armed
  | IJump => armed
  | IBnz _ _ => armed
  | _ => true
  end.

Fixpoint rone_check (c : Machine.code) (armed : bool) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      rone_cond i armed && rone_check c' (rone_step i armed)
  end.

Lemma rone_check_sound (c : Machine.code) :
  forall (armed : bool),
  rone_check c armed = true ->
  forall (o : nat) (i : Machine.instr),
    List.nth_error c o = Some i ->
    rone_cond i (rone_scan c armed o) = true.
Proof.
elim: c => [|i0 c' IH] armed.
- by move=> _ o i; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o i.
  case: o => [|o'] /=.
  + by move=> [<-].
  + move=> Hnth. exact: (IH _ Hrest _ _ Hnth).
Qed.

Lemma rone_check_cat (c1 c2 : Machine.code) (s : bool) :
  rone_check (c1 ++ c2) s
  = rone_check c1 s && rone_check c2 (rone_scan c1 s (size c1)).
Proof.
elim: c1 s => [|i c1' IH] s /=.
- by [].
- by rewrite IH andbA.
Qed.

(* the compositional form for fragments: armed-in gives checked
   positions and armed-out *)
Record rone_ok (c : Machine.code) : Prop := ROneOk {
  ro_check : rone_check c true = true;
  ro_end : rone_scan c true (size c) = true
}.

Lemma rone_ok_cat (c1 c2 : Machine.code) :
  rone_ok c1 -> rone_ok c2 -> rone_ok (c1 ++ c2).
Proof.
move=> [C1 E1] [C2 E2].
constructor.
- by rewrite rone_check_cat C1 E1 C2.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  by rewrite rone_scan_cat_r E1 E2.
Qed.

Lemma rone_ok_cons (i : Machine.instr) (c : Machine.code) :
  rone_cond i true = true ->
  rone_step i true = true ->
  rone_ok c ->
  rone_ok (i :: c).
Proof.
move=> Hc Hs [C E].
constructor.
- by rewrite /= Hc Hs C.
- by rewrite /= Hs E.
Qed.

Lemma rone_check_okP (c : Machine.code) :
  rone_check c true = true ->
  rone_scan c true (size c) = true ->
  rone_ok c.
Proof. by move=> Hc He; constructor. Qed.

(* compiled expression fragments preserve the arming *)
Lemma compile_expr_rone (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  rone_ok c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _]; by apply: rone_check_okP.
- (* E_arg *)
  move: Hc => /= [<- _]. by apply: rone_check_okP.
- (* E_local *)
  move: Hc => /= [<- _]. by apply: rone_check_okP.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rone_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: rone_ok_cons => //.
  apply: rone_ok_cons => //.
  apply: rone_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: rone_check_okP; case: bop.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (rone_ok_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: rone_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: rone_ok_cons => //.
  apply: rone_ok_cat; first exact: (IH3 _ _ _ E3).
  apply: rone_ok_cons => //.
  apply: rone_ok_cons => //.
  apply: rone_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: rone_check_okP.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rone_ok_cat; first exact: (IH _ _ _ E1).
  by apply: rone_check_okP.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rone_ok_cat; first exact: (IH _ _ _ E1).
  by apply: rone_check_okP.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rone_ok_cat; first exact: (IH2 _ _ _ E2).
  apply: rone_ok_cons => //.
  apply: rone_ok_cons => //.
  apply: rone_ok_cat; first exact: (IH1 _ _ _ E1).
  by apply: rone_check_okP.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: rone_ok_cat; first exact: (IH _ _ _ E1).
    by apply: rone_check_okP.
  + move=> [<- _].
    apply: rone_ok_cat; first exact: (IH _ _ _ E1).
    by apply: rone_check_okP.
- (* E_exit *)
  move: Hc => /= [<- _]. by apply: rone_check_okP.
Qed.

(* whole compiled procedures check from the cold seed: the wrapper's
   first cell arms R_ONE *)
Lemma compile_proc_rone (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : Machine.code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  rone_check cd false = true.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have [Fchk Fend] := compile_expr_rone E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
have KEY : forall PRE : Machine.code,
    rone_check PRE false = true ->
    rone_scan PRE false (size PRE) = true ->
    rone_check (PRE ++ pcode ++ POST) false = true.
{ move=> PRE Hpre Hend.
  rewrite rone_check_cat Hpre Hend /=.
  by rewrite rone_check_cat Fchk Fend /=. }
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (KEY ([:: IHalt] ++ EEM ++ PROL)).
  + by apply: (KEY (EEM ++ PROL)).
- by apply: (KEY (EEN ++ PROL)).
Qed.

(* program level: every ±SP binop of a compiled procedure sits at an
   armed position (from the cold seed) *)
Theorem compiled_rone (p : Source.program) (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    rone_check cd false = true.
Proof.
move=> Hcomp C Cprocs P cd Hget HgetP.
have [plm [nb [Hbound Hper]]] := compiled_comp_origin Hcomp Hget.
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd _]]].
- exact: (compile_proc_rone Hcpc).
- by subst cd.
Qed.

(* ==================== the R_SP constant track ==================== *)

(* the last constant written to R_SP, if still current: [IConst v R_SP]
   sets it, any other write to R_SP (and cross calls) clears it *)
Definition rsp_step (i : Machine.instr) (tr : option imvalue)
  : option imvalue :=
  match i with
  | IConst v r =>
      match r with R_SP => Some v | _ => tr end
  | IMov _ r2 =>
      match r2 with R_SP => None | _ => tr end
  | IBinOp _ _ _ r3 =>
      match r3 with R_SP => None | _ => tr end
  | ILoad _ r2 =>
      match r2 with R_SP => None | _ => tr end
  | IAlloc r _ =>
      match r with R_SP => None | _ => tr end
  | ICall _ _ => None
  | _ => tr
  end.

Fixpoint rsp_track (c : Machine.code) (tr : option imvalue) (o : nat)
  : option imvalue :=
  match o, c with
  | 0, _ => tr
  | _.+1, [::] => tr
  | o'.+1, i :: c' => rsp_track c' (rsp_step i tr) o'
  end.

Lemma rsp_track0 (c : Machine.code) (tr : option imvalue) :
  rsp_track c tr 0 = tr.
Proof. by case: c. Qed.

Lemma rsp_track_S (c : Machine.code) (tr : option imvalue) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  rsp_track c tr o.+1 = rsp_step i (rsp_track c tr o).
Proof.
elim: c tr o => [|i0 c' IH] tr o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite rsp_track0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

(* pointer literal equality *)
Definition ptr_eqb (p q : Pointer.t) : bool :=
  match p, q with
  | (c, b, o), (c', b', o') =>
      (c == c') && (b == b') && (o =? o')%Z
  end.

Lemma ptr_eqb_eq (p q : Pointer.t) : ptr_eqb p q = true -> p = q.
Proof.
case: p => [[c b] o]; case: q => [[c' b'] o'] /=.
move=> /andP [/andP [/eqP -> /eqP ->] /Z.eqb_eq ->].
by [].
Qed.

Lemma ptr_eqb_refl (p : Pointer.t) : ptr_eqb p p = true.
Proof.
case: p => [[c b] o] /=.
by rewrite !eqxx Z.eqb_refl.
Qed.

(* the condition: post-call reloads see the scratch pointer; labels and
   jal sites carry no live track (so every transfer target is clean) *)
Definition rspt_cond (scr : Pointer.t) (i : Machine.instr)
    (tr : option imvalue) (ph : bool) : bool :=
  match i with
  | ILoad r1 r2 =>
      match r1, r2 with
      | R_SP, R_SP =>
          if ph
          then match tr with
               | Some (IPtr p) => ptr_eqb p scr
               | _ => false
               end
          else true
      | _, _ => true
      end
  | ILabel _ =>
      match tr with None => true | _ => false end
  | IJal _ =>
      match tr with None => true | _ => false end
  | _ => true
  end.

Fixpoint rspt_check (scr : Pointer.t) (c : Machine.code)
    (tr : option imvalue) (ph : bool) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      rspt_cond scr i tr ph
      && rspt_check scr c' (rsp_step i tr) (ph_step i ph)
  end.

Lemma rspt_check_sound (scr : Pointer.t) (c : Machine.code) :
  forall (tr : option imvalue) (ph : bool),
  rspt_check scr c tr ph = true ->
  forall (o : nat) (i : Machine.instr),
    List.nth_error c o = Some i ->
    rspt_cond scr i (rsp_track c tr o) (ph_scan c ph o) = true.
Proof.
elim: c => [|i0 c' IH] tr ph.
- by move=> _ o i; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o i.
  case: o => [|o'] /=.
  + by move=> [<-].
  + move=> Hnth. exact: (IH _ _ Hrest _ _ Hnth).
Qed.

Lemma rspt_check_cat (scr : Pointer.t) (c1 c2 : Machine.code)
    (tr : option imvalue) (ph : bool) :
  rspt_check scr (c1 ++ c2) tr ph
  = rspt_check scr c1 tr ph
    && rspt_check scr c2 (rsp_track c1 tr (size c1))
         (ph_scan c1 ph (size c1)).
Proof.
elim: c1 tr ph => [|i c1' IH] tr ph /=.
- by [].
- by rewrite IH andbA.
Qed.

Lemma rsp_track_cat_r (c1 c2 : Machine.code) (tr : option imvalue)
    (o : nat) :
  rsp_track (c1 ++ c2) tr (size c1 + o)
  = rsp_track c2 (rsp_track c1 tr (size c1)) o.
Proof. by elim: c1 tr => [|i c1' IH] tr //=. Qed.

Lemma rsp_track_cat_l (c1 c2 : Machine.code) (tr : option imvalue)
    (o : nat) :
  o <= size c1 ->
  rsp_track (c1 ++ c2) tr o = rsp_track c1 tr o.
Proof.
elim: c1 tr o => [|i c1' IH] tr o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite rsp_track0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

(* fragment form: clean-in/clean-out on both threads *)
Record rspt_ok (scr : Pointer.t) (c : Machine.code) : Prop := RsptOk {
  rso_check : rspt_check scr c None false = true;
  rso_end : rsp_track c None (size c) = None;
  rso_phend : ph_scan c false (size c) = false
}.

Lemma rspt_ok_cat (scr : Pointer.t) (c1 c2 : Machine.code) :
  rspt_ok scr c1 -> rspt_ok scr c2 -> rspt_ok scr (c1 ++ c2).
Proof.
move=> [C1 E1 P1] [C2 E2 P2].
constructor.
- by rewrite rspt_check_cat C1 E1 P1 C2.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  by rewrite rsp_track_cat_r E1 E2.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  by rewrite ph_scan_cat_r P1 P2.
Qed.

Lemma rspt_ok_cons (scr : Pointer.t) (i : Machine.instr)
    (c : Machine.code) :
  rspt_cond scr i None false = true ->
  rsp_step i None = None ->
  ph_step i false = false ->
  rspt_ok scr c ->
  rspt_ok scr (i :: c).
Proof.
move=> Hc Hs Hp [C E P].
constructor.
- by rewrite /= Hc Hs Hp C.
- by rewrite /= Hs E.
- by rewrite /= Hp P.
Qed.

Lemma rspt_check_okP (scr : Pointer.t) (c : Machine.code) :
  rspt_check scr c None false = true ->
  rsp_track c None (size c) = None ->
  ph_scan c false (size c) = false ->
  rspt_ok scr c.
Proof. by move=> Hc He Hp; constructor. Qed.

(* compiled expression fragments *)
Lemma compile_expr_rspt (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  rspt_ok scr c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _]; by apply: rspt_check_okP.
- (* E_arg *)
  move: Hc => /= [<- _]. by apply: rspt_check_okP.
- (* E_local *)
  move: Hc => /= [<- _]. by apply: rspt_check_okP.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rspt_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: rspt_check_okP; case: bop.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (rspt_ok_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: rspt_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cat; first exact: (IH3 _ _ _ E3).
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: rspt_check_okP.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rspt_ok_cat; first exact: (IH _ _ _ E1).
  by apply: rspt_check_okP.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rspt_ok_cat; first exact: (IH _ _ _ E1).
  by apply: rspt_check_okP.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: rspt_ok_cat; first exact: (IH2 _ _ _ E2).
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cons => //.
  apply: rspt_ok_cat; first exact: (IH1 _ _ _ E1).
  by apply: rspt_check_okP.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: rspt_ok_cat; first exact: (IH _ _ _ E1).
    by apply: rspt_check_okP; rewrite /= ?ptr_eqb_refl.
  + move=> [<- _].
    apply: rspt_ok_cat; first exact: (IH _ _ _ E1).
    by apply: rspt_check_okP; rewrite /= ?ptr_eqb_refl.
- (* E_exit *)
  move: Hc => /= [<- _]. by apply: rspt_check_okP.
Qed.

(* whole compiled procedures from the cold seed *)
Lemma compile_proc_rspt (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : Machine.code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  rspt_check scr cd None false = true.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have [Fchk Fend Fph] := compile_expr_rspt E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
have KEY : forall PRE : Machine.code,
    rspt_check scr PRE None false = true ->
    rsp_track PRE None (size PRE) = None ->
    ph_scan PRE false (size PRE) = false ->
    rspt_check scr (PRE ++ pcode ++ POST) None false = true.
{ move=> PRE Hpre Hend Hph.
  rewrite rspt_check_cat Hpre Hend Hph /=.
  by rewrite rspt_check_cat Fchk Fend Fph /=. }
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (KEY ([:: IHalt] ++ EEM ++ PROL)).
  + by apply: (KEY (EEM ++ PROL)).
- by apply: (KEY (EEN ++ PROL)).
Qed.

(* program level, at the concrete per-component scratch pointer *)
Theorem compiled_rspt (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    rspt_check (C, 1, 0%Z) cd None false = true.
Proof.
move=> Hcomp C Cprocs P cd Hget HgetP.
have [plm [nb [Hbound Hper]]] := compiled_comp_origin Hcomp Hget.
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc _ _]]]]] | [lab [Ecd _]]].
- exact: (compile_proc_rspt Hcpc).
- by subst cd.
Qed.

(* ==================== the R_AUX1 dirty scan ==================== *)

(* whether R_AUX1 may hold a frame/scratch pointer: set by the
   prologue's SP copy, by scratch-pointer constants and by the
   re-entrant scr load ([ILoad R_AUX1 R_AUX1]); cleared by frame-temp
   pops ([ILoad R_SP R_AUX1]), integer constants and cross calls *)
Definition aux1_step (i : Machine.instr) (dirty : bool) : bool :=
  match i with
  | IMov _ r2 =>
      match r2 with R_AUX1 => true | _ => dirty end
  | IConst v r =>
      match r with
      | R_AUX1 => match v with IInt _ => false | IPtr _ => true end
      | _ => dirty
      end
  | ILoad r1 r2 =>
      match r2 with
      | R_AUX1 => match r1 with R_SP => false | _ => true end
      | _ => dirty
      end
  | IBinOp _ _ _ r3 =>
      match r3 with R_AUX1 => true | _ => dirty end
  | IAlloc r _ =>
      match r with R_AUX1 => true | _ => dirty end
  | ICall _ _ => false
  (* conservative joins: everything after a label (a possible branch
     target) or a jal fall-through (a return point) counts dirty; the
     run invariant additionally skips the label position itself *)
  | ILabel _ => true
  | IJal _ => true
  | _ => dirty
  end.

Fixpoint aux1_scan (c : Machine.code) (dirty : bool) (o : nat)
  : bool :=
  match o, c with
  | 0, _ => dirty
  | _.+1, [::] => dirty
  | o'.+1, i :: c' => aux1_scan c' (aux1_step i dirty) o'
  end.

Lemma aux1_scan0 (c : Machine.code) (dirty : bool) :
  aux1_scan c dirty 0 = dirty.
Proof. by case: c. Qed.

Lemma aux1_scan_S (c : Machine.code) (dirty : bool) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  aux1_scan c dirty o.+1 = aux1_step i (aux1_scan c dirty o).
Proof.
elim: c dirty o => [|i0 c' IH] dirty o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite aux1_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

Lemma aux1_scan_cat_l (c1 c2 : Machine.code) (s : bool) (o : nat) :
  o <= size c1 ->
  aux1_scan (c1 ++ c2) s o = aux1_scan c1 s o.
Proof.
elim: c1 s o => [|i c1' IH] s o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite aux1_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma aux1_scan_cat_r (c1 c2 : Machine.code) (s : bool) (o : nat) :
  aux1_scan (c1 ++ c2) s (size c1 + o)
  = aux1_scan c2 (aux1_scan c1 s (size c1)) o.
Proof. by elim: c1 s => [|i c1' IH] s //=. Qed.

(* the compiled expression fragments never return *)
Fixpoint jump_free (c : Machine.code) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      (match i with IJump => false | _ => true end) && jump_free c'
  end.

Lemma jump_free_cat (c1 c2 : Machine.code) :
  jump_free (c1 ++ c2) = jump_free c1 && jump_free c2.
Proof. by elim: c1 => [|i c1' IH] //=; rewrite IH andbA. Qed.

Lemma jump_free_cons (i : Machine.instr) (c : Machine.code) :
  jump_free (i :: c)
  = (match i with IJump => false | _ => true end) && jump_free c.
Proof. by []. Qed.

Lemma jump_free_nth (c : Machine.code) (o : nat) :
  jump_free c = true ->
  List.nth_error c o <> Some IJump.
Proof.
elim: c o => [|i0 c' IH] o.
- by rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest].
  case: o => [|o'] /=.
  + by case: i0 Hc => // _ [].
  + exact: (IH _ Hrest).
Qed.

Lemma compile_expr_jump_free (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  jump_free c = true.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- case: v Hc => [i|p|] //= [<- _]; by [].
- by move: Hc => /= [<- _].
- by move: Hc => /= [<- _].
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite !jump_free_cat /= ?jump_free_cat
       ?(IH1 _ _ _ E1) ?(IH2 _ _ _ E2).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite !jump_free_cat /= ?jump_free_cat
       ?(IH1 _ _ _ E1) ?(IH2 _ _ _ E2).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|] //=.
  case E4: (fresh_label C s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C s4) => [[lend s5]|] //=.
  move=> [<- _].
  by rewrite !(jump_free_cat, jump_free_cons,
               (IH1 _ _ _ E1), (IH2 _ _ _ E2), (IH3 _ _ _ E3)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite !jump_free_cat /= ?jump_free_cat ?(IH _ _ _ E1).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite !jump_free_cat /= ?jump_free_cat ?(IH _ _ _ E1).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite !jump_free_cat /= ?jump_free_cat
       ?(IH1 _ _ _ E1) ?(IH2 _ _ _ E2).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|] //=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|] //=.
    move=> [<- _].
    by rewrite !jump_free_cat /= ?jump_free_cat ?(IH _ _ _ E1).
  + move=> [<- _].
    by rewrite !jump_free_cat /= ?jump_free_cat ?(IH _ _ _ E1).
- by move: Hc => /= [<- _].
Qed.

(* jumps in a compiled procedure only sit in the epilogue, where the
   frame-temp pop has just cleaned R_AUX1 — regardless of the body's
   abstract flow *)
Lemma aux1_scan_jump_free (c : Machine.code) (d : bool) (o : nat) :
  jump_free c = true ->
  List.nth_error c o <> Some IJump.
Proof. exact: jump_free_nth. Qed.

Theorem compile_proc_aux1_jump (C0 : Component.id)
    (lbp scr : Pointer.t) (plm : NMap label) (P0 : Procedure.id)
    (e : expr) (s : comp_env) (cd : Machine.code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  forall o,
    List.nth_error cd o = Some IJump ->
    aux1_scan cd false o = false.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Fjf := compile_expr_jump_free E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
have KEY : forall PRE : Machine.code,
    jump_free PRE = true ->
    forall o,
      List.nth_error (PRE ++ pcode ++ POST) o = Some IJump ->
      aux1_scan (PRE ++ pcode ++ POST) false o = false.
{ move=> PRE Hjf o Hnth.
  have Hjf2 : jump_free (PRE ++ pcode) = true.
  { by rewrite jump_free_cat Hjf Fjf. }
  case: (ltnP o (size (PRE ++ pcode))) => Ho.
  - exfalso.
    move: Hnth.
    rewrite catA List.nth_error_app1; last first.
    { by apply/ltP. }
    exact: (@jump_free_nth (PRE ++ pcode) o Hjf2).
  - have Eo : o = size (PRE ++ pcode) + (o - size (PRE ++ pcode))
      by rewrite subnKC.
    have Hnth2 : List.nth_error POST (o - size (PRE ++ pcode))
                 = Some IJump.
    { move: Hnth.
      rewrite catA List.nth_error_app2; last by apply/leP.
      by have -> : (o - size (PRE ++ pcode))%coq_nat
                   = o - size (PRE ++ pcode) by lia. }
    rewrite catA Eo aux1_scan_cat_r /POST.
    move: Hnth2.
    rewrite /POST.
    case: (o - size (PRE ++ pcode)) => [|[|[|[|[|[|[|[|[|n]]]]]]]]] //=;
      last by case: n.
}
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (KEY ([:: IHalt] ++ EEM ++ PROL)).
  + by apply: (KEY (EEM ++ PROL)).
- by apply: (KEY (EEN ++ PROL)).
Qed.

(* ==================== generic positional checker ==================== *)

(* a per-position boolean condition over the three running scans *)
Fixpoint pos_check
    (f : Machine.instr -> bool -> Z -> bool -> bool)
    (c : Machine.code) (dead : bool) (d : Z) (ph : bool) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      f i dead d ph
      && pos_check f c' (ra_dead_step i dead) (sp_step i d)
           (ph_step i ph)
  end.

Lemma pos_check_sound
    (f : Machine.instr -> bool -> Z -> bool -> bool)
    (c : Machine.code) :
  forall (dead : bool) (d : Z) (ph : bool),
  pos_check f c dead d ph = true ->
  forall (o : nat) (i : Machine.instr),
    List.nth_error c o = Some i ->
    f i (ra_dead_scan c dead o) (sp_scan c d o) (ph_scan c ph o)
      = true.
Proof.
elim: c => [|i0 c' IH] dead d ph.
- by move=> _ o i; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o i.
  case: o => [|o'] /=.
  + by move=> [<-].
  + move=> Hnth. exact: (IH _ _ _ Hrest _ _ Hnth).
Qed.

(* ==================== body labels are live ==================== *)

Fixpoint llive_check (c : Machine.code) (dead : bool) : bool :=
  match c with
  | [::] => ~~ dead
  | i :: c' =>
      (match i with ILabel _ => ~~ dead | _ => true end)
      && llive_check c' (ra_dead_step i dead)
  end.

Lemma llive_check_sound (c : Machine.code) :
  forall (dead : bool),
  llive_check c dead = true ->
  forall (o : nat) (l : label),
    List.nth_error c o = Some (ILabel l) ->
    ra_dead_scan c dead o = false.
Proof.
elim: c => [|i0 c' IH] dead.
- by move=> _ o l; rewrite List.nth_error_nil.
- move=> /andP [Hc Hrest] o l.
  case: o => [|o'] /=.
  + move=> [E]. rewrite E in Hc.
    exact: (negbTE Hc).
  + move=> Hnth. exact: (IH _ Hrest _ _ Hnth).
Qed.

Lemma llive_check_bal (c : Machine.code) :
  forall (dead : bool),
  llive_check c dead = true ->
  ra_dead_scan c dead (size c) = false.
Proof.
elim: c => [|i c IH] dead /=.
- by move=> /negbTE.
- move=> /andP [_ Hrest]. exact: (IH _ Hrest).
Qed.

Record lab_live_ok (c : Machine.code) : Prop := LabLiveOk {
  llo_bal : ra_dead_scan c false (size c) = false;
  llo_live : forall (o : nat) (l : label),
      List.nth_error c o = Some (ILabel l) ->
      ra_dead_scan c false o = false
}.

Lemma lab_live_cat (c1 c2 : Machine.code) :
  lab_live_ok c1 -> lab_live_ok c2 -> lab_live_ok (c1 ++ c2).
Proof.
move=> [B1 F1] [B2 F2].
constructor.
- have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  rewrite ra_dead_scan_cat_r B1.
  exact: B2.
- move=> o l Hnth.
  case: (ltnP o (size c1)) => Ho.
  + have Hn1 : List.nth_error c1 o = Some (ILabel l).
    { move: Hnth. rewrite List.nth_error_app1 //. by apply/ltP. }
    rewrite (ra_dead_scan_cat_l _ _ (ltnW Ho)).
    exact: (F1 _ _ Hn1).
  + have Eo : o = size c1 + (o - size c1) by rewrite subnKC.
    have Hn2 : List.nth_error c2 (o - size c1) = Some (ILabel l).
    { move: Hnth.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size c1)%coq_nat = o - size c1 by lia. }
    rewrite Eo ra_dead_scan_cat_r B1.
    exact: (F2 _ _ Hn2).
Qed.

Lemma lab_live_cons (i : Machine.instr) (c : Machine.code) :
  ra_dead_step i false = false ->
  lab_live_ok c ->
  lab_live_ok (i :: c).
Proof.
move=> Hs [B F].
constructor.
- by rewrite /= Hs.
- move=> o l.
  case: o => [|o'] /=.
  + by [].
  + rewrite Hs. exact: F.
Qed.

Lemma llive_check_okP (c : Machine.code) :
  llive_check c false = true -> lab_live_ok c.
Proof.
move=> Hc.
constructor.
- exact: (llive_check_bal Hc).
- move=> o l Hnth. exact: (llive_check_sound Hc Hnth).
Qed.

(* compiled expression fragments hold every label live *)
Lemma compile_expr_lab_live (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  lab_live_ok c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _]; by apply: llive_check_okP.
- (* E_arg *)
  move: Hc => /= [<- _]. by apply: llive_check_okP.
- (* E_local *)
  move: Hc => /= [<- _]. by apply: llive_check_okP.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: lab_live_cat; first exact: (IH1 _ _ _ E1).
  apply: lab_live_cons => //.
  apply: lab_live_cons => //.
  apply: lab_live_cat; first exact: (IH2 _ _ _ E2).
  by apply: llive_check_okP.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (lab_live_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: lab_live_cat; first exact: (IH1 _ _ _ E1).
  apply: lab_live_cons => //.
  apply: lab_live_cat; first exact: (IH3 _ _ _ E3).
  apply: lab_live_cons => //.
  apply: lab_live_cons => //.
  apply: lab_live_cat; first exact: (IH2 _ _ _ E2).
  by apply: llive_check_okP.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: lab_live_cat; first exact: (IH _ _ _ E1).
  by apply: llive_check_okP.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: lab_live_cat; first exact: (IH _ _ _ E1).
  by apply: llive_check_okP.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: lab_live_cat; first exact: (IH2 _ _ _ E2).
  apply: lab_live_cons => //.
  apply: lab_live_cons => //.
  apply: lab_live_cat; first exact: (IH1 _ _ _ E1).
  by apply: llive_check_okP.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: lab_live_cat; first exact: (IH _ _ _ E1).
    by apply: llive_check_okP.
  + move=> [<- _].
    apply: lab_live_cat; first exact: (IH _ _ _ E1).
    by apply: llive_check_okP.
- (* E_exit *)
  move: Hc => /= [<- _]. by apply: llive_check_okP.
Qed.

(* ==================== the branch-target theorem ==================== *)

(* a taken branch in a compiled procedure lands on a live label, or —
   the entry wrapper's flag dispatch — stays in the same window with
   the same scan values *)
Lemma compile_proc_bnztgt (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : Machine.code) (s' : comp_env) (pl0 : label) :
  getm plm P0 = Some pl0 ->
  pl0 < nlab s C0 ->
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  forall (o o' : nat) (r : Machine.register) (l : label),
    List.nth_error cd o = Some (IBnz r l) ->
    List.nth_error cd o' = Some (ILabel l) ->
    dead_at cd o' = false
    \/ [/\ dead_at cd o = true,
           sp_scan cd 0%Z o' = sp_scan cd 0%Z o
         & ph_scan cd false o' = ph_scan cd false o].
Proof.
move=> Hpl0 Hplb Hcpc o o' r l Hb Hl.
case: (ltnP l (nlab s C0)) => Hlow.
{ left. exact: (compile_proc_label_low Hlow Hcpc Hl). }
move: Hcpc.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret Hpl0 /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=.
have [Ec2 Hn2] := fresh_label_inv E2.
have [Ec3 Hn3] := fresh_label_inv E3.
have [Hm4 [HlabIn _]] := compile_expr_labels E4.
have Hbnzi := compile_expr_bnz E4.
have Hbody := compile_expr_lab_live E4.
have Hpm : (lmain == pl0) = false by apply/eqP => E; lia.
have Hrp : (lreturn == pl0) = false by apply/eqP => E; lia.
have Hrm : (lreturn == lmain) = false by apply/eqP => E; lia.
set F := (fun (i : Machine.instr) (dead : bool) (d : Z) (ph : bool) =>
  match i with
  | ILabel l' =>
      [|| l' == pl0,
          (l' == lmain) && [&& dead, (d =? 2)%Z & ~~ ph]
        | (l' == lreturn) && ~~ dead]
  | IBnz _ l' =>
      (l' == lmain) ==> [&& dead, (d =? 2)%Z & ~~ ph]
  | _ => true
  end).
set SFZ := Z.of_nat (4 + stack_need e).
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set PROL := [:: ILabel pl0; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl0] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl0] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
have KEY : forall PRE : Machine.code,
    pos_check F PRE false 0%Z false = true ->
    ra_dead_scan PRE false (size PRE) = false ->
    cd = PRE ++ pcode ++ POST ->
    dead_at cd o' = false
    \/ [/\ dead_at cd o = true,
           sp_scan cd 0%Z o' = sp_scan cd 0%Z o
         & ph_scan cd false o' = ph_scan cd false o].
{ move=> PRE HPRE Hbal Ecd.
  rewrite Ecd in Hb Hl *.
  case: (ltnP o' (size PRE)) => Ho'.
  - have Hl'P : List.nth_error PRE o' = Some (ILabel l).
    { move: Hl. rewrite List.nth_error_app1 //. by apply/ltP. }
    have HF' := pos_check_sound HPRE Hl'P.
    move: HF'. rewrite /F /=.
    case/orP => [/eqP El | HF'].
    { exfalso. lia. }
    case/orP: HF'
      => [/andP [/eqP El Hpat] | /andP [/eqP El Hlive]]; last first.
    { left.
      rewrite /dead_at (ra_dead_scan_cat_l _ _ (ltnW Ho')).
      exact: (negbTE Hlive). }
    subst l.
    case/and3P: Hpat => Hd' /Z.eqb_eq Hd2' Hp'.
    have HoP : o < size PRE.
    { case: (ltnP o (size PRE)) => // HoG. exfalso.
      have Hk : List.nth_error (pcode ++ POST) (o - size PRE)
                = Some (IBnz r lmain).
      { move: Hb. rewrite List.nth_error_app2; last by apply/leP.
        by have -> : (o - size PRE)%coq_nat = o - size PRE by lia. }
      case: (ltnP (o - size PRE) (size pcode)) => Hk2.
      - have Hkp : List.nth_error pcode (o - size PRE)
                   = Some (IBnz r lmain).
        { move: Hk. rewrite List.nth_error_app1 //. by apply/ltP. }
        have := Hbnzi _ _ (List.nth_error_In _ _ Hkp).
        by lia.
      - have Hkq : List.nth_error POST (o - size PRE - size pcode)
                   = Some (IBnz r lmain).
        { move: Hk. rewrite List.nth_error_app2; last by apply/leP.
          by have -> : (o - size PRE - size pcode)%coq_nat
                       = o - size PRE - size pcode by lia. }
        have := List.nth_error_In _ _ Hkq.
        by move=> /= [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]];
          case: E. }
    have HbP : List.nth_error PRE o = Some (IBnz r lmain).
    { move: Hb. rewrite List.nth_error_app1 //. by apply/ltP. }
    have HFb := pos_check_sound HPRE HbP.
    move: HFb. rewrite /F /= eqxx /=.
    case/and3P => Hd /Z.eqb_eq Hd2 Hp.
    right.
    rewrite /dead_at (ra_dead_scan_cat_l _ _ (ltnW HoP))
            (sp_scan_cat_l _ _ (ltnW Ho'))
            (sp_scan_cat_l _ _ (ltnW HoP))
            (ph_scan_cat_l _ _ (ltnW Ho'))
            (ph_scan_cat_l _ _ (ltnW HoP)).
    split.
    + exact: Hd.
    + by rewrite Hd2' Hd2.
    + by rewrite (negbTE Hp') (negbTE Hp).
  - have Hk : List.nth_error (pcode ++ POST) (o' - size PRE)
              = Some (ILabel l).
    { move: Hl. rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o' - size PRE)%coq_nat = o' - size PRE by lia. }
    have Eo' : o' = size PRE + (o' - size PRE) by rewrite subnKC.
    case: (ltnP (o' - size PRE) (size pcode)) => Hk2.
    + have Hkp : List.nth_error pcode (o' - size PRE)
                 = Some (ILabel l).
      { move: Hk. rewrite List.nth_error_app1 //. by apply/ltP. }
      left.
      rewrite /dead_at Eo' ra_dead_scan_cat_r Hbal
              (ra_dead_scan_cat_l _ _ (ltnW Hk2)).
      exact: (llo_live Hbody Hkp).
    + exfalso.
      have Hkq : List.nth_error POST (o' - size PRE - size pcode)
                 = Some (ILabel l).
      { move: Hk. rewrite List.nth_error_app2; last by apply/leP.
        by have -> : (o' - size PRE - size pcode)%coq_nat
                     = o' - size PRE - size pcode by lia. }
      have := List.nth_error_In _ _ Hkq.
      by move=> /= [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]];
        case: E. }
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + move=> [Ecd _].
    apply: (KEY ([:: IHalt] ++ EEM ++ PROL)).
    * by rewrite /F /= !eqxx ?Hpm ?Hrp ?Hrm /=.
    * by [].
    * by rewrite -Ecd.
  + move=> [Ecd _].
    apply: (KEY (EEM ++ PROL)).
    * by rewrite /F /= !eqxx ?Hpm ?Hrp ?Hrm /=.
    * by [].
    * by rewrite -Ecd.
- move=> [Ecd _].
  apply: (KEY (EEN ++ PROL)).
  + by rewrite /F /= !eqxx ?Hpm ?Hrp ?Hrm /=.
  + by [].
  + by rewrite -Ecd.
Qed.

(* the I-side run invariant, v1: the return register is clear, and
   inside call windows the RA slot is pinned and cleared *)
Definition iinv (scr_of : Component.id -> Pointer.t) (s : CS.state)
  : Prop :=
  match s with
  | (gps, imem, iregs, pc) =>
      Intermediate.Register.get R_RA iregs = Undef
      /\ (forall (Cprocs : NMap Machine.code) (j : nat)
                 (P0 : Procedure.id) (Pcode : Machine.code),
            Intermediate.prog_procedures ilp (Pointer.component pc)
              = Some Cprocs ->
            Pointer.block pc
              = proc_nb0 ilp (Pointer.component pc) + j ->
            List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
            (0 <= Pointer.offset pc)%Z ->
            dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
            win_state imem iregs (scr_of (Pointer.component pc))
              (Pointer.component pc) Pcode
              (Z.to_nat (Pointer.offset pc)))
      /\ (exists fbs, iframes imem gps fbs)
  end.

(* ---- preservation: neutral pc-increment steps ---- *)

(* covers every case that advances the pc without touching memory, the
   stack, R_RA, R_SP, or the window/offset/phase classes *)
Lemma iinv_step_neutral (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  ra_dead_step i = id ->
  sp_step i = id ->
  ph_step i = id ->
  Intermediate.Register.get R_RA iregs'
    = Intermediate.Register.get R_RA iregs ->
  Intermediate.Register.get R_SP iregs'
    = Intermediate.Register.get R_SP iregs ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs', Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hsp Hph Era Esp [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- by rewrite Era.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= => Hdead.
  have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
  move: Hwin.
  rewrite /win_state
    (sp_scan_S _ Hnth) Hsp (ph_scan_S _ Hnth) Hph /=.
  move=> [fb [spo [Hslot Hloc]]].
  exists fb, spo.
  split; first exact: Hslot.
  case: (ph_scan Pcode false (Z.to_nat oI)) Hloc => Hloc.
  + exact: Hloc.
  + by rewrite Esp.
- exact: H3.
Qed.

(* parked frames live in other components or other blocks than a given
   store target *)
Fixpoint frames_sep (gps : list Pointer.t)
    (fbs : list (option (Block.id * Z)))
    (cp : Component.id) (bp : Block.id) : Prop :=
  match gps, fbs with
  | p :: rest, Some (fb, _) :: fbs' =>
      (Pointer.component p <> cp \/ fb <> bp)
      /\ frames_sep rest fbs' cp bp
  | p :: rest, None :: fbs' => frames_sep rest fbs' cp bp
  | _, _ => True
  end.

Lemma iframes_store (imem imem' : Memory.Memory.t)
    (ptr : Pointer.t) (v : value)
    (gps : list Pointer.t) (fbs : list (option (Block.id * Z))) :
  Memory.Memory.store imem ptr v = Some imem' ->
  frames_sep gps fbs (Pointer.component ptr) (Pointer.block ptr) ->
  iframes imem gps fbs ->
  iframes imem' gps fbs.
Proof.
move=> Hst.
elim: gps fbs => [|p rest IH] [|[[fb sl]|] fbs'] //=; last first.
- move=> Hsep Hrest. exact: (IH _ Hsep Hrest).
- move=> [Hd Hsep] [Hload Hrest].
  split; last exact: (IH _ Hsep Hrest).
  case: Hd => Hd.
  + by rewrite (@load_store_other_comp _ _ _ _ _ _ _ Hst
        (not_eq_sym Hd)).
  + by rewrite (@load_store_other_block _ _ _ _ _ _ _ Hst
        (not_eq_sym Hd)).
Qed.

(* ---- preservation: the window-opening push of R_RA ---- *)

Lemma iinv_step_push_ra (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code)
    (bp : Block.id) (op : Z) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc))
    = Some (IStore R_SP R_RA) ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  Intermediate.Register.get R_SP iregs
    = Ptr (Pointer.component pc, bp, op) ->
  Memory.Memory.store imem (Pointer.component pc, bp, op)
    (Intermediate.Register.get R_RA iregs) = Some imem' ->
  (forall fbs, iframes imem gps fbs ->
     frames_sep gps fbs (Pointer.component pc) bp) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem', iregs, Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hph Hsp Hst Hsepall [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- exact: H1.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' => /= Hilp' Hblk' Hjnth'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  rewrite /win_state Hoffi
    (sp_scan_S _ Hnth) (ph_scan_S _ Hnth) /= Hph.
  exists bp, op.
  split.
  + rewrite Z.sub_0_r.
    rewrite H1 in Hst.
    exact: (Memory.Memory.load_after_store_eq _ _ _ _ Hst).
  + exact: Hsp.
- case: H3 => fbs Hfr.
  exists fbs.
  apply: (iframes_store Hst _ Hfr).
  exact: (Hsepall _ Hfr).
Qed.

(* ---- preservation: the window-closing pop of R_RA ---- *)

Lemma get_set_eq (regs : Intermediate.Register.t)
    (r : Machine.register) (v : value) :
  Intermediate.Register.get r (Intermediate.Register.set r v regs) = v.
Proof.
by rewrite /Intermediate.Register.get /Intermediate.Register.set
  setmE eqxx.
Qed.

Lemma get_set_other (regs : Intermediate.Register.t)
    (r r' : Machine.register) (v : value) :
  Intermediate.Register.to_nat r <> Intermediate.Register.to_nat r' ->
  Intermediate.Register.get r (Intermediate.Register.set r' v regs)
  = Intermediate.Register.get r regs.
Proof.
move=> Hne.
by rewrite /Intermediate.Register.get /Intermediate.Register.set
  setmE; case: eqP => // E; rewrite E in Hne.
Qed.

(* the pop reads the pinned slot, so R_RA comes back Undef and the
   window closes *)
Lemma iinv_step_pop_ra (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code)
    (ptr : Pointer.t) (v : value) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc))
    = Some (ILoad R_SP R_RA) ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
  sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc)) = 0%Z ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  Intermediate.Register.get R_SP iregs = Ptr ptr ->
  Memory.Memory.load imem ptr = Some v ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (gps, imem, Intermediate.Register.set R_RA v iregs,
     Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hdead Hd0 Hph Hsp Hload [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
move: Hwin. rewrite /win_state Hph Hd0.
move=> [fb [spo [Hslot Hloc]]].
have Eptr : ptr = (cI, fb, spo).
{ move: Hsp. rewrite Hloc. by move=> [->]. }
have Ev : v = Undef.
{ move: Hload. rewrite Eptr.
  move: Hslot. rewrite Z.sub_0_r. move=> ->.
  by move=> [->]. }
split; [|split].
- by rewrite Ev get_set_eq.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hdead /=.
  by [].
- exact: H3.
Qed.

(* ---- preservation: general stores (window-neutral targets) ---- *)

Lemma iinv_step_store (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (r1 r2 : Machine.register)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code)
    (bp : Block.id) (op : Z) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc))
    = Some (IStore r1 r2) ->
  ra_dead_step (IStore r1 r2) = id ->
  sp_step (IStore r1 r2) = id ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  Memory.Memory.store imem (Pointer.component pc, bp, op)
    (Intermediate.Register.get r2 iregs) = Some imem' ->
  (forall fb spo,
     Intermediate.Register.get R_SP iregs
       = Ptr (Pointer.component pc, fb, spo) ->
     bp <> fb
     \/ op <> (spo - sp_scan Pcode 0%Z
                       (Z.to_nat (Pointer.offset pc)))%Z) ->
  (forall fbs, iframes imem gps fbs ->
     frames_sep gps fbs (Pointer.component pc) bp) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem', iregs, Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hsp Hph Hst Hsep Hsepf
  [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- exact: H1.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= => Hdead.
  have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
  move: Hwin.
  rewrite /win_state
    (sp_scan_S _ Hnth) Hsp (ph_scan_S _ Hnth) /= Hph.
  move=> [fb [spo [Hslot Hloc]]].
  exists fb, spo.
  split; last exact: Hloc.
  case: (Hsep _ _ Hloc) => Hne.
  + by rewrite (@load_store_other_block _ _ _ _ _ _ _ Hst Hne).
  + by rewrite (@load_store_other_off _ _ _ _ _ _ _ Hst Hne).
- case: H3 => fbs Hfr.
  exists fbs.
  apply: (iframes_store Hst _ Hfr).
  exact: (Hsepf _ Hfr).
Qed.

(* ---- preservation: live-position silent steps and branches ---- *)

(* outside a window ANY register write is fine: the successor of a
   window-neutral live position is live, so the window conjunct is
   vacuous *)
Lemma iinv_step_live_any (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  ra_dead_step i = id ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = false ->
  Intermediate.Register.get R_RA iregs'
    = Intermediate.Register.get R_RA iregs ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs', Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hlive Era [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- by rewrite Era.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= Hlive.
  by [].
- exact: H3.
Qed.

(* a silent branch/jump landing on a LIVE position of the same
   procedure keeps everything (memory, registers, stack unchanged) *)
Lemma iinv_step_live_jump (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc')
    = Some Cprocs ->
  Pointer.block pc' = proc_nb0 ilp (Pointer.component pc') + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  ((0 <= Pointer.offset pc')%Z ->
   dead_at Pcode (Z.to_nat (Pointer.offset pc')) = false) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs, pc').
Proof.
move=> Hilp Hblk Hjnth Hlive [H1 [H2 H3]].
split; [|split].
- exact: H1.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  by rewrite (Hlive Hoff') in Hdead'.
- exact: H3.
Qed.

(* a branch inside a window whose target stays in the SAME window with
   the same scan values (the entry wrapper's flag dispatch): the open
   window's data transfers verbatim *)
Lemma iinv_step_window_jump (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  Pointer.component pc = Pointer.component pc' ->
  Pointer.block pc = Pointer.block pc' ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
  sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc'))
    = sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc)) ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc'))
    = ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs, pc').
Proof.
move=> Hilp Hblk Hjnth Hoff Hcm Hbk Hd Esp Eph [H1 [H2 H3]].
split; [|split].
- exact: H1.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk'. rewrite -Hcm -Hbk => Hilp' Hblk'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  rewrite /win_state Esp Eph.
  exact: (H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hd).
- exact: H3.
Qed.

(* ---- preservation: the cross-window R_SP reload ---- *)

Lemma iinv_step_reload (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) (v : value) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc))
    = Some (ILoad R_SP R_SP) ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
  Intermediate.Register.get R_SP iregs
    = Ptr (scr_of (Pointer.component pc)) ->
  Memory.Memory.load imem (scr_of (Pointer.component pc)) = Some v ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (gps, imem, Intermediate.Register.set R_SP v iregs,
     Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hdead Hph Hsp Hload [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
move: Hwin. rewrite /win_state Hph.
move=> [fb [spo [Hslot Hloc]]].
have Ev : v = Ptr (cI, fb, spo).
{ move: Hload.
  have -> : scr_of cI
            = (Pointer.component (scr_of cI),
               Pointer.block (scr_of cI),
               Pointer.offset (scr_of cI)).
  { by case: (scr_of cI) => [[? ?] ?]. }
  rewrite Hloc. by move=> [->]. }
split; [|split].
- rewrite get_set_other; first exact: H1.
  by [].
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' => /= Hilp' Hblk' Hjnth'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  rewrite /win_state Hoffi
    (sp_scan_S _ Hnth) (ph_scan_S _ Hnth) Hph /=.
  exists fb, spo.
  split; first exact: Hslot.
  rewrite Ev.
  exact: get_set_eq.
- exact: H3.
Qed.

(* ---- preservation: allocation ---- *)

(* allocation leaves every cell outside the fresh block untouched *)
Lemma load_after_alloc_other (mem mem' : Memory.Memory.t)
    (C0 : Component.id) (n : nat) (ptr : Pointer.t)
    (C : Component.id) (b : Block.id) (o : Z) :
  Memory.Memory.alloc mem C0 n = Some (mem', ptr) ->
  (C <> C0 \/ b <> Pointer.block ptr) ->
  Memory.Memory.load mem' (C, b, o) = Memory.Memory.load mem (C, b, o).
Proof.
rewrite /Memory.Memory.alloc /Memory.Memory.load /=.
case EmC: (mem C0) => [memC|] //.
case Ea: (ComponentMemory.alloc memC n) => [memC' bf].
move=> [E1 E2]. subst mem'.
have Eb : Pointer.block ptr = bf by rewrite -E2.
rewrite setmE.
case: eqP => [EC | //].
subst C.
move=> [Hne | Hne]; first by [].
rewrite EmC.
apply: (ComponentMemory.load_after_alloc _ _ _ _ Ea).
by rewrite -Eb.
Qed.

Lemma iframes_alloc (mem mem' : Memory.Memory.t)
    (C0 : Component.id) (n : nat) (ptr : Pointer.t)
    (gps : list Pointer.t) (fbs : list (option (Block.id * Z))) :
  Memory.Memory.alloc mem C0 n = Some (mem', ptr) ->
  frames_sep gps fbs C0 (Pointer.block ptr) ->
  iframes mem gps fbs ->
  iframes mem' gps fbs.
Proof.
move=> Hal.
elim: gps fbs => [|p rest IH] [|[[fb sl]|] fbs'] //=; last first.
- move=> Hsep Hrest. exact: (IH _ Hsep Hrest).
- move=> [Hd Hsep] [Hload Hrest].
  split; last exact: (IH _ Hsep Hrest).
  by rewrite (@load_after_alloc_other _ _ _ _ _ _ _ _ Hal) //.
Qed.

(* live-position allocation: the fresh block misses every slot *)
Lemma iinv_step_alloc_live (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code)
    (n : nat) (ptr : Pointer.t) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  ra_dead_step i = id ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = false ->
  Memory.Memory.alloc imem (Pointer.component pc) n
    = Some (imem', ptr) ->
  Intermediate.Register.get R_RA iregs'
    = Intermediate.Register.get R_RA iregs ->
  (forall fbs, iframes imem gps fbs ->
     frames_sep gps fbs (Pointer.component pc) (Pointer.block ptr)) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem', iregs', Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hlive Hal Era Hsepall
  [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- by rewrite Era.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= Hlive.
  by [].
- case: H3 => fbs Hfr.
  exists fbs.
  apply: (iframes_alloc Hal _ Hfr).
  exact: (Hsepall _ Hfr).
Qed.

(* ---- preservation: the pushes (Jal / Call) ---- *)

(* an intra-component call: R_RA is clobbered, the open window's slot
   parks into the frame chain, and the entry label target is live *)
Lemma iinv_step_jal (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  (forall (Cprocs' : NMap Machine.code) (j' : nat)
          (P0' : Procedure.id) (Pcode' : Machine.code),
     Intermediate.prog_procedures ilp (Pointer.component pc')
       = Some Cprocs' ->
     Pointer.block pc'
       = proc_nb0 ilp (Pointer.component pc') + j' ->
     List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
     (0 <= Pointer.offset pc')%Z ->
     dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = false) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (Pointer.inc pc :: gps, imem,
     Intermediate.Register.set R_RA Undef iregs, pc').
Proof.
move=> Hilp Hblk Hjnth Hoff Hdead Hph Htgt [H1 [H2 H3]].
have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
move: Hwin. rewrite /win_state Hph.
move=> [fb [spo [Hslot Hloc]]].
split; [|split].
- exact: get_set_eq.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  by rewrite (Htgt _ _ _ _ Hilp' Hblk' Hjnth' Hoff') in Hdead'.
- case: H3 => fbs Hfr.
  exists (Some (fb, (spo - sp_scan Pcode 0%Z
                       (Z.to_nat (Pointer.offset pc)))%Z) :: fbs).
  rewrite /=.
  split; last exact: Hfr.
  rewrite Pointer.inc_preserves_component.
  exact: Hslot.
Qed.

(* a cross-component call: registers are invalidated, the target entry
   position is live by construction *)
Lemma iinv_step_call (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (C' : Component.id) (b' : Block.id)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (Pointer.inc pc :: gps, imem,
     Intermediate.Register.invalidate iregs, (C', b', 0%Z)).
Proof.
move=> Hilp Hblk Hjnth Hoff Hdead Hph [H1 [H2 H3]].
have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
move: Hwin. rewrite /win_state Hph.
move=> [fb [spo [Hslot Hloc]]].
split; [|split].
- by rewrite invalidate_get.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hdead' => /=.
  by rewrite dead_at0.
- case: H3 => fbs Hfr.
  exists (Some (fb, (spo - sp_scan Pcode 0%Z
                       (Z.to_nat (Pointer.offset pc)))%Z) :: fbs).
  rewrite /=.
  split; last exact: Hfr.
  rewrite Pointer.inc_preserves_component.
  exact: Hslot.
Qed.

(* a live jal (the bottom stub's dispatch): no window is open, so the
   pushed return address carries no frame; its target is live, so the
   matching pop never needs one *)
Lemma iinv_step_jal_live (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t) :
  (forall (Cprocs' : NMap Machine.code) (j' : nat)
          (P0' : Procedure.id) (Pcode' : Machine.code),
     Intermediate.prog_procedures ilp (Pointer.component pc')
       = Some Cprocs' ->
     Pointer.block pc'
       = proc_nb0 ilp (Pointer.component pc') + j' ->
     List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
     (0 <= Pointer.offset pc')%Z ->
     dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = false) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (Pointer.inc pc :: gps, imem,
     Intermediate.Register.set R_RA Undef iregs, pc').
Proof.
move=> Htgt [H1 [H2 H3]].
split; [|split].
- exact: get_set_eq.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  by rewrite (Htgt _ _ _ _ Hilp' Hblk' Hjnth' Hoff') in Hdead'.
- case: H3 => fbs Hfr.
  by exists (None :: fbs).
Qed.

(* ---- preservation: the pops (Jump / Return) ---- *)

(* an intra-component return: the popped frame's slot re-opens as the
   running window; the restored R_SP locates it (given here as a
   run-level premise, discharged by the restore-chain model) *)
Lemma iinv_step_jump (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t) :
  (forall (f : option (Block.id * Z))
          (fbs' : list (option (Block.id * Z)))
          (Cprocs' : NMap Machine.code) (j' : nat)
          (P0' : Procedure.id) (Pcode' : Machine.code),
     iframes imem (pc' :: gps) (f :: fbs') ->
     Intermediate.prog_procedures ilp (Pointer.component pc')
       = Some Cprocs' ->
     Pointer.block pc'
       = proc_nb0 ilp (Pointer.component pc') + j' ->
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
                          (Z.to_nat (Pointer.offset pc')))%Z)]) ->
  iinv scr_of (pc' :: gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs, pc').
Proof.
move=> Htie [H1 [H2 H3]].
case: H3 => [[|f fbs']] //= Hifr.
split; [|split].
- exact: H1.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  have [fb [sl [Ef Hph HSP]]] := Htie f fbs' _ _ _ _
    Hifr Hilp' Hblk' Hjnth' Hoff' Hdead'.
  rewrite /win_state Hph.
  exists fb, (sl + sp_scan Pcode' 0%Z
                     (Z.to_nat (Pointer.offset pc')))%Z.
  split; last exact: HSP.
  have -> : ((sl + sp_scan Pcode' 0%Z (Z.to_nat (Pointer.offset pc')))
             - sp_scan Pcode' 0%Z (Z.to_nat (Pointer.offset pc')))%Z
            = sl by lia.
  move: Hifr. rewrite Ef /=.
  by move=> [Hslot _].
- exists fbs'.
  move: Hifr.
  by case: f => [[fb sl]|] /= => [[_ H]|H].
Qed.

(* a cross-component return: registers are invalidated; the caller sits
   in its post-call phase with R_SP parked in the scratch cell *)
Lemma iinv_step_return (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc pc' : Pointer.t) :
  (forall (f : option (Block.id * Z))
          (fbs' : list (option (Block.id * Z)))
          (Cprocs' : NMap Machine.code) (j' : nat)
          (P0' : Procedure.id) (Pcode' : Machine.code),
     iframes imem (pc' :: gps) (f :: fbs') ->
     Intermediate.prog_procedures ilp (Pointer.component pc')
       = Some Cprocs' ->
     Pointer.block pc'
       = proc_nb0 ilp (Pointer.component pc') + j' ->
     List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
     (0 <= Pointer.offset pc')%Z ->
     dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
     exists fb sl,
       [/\ f = Some (fb, sl),
           ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
             = true
         & Memory.Memory.load imem
             (Pointer.component (scr_of (Pointer.component pc')),
              Pointer.block (scr_of (Pointer.component pc')),
              Pointer.offset (scr_of (Pointer.component pc')))
           = Some (Ptr (Pointer.component pc', fb,
                        (sl + sp_scan Pcode' 0%Z
                                (Z.to_nat (Pointer.offset pc')))%Z))]) ->
  iinv scr_of (pc' :: gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, Intermediate.Register.invalidate iregs, pc').
Proof.
move=> Htie [H1 [H2 H3]].
case: H3 => [[|f fbs']] //= Hifr.
split; [|split].
- by rewrite invalidate_get.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  have [fb [sl [Ef Hph Hscr]]] := Htie f fbs' _ _ _ _
    Hifr Hilp' Hblk' Hjnth' Hoff' Hdead'.
  rewrite /win_state Hph.
  exists fb, (sl + sp_scan Pcode' 0%Z
                     (Z.to_nat (Pointer.offset pc')))%Z.
  split.
  + have -> : ((sl + sp_scan Pcode' 0%Z
                       (Z.to_nat (Pointer.offset pc')))
               - sp_scan Pcode' 0%Z
                   (Z.to_nat (Pointer.offset pc')))%Z
              = sl by lia.
    move: Hifr. rewrite Ef /=.
    by move=> [Hslot _].
  + exact: Hscr.
- exists fbs'.
  move: Hifr.
  by case: f => [[fb sl]|] /= => [[_ H]|H].
Qed.

(* ---- preservation: the in-window SP moves ---- *)

(* the push/pop increments: R_SP and the tracked offset move together,
   so the located slot is unchanged *)
Lemma iinv_step_spmove (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr) (dz : Z) (v' : value)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  ra_dead_step i = id ->
  ph_step i = ssrfun.id ->
  (forall d : Z, sp_step i d = (d + dz)%Z) ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false ->
  (forall (c : Component.id) (b : Block.id) (o : Z),
     Intermediate.Register.get R_SP iregs = Ptr (c, b, o) ->
     v' = Ptr (c, b, (o + dz)%Z)) ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of
    (gps, imem, Intermediate.Register.set R_SP v' iregs,
     Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hph Hspd Hphv Hev [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- rewrite get_set_other; first exact: H1.
  by [].
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= => Hdead.
  have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
  move: Hwin.
  rewrite /win_state (sp_scan_S _ Hnth) Hspd (ph_scan_S _ Hnth) Hph
    /= Hphv.
  move=> [fb [spo [Hslot Hloc]]].
  exists fb, (spo + dz)%Z.
  split.
  + have -> : ((spo + dz)
               - (sp_scan Pcode 0%Z (Z.to_nat oI) + dz))%Z
              = (spo - sp_scan Pcode 0%Z (Z.to_nat oI))%Z by lia.
    exact: Hslot.
  + rewrite (Hev _ _ _ Hloc).
    exact: get_set_eq.
- exact: H3.
Qed.

(* during the post-call phase the slot is located through the scratch
   cell, so even R_SP writes are free *)
Lemma iinv_step_neutral_ph (scr_of : Component.id -> Pointer.t)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  ra_dead_step i = id ->
  sp_step i = ssrfun.id ->
  ph_step i = ssrfun.id ->
  ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
  Intermediate.Register.get R_RA iregs'
    = Intermediate.Register.get R_RA iregs ->
  iinv scr_of (gps, imem, iregs, pc) ->
  iinv scr_of (gps, imem, iregs', Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hrd Hsp Hph Hphv Era [H1 [H2 H3]].
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ by lia. }
split; [|split].
- by rewrite Era.
- move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Hdead'.
  move: Hilp' Hblk' Hjnth' Hdead' => /= Hilp' Hblk' Hjnth' Hdead'.
  have Ecp : Cprocs' = Cprocs.
  { move: Hilp'. rewrite Hilp. by move=> [->]. }
  subst Cprocs'.
  have Ej : j' = j by lia.
  subst j'.
  have EQ : (P0', Pcode') = (P0, Pcode).
  { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
  case: EQ => E1 E2. subst P0' Pcode'.
  move: Hdead'. rewrite Hoffi (dead_at_S Hnth) Hrd /= => Hdead.
  have Hwin := H2 _ _ _ _ Hilp Hblk Hjnth Hoff Hdead.
  move: Hwin.
  rewrite /win_state
    (sp_scan_S _ Hnth) Hsp (ph_scan_S _ Hnth) Hph /= Hphv.
  move=> [fb [spo [Hslot Hloc]]].
  exists fb, spo.
  by split.
- exact: H3.
Qed.

(* ---- the assembly layer ---- *)

(* an executing pc decomposes into the linked position bundle *)
Lemma executing_bundle (pc : Pointer.t) (i : Machine.instr) :
  Intermediate.well_formed_program ilp ->
  Intermediate.GlobalEnv.executing G pc i ->
  exists (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    [/\ Intermediate.prog_procedures ilp (Pointer.component pc)
          = Some Cprocs,
        Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j,
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode),
        (0 <= Pointer.offset pc)%Z
      & List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i].
Proof.
move=> Hwf Hex.
have Hin := executing_domm Hex.
case: (Hex) => C_procs [P_code [HgC [HgB [Hge Hnth]]]].
have [Cprocs Hilp] : exists Cprocs,
    Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs.
{ move: (Hin).
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm.
  case E: (Intermediate.prog_procedures _ _) => [Cprocs|] // _.
  by exists Cprocs. }
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
have E : CprocsB = C_procs.
{ move: HgB'. rewrite HgC. by move=> [->]. }
subst CprocsB.
have [j [P0 [Hblk Hjnth]]] := Hbwd _ _ HgB.
exists Cprocs, j, P0, P_code.
split=> //.
by lia.
Qed.

(* the initial state satisfies the invariant *)
Lemma iinv_init (scr_of : Component.id -> Pointer.t) :
  iinv scr_of (CS.initial_machine_state ilp).
Proof.
rewrite /CS.initial_machine_state.
case: (Intermediate.prog_main ilp).
- case: (Intermediate.prepare_procedures_initial_memory ilp)
    => [[mem0 procs0] entry0].
  split; [|split].
  + by [].
  + move=> Cprocs' j' P0' Pcode' _ _ _ _ /=.
    by rewrite dead_at0.
  + by exists [::].
- split; [|split].
  + by [].
  + move=> Cprocs' j' P0' Pcode' _ _ _ _ /=.
    by rewrite dead_at0.
  + by exists [::].
Qed.

(* step-shape helpers for abstract registers *)
Lemma reg_sp_dec (r : Machine.register) : r = R_SP \/ r <> R_SP.
Proof. by case: r; [right|right|right|right|right|left|right]. Qed.

Lemma ra_dead_step_store_other (r1 r2 : Machine.register) :
  r2 <> R_RA -> ra_dead_step (IStore r1 r2) = id.
Proof. by case: r2. Qed.

Lemma ra_dead_step_load_other (r1 r2 : Machine.register) :
  r2 <> R_RA -> ra_dead_step (ILoad r1 r2) = id.
Proof. by case: r2. Qed.

Lemma sp_step_store_other (r1 r2 : Machine.register) :
  r2 <> R_RA -> sp_step (IStore r1 r2) = ssrfun.id.
Proof. by case: r2. Qed.

Lemma sp_step_binop_other (op : Values.binop)
    (r1 r2 r3 : Machine.register) :
  r3 <> R_SP -> sp_step (IBinOp op r1 r2 r3) = ssrfun.id.
Proof.
move=> Hne.
by case: op => //=; case: r1 => //=; case: r2 => //=;
  case: r3 Hne => //= Hne; case: (Hne erefl).
Qed.

Lemma get_set_neq (regs : Intermediate.Register.t)
    (r r' : Machine.register) (v : value) :
  r <> r' ->
  Intermediate.Register.get r (Intermediate.Register.set r' v regs)
  = Intermediate.Register.get r regs.
Proof.
move=> Hne. apply: get_set_other => E.
apply: Hne. exact: (to_nat_inj E).
Qed.

Section IInvAssembly.

Variable scr_of : Component.id -> Pointer.t.
Hypothesis Hwf : Intermediate.well_formed_program ilp.

(* static class facts of compiled code at the fetched instruction
   (discharged from the shape/discipline theorems + a phase checker) *)
Hypothesis Hclass :
  forall (pc : Pointer.t) (i : Machine.instr)
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures ilp (Pointer.component pc)
      = Some Cprocs ->
    Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
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
        (* NOT dead ∧ ¬ph: the bottom stub's jal is live.  In a window
           the phase is off; live jals push no frame. *)
        dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true ->
        ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false
    | ICall _ _ =>
        dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true
        /\ ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = false
    | _ => True
    end.

(* run-level residuals (the chain/taint model) *)
Hypothesis Hone :
  forall (gps : CS.stack) (imem : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc : Pointer.t)
         (op : Values.binop) (c : Component.id) (b : Block.id) (o : Z),
    ireach pra prb (gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing G pc
      (IBinOp op R_SP R_ONE R_SP) ->
    Intermediate.Register.get R_SP iregs = Ptr (c, b, o) ->
    eval_binop op (Ptr (c, b, o))
      (Intermediate.Register.get R_ONE iregs)
    = Ptr (c, b, (o + match op with Add => 1 | _ => -1 end)%Z).

(* only the POST-CALL reload (phase on) — the epilogue's pop of the
   saved SP is also an [ILoad R_SP R_SP] but reads a frame slot *)
Hypothesis Hreload :
  forall (gps : CS.stack) (imem : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc : Pointer.t)
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    ireach pra prb (gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing G pc (ILoad R_SP R_SP) ->
    Intermediate.prog_procedures ilp (Pointer.component pc)
      = Some Cprocs ->
    Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    ph_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
    Intermediate.Register.get R_SP iregs
      = Ptr (scr_of (Pointer.component pc)).

Hypothesis Hjaltgt :
  forall (pc : Pointer.t) (l : label) (pc' : Pointer.t),
    Intermediate.GlobalEnv.executing G pc (IJal l) ->
    Intermediate.GlobalEnv.find_label_in_component G pc l
      = Some pc' ->
    forall (Cprocs' : NMap Machine.code) (j' : nat)
           (P0' : Procedure.id) (Pcode' : Machine.code),
      Intermediate.prog_procedures ilp (Pointer.component pc')
        = Some Cprocs' ->
      Pointer.block pc'
        = proc_nb0 ilp (Pointer.component pc') + j' ->
      List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
      (0 <= Pointer.offset pc')%Z ->
      dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = false.

(* a taken branch either leaves every window (the expression-level
   forward branches) or stays inside the SAME window with the same
   scan values (the entry wrapper's flag dispatch, [IBnz _ lmain]) —
   both stated over the SOURCE bundle, valid since the target shares
   its component and block *)
Hypothesis Hbnztgt :
  forall (pc : Pointer.t) (r : Machine.register) (l : label)
         (pc' : Pointer.t),
    Intermediate.GlobalEnv.executing G pc (IBnz r l) ->
    Intermediate.GlobalEnv.find_label_in_procedure G pc l
      = Some pc' ->
    forall (Cprocs : NMap Machine.code) (j : nat)
           (P0 : Procedure.id) (Pcode : Machine.code),
      Intermediate.prog_procedures ilp (Pointer.component pc)
        = Some Cprocs ->
      Pointer.block pc
        = proc_nb0 ilp (Pointer.component pc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      dead_at Pcode (Z.to_nat (Pointer.offset pc')) = false
      \/ [/\ dead_at Pcode (Z.to_nat (Pointer.offset pc)) = true,
             sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc'))
               = sp_scan Pcode 0%Z (Z.to_nat (Pointer.offset pc))
           & ph_scan Pcode false (Z.to_nat (Pointer.offset pc'))
               = ph_scan Pcode false (Z.to_nat (Pointer.offset pc))].

Hypothesis Hjumptie :
  forall (gps : CS.stack) (imem : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc pc' : Pointer.t),
    ireach pra prb (pc' :: gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing G pc IJump ->
    forall (f : option (Block.id * Z))
           (fbs' : list (option (Block.id * Z)))
           (Cprocs' : NMap Machine.code) (j' : nat)
           (P0' : Procedure.id) (Pcode' : Machine.code),
      iframes imem (pc' :: gps) (f :: fbs') ->
      Intermediate.prog_procedures ilp (Pointer.component pc')
        = Some Cprocs' ->
      Pointer.block pc'
        = proc_nb0 ilp (Pointer.component pc') + j' ->
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
                           (Z.to_nat (Pointer.offset pc')))%Z)].

Hypothesis Hreturntie :
  forall (gps : CS.stack) (imem : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc pc' : Pointer.t),
    ireach pra prb (pc' :: gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing G pc IReturn ->
    forall (f : option (Block.id * Z))
           (fbs' : list (option (Block.id * Z)))
           (Cprocs' : NMap Machine.code) (j' : nat)
           (P0' : Procedure.id) (Pcode' : Machine.code),
      iframes imem (pc' :: gps) (f :: fbs') ->
      Intermediate.prog_procedures ilp (Pointer.component pc')
        = Some Cprocs' ->
      Pointer.block pc'
        = proc_nb0 ilp (Pointer.component pc') + j' ->
      List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
      (0 <= Pointer.offset pc')%Z ->
      dead_at Pcode' (Z.to_nat (Pointer.offset pc')) = true ->
      exists fb sl,
        [/\ f = Some (fb, sl),
            ph_scan Pcode' false (Z.to_nat (Pointer.offset pc'))
              = true
          & Memory.Memory.load imem
              (Pointer.component (scr_of (Pointer.component pc')),
               Pointer.block (scr_of (Pointer.component pc')),
               Pointer.offset (scr_of (Pointer.component pc')))
            = Some (Ptr (Pointer.component pc', fb,
                         (sl + sp_scan Pcode' 0%Z
                                 (Z.to_nat (Pointer.offset pc')))%Z))].

Hypothesis Hstoresep :
  forall (gps : CS.stack) (imem : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc : Pointer.t)
         (r1 r2 : Machine.register) (bp : Block.id) (op : Z)
         (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    ireach pra prb (gps, imem, iregs, pc) ->
    Intermediate.GlobalEnv.executing G pc (IStore r1 r2) ->
    Intermediate.prog_procedures ilp (Pointer.component pc)
      = Some Cprocs ->
    Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
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
          frames_sep gps fbs (Pointer.component pc) bp).

Hypothesis Hallocsep :
  forall (gps : CS.stack) (imem imem' : Memory.Memory.t)
         (iregs : Intermediate.Register.t) (pc : Pointer.t)
         (n : nat) (ptr : Pointer.t),
    ireach pra prb (gps, imem, iregs, pc) ->
    Memory.Memory.alloc imem (Pointer.component pc) n
      = Some (imem', ptr) ->
    forall fbs, iframes imem gps fbs ->
      frames_sep gps fbs (Pointer.component pc) (Pointer.block ptr).

(* the dispatcher *)
Lemma iinv_step (s : CS.state) (t : Events.trace) (s' : CS.state) :
  ireach pra prb s ->
  CS.step G s t s' ->
  iinv scr_of s -> iinv scr_of s'.
Proof.
move=> Hreach Hstep.
case: Hstep Hreach => {s t s'}.
- (* Nop *)
  move=> gps mem regs pc Hex _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  exact: (@iinv_step_neutral scr_of gps mem regs regs pc INop
            Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
            erefl erefl erefl erefl erefl).
- (* Label *)
  move=> gps mem regs pc l Hex _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  exact: (@iinv_step_neutral scr_of gps mem regs regs pc (ILabel l)
            Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
            erefl erefl erefl erefl erefl).
- (* Const *)
  move=> gps mem regs regs' pc r v Hex Hset _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HrRA HrSP] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  case Hd: (dead_at Pc (Z.to_nat (Pointer.offset pc))).
  + case Hp: (ph_scan Pc false (Z.to_nat (Pointer.offset pc))).
    * apply: (@iinv_step_neutral_ph scr_of gps mem regs regs' pc
                (IConst v r) Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
                erefl erefl erefl Hp).
      by rewrite -Hset get_set_neq //; apply: not_eq_sym.
    * apply: (@iinv_step_neutral scr_of gps mem regs regs' pc
                (IConst v r) Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
                erefl erefl erefl).
      -- by rewrite -Hset get_set_neq //; apply: not_eq_sym.
      -- by rewrite -Hset get_set_neq //;
           apply: not_eq_sym; exact: (HrSP Hd Hp).
  + apply: (@iinv_step_live_any scr_of gps mem regs regs' pc
              (IConst v r) Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
              erefl Hd).
    by rewrite -Hset get_set_neq //; apply: not_eq_sym.
- (* Mov *)
  move=> gps mem regs regs' pc r1 r2 Hex Hset _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HrRA HrSP] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  apply: (@iinv_step_neutral scr_of gps mem regs regs' pc
            (IMov r1 r2) Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
            erefl erefl erefl).
  + by rewrite -Hset get_set_neq //; apply: not_eq_sym.
  + by rewrite -Hset get_set_neq //; apply: not_eq_sym.
- (* BinOp *)
  move=> gps mem regs regs' pc r1 r2 r3 op Hex.
  cbv zeta. move=> Hset Hreach.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HrRA Hshape] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  case: (reg_sp_dec r3) => HrSP.
  + subst r3.
    have [E1 E2 Hop Hph] := Hshape erefl.
    subst r1 r2.
    case Hd: (dead_at Pc (Z.to_nat (Pointer.offset pc))).
    * rewrite -Hset.
      case: Hop => Eop; subst op.
      -- apply: (@iinv_step_spmove scr_of gps mem regs pc
                   (IBinOp Add R_SP R_ONE R_SP) 1%Z
                   (eval_binop Add
                      (Intermediate.Register.get R_SP regs)
                      (Intermediate.Register.get R_ONE regs))
                   Cp j P0 Pc
                   Hilp Hblk Hjnth Hoff Hnth erefl erefl _ Hph _).
         ++ by move=> d.
         ++ move=> c b o HSP. rewrite HSP.
            exact: (Hone Hreach Hex HSP).
      -- apply: (@iinv_step_spmove scr_of gps mem regs pc
                   (IBinOp Minus R_SP R_ONE R_SP) (-1)%Z
                   (eval_binop Minus
                      (Intermediate.Register.get R_SP regs)
                      (Intermediate.Register.get R_ONE regs))
                   Cp j P0 Pc
                   Hilp Hblk Hjnth Hoff Hnth erefl erefl _ Hph _).
         ++ by move=> d.
         ++ move=> c b o HSP. rewrite HSP.
            exact: (Hone Hreach Hex HSP).
    * apply: (@iinv_step_live_any scr_of gps mem regs regs' pc
                (IBinOp op R_SP R_ONE R_SP) Cp j P0 Pc
                Hilp Hblk Hjnth Hoff Hnth erefl Hd).
      by rewrite -Hset get_set_neq //; apply: not_eq_sym.
  + apply: (@iinv_step_neutral scr_of gps mem regs regs' pc
              (IBinOp op r1 r2 r3) Cp j P0 Pc
              Hilp Hblk Hjnth Hoff Hnth erefl
              (@sp_step_binop_other op r1 r2 r3 HrSP) erefl).
    * by rewrite -Hset get_set_neq //; apply: not_eq_sym.
    * by rewrite -Hset get_set_neq //; apply: not_eq_sym.
- (* Load *)
  move=> gps mem regs regs' pc r1 r2 ptr v Hex Hget Hcomp Hload Hset
    Hreach.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HRA HSP2] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  case: (reg_ra_dec r2) => [Era | Hne2].
  + subst r2.
    have [E1 Hd Hd0 Hph] := HRA erefl.
    subst r1.
    rewrite -Hset.
    exact: (@iinv_step_pop_ra scr_of gps mem regs pc Cp j P0 Pc
              ptr v Hilp Hblk Hjnth Hoff Hnth
              Hd Hd0 Hph Hget Hload).
  + case: (reg_sp_dec r2) => [Esp | Hne2sp].
    * subst r2.
      case Hd: (dead_at Pc (Z.to_nat (Pointer.offset pc))).
      -- have [E1 Hph] := HSP2 erefl Hd.
         subst r1.
         rewrite -Hset.
         have Hscr := Hreload Hreach Hex Hilp Hblk Hjnth Hph.
         have Eptr : ptr = scr_of (Pointer.component pc).
         { move: Hget. rewrite Hscr. by move=> [->]. }
         rewrite Eptr in Hload.
         exact: (@iinv_step_reload scr_of gps mem regs pc
                   Cp j P0 Pc v Hilp Hblk Hjnth Hoff Hnth
                   Hd Hph Hscr Hload).
      -- rewrite -Hset.
         apply: (@iinv_step_live_any scr_of gps mem regs
                   (Intermediate.Register.set R_SP v regs) pc
                   (ILoad r1 R_SP) Cp j P0 Pc
                   Hilp Hblk Hjnth Hoff Hnth _ Hd).
         ++ by apply: ra_dead_step_load_other.
         ++ by rewrite get_set_neq.
    * rewrite -Hset.
      case Hd: (dead_at Pc (Z.to_nat (Pointer.offset pc))).
      -- case Hp: (ph_scan Pc false (Z.to_nat (Pointer.offset pc))).
         ** apply: (@iinv_step_neutral_ph scr_of gps mem regs
                      (Intermediate.Register.set r2 v regs) pc
                      (ILoad r1 r2) Cp j P0 Pc
                      Hilp Hblk Hjnth Hoff Hnth _ erefl _ Hp).
            --- exact: (ra_dead_step_load_other _ Hne2).
            --- by case: (r1) Hne2sp; case: (r2) => //.
            --- by rewrite get_set_neq //; apply: not_eq_sym.
         ** apply: (@iinv_step_neutral scr_of gps mem regs
                      (Intermediate.Register.set r2 v regs) pc
                      (ILoad r1 r2) Cp j P0 Pc
                      Hilp Hblk Hjnth Hoff Hnth _ erefl _).
            --- exact: (ra_dead_step_load_other _ Hne2).
            --- by case: (r1) Hne2sp; case: (r2) => //.
            --- by rewrite get_set_neq //; apply: not_eq_sym.
            --- by rewrite get_set_neq //; apply: not_eq_sym.
      -- apply: (@iinv_step_live_any scr_of gps mem regs
                   (Intermediate.Register.set r2 v regs) pc
                   (ILoad r1 r2) Cp j P0 Pc
                   Hilp Hblk Hjnth Hoff Hnth _ Hd).
         ++ exact: (ra_dead_step_load_other _ Hne2).
         ++ by rewrite get_set_neq //; apply: not_eq_sym.
- (* Store *)
  move=> gps mem mem' regs pc ptr r1 r2 Hex Hget Hcomp Hst Hreach.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HRA Hother] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  case: ptr Hget Hcomp Hst => [[cp bp] opz] Hget /= Hcomp Hst.
  subst cp.
  case: (reg_ra_dec r2) => [Era | Hne2].
  + subst r2.
    have [E1 Hlive Hph] := HRA erefl.
    subst r1.
    apply: (@iinv_step_push_ra scr_of gps mem mem' regs pc
              Cp j P0 Pc bp opz Hilp Hblk Hjnth Hoff Hnth
              Hph Hget Hst).
    have [_ Hfs] := Hstoresep Hreach Hex Hilp Hblk Hjnth Hget.
    exact: Hfs.
  + have Hph := Hother Hne2.
    have [Hsl Hfs] := Hstoresep Hreach Hex Hilp Hblk Hjnth Hget.
    apply: (@iinv_step_store scr_of gps mem mem' regs pc r1 r2
              Cp j P0 Pc bp opz Hilp Hblk Hjnth Hoff Hnth
              _ _ Hph Hst Hsl Hfs).
    * exact: (ra_dead_step_store_other _ Hne2).
    * exact: (sp_step_store_other _ Hne2).
- (* Jal *)
  move=> gps mem regs regs' pc pc' l Hex HF Hset _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have Hdph := Hclass Hilp Hblk Hjnth Hoff Hnth.
  rewrite -Hset.
  case Hd: (dead_at Pc (Z.to_nat (Pointer.offset pc))).
  + exact: (@iinv_step_jal scr_of gps mem regs pc pc'
              Cp j P0 Pc Hilp Hblk Hjnth Hoff Hd (Hdph Hd)
              (Hjaltgt Hex HF)).
  + exact: (@iinv_step_jal_live scr_of gps mem regs pc pc'
              (Hjaltgt Hex HF)).
- (* Jump *)
  move=> gps mem regs pc pc' Hex Hcomp Hreach.
  exact: (@iinv_step_jump scr_of gps mem regs pc pc'
            (Hjumptie Hreach Hex)).
- (* BnzNZ *)
  move=> gps mem regs pc pc' r l val Hex Hget Hnz HFp _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [Hcm Hbk]
    := Intermediate.GlobalEnv.find_label_in_procedure_guarantees
         _ _ _ _ HFp.
  case: (Hbnztgt Hex HFp Hilp Hblk Hjnth)
    => [Hlive | [Hd Esp Eph]].
  + apply: (@iinv_step_live_jump scr_of gps mem regs pc pc'
              Cp j P0 Pc).
    * by rewrite -Hcm.
    * by rewrite -Hbk -Hcm.
    * exact: Hjnth.
    * move=> _. exact: Hlive.
  + exact: (@iinv_step_window_jump scr_of gps mem regs pc pc'
              Cp j P0 Pc Hilp Hblk Hjnth Hoff Hcm Hbk Hd Esp Eph).
- (* BnzZ *)
  move=> gps mem regs pc r l Hex Hget _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  exact: (@iinv_step_neutral scr_of gps mem regs regs pc (IBnz r l)
            Cp j P0 Pc Hilp Hblk Hjnth Hoff Hnth
            erefl erefl erefl erefl erefl).
- (* Alloc *)
  move=> gps mem mem' regs regs' pc rsize rptr size ptr Hex Hget Hpos
    Hal Hset Hreach.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [HrRA Hlive] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  rewrite -Hset.
  apply: (@iinv_step_alloc_live scr_of gps mem mem' regs
            (Intermediate.Register.set rptr (Ptr ptr) regs) pc
            (IAlloc rptr rsize) Cp j P0 Pc (Z.to_nat size) ptr
            Hilp Hblk Hjnth Hoff Hnth erefl Hlive Hal).
  + by rewrite get_set_neq //; apply: not_eq_sym.
  + move=> fbs Hfr.
    exact: (Hallocsep Hreach Hal Hfr).
- (* Call *)
  move=> gps mem regs pc b C' P call_arg Hex Hne Himp Hep Hcom _.
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have [Hd Hph] := Hclass Hilp Hblk Hjnth Hoff Hnth.
  exact: (@iinv_step_call scr_of gps mem regs pc C' b
            Cp j P0 Pc Hilp Hblk Hjnth Hoff Hd Hph).
- (* Return *)
  move=> gps' mem regs pc pc' ret_arg Hex Hne Hcom Hreach.
  exact: (@iinv_step_return scr_of gps' mem regs pc pc'
            (Hreturntie Hreach Hex)).
Qed.

(* the invariant holds along every reachable run *)
Theorem ireach_iinv (s : CS.state) :
  ireach pra prb s -> iinv scr_of s.
Proof.
move=> [t Hst].
move: Hst (ireach_init pra prb) (iinv_init scr_of).
move: (CS.initial_machine_state ilp) => s0 Hst.
elim: Hst => [s1 Hr Hi
             | s1 t1 s2 t2 s3 tt Hstep Hstar IH Et Hr Hi].
- exact: Hi.
- apply: IH.
  + exact: (ireach_step Hr Hstep).
  + exact: (iinv_step Hr Hstep Hi).
Qed.

End IInvAssembly.

(* ==================== the R_ONE run invariant ==================== *)

(* [Int 1] sits in R_ONE at every armed position; armed stack entries
   share their component with the frame above (so cross returns only
   pop unarmed entries) *)
Definition r1main (iregs : Intermediate.Register.t) (pc : Pointer.t)
  : Prop :=
  forall (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures ilp (Pointer.component pc)
      = Some Cprocs ->
    Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    (0 <= Pointer.offset pc)%Z ->
    rone_scan Pcode false (Z.to_nat (Pointer.offset pc)) = true ->
    Intermediate.Register.get R_ONE iregs = Int 1.

Fixpoint rchain (prev : Pointer.t) (gps : list Pointer.t) : Prop :=
  match gps with
  | [::] => True
  | p :: rest =>
      (forall (Cprocs : NMap Machine.code) (j : nat)
              (P0 : Procedure.id) (Pcode : Machine.code),
         Intermediate.prog_procedures ilp (Pointer.component p)
           = Some Cprocs ->
         Pointer.block p = proc_nb0 ilp (Pointer.component p) + j ->
         List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
         (0 <= Pointer.offset p)%Z ->
         rone_scan Pcode false (Z.to_nat (Pointer.offset p)) = true ->
         Pointer.component p = Pointer.component prev)
      /\ rchain p rest
  end.

Lemma rchain_prev_comp (prev prev' : Pointer.t)
    (gps : list Pointer.t) :
  Pointer.component prev = Pointer.component prev' ->
  rchain prev gps -> rchain prev' gps.
Proof.
case: gps => [|p rest] //= Ecomp [Hhead Hrest].
split=> //.
move=> Cprocs j P0 Pcode Hilp Hblk Hjnth Hoff Harm.
rewrite -Ecomp.
exact: (Hhead _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
Qed.

Definition r1inv (s : CS.state) : Prop :=
  match s with
  | (gps, imem, iregs, pc) => r1main iregs pc /\ rchain pc gps
  end.

Section ROneInv.

Hypothesis Hwf : Intermediate.well_formed_program ilp.

(* the static half: every bundle checks from the cold seed *)
Hypothesis Hrone :
  forall (C0 : Component.id) (Cprocs : NMap Machine.code)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures ilp C0 = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    rone_check Pcode false = true.

(* sequential helper: the target bundle at [inc pc] is the source
   bundle one position further *)
Lemma r1main_inc (iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  (rone_step i
     (rone_scan Pcode false (Z.to_nat (Pointer.offset pc))) = true ->
   Intermediate.Register.get R_ONE iregs' = Int 1) ->
  r1main iregs' (Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Harm
  Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Harm'.
move: Hilp' Hblk' Hjnth' Harm' => /= Hilp' Hblk' Hjnth' Harm'.
have Ecp : Cprocs' = Cprocs.
{ move: Hilp'. rewrite Hilp. by move=> [->]. }
subst Cprocs'.
have Ej : j' = j by lia.
subst j'.
have EQ : (P0', Pcode') = (P0, Pcode).
{ move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pcode'.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1 by lia.
move: Harm'. rewrite Hoffi (rone_scan_S _ Hnth) /=.
exact: Harm.
Qed.

(* unconditional helper *)
Lemma r1main_any (iregs' : Intermediate.Register.t) (pc' : Pointer.t) :
  Intermediate.Register.get R_ONE iregs' = Int 1 ->
  r1main iregs' pc'.
Proof. by move=> H Cprocs' j' P0' Pcode' _ _ _ _ _. Qed.

(* entry helper: offset 0 is never armed *)
Lemma r1main_entry (iregs' : Intermediate.Register.t)
    (C' : Component.id) (b' : Block.id) :
  r1main iregs' (C', b', 0%Z).
Proof.
move=> Cprocs' j' P0' Pcode' _ _ _ _ /=.
by rewrite rone_scan0.
Qed.

(* the source-armed fact at a checked control site *)
Lemma r1_source_armed (pc : Pointer.t) (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  rone_cond i
    (rone_scan Pcode false (Z.to_nat (Pointer.offset pc))) = true.
Proof.
move=> Hilp Hjnth Hnth.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hchk := Hrone Hilp HgetP.
exact: (rone_check_sound Hchk Hnth).
Qed.

Lemma r1inv_step (s : CS.state) (t : Events.trace) (s' : CS.state) :
  CS.step G s t s' ->
  r1inv s -> r1inv s'.
Proof.
move=> Hstep.
case: Hstep => {s t s'}.
- (* Nop *)
  move=> gps mem regs pc Hex [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split.
  + apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /= Harm.
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
  + apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component.
- (* Label *)
  move=> gps mem regs pc l Hex [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split.
  + apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /= Harm.
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
  + apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component.
- (* Const *)
  move=> gps mem regs regs' pc r v Hex Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /=.
  case: r Hnth Hex Hset => //= Hnth Hex Hset; try by
    (move=> Harm;
     rewrite get_set_neq //;
     exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm)).
  (* R_ONE *)
  case: v Hnth Hex Hset => [z|p] //= Hnth Hex Hset.
  case Ez: (z =? 1)%Z => //= _.
  rewrite get_set_eq /=.
  move: Ez => /Z.eqb_eq ->.
  by [].
- (* Mov *)
  move=> gps mem regs regs' pc r1 r2 Hex Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /=.
  case: r2 Hnth Hex Hset => //= Hnth Hex Hset Harm;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
- (* BinOp *)
  move=> gps mem regs regs' pc r1 r2 r3 op Hex.
  cbv zeta. move=> Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /=.
  case: r3 Hnth Hex Hset => //= Hnth Hex Hset Harm;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
- (* Load *)
  move=> gps mem regs regs' pc r1 r2 ptr v Hex Hget Hcomp Hload Hset
    [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /=.
  case: r2 Hnth Hex Hset => //= Hnth Hex Hset Harm;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
- (* Store *)
  move=> gps mem mem' regs pc ptr r1 r2 Hex Hget Hcomp Hst [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /= Harm.
  exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
- (* Jal *)
  move=> gps mem regs regs' pc pc' l Hex HF Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have Hcond := r1_source_armed Hilp Hjnth Hnth.
  have Hone1 : Intermediate.Register.get R_ONE regs = Int 1.
  { exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Hcond). }
  have Hcm := esym (Intermediate.GlobalEnv.find_label_in_component_1
                      _ _ _ _ HF).
  rewrite -Hset.
  split.
  + apply: r1main_any.
    by rewrite get_set_neq.
  + rewrite /= ; split.
    * move=> Cprocs' j' P0' Pcode' _ _ _ _ _.
      by rewrite Pointer.inc_preserves_component Hcm.
    * apply: (rchain_prev_comp _ H2).
      by rewrite Pointer.inc_preserves_component.
- (* Jump *)
  move=> gps mem regs pc pc' Hex Hcomp [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have Hcond := r1_source_armed Hilp Hjnth Hnth.
  have Hone1 : Intermediate.Register.get R_ONE regs = Int 1.
  { exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Hcond). }
  case: H2 => /= [_ Hrest].
  split.
  + exact: r1main_any.
  + exact: Hrest.
- (* BnzNZ *)
  move=> gps mem regs pc pc' r l val Hex Hget Hnz HFp [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have Hcond := r1_source_armed Hilp Hjnth Hnth.
  have Hone1 : Intermediate.Register.get R_ONE regs = Int 1.
  { exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Hcond). }
  have [Hcm Hbk]
    := Intermediate.GlobalEnv.find_label_in_procedure_guarantees
         _ _ _ _ HFp.
  split.
  + exact: r1main_any.
  + exact: (rchain_prev_comp Hcm H2).
- (* BnzZ *)
  move=> gps mem regs pc r l Hex Hget [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split.
  + apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /= Harm.
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
  + apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component.
- (* Alloc *)
  move=> gps mem mem' regs regs' pc rsize rptr size ptr Hex Hget Hpos
    Hal Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split; last first.
  { apply: (rchain_prev_comp _ H2).
    by rewrite Pointer.inc_preserves_component. }
  apply: (r1main_inc Hilp Hblk Hjnth Hoff Hnth) => /=.
  case: rptr Hnth Hex Hset => //= Hnth Hex Hset Harm;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ Hilp Hblk Hjnth Hoff Harm).
- (* Call *)
  move=> gps mem regs pc b C' P' call_arg Hex Hne Himp Hep Hcom
    [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split.
  + exact: r1main_entry.
  + rewrite /=; split.
    * move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Harm'.
      exfalso.
      move: Hilp' Hblk' Hjnth' Harm'
        => /= Hilp' Hblk' Hjnth' Harm'.
      move: Hilp'. rewrite Pointer.inc_preserves_component Hilp.
      move=> [E]; subst Cprocs'.
      have Ej : j' = j.
      { move: Hblk'.
        rewrite Pointer.inc_preserves_component /=.
        case: (pc) Hblk => [[cI bI] oI] /= Hblk Hblk'.
        by lia. }
      subst j'.
      have EQ : (P0', Pcode') = (P0, Pc).
      { move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
      case: EQ => E1 E2. subst P0' Pcode'.
      move: Harm'.
      case: (pc) Hoff Hnth => [[cI bI] oI] /= Hoff Hnth.
      have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1 by lia.
      rewrite Hoffi (rone_scan_S _ Hnth) /=.
      by [].
    * apply: (rchain_prev_comp _ H2).
      by rewrite Pointer.inc_preserves_component.
- (* Return *)
  move=> gps' mem regs pc pc' ret_arg Hex Hne Hcom [H1 H2].
  case: H2 => /= [Hhead Hrest].
  split.
  + move=> Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff' Harm'.
    exfalso.
    apply: Hne.
    by rewrite (Hhead _ _ _ _ Hilp' Hblk' Hjnth' Hoff' Harm').
  + exact: Hrest.
Qed.

Theorem ireach_r1 (s : CS.state) :
  ireach pra prb s -> r1inv s.
Proof.
move=> [t Hst].
move: Hst.
have Hinit : r1inv (CS.initial_machine_state ilp).
{ rewrite /CS.initial_machine_state.
  case: (Intermediate.prog_main ilp).
  - case: (Intermediate.prepare_procedures_initial_memory ilp)
      => [[mem ?] entrypoints] /=.
    split=> //.
    move=> Cprocs' j' P0' Pcode' _ _ _ _ /=.
    by rewrite rone_scan0.
  - split=> //.
    move=> Cprocs' j' P0' Pcode' _ _ _ _ /=.
    by rewrite rone_scan0. }
move: Hinit.
move: (CS.initial_machine_state ilp) => s0 Hinit Hst.
elim: Hst Hinit => [s1 Hi
             | s1 t1 s2 t2 s3 tt Hstep Hstar IH Et Hi].
- exact: Hi.
- apply: IH.
  exact: (r1inv_step Hstep Hi).
Qed.

End ROneInv.

(* ==================== the R_SP constant-track invariant ============ *)

(* wherever the track records a constant, R_SP holds it *)
Definition rspmain (iregs : Intermediate.Register.t) (pc : Pointer.t)
  : Prop :=
  forall (Cprocs : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code) (v : imvalue),
    Intermediate.prog_procedures ilp (Pointer.component pc)
      = Some Cprocs ->
    Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    (0 <= Pointer.offset pc)%Z ->
    rsp_track Pcode None (Z.to_nat (Pointer.offset pc)) = Some v ->
    Intermediate.Register.get R_SP iregs = imm_to_val v.

Fixpoint rspstack (gps : list Pointer.t) : Prop :=
  match gps with
  | [::] => True
  | p :: rest =>
      (forall (Cprocs : NMap Machine.code) (j : nat)
              (P0 : Procedure.id) (Pcode : Machine.code),
         Intermediate.prog_procedures ilp (Pointer.component p)
           = Some Cprocs ->
         Pointer.block p = proc_nb0 ilp (Pointer.component p) + j ->
         List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
         (0 <= Pointer.offset p)%Z ->
         rsp_track Pcode None (Z.to_nat (Pointer.offset p)) = None)
      /\ rspstack rest
  end.

Definition rspinv (s : CS.state) : Prop :=
  match s with
  | (gps, imem, iregs, pc) => rspmain iregs pc /\ rspstack gps
  end.

Section RspInv.

Hypothesis Hwf : Intermediate.well_formed_program ilp.
Hypothesis Hcl : Intermediate.closed_program ilp.

Hypothesis Hrspt :
  forall (C0 : Component.id) (Cprocs : NMap Machine.code)
         (P0 : Procedure.id) (Pcode : Machine.code),
    Intermediate.prog_procedures ilp C0 = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    rspt_check (C0, 1, 0%Z) Pcode None false = true.

Let RHmain : Component.main
             \in domm (Intermediate.prog_interface ilp).
Proof.
have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
rewrite (Intermediate.wfprog_defined_procedures Hwf).
by rewrite mem_domm Hget.
Qed.

Let RHproci : forall cid,
    cid \in domm (Intermediate.prog_interface ilp) ->
    exists Cprocs,
      Intermediate.prog_procedures ilp cid = Some Cprocs.
Proof.
move=> cid Hin0.
rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin0.
case E: (Intermediate.prog_procedures _ cid) Hin0 => [Cprocs0|] //.
move=> _. by exists Cprocs0.
Qed.

(* sequential helper *)
Lemma rspmain_inc (iregs' : Intermediate.Register.t) (pc : Pointer.t)
    (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  (forall v,
     rsp_step i
       (rsp_track Pcode None (Z.to_nat (Pointer.offset pc)))
       = Some v ->
     Intermediate.Register.get R_SP iregs' = imm_to_val v) ->
  rspmain iregs' (Pointer.inc pc).
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Harm
  Cprocs' j' P0' Pcode' v Hilp' Hblk' Hjnth' Hoff' Htr'.
move: Hilp' Hblk' Hjnth' Htr' => /= Hilp' Hblk' Hjnth' Htr'.
have Ecp : Cprocs' = Cprocs.
{ move: Hilp'. rewrite Hilp. by move=> [->]. }
subst Cprocs'.
have Ej : j' = j by lia.
subst j'.
have EQ : (P0', Pcode') = (P0, Pcode).
{ move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pcode'.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1 by lia.
move: Htr'. rewrite Hoffi (rsp_track_S _ Hnth).
exact: Harm.
Qed.

(* vacuity: the target position carries no track *)
Lemma rspmain_vac (iregs' : Intermediate.Register.t)
    (pc' : Pointer.t) :
  (forall (Cprocs : NMap Machine.code) (j : nat)
          (P0 : Procedure.id) (Pcode : Machine.code),
     Intermediate.prog_procedures ilp (Pointer.component pc')
       = Some Cprocs ->
     Pointer.block pc' = proc_nb0 ilp (Pointer.component pc') + j ->
     List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
     (0 <= Pointer.offset pc')%Z ->
     rsp_track Pcode None (Z.to_nat (Pointer.offset pc')) = None) ->
  rspmain iregs' pc'.
Proof.
move=> Hnone Cprocs' j' P0' Pcode' v Hilp' Hblk' Hjnth' Hoff' Htr'.
by rewrite (Hnone _ _ _ _ Hilp' Hblk' Hjnth' Hoff') in Htr'.
Qed.

(* label positions carry no track: from the checker's ILabel arm *)
Lemma rsp_track_at_label (pc' : Pointer.t) (l : label)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc')
    = Some Cprocs ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc'))
    = Some (ILabel l) ->
  rsp_track Pcode None (Z.to_nat (Pointer.offset pc')) = None.
Proof.
move=> Hilp Hjnth Hnth.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hchk := Hrspt Hilp HgetP.
have := rspt_check_sound Hchk Hnth.
rewrite /rspt_cond.
by case: (rsp_track Pcode None (Z.to_nat (Pointer.offset pc'))).
Qed.

(* jal sites carry no track *)
Lemma rsp_track_at_jal (pc : Pointer.t) (l : label)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc))
    = Some (IJal l) ->
  rsp_track Pcode None (Z.to_nat (Pointer.offset pc)) = None.
Proof.
move=> Hilp Hjnth Hnth.
have HgetP : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have Hchk := Hrspt Hilp HgetP.
have := rspt_check_sound Hchk Hnth.
rewrite /rspt_cond.
by case: (rsp_track Pcode None (Z.to_nat (Pointer.offset pc))).
Qed.

(* the label-resolution targets are label positions: vacuity *)
Lemma rspmain_flc (iregs' : Intermediate.Register.t)
    (pc pc' : Pointer.t) (l : label) :
  Pointer.component pc \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.find_label_in_component G pc l = Some pc' ->
  rspmain iregs' pc'.
Proof.
move=> Hin HF.
have [Ecomp [Ptcode0 [Hrun Hofft Hlbl]]]
  := find_label_in_component_nth RHmain RHproci Hin HF.
case: Hrun => [Cprocs0 [j0 [P00 [HA HB HC0]]]].
apply: rspmain_vac => Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
have Ecp : Cprocs' = Cprocs0.
{ move: HA. rewrite Hilp'. by move=> [->]. }
subst Cprocs'.
have Ej : j' = j0.
{ move: HB. rewrite Hblk' => HB. by lia. }
subst j'.
have EQ : (P0', Pcode') = (P00, Ptcode0).
{ move: HC0. rewrite Hjnth'. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pcode'.
exact: (rsp_track_at_label HA HC0 Hlbl).
Qed.

Lemma rspmain_flp (iregs' : Intermediate.Register.t)
    (pc pc' : Pointer.t) (l : label) :
  Pointer.component pc \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.find_label_in_procedure G pc l = Some pc' ->
  rspmain iregs' pc'.
Proof.
move=> Hin HF.
have [Ptcode0 [Hrun Hofft Hlbl]]
  := find_label_in_procedure_nth' RHmain RHproci Hin HF.
case: Hrun => [Cprocs0 [j0 [P00 [HA HB HC0]]]].
apply: rspmain_vac => Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
have Ecp : Cprocs' = Cprocs0.
{ move: HA. rewrite Hilp'. by move=> [->]. }
subst Cprocs'.
have Ej : j' = j0.
{ move: HB. rewrite Hblk' => HB. by lia. }
subst j'.
have EQ : (P0', Pcode') = (P00, Ptcode0).
{ move: HC0. rewrite Hjnth'. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pcode'.
exact: (rsp_track_at_label HA HC0 Hlbl).
Qed.

(* pushed return addresses carry no track *)
Lemma rspstack_push (pc : Pointer.t) (i : Machine.instr)
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component pc)
    = Some Cprocs ->
  Pointer.block pc = proc_nb0 ilp (Pointer.component pc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset pc)%Z ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset pc)) = Some i ->
  rsp_step i (rsp_track Pcode None (Z.to_nat (Pointer.offset pc)))
    = None ->
  forall (Cprocs' : NMap Machine.code) (j' : nat)
         (P0' : Procedure.id) (Pcode' : Machine.code),
    Intermediate.prog_procedures ilp
      (Pointer.component (Pointer.inc pc)) = Some Cprocs' ->
    Pointer.block (Pointer.inc pc)
      = proc_nb0 ilp (Pointer.component (Pointer.inc pc)) + j' ->
    List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode') ->
    (0 <= Pointer.offset (Pointer.inc pc))%Z ->
    rsp_track Pcode' None
      (Z.to_nat (Pointer.offset (Pointer.inc pc))) = None.
Proof.
case: pc => [[cI bI] oI] /=.
move=> Hilp Hblk Hjnth Hoff Hnth Hstep
  Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
move: Hilp' Hblk' Hjnth' => /= Hilp' Hblk' Hjnth'.
have Ecp : Cprocs' = Cprocs.
{ move: Hilp'. rewrite Hilp. by move=> [->]. }
subst Cprocs'.
have Ej : j' = j by lia.
subst j'.
have EQ : (P0', Pcode') = (P0, Pcode).
{ move: Hjnth'. rewrite Hjnth. by move=> [-> ->]. }
case: EQ => E1 E2. subst P0' Pcode'.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1 by lia.
by rewrite Hoffi (rsp_track_S _ Hnth).
Qed.

Lemma rspinv_step (s : CS.state) (t : Events.trace) (s' : CS.state) :
  CS.step G s t s' ->
  rspinv s -> rspinv s'.
Proof.
move=> Hstep.
case: Hstep => {s t s'}.
- (* Nop *)
  move=> gps mem regs pc Hex [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /= Htr.
  exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Label *)
  move=> gps mem regs pc l Hex [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /= Htr.
  exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Const *)
  move=> gps mem regs regs' pc r v Hex Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v0 /=.
  case: r Hnth Hex Hset => Hnth Hex Hset /=; try by
    (move=> Htr;
     rewrite get_set_neq //;
     exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr)).
  (* R_SP *)
  move=> [<-].
  by rewrite get_set_eq.
- (* Mov *)
  move=> gps mem regs regs' pc r1 r2 Hex Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /=.
  case: r2 Hnth Hex Hset => //= Hnth Hex Hset Htr;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* BinOp *)
  move=> gps mem regs regs' pc r1 r2 r3 op Hex.
  cbv zeta. move=> Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /=.
  case: r3 Hnth Hex Hset => //= Hnth Hex Hset Htr;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Load *)
  move=> gps mem regs regs' pc r1 r2 ptr v Hex Hget Hcomp Hload Hset
    [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v0 /=.
  case: r2 Hnth Hex Hset => //= Hnth Hex Hset Htr;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Store *)
  move=> gps mem mem' regs pc ptr r1 r2 Hex Hget Hcomp Hst [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /= Htr.
  exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Jal *)
  move=> gps mem regs regs' pc pc' l Hex HF Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  have Hin := executing_domm Hex.
  rewrite -Hset.
  split.
  + exact: (rspmain_flc _ Hin HF).
  + rewrite /=; split=> //.
    have Hnone := rsp_track_at_jal Hilp Hjnth Hnth.
    apply: (rspstack_push Hilp Hblk Hjnth Hoff Hnth).
    by rewrite Hnone.
- (* Jump *)
  move=> gps mem regs pc pc' Hex Hcomp [H1 H2].
  case: H2 => /= [Hhead Hrest].
  split=> //.
  apply: rspmain_vac => Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
  exact: (Hhead _ _ _ _ Hilp' Hblk' Hjnth' Hoff').
- (* BnzNZ *)
  move=> gps mem regs pc pc' r l val Hex Hget Hnz HFp [H1 H2].
  have Hin := executing_domm Hex.
  split=> //.
  exact: (rspmain_flp _ Hin HFp).
- (* BnzZ *)
  move=> gps mem regs pc r l Hex Hget [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /= Htr.
  exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Alloc *)
  move=> gps mem mem' regs regs' pc rsize rptr size ptr Hex Hget Hpos
    Hal Hset [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  rewrite -Hset.
  split=> //.
  apply: (rspmain_inc Hilp Hblk Hjnth Hoff Hnth) => v /=.
  case: rptr Hnth Hex Hset => //= Hnth Hex Hset Htr;
    rewrite get_set_neq //;
    exact: (H1 _ _ _ _ _ Hilp Hblk Hjnth Hoff Htr).
- (* Call *)
  move=> gps mem regs pc b C' P' call_arg Hex Hne Himp Hep Hcom
    [H1 H2].
  have [Cp [j [P0 [Pc [Hilp Hblk Hjnth Hoff Hnth]]]]]
    := executing_bundle Hwf Hex.
  split.
  + apply: rspmain_vac
      => Cprocs' j' P0' Pcode' _ _ _ _ /=.
    by rewrite rsp_track0.
  + rewrite /=; split=> //.
    apply: (rspstack_push Hilp Hblk Hjnth Hoff Hnth).
    by [].
- (* Return *)
  move=> gps' mem regs pc pc' ret_arg Hex Hne Hcom [H1 H2].
  case: H2 => /= [Hhead Hrest].
  split=> //.
  apply: rspmain_vac => Cprocs' j' P0' Pcode' Hilp' Hblk' Hjnth' Hoff'.
  exact: (Hhead _ _ _ _ Hilp' Hblk' Hjnth' Hoff').
Qed.

Theorem ireach_rsp (s : CS.state) :
  ireach pra prb s -> rspinv s.
Proof.
move=> [t Hst].
move: Hst.
have Hinit : rspinv (CS.initial_machine_state ilp).
{ rewrite /CS.initial_machine_state.
  case: (Intermediate.prog_main ilp).
  - case: (Intermediate.prepare_procedures_initial_memory ilp)
      => [[mem ?] entrypoints] /=.
    split=> //.
    move=> Cprocs' j' P0' Pcode' v _ _ _ _ /=.
    by rewrite rsp_track0.
  - split=> //.
    move=> Cprocs' j' P0' Pcode' v _ _ _ _ /=.
    by rewrite rsp_track0. }
move: Hinit.
move: (CS.initial_machine_state ilp) => s0 Hinit Hst.
elim: Hst Hinit => [s1 Hi
             | s1 t1 s2 t2 s3 tt Hstep Hstar IH Et Hi].
- exact: Hi.
- apply: IH.
  exact: (rspinv_step Hstep Hi).
Qed.

End RspInv.

(* ==================== memory well-formedness ==================== *)

(* every component memory keeps its allocation cursor above its blocks;
   this makes freshly allocated blocks disjoint from every loadable
   cell — in particular from every parked frame slot *)
Definition memwf (imem : Memory.Memory.t) : Prop :=
  forall (C : Component.id) (memC : ComponentMemory.t),
    getm imem C = Some memC -> ComponentMemory.wf memC.

Lemma memwf_store (imem imem' : Memory.Memory.t) (ptr : Pointer.t)
    (v : value) :
  Memory.Memory.store imem ptr v = Some imem' ->
  memwf imem -> memwf imem'.
Proof.
rewrite /Memory.Memory.store.
case EmC: (getm imem (Pointer.component ptr)) => [memC|] //.
case Est: (ComponentMemory.store memC (Pointer.block ptr)
             (Pointer.offset ptr) v) => [memC'|] //.
move=> [<-] Hwf C0 memC0.
rewrite setmE.
case: eqP => [_ [<-] | _].
- exact: (ComponentMemory.wf_store _ _ _ _ _ (Hwf _ _ EmC) Est).
- exact: Hwf.
Qed.

Lemma memwf_alloc (imem imem' : Memory.Memory.t)
    (C : Component.id) (n : nat) (ptr : Pointer.t) :
  Memory.Memory.alloc imem C n = Some (imem', ptr) ->
  memwf imem -> memwf imem'.
Proof.
rewrite /Memory.Memory.alloc.
case EmC: (getm imem C) => [memC|] //.
case Eal: (ComponentMemory.alloc memC n) => [memC' b].
move=> [<- _] Hwf C0 memC0.
rewrite setmE.
case: eqP => [_ [<-] | _].
- exact: (ComponentMemory.wf_alloc _ _ _ _ (Hwf _ _ EmC) Eal).
- exact: Hwf.
Qed.

Lemma reserve_blocks_wf (memC memC' : ComponentMemory.t) (n : nat)
    (bs : list Block.id) :
  ComponentMemory.wf memC ->
  ComponentMemoryExtra.reserve_blocks memC n = (memC', bs) ->
  ComponentMemory.wf memC'.
Proof.
rewrite /ComponentMemoryExtra.reserve_blocks.
elim: n memC' bs => [|n IH] memC' bs /=.
- by move=> Hwf [<- _].
- move=> Hwf.
  case Eit: (iter n _ (memC, [::])) => [memi bsi] /=.
  case Erb: (ComponentMemory.reserve_block memi) => [memi' b'].
  move=> [<- _].
  have Hwi : ComponentMemory.wf memi.
  { have := IH memi bsi Hwf. by rewrite Eit; apply. }
  exact: (ComponentMemory.wf_reserve_block _ _ _ Hwi Erb).
Qed.

Lemma memwf_init : memwf
  (match CS.initial_machine_state ilp with
   | (_, imem, _, _) => imem
   end).
Proof.
rewrite /CS.initial_machine_state.
case Emain: (Intermediate.prog_main ilp); last first.
{ by move=> C memC. }
rewrite /Intermediate.prepare_procedures_initial_memory /=.
move=> C memC.
rewrite mapmE /Intermediate.prepare_procedures_initial_memory_aux
  mkfmapfE.
case: ifP => // _ /=.
rewrite /Intermediate.reserve_component_blocks.
case Erb: (ComponentMemoryExtra.reserve_blocks _ _) => [Cmem' bs] /=.
move=> [<-].
exact: (reserve_blocks_wf (ComponentMemory.wf_prealloc _) Erb).
Qed.

Theorem ireach_memwf (s : CS.state) :
  ireach pra prb s ->
  memwf (match s with (_, imem, _, _) => imem end).
Proof.
move=> [t Hst].
move: Hst memwf_init.
move: (CS.initial_machine_state ilp) => s0 Hst.
elim: Hst => [s1 Hi
             | s1 t1 s2 t2 s3 tt Hstep Hstar IH Et Hi].
- exact: Hi.
- apply: IH.
  clear Hstar Et.
  case: Hstep Hi => {s1 t1 s2} //=.
  + (* Store *)
    move=> gps mem mem' regs pc ptr r1 r2 _ _ _ Hst Hi.
    exact: (memwf_store Hst Hi).
  + (* Alloc *)
    move=> gps mem mem' regs regs' pc rsize rptr size ptr _ _ _
      Hal _ Hi.
    exact: (memwf_alloc Hal Hi).
Qed.

(* ==================== the absolute SP offset scan ==================== *)

(* R_SP's offset within the current frame: reset by the frame alloc,
   stepped by the ± pushes/pops, parked across the cross-call reload
   pair, killed by the epilogue's own pop of the saved SP *)
Inductive spabs_state : Type :=
| SATracked : nat -> spabs_state
| SAParked : nat -> spabs_state
| SARestored : spabs_state
| SADead : spabs_state.

Definition spabs_step (i : Machine.instr) (k : spabs_state)
  : spabs_state :=
  match i with
  | IAlloc r _ =>
      match r with R_SP => SATracked 0 | _ => k end
  | IBinOp op r1 r2 r3 =>
      match r3 with
      | R_SP =>
          match k with
          | SATracked n =>
              match op with
              | Add => SATracked n.+1
              | Minus => match n with
                         | S n' => SATracked n'
                         | O => SADead
                         end
              | _ => SADead
              end
          | _ => SADead
          end
      | _ => k
      end
  | IConst v r =>
      match r with
      | R_SP =>
          match v, k with
          | IPtr _, SATracked n => SAParked n
          | _, _ => SADead
          end
      | _ => k
      end
  | ILoad _ r2 =>
      match r2 with
      | R_SP =>
          match k with
          | SAParked n => SATracked n
          | SATracked 0 => SARestored
          | _ => SADead
          end
      | _ => k
      end
  | IMov _ r2 =>
      match r2 with R_SP => SADead | _ => k end
  | _ => k
  end.

Fixpoint spabs_scan (c : Machine.code) (k : spabs_state) (o : nat)
  : spabs_state :=
  match o, c with
  | 0, _ => k
  | _.+1, [::] => k
  | o'.+1, i :: c' => spabs_scan c' (spabs_step i k) o'
  end.

Lemma spabs_scan0 (c : Machine.code) (k : spabs_state) :
  spabs_scan c k 0 = k.
Proof. by case: c. Qed.

Lemma spabs_scan_S (c : Machine.code) (k : spabs_state) (o : nat)
    (i : Machine.instr) :
  List.nth_error c o = Some i ->
  spabs_scan c k o.+1 = spabs_step i (spabs_scan c k o).
Proof.
elim: c k o => [|i0 c' IH] k o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite spabs_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

Lemma spabs_scan_cat_l (c1 c2 : Machine.code) (k : spabs_state)
    (o : nat) :
  o <= size c1 ->
  spabs_scan (c1 ++ c2) k o = spabs_scan c1 k o.
Proof.
elim: c1 k o => [|i c1' IH] k o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite spabs_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma spabs_scan_cat_r (c1 c2 : Machine.code) (k : spabs_state)
    (o : nat) :
  spabs_scan (c1 ++ c2) k (size c1 + o)
  = spabs_scan c2 (spabs_scan c1 k (size c1)) o.
Proof. by elim: c1 k => [|i c1' IH] k //=. Qed.

(* the fragment checker: run the scan from the zero probe and demand
   it never dies and ends where it started — the shift lemma then
   gives balance at every seed *)
Definition spabs_shift (j : nat) (k : spabs_state) : spabs_state :=
  match k with
  | SATracked n => SATracked (j + n)
  | SAParked n => SAParked (j + n)
  | SARestored => SARestored
  | SADead => SADead
  end.

(* checked code never frame-allocates and only reloads R_SP from the
   parked state (the epilogue's own pop, which restores from a tracked
   zero, lives outside fragments) — both arms break shift equivariance *)
Definition spabs_ok_ik (i : Machine.instr) (k : spabs_state) : bool :=
  match i with
  | IAlloc r _ => match r with R_SP => false | _ => true end
  | ILoad _ r2 =>
      match r2 with
      | R_SP => match k with SAParked _ => true | _ => false end
      | _ => true
      end
  | _ => true
  end.

Fixpoint spabs_check (c : Machine.code) (k : spabs_state) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      spabs_ok_ik i k
      && (match spabs_step i k with SADead => false | _ => true end)
      && spabs_check c' (spabs_step i k)
  end.

Lemma spabs_step_shift (i : Machine.instr) (j : nat)
    (k : spabs_state) :
  spabs_ok_ik i k = true ->
  spabs_step i k <> SADead ->
  spabs_step i (spabs_shift j k) = spabs_shift j (spabs_step i k).
Proof.
case: i => //=.
- (* IConst *)
  move=> v r _.
  case: r => //=.
  case: v => [z|p] /=; case: k => [n|n||] /= H; try by case: (H erefl).
  by [].
- (* IMov *)
  move=> r1 r2 _.
  by case: r2 => //=.
- (* IBinOp *)
  move=> op r1 r2 r3 _.
  case: r3 => //=.
  case: k => [n|n||] /= H; try by case: (H erefl).
  move: H.
  case: op => /= H; try by case: (H erefl).
  + by rewrite addnS.
  + case: n H => [|n'] /= H; first by case: (H erefl).
    by rewrite addnS.
- (* ILoad *)
  move=> r1 r2.
  case: r2 => //=.
  by case: k => [n|n||] //=.
- (* IAlloc *)
  move=> r sz.
  by case: r => //=; case: k.
Qed.

Lemma spabs_scan_shift (c : Machine.code) :
  forall (j : nat) (k0 : spabs_state) (o : nat),
  spabs_check c k0 = true ->
  o <= size c ->
  spabs_scan c (spabs_shift j k0) o = spabs_shift j (spabs_scan c k0 o).
Proof.
elim: c => [|i0 c' IH] j k0 o /=.
- move=> _.
  rewrite leqn0 => /eqP ->.
  by [].
- move=> /andP [/andP [Hoki Hc] Hrest].
  case: o => [|o'] Ho /=.
  + by [].
  + have Hnd : spabs_step i0 k0 <> SADead.
    { by case: (spabs_step i0 k0) Hc. }
    rewrite (spabs_step_shift j Hoki Hnd).
    exact: (IH _ _ _ Hrest Ho).
Qed.

Lemma spabs_check_cat (c1 c2 : Machine.code) (k : spabs_state) :
  spabs_check (c1 ++ c2) k
  = spabs_check c1 k && spabs_check c2 (spabs_scan c1 k (size c1)).
Proof.
elim: c1 k => [|i c1' IH] k /=.
- by [].
- by rewrite IH andbA.
Qed.

Lemma spabs_ok_ik_shift (i : Machine.instr) (j : nat)
    (k : spabs_state) :
  spabs_ok_ik i (spabs_shift j k) = spabs_ok_ik i k.
Proof.
case: i => //=.
- by move=> r1 r2; case: r2 => //=; case: k.
Qed.

Lemma spabs_check_shift (c : Machine.code) :
  forall (j : nat) (k0 : spabs_state),
  spabs_check c k0 = true ->
  spabs_check c (spabs_shift j k0) = true.
Proof.
elim: c => [|i0 c' IH] j k0 //=.
move=> /andP [/andP [Hoki Hc] Hrest].
have Hnd : spabs_step i0 k0 <> SADead.
{ by case: (spabs_step i0 k0) Hc. }
rewrite spabs_ok_ik_shift Hoki (spabs_step_shift j Hoki Hnd) /=.
rewrite (IH _ _ Hrest) andbT.
by case: (spabs_step i0 k0) Hnd => [n|n||] //=.
Qed.

(* ==================== the canonical frame chain ==================== *)

(* a saved-SP value anchors the record below: if the resume point is
   inside a window, the value locates that record's slot *)
Definition canchor (rv : value) (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value))) : Prop :=
  match gps, ch with
  | p :: _, Some (fb, sl, _) :: _ =>
      forall (Cprocs : NMap Machine.code) (j : nat)
             (P0 : Procedure.id) (Pcode : Machine.code),
        Intermediate.prog_procedures ilp (Pointer.component p)
          = Some Cprocs ->
        Pointer.block p = proc_nb0 ilp (Pointer.component p) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        (0 <= Pointer.offset p)%Z ->
        dead_at Pcode (Z.to_nat (Pointer.offset p)) = true ->
        rv = Ptr (Pointer.component p, fb,
                  (sl + sp_scan Pcode 0%Z
                          (Z.to_nat (Pointer.offset p)))%Z)
  | _, _ => True
  end.

(* one record per pushed return address: the pushing activation's
   frame block, its RA-slot offset, and the saved-SP cell's content
   (frame offset 0).  [None] marks the stub's frameless push, whose
   return target is live. *)
Fixpoint cchain (imem : Memory.Memory.t) (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value))) : Prop :=
  match gps, ch with
  | [::], [::] => True
  | p :: rest, Some (fb, sl, rv) :: ch' =>
      [/\ Memory.Memory.load imem (Pointer.component p, fb, sl)
            = Some Undef,
          Memory.Memory.load imem (Pointer.component p, fb, 0%Z)
            = Some rv,
          canchor rv rest ch'
        & cchain imem rest ch']
  | p :: rest, None :: ch' =>
      (forall (Cprocs : NMap Machine.code) (j : nat)
              (P0 : Procedure.id) (Pcode : Machine.code),
         Intermediate.prog_procedures ilp (Pointer.component p)
           = Some Cprocs ->
         Pointer.block p = proc_nb0 ilp (Pointer.component p) + j ->
         List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
         (0 <= Pointer.offset p)%Z ->
         dead_at Pcode (Z.to_nat (Pointer.offset p)) = false)
      /\ cchain imem rest ch'
  | _, _ => False
  end.

(* block-level separation from a chain (both slots live in [fb]) *)
Fixpoint cchain_sep (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value)))
    (cp : Component.id) (bp : Block.id) : Prop :=
  match gps, ch with
  | p :: rest, Some (fb, _, _) :: ch' =>
      (Pointer.component p <> cp \/ fb <> bp)
      /\ cchain_sep rest ch' cp bp
  | p :: rest, None :: ch' => cchain_sep rest ch' cp bp
  | _, _ => True
  end.

Lemma cchain_store (imem imem' : Memory.Memory.t)
    (ptr : Pointer.t) (v : value)
    (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value))) :
  Memory.Memory.store imem ptr v = Some imem' ->
  cchain_sep gps ch (Pointer.component ptr) (Pointer.block ptr) ->
  cchain imem gps ch ->
  cchain imem' gps ch.
Proof.
move=> Hst.
elim: gps ch => [|p rest IH] [|[[[fb sl] rv]|] ch'] //=; last first.
- move=> Hsep [Hlive Hrest].
  split=> //. exact: (IH _ Hsep Hrest).
- move=> [Hd Hsep] [Hload Hload0 Hanc Hrest].
  split; [ | | exact: Hanc | exact: (IH _ Hsep Hrest)].
  + case: Hd => Hd.
    * by rewrite (@load_store_other_comp _ _ _ _ _ _ _ Hst
          (not_eq_sym Hd)).
    * by rewrite (@load_store_other_block _ _ _ _ _ _ _ Hst
          (not_eq_sym Hd)).
  + case: Hd => Hd.
    * by rewrite (@load_store_other_comp _ _ _ _ _ _ _ Hst
          (not_eq_sym Hd)).
    * by rewrite (@load_store_other_block _ _ _ _ _ _ _ Hst
          (not_eq_sym Hd)).
Qed.

Lemma cchain_alloc (mem mem' : Memory.Memory.t)
    (C0 : Component.id) (n : nat) (ptr : Pointer.t)
    (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value))) :
  Memory.Memory.alloc mem C0 n = Some (mem', ptr) ->
  cchain_sep gps ch C0 (Pointer.block ptr) ->
  cchain mem gps ch ->
  cchain mem' gps ch.
Proof.
move=> Hal.
elim: gps ch => [|p rest IH] [|[[[fb sl] rv]|] ch'] //=; last first.
- move=> Hsep [Hlive Hrest].
  split=> //. exact: (IH _ Hsep Hrest).
- move=> [Hd Hsep] [Hload Hload0 Hanc Hrest].
  split; [ | | exact: Hanc | exact: (IH _ Hsep Hrest)].
  + by rewrite (@load_after_alloc_other _ _ _ _ _ _ _ _ Hal) //.
  + by rewrite (@load_after_alloc_other _ _ _ _ _ _ _ _ Hal) //.
Qed.

(* the chain's slots are loadable, so fresh allocations miss them *)
Lemma cchain_alloc_sep (imem imem' : Memory.Memory.t)
    (C0 : Component.id) (n : nat) (ptr : Pointer.t)
    (gps : list Pointer.t)
    (ch : list (option (Block.id * Z * value))) :
  memwf imem ->
  Memory.Memory.alloc imem C0 n = Some (imem', ptr) ->
  cchain imem gps ch ->
  cchain_sep gps ch C0 (Pointer.block ptr).
Proof.
move=> Hwf.
rewrite /Memory.Memory.alloc.
case EmC: (getm imem C0) => [memC|] //.
case Eal: (ComponentMemory.alloc memC n) => [memC' b].
move=> [_ Eptr].
have Eb : Pointer.block ptr = b by rewrite -Eptr.
have Hfresh : b \notin ComponentMemory.domm memC.
{ exact: (ComponentMemory.alloc_fresh _ _ _ _ (Hwf _ _ EmC) Eal). }
elim: gps ch => [|p rest IH] [|[[[fb sl] rv]|] ch'] //=.
- move=> [Hload _ _ Hrest].
  split; last exact: (IH _ Hrest).
  case: (altP (Pointer.component p =P C0))
    => [Ecomp | Hne]; last by (left; apply/eqP).
  right.
  rewrite Eb => Efb.
  subst fb.
  move: Hload.
  rewrite /Memory.Memory.load /= Ecomp EmC.
  move=> Hload.
  have Hin := ComponentMemory.load_domm _ _ _ _ Hload.
  by rewrite Hin in Hfresh.
- move=> [_ Hrest].
  exact: (IH _ Hrest).
Qed.

(* the Hallocsep tie, outright: fresh blocks miss every parked slot *)
Theorem ireach_allocsep (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (pc : Pointer.t)
    (n : nat) (ptr : Pointer.t) :
  ireach pra prb (gps, imem, iregs, pc) ->
  Memory.Memory.alloc imem (Pointer.component pc) n
    = Some (imem', ptr) ->
  forall (fbs : list (option (Block.id * Z))),
    iframes imem gps fbs ->
    frames_sep gps fbs (Pointer.component pc) (Pointer.block ptr).
Proof.
move=> Hreach Hal fbs Hfr.
have Hwf := ireach_memwf Hreach.
move: Hal.
rewrite /Memory.Memory.alloc.
case EmC: (getm imem (Pointer.component pc)) => [memC|] //.
case Eal: (ComponentMemory.alloc memC n) => [memC' b].
move=> [_ Eptr].
have Eb : Pointer.block ptr = b by rewrite -Eptr.
have Hfresh : b \notin ComponentMemory.domm memC.
{ exact: (ComponentMemory.alloc_fresh _ _ _ _ (Hwf _ _ EmC) Eal). }
clear Hreach.
elim: gps fbs Hfr => [|p rest IH] [|[[fb sl]|] fbs'] //=.
- move=> [Hload Hrest].
  split; last exact: (IH _ Hrest).
  case: (altP (Pointer.component p =P Pointer.component pc))
    => [Ecomp | Hne]; last by (left; apply/eqP).
  right.
  rewrite Eb => Efb.
  subst fb.
  move: Hload.
  rewrite /Memory.Memory.load /= Ecomp EmC.
  move=> Hload.
  have Hin := ComponentMemory.load_domm _ _ _ _ Hload.
  by rewrite Hin in Hfresh.
- move=> Hrest.
  exact: (IH _ Hrest).
Qed.

End LinReach.

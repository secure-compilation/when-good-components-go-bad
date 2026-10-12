(* The SINV instance, part 1: position classes of compiled code.

   The compiled calling convention keeps the running procedure's return
   capability in R_RA everywhere EXCEPT inside a call window — the span
   after a push-R_RA ([IStore _ R_RA]) up to and including the matching
   pop-R_RA ([ILoad _ R_RA]).  S2I's windows never nest.  [dead_at c o]
   scans the first [o] instructions of [c] and reports whether position
   [o] is inside such a window (R_RA "dead", the capability parked in the
   frame's stack cell). *)

Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the scan itself ([ra_dead_step]/[ra_dead_scan]/[dead_at]) lives in
   LinSim, where the [ss_push_jal] clause states its window premise *)
Require Import MicroPolicies.Recomposition.LinSim.

Lemma ra_dead_scan0 (c : code) (dead : bool) :
  ra_dead_scan c dead 0 = dead.
Proof. by case: c. Qed.

(* the scan's one-step unfolding at a fetched instruction *)
Lemma ra_dead_scan_S (c : code) (dead : bool) (o : nat) (i : instr) :
  List.nth_error c o = Some i ->
  ra_dead_scan c dead o.+1 = ra_dead_step i (ra_dead_scan c dead o).
Proof.
elim: c dead o => [|i0 c' IH] dead o.
- by rewrite List.nth_error_nil.
- case: o => [|o'] /=.
  + move=> [<-]. by rewrite ra_dead_scan0.
  + move=> Hnth. exact: (IH _ _ Hnth).
Qed.

Lemma dead_at_S (c : code) (o : nat) (i : instr) :
  List.nth_error c o = Some i ->
  dead_at c o.+1 = ra_dead_step i (dead_at c o).
Proof. exact: ra_dead_scan_S. Qed.

Lemma dead_at0 (c : code) : dead_at c 0 = false.
Proof. by rewrite /dead_at ra_dead_scan0. Qed.

(* the class is untouched by instructions that don't move the
   capability *)
Lemma dead_at_S_skip (c : code) (o : nat) (i : instr) :
  List.nth_error c o = Some i ->
  ra_dead_step i = id ->
  dead_at c o.+1 = dead_at c o.
Proof. by move=> Hnth Hi; rewrite (dead_at_S Hnth) Hi. Qed.

(* skip-shape: everything except Load/Store into R_RA *)
Lemma ra_dead_step_skip (i : instr) :
  match i with
  | IStore _ r2 => r2 <> R_RA
  | ILoad _ r2 => r2 <> R_RA
  | _ => True
  end ->
  forall dead, ra_dead_step i dead = dead.
Proof.
case: i => //=.
- by move=> r1 r2; case: r2.
- by move=> r1 r2; case: r2.
Qed.

(* ==================== part 2: the frame chain ==================== *)

Require Import Common.Values.
Require Import Common.Memory.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import S2I.SimCode.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.LinGenv.
Require Import MicroPolicies.Recomposition.LinMem.
Require Import MicroPolicies.Recomposition.LinMatch.
Require Import MicroPolicies.Recomposition.LinSim.

Import Intermediate.

Section LinInv.

Variables L P C : nat.
Variables pra prb : Intermediate.program.

Local Notation ilp := (Intermediate.program_link pra prb).
Local Notation pbW :=
  (unionm (Intermediate.prog_buffers pra)
          (Intermediate.prog_buffers prb)).

(* the flat code word a frame pointer denotes, together with its
   position-validity bundle (exactly what ss_frame_jump/ret extract).
   [deep] records whether the frame sits above another one; only such
   frames must return into a call window (the wrap-main stub's bottom
   frame returns onto its live IHalt) *)
Definition frame_pos_spec (deep : bool) (p : Pointer.t) (w : mword mt)
  : Prop :=
  exists (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id)
         (Pcode : Machine.code),
    [/\ Intermediate.prog_procedures ilp (Pointer.component p)
          = Some Cprocs,
        Pointer.block p = proc_nb0 ilp (Pointer.component p) + j,
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode),
        (0 <= Pointer.offset p)%Z
      & w = @word_of_nat (word_size mt)
              (side_flat_pos L P C pra prb (Pointer.component p) P0
                 Pcode (Z.to_nat (Pointer.offset p))
               + size (initial_memory (mt := mt) pbW))]
    /\ (exists i,
          List.nth_error Pcode (Z.to_nat (Pointer.offset p)) = Some i)
    (* non-bottom return positions are inside their call window *)
    /\ (deep -> dead_at Pcode (Z.to_nat (Pointer.offset p)) = true).

(* the capability tag of a frame, seen from the component running above
   it: intra frames carry InternalJump, cross frames the Ret level *)
Definition frame_tag (cur : Component.id) (p : Pointer.t)
    (rest : list Pointer.t) : LRC.value_tag :=
  if Pointer.component p == cur then LRC.InternalJump
  else LRC.Ret (cross_frames (Pointer.component p) rest).

(* the tags a live capability may carry — never Other *)
Lemma frame_tag_address (cur : Component.id) (p : Pointer.t)
    (rest : list Pointer.t) :
  LRC.is_address (frame_tag cur p rest) = true.
Proof. by rewrite /frame_tag; case: eqP. Qed.

(* a parked capability cell for frame [p]: the frame word under the
   frame's tag, any owner colour/entry, data cell *)
Definition cap_cell (mmem : {fmap mword mt -> matom})
    (ad : mword mt) (w : mword mt) (tg : LRC.value_tag) : Prop :=
  exists (c0 : Component.id)
         (e : option (Procedure.id * seq Component.id)),
    getm mmem ad = Some (w@(LRC.MTag tg c0 e false)).

(* the deep chain: every frame below the top sits parked in a cell *)
Fixpoint frames_cells (cur : Component.id) (gps : list Pointer.t)
    (ads : list (mword mt))
    (mmem : {fmap mword mt -> matom}) {struct gps} : Prop :=
  match gps, ads with
  | [::], [::] => True
  | p :: rest, ad :: ads' =>
      (exists w, frame_pos_spec (~~ nilp rest) p w
                 /\ cap_cell mmem ad w (frame_tag cur p rest))
      /\ frames_cells (Pointer.component p) rest ads' mmem
  | _, _ => False
  end.

(* ---- transport lemmas: the chain survives the diagram's writes ---- *)

(* monotone memory growth (alloc) *)
Lemma frames_cells_grow (cur : Component.id) (gps : list Pointer.t)
    (ads : list (mword mt)) (mmem mmem' : {fmap mword mt -> matom}) :
  (forall w a, getm mmem w = Some a -> getm mmem' w = Some a) ->
  frames_cells cur gps ads mmem -> frames_cells cur gps ads mmem'.
Proof.
move=> Hmono.
elim: gps cur ads => [|p rest IH] cur [|ad ads'] //=.
move=> [[w [Hpos [c0 [e Hget]]]] Hrest].
split; last exact: (IH _ _ Hrest).
exists w; split; first exact Hpos.
exists c0, e. exact: (Hmono _ _ Hget).
Qed.

(* a store over an Other-vtag cell never hits a parked capability
   (capability cells carry address vtags) *)
Lemma frames_cells_store (cur : Component.id) (gps : list Pointer.t)
    (ads : list (mword mt)) (mmem : {fmap mword mt -> matom})
    (addr : mword mt) (w oldv : mword mt) (c0 : Component.id)
    (ent : option (Procedure.id * seq Component.id))
    (vt' : LRC.value_tag) :
  getm mmem addr = Some (oldv@(LRC.MTag LRC.Other c0 ent false)) ->
  frames_cells cur gps ads mmem ->
  frames_cells cur gps ads
    (setm mmem addr (w@(LRC.MTag vt' c0 ent false))).
Proof.
move=> Hold.
elim: gps cur ads => [|p rest IH] cur [|ad ads'] //=.
move=> [[wf [Hpos [cf [ef Hget]]]] Hrest].
split; last exact: (IH _ _ Hrest).
exists wf; split; first exact Hpos.
exists cf, ef.
rewrite setmE.
case: eqP => [Ead | _]; last exact Hget.
exfalso.
rewrite Ead Hold in Hget.
have /= Evt := congr1 (omap (fun a : matom => LRC.vtag (taga a))) Hget.
case: Evt => Evt.
have HA := frame_tag_address cur p rest.
by rewrite -Evt in HA.
Qed.

(* ==================== part 3: the assembled invariant ============== *)

(* the running position's code: the procedure body [ipc] executes in *)
Definition running_code (ipc : Pointer.t) (Pcode : Machine.code)
  : Prop :=
  exists (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id),
    [/\ Intermediate.prog_procedures ilp (Pointer.component ipc)
          = Some Cprocs,
        Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j
      & List.nth_error (elementsm Cprocs) j = Some (P0, Pcode)].

(* the top frame's capability placement, conditioned on the position
   class of the RUNNING code: outside a call window it is live in R_RA;
   inside a window it is parked in some cell.  (The SP-tie pinning the
   parked cell's address to the I-side stack pointer is added as a
   strengthening when the pop case is proven.) *)
Definition top_ok (gps : list Pointer.t)
    (ipc : Pointer.t)
    (mmem : {fmap mword mt -> matom})
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  match gps with
  | [::] => True
  | p :: rest =>
      forall Pcode,
        running_code ipc Pcode ->
        (0 <= Pointer.offset ipc)%Z ->
        if dead_at Pcode (Z.to_nat (Pointer.offset ipc))
        then exists ad w,
            frame_pos_spec (~~ nilp rest) p w
            /\ cap_cell mmem ad w
                 (frame_tag (Pointer.component ipc) p rest)
        else exists w,
            frame_pos_spec (~~ nilp rest) p w
            /\ getm mregs
                 (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat R_RA))
               = Some (w@(frame_tag (Pointer.component ipc) p rest))
  end.

(* the deep frames sit parked in cells *)
Definition deep_ok (gps : list Pointer.t)
    (mmem : {fmap mword mt -> matom}) : Prop :=
  match gps with
  | [::] => True
  | p :: rest =>
      exists ads, frames_cells (Pointer.component p) rest ads mmem
  end.

(* THE instance (v1: chain layer; the SP-tie and the dead-cell
   discipline conjuncts are added as strengthenings with the clauses
   that need them) *)
Definition sinv_inst (bmap : addr_map) (gps : list Pointer.t)
    (imem : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) : Prop :=
  [/\ Pointer.component ipc \in domm (Intermediate.prog_interface ilp),
      top_ok gps ipc (Symbolic.mem ms) (Symbolic.regs ms)
    & deep_ok gps (Symbolic.mem ms)].

(* the linked program is closed, so main is interfaced *)
Hypothesis Hmainiface :
  Component.main \in domm (Intermediate.prog_interface ilp).

(* the empty-stack case — [sr_init]'s shape *)
Lemma sinv_inst_init (bmap : addr_map) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (bM : Block.id)
    (ms0 : @Symbolic.state mt lrc_tags unit) :
  sinv_inst bmap [::] imem iregs (Component.main, bM, 0%Z) ms0.
Proof. by split. Qed.

Local Notation G := (Intermediate.GlobalEnv.prepare_global_env ilp).

(* an executing position inside a known running procedure fetches from
   THAT procedure's code (the genv block-map correspondence) *)
Lemma running_fetch (ipc : Pointer.t) (Pcode : Machine.code)
    (i : Machine.instr) :
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  running_code ipc Pcode ->
  Intermediate.GlobalEnv.executing G ipc i ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)) = Some i.
Proof.
move=> Hin [Cprocs [j [P0 [Hilp Hblk Hnth]]]] Hex.
case: Hex => C_procs [P_code [HgC [HgB [_ Hfetch]]]].
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
have EC : C_procs = CprocsB by congruence.
subst C_procs.
have [j' [P' [Hb' Hnth']]] := Hbwd _ _ HgB.
have Ej : j = j'.
{ move: Hb'; rewrite Hblk => /addnI. by []. }
subst j'.
rewrite Hnth in Hnth'.
case: Hnth' => _ ->.
exact: Hfetch.
Qed.

(* running-position bundles are unique per pc *)
Lemma running_code_uniq (ipc : Pointer.t) (Pc1 Pc2 : Machine.code) :
  running_code ipc Pc1 -> running_code ipc Pc2 -> Pc1 = Pc2.
Proof.
move=> [C1 [j1 [P1 [HA1 HB1 HC1]]]] [C2 [j2 [P2 [HA2 HB2 HC2]]]].
have EC : C1 = C2 by congruence.
subst C2.
have Ej : j1 = j2.
{ move: HB2; rewrite HB1 => /addnI. by []. }
subst j2.
rewrite HC1 in HC2.
by case: HC2.
Qed.

(* [Pointer.inc] preserves the running procedure *)
Lemma running_code_inc (ipc : Pointer.t) (Pcode : Machine.code) :
  running_code ipc Pcode -> running_code (Pointer.inc ipc) Pcode.
Proof.
move=> [Cprocs [j [P0 [HA HB HC]]]].
exists Cprocs, j, P0.
case: ipc HA HB HC => [[c b] o] /= HA HB HC.
by split.
Qed.

(* ---- preservation: the silent pc-advance cases ---- *)

(* the shared transport: any instruction whose [ra_dead_step] is the
   identity advances the class unchanged; the state is untouched *)
Lemma sinv_inst_skip (bmap : addr_map) (gps : list Pointer.t)
    (imem : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit)
    (i : Machine.instr) mpc' :
  Intermediate.GlobalEnv.executing G ipc i ->
  (forall dead, ra_dead_step i dead = dead) ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap gps imem iregs (Pointer.inc ipc)
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
       (Symbolic.regs ms) mpc' tt).
Proof.
case: ipc => [[cI bI] oI].
move=> Hex Hskip [Hin Htop Hdeep].
split; [exact: Hin | | exact Hdeep].
move: Htop; rewrite /top_ok.
case: gps {Hdeep} => [|p rest] //= Htop.
move=> Pcode Hrun' _.
have Hrun : running_code (cI, bI, oI) Pcode.
{ case: Hrun' => Cprocs [j [P0 [HA HB HC]]].
  by exists Cprocs, j, P0. }
have Hoff : (0 <= oI)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]].
  move: Hge => /= Hge. by lia. }
have Hnth := running_fetch Hin Hrun Hex.
have Hoffi : Z.to_nat (Pointer.offset (Pointer.inc (cI, bI, oI)))
             = (Z.to_nat oI).+1.
{ rewrite /=. by lia. }
rewrite Hoffi /=.
move: Hnth => /= Hnth.
rewrite (dead_at_S Hnth) Hskip.
exact: (Htop _ Hrun Hoff).
Qed.

(* ---- preservation: non-RA register writes (Const/Mov/BinOp/Load) ---- *)

(* the instance is (so far) blind to the I-state, so the I-side memory
   and registers may change arbitrarily; the ME write is at a non-RA
   register key *)
Lemma sinv_inst_reg_write (bmap bmap2 : addr_map)
    (gps : list Pointer.t)
    (imem imem2 : Memory.Memory.t)
    (iregs iregs2 : Intermediate.Register.t)
    (ipc : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit)
    (i : Machine.instr) (r : register) (a : @ratom mt) mpc' :
  Intermediate.GlobalEnv.executing G ipc i ->
  (forall dead, ra_dead_step i dead = dead) ->
  r <> R_RA ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap2 gps imem2 iregs2 (Pointer.inc ipc)
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
       (setm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat r)) a) mpc' tt).
Proof.
case: ipc => [[cI bI] oI].
move=> Hex Hskip Hr [Hin Htop Hdeep].
split; [exact: Hin | | exact Hdeep].
move: Htop; rewrite /top_ok.
case: gps {Hdeep} => [|p rest] //= Htop.
move=> Pcode Hrun' _.
have Hrun : running_code (cI, bI, oI) Pcode.
{ case: Hrun' => Cprocs [j [P0 [HA HB HC]]].
  by exists Cprocs, j, P0. }
have Hoff : (0 <= oI)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]].
  move: Hge => /= Hge. by lia. }
have Hnth := running_fetch Hin Hrun Hex.
have Hoffi : Z.to_nat (Pointer.offset (Pointer.inc (cI, bI, oI)))
             = (Z.to_nat oI).+1.
{ rewrite /=. by lia. }
rewrite Hoffi /=.
move: Hnth => /= Hnth.
rewrite (dead_at_S Hnth) Hskip.
have Htop' := Htop _ Hrun Hoff.
case: (dead_at Pcode (Z.to_nat oI)) Htop' => Htop'.
- exact Htop'.
- case: Htop' => w [Hpos Hra].
  exists w; split; first exact Hpos.
  rewrite /= setmE.
  rewrite (won_eqE (small_lt_reg (isT : 4 < 32))
             (small_lt_reg (to_nat_lt32 r))).
  have -> : (4 == Intermediate.Register.to_nat r) = false.
  { apply/negbTE/negP => /eqP E.
    have E' : Intermediate.Register.to_nat r
              = Intermediate.Register.to_nat R_RA by rewrite -E.
    exact: (Hr (to_nat_inj E')). }
  exact Hra.
Qed.

(* a parked capability cell survives a store over an Other-vtag cell *)
Lemma cap_cell_store (mmem : {fmap mword mt -> matom})
    (addr : mword mt) (w oldv : mword mt) (c0 : Component.id)
    (ent : option (Procedure.id * seq Component.id))
    (vt' : LRC.value_tag) (ad : mword mt) (wf : mword mt)
    (tg : LRC.value_tag) :
  LRC.is_address tg = true ->
  getm mmem addr = Some (oldv@(LRC.MTag LRC.Other c0 ent false)) ->
  cap_cell mmem ad wf tg ->
  cap_cell (setm mmem addr (w@(LRC.MTag vt' c0 ent false))) ad wf tg.
Proof.
move=> Htg Hold [cf [ef Hget]].
exists cf, ef.
rewrite setmE.
case: eqP => [Ead | _]; last exact Hget.
exfalso.
rewrite Ead Hold in Hget.
have /= Evt := congr1 (omap (fun a : matom => LRC.vtag (taga a))) Hget.
case: Evt => Evt.
by rewrite -Evt in Htg.
Qed.

(* ---- preservation: the generic data store (IStore, r2 <> R_RA) ---- *)
Lemma sinv_inst_store (bmap bmap2 : addr_map)
    (gps : list Pointer.t)
    (imem imem2 : Memory.Memory.t)
    (iregs iregs2 : Intermediate.Register.t)
    (ipc : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit)
    (i : Machine.instr) (addr : mword mt) (w oldv : mword mt)
    (c0 : Component.id)
    (ent : option (Procedure.id * seq Component.id))
    (vt' : LRC.value_tag) mpc' :
  Intermediate.GlobalEnv.executing G ipc i ->
  (forall dead, ra_dead_step i dead = dead) ->
  getm (Symbolic.mem ms) addr
    = Some (oldv@(LRC.MTag LRC.Other c0 ent false)) ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap2 gps imem2 iregs2 (Pointer.inc ipc)
    (@Symbolic.State mt lrc_tags _
       (setm (Symbolic.mem ms) addr (w@(LRC.MTag vt' c0 ent false)))
       (Symbolic.regs ms) mpc' tt).
Proof.
case: ipc => [[cI bI] oI].
move=> Hex Hskip Hold [Hin Htop Hdeep].
split; first exact: Hin.
- move: Htop; rewrite /top_ok.
  case: gps Hdeep => [|p rest] //= _ Htop.
  move=> Pcode Hrun' _.
  have Hrun : running_code (cI, bI, oI) Pcode.
  { case: Hrun' => Cprocs [j [P0 [HA HB HC]]].
    by exists Cprocs, j, P0. }
  have Hoff : (0 <= oI)%Z.
  { case: Hex => ? [? [_ [_ [Hge _]]]].
    move: Hge => /= Hge. by lia. }
  have Hnth := running_fetch Hin Hrun Hex.
  have Hoffi : Z.to_nat (Pointer.offset (Pointer.inc (cI, bI, oI)))
               = (Z.to_nat oI).+1.
  { rewrite /=. by lia. }
  rewrite Hoffi /=.
  move: Hnth => /= Hnth.
  rewrite (dead_at_S Hnth) Hskip.
  have Htop' := Htop _ Hrun Hoff.
  case: (dead_at Pcode (Z.to_nat oI)) Htop' => Htop'.
  + case: Htop' => ad [wf [Hpos Hcap]].
    exists ad, wf; split; first exact Hpos.
    apply: (cap_cell_store _ _ (frame_tag_address _ _ _) Hold Hcap).
  + exact Htop'.
- move: Hdeep; rewrite /deep_ok.
  case: gps {Htop} => [|p rest] //=.
  move=> [ads Hcells].
  exists ads.
  exact: (frames_cells_store _ _ Hold Hcells).
Qed.

(* ---- find_label target characterization ---- *)

Lemma find_label_aux_nth (c : Machine.code) (l : label) (o0 o : Z) :
  find_label_aux c l o0 = Some o ->
  (o0 <= o)%Z
  /\ List.nth_error c (Z.to_nat (o - o0)) = Some (ILabel l).
Proof.
elim: c o0 => [|i c' IH] o0 //=.
have FALL : find_label_aux c' l (1 + o0)%Z = Some o ->
            (o0 <= o)%Z /\
            List.nth_error (i :: c') (Z.to_nat (o - o0))
            = Some (ILabel l).
{ move=> /IH [Hle Hnth].
  split; first by lia.
  have -> : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1 by lia.
  exact Hnth. }
case: i FALL => //= l' FALL.
case E: (Nat.eqb l l') => /=; last exact: FALL.
move=> [<-].
split; first by lia.
rewrite Z.sub_diag /=.
by move/PeanoNat.Nat.eqb_eq: E => ->.
Qed.

Lemma find_label_nth (c : Machine.code) (l : label) (o : Z) :
  Intermediate.GlobalEnv.find_label c l = Some o ->
  (0 <= o)%Z /\ List.nth_error c (Z.to_nat o) = Some (ILabel l).
Proof.
rewrite find_labelE => /find_label_aux_nth [Hle Hnth].
split; first by lia.
by rewrite Z.sub_0_r in Hnth.
Qed.

(* the in-procedure label search lands on the label cell of the SAME
   running procedure *)
Lemma find_label_in_procedure_nth (ipc tpc : Pointer.t) (l : label)
    (Pcode : Machine.code) :
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  running_code ipc Pcode ->
  Intermediate.GlobalEnv.find_label_in_procedure G ipc l = Some tpc ->
  [/\ running_code tpc Pcode, (0 <= Pointer.offset tpc)%Z
    & List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
      = Some (ILabel l)].
Proof.
move=> Hin Hrun Hfind.
case: (Hrun) => Cprocs [j [P0 [Hilp Hblk Hnth]]].
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
have HgBlk : getm CprocsB (Pointer.block ipc) = Some Pcode.
{ rewrite Hblk. exact: (Hfwd _ _ _ Hnth). }
move: Hfind.
rewrite /Intermediate.GlobalEnv.find_label_in_procedure HgB' HgBlk.
case E: (Intermediate.GlobalEnv.find_label Pcode l) => [off|] //.
move=> [<-].
have [Hle Hnth'] := find_label_nth E.
by split => //=.
Qed.

(* ---- the compiled-code window shape (discharged from compiledness
   by the scan-shape campaign; consumed here as a hypothesis) ---- *)
Record code_shape (c : Machine.code) : Prop := CodeShape {
  (* a branch and its targeted label share a window class (both live in
     expression code; both dead for the entry stub's started-flag test) *)
  cs_bnz_label_same : forall o r l o',
      List.nth_error c o = Some (IBnz r l) ->
      List.nth_error c o' = Some (ILabel l) ->
      dead_at c o' = dead_at c o;
  cs_jump_live : forall o,
      List.nth_error c o = Some IJump -> dead_at c o = false;
  cs_ret_live : forall o,
      List.nth_error c o = Some IReturn -> dead_at c o = false;
  (* cross-calls sit INSIDE their window (jals need not: the wrap-main
     stub's jal is naked — its deadness above a nonempty stack is the
     run-level [ss_push_jal] window premise instead) *)
  cs_call_dead : forall o C' P',
      List.nth_error c o = Some (ICall C' P') -> dead_at c o = true;
  (* push sites live outside windows (windows don't nest) *)
  cs_storera_live : forall o r,
      List.nth_error c o = Some (IStore r R_RA) -> dead_at c o = false;
  (* non-terminal instructions have a successor cell *)
  cs_next : forall o i,
      List.nth_error c o = Some i ->
      i <> IHalt -> i <> IReturn -> i <> IJump ->
      exists i', List.nth_error c o.+1 = Some i'
}.

Hypothesis Hshape : forall cid Cprocs P0 Pcode,
  Intermediate.prog_procedures ilp cid = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  code_shape Pcode.

(* jal-targeted labels (procedure entry labels) are live, across the
   component's procedures *)
Hypothesis Hjal_target : forall cid Cprocs P1 Pcode1 o1 (l : label)
    P2 Pcode2 o2,
  Intermediate.prog_procedures ilp cid = Some Cprocs ->
  getm Cprocs P1 = Some Pcode1 ->
  getm Cprocs P2 = Some Pcode2 ->
  List.nth_error Pcode1 o1 = Some (IJal l) ->
  List.nth_error Pcode2 o2 = Some (ILabel l) ->
  dead_at Pcode2 o2 = false.

Lemma running_shape (ipc : Pointer.t) (Pcode : Machine.code) :
  running_code ipc Pcode -> code_shape Pcode.
Proof.
move=> [Cprocs [j [P0 [HA HB HC]]]].
apply: (Hshape HA).
apply: BufferLayout.In_fmap_getm.
exact: (List.nth_error_In _ _ HC).
Qed.

(* ---- preservation: the taken branch (IBnz, nonzero) ---- *)
Lemma sinv_inst_bnz_nz (bmap bmap2 : addr_map) (gps : list Pointer.t)
    (imem imem2 : Memory.Memory.t)
    (iregs iregs2 : Intermediate.Register.t)
    (ipc tpc : Pointer.t) (r : register) (l : nat)
    (ms : @Symbolic.state mt lrc_tags unit) mpc' :
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  Intermediate.GlobalEnv.find_label_in_procedure G ipc l = Some tpc ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap2 gps imem2 iregs2 tpc
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
       (Symbolic.regs ms) mpc' tt).
Proof.
move=> Hex Hfind [Hin Htop Hdeep].
have [Ecomp0 _] :=
  Intermediate.GlobalEnv.find_label_in_procedure_guarantees _ _ _ _
    Hfind.
split; [by rewrite -Ecomp0 | | exact Hdeep].
move: Htop; rewrite /top_ok.
case: gps {Hdeep} => [|p rest] //= Htop.
move=> Pcode Hrun' Hoff'.
have [Ecomp Eblk] :=
  Intermediate.GlobalEnv.find_label_in_procedure_guarantees _ _ _ _
    Hfind.
have Hrun : running_code ipc Pcode.
{ case: Hrun' => Cprocs [j [P0 [HA HB HC]]].
  exists Cprocs, j, P0.
  rewrite Ecomp Eblk.
  by split. }
have Hoffs : (0 <= Pointer.offset ipc)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]]. by lia. }
have [_ Hofft Hlbl] := find_label_in_procedure_nth Hin Hrun Hfind.
have Hsh := running_shape Hrun.
have Hnths := running_fetch Hin Hrun Hex.
have Hsame : dead_at Pcode (Z.to_nat (Pointer.offset tpc))
             = dead_at Pcode (Z.to_nat (Pointer.offset ipc))
  := cs_bnz_label_same Hsh Hnths Hlbl.
rewrite Hsame.
have Htop' := Htop _ Hrun Hoffs.
case: (dead_at Pcode (Z.to_nat (Pointer.offset ipc))) Htop' => Htop'.
- case: Htop' => ad [w [Hpos Hcap]].
  exists ad, w.
  split; first exact Hpos.
  by rewrite -Ecomp.
- case: Htop' => w [Hpos Hra].
  exists w; split; first exact Hpos.
  by rewrite -Ecomp.
Qed.

(* ---- wf bridges: interface and procedure domains agree ---- *)
Hypothesis Hprociface : forall cid,
  cid \in domm (Intermediate.prog_interface ilp) ->
  exists Cprocs, Intermediate.prog_procedures ilp cid = Some Cprocs.
Hypothesis Hdommi : forall cid,
  cid \in domm (Intermediate.prog_procedures ilp) ->
  cid \in domm (Intermediate.prog_interface ilp).

(* an interfaced executing position determines its running procedure *)
Lemma executing_running (ipc : Pointer.t) (i : Machine.instr) :
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.executing G ipc i ->
  exists Pcode,
    running_code ipc Pcode
    /\ List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)) = Some i.
Proof.
move=> Hin Hex.
have [Cprocs Hilp] := Hprociface Hin.
case: Hex => C_procs [P_code [HgC [HgB [Hge Hfetch]]]].
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
have EC : C_procs = CprocsB by congruence.
subst C_procs.
have [j' [P' [Hb' Hnth']]] := Hbwd _ _ HgB.
exists P_code.
split => //.
by exists Cprocs, j', P'.
Qed.

(* the popped frame's own bundle IS a running_code at the pop target;
   a deep frame's position is moreover inside its call window *)
Lemma frame_pos_running (deep : bool) (p : Pointer.t) (w : mword mt) :
  frame_pos_spec deep p w ->
  exists Pcode,
    [/\ running_code p Pcode,
        Pointer.component p \in domm (Intermediate.prog_interface ilp)
      & deep -> dead_at Pcode (Z.to_nat (Pointer.offset p)) = true].
Proof.
move=> [Cprocs [j [P0 [Pcode [[HA HB HC _ _] [_ Hdead]]]]]].
exists Pcode.
split.
- by exists Cprocs, j, P0.
- apply: Hdommi. by rewrite mem_domm HA.
- exact Hdead.
Qed.

(* probe form of the in-procedure label search: the target's procedure
   is produced rather than consumed *)
Lemma find_label_in_procedure_nth' (qpc tpc : Pointer.t) (l : label) :
  Pointer.component qpc \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.find_label_in_procedure G qpc l = Some tpc ->
  exists Pcode,
    [/\ running_code tpc Pcode, (0 <= Pointer.offset tpc)%Z
      & List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
        = Some (ILabel l)].
Proof.
move=> Hin Hfind.
have [Cprocs Hilp] := Hprociface Hin.
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
move: Hfind.
rewrite /Intermediate.GlobalEnv.find_label_in_procedure HgB'.
case HgBlk : (getm CprocsB (Pointer.block qpc)) => [P_code|] //.
case E: (Intermediate.GlobalEnv.find_label P_code l) => [off|] //.
move=> [<-].
have [Hle Hnth'] := find_label_nth E.
have [j' [P' [Hb' Hnthj]]] := Hbwd _ _ HgBlk.
exists P_code.
split => //=.
by exists Cprocs, j', P'.
Qed.

(* the in-component label search: same component, and the target is a
   label cell of one of the component's procedures *)
Lemma find_label_in_component_nth (ipc tpc : Pointer.t) (l : label) :
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.find_label_in_component G ipc l = Some tpc ->
  Pointer.component tpc = Pointer.component ipc
  /\ exists Pcode,
      [/\ running_code tpc Pcode, (0 <= Pointer.offset tpc)%Z
        & List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
          = Some (ILabel l)].
Proof.
move=> Hin.
rewrite /Intermediate.GlobalEnv.find_label_in_component.
case HgC : (getm _ (Pointer.component ipc)) => [C_procs|] //.
elim: (elementsm C_procs) => [|[b' code'] bs IH] //=.
case Hf : (Intermediate.GlobalEnv.find_label_in_procedure
             G (Pointer.component ipc, b', 0%Z) l) => [tpc'|];
  last exact: IH.
move=> [Etpc]; subst tpc'.
have Hcomp' := Intermediate.GlobalEnv.find_label_in_procedure_1
                 _ _ _ _ Hf.
split; first by rewrite -Hcomp'.
apply: (find_label_in_procedure_nth' _ Hf).
by rewrite /=.
Qed.

(* ---- preservation: the intra-component return (IJump pop) ---- *)
Lemma sinv_inst_pop_jump (bmap bmap2 : addr_map)
    (gps' : list Pointer.t)
    (imem imem2 : Memory.Memory.t)
    (iregs iregs2 : Intermediate.Register.t)
    (ipc tpc : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit)
    mpc' :
  Intermediate.GlobalEnv.executing G ipc IJump ->
  Pointer.component tpc = Pointer.component ipc ->
  sinv_inst bmap (tpc :: gps') imem iregs ipc ms ->
  sinv_inst bmap2 gps' imem2 iregs2 tpc
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
       (Symbolic.regs ms) mpc' tt).
Proof.
move=> Hex Hcmp [Hin Htop Hdeep].
have Hoffs : (0 <= Pointer.offset ipc)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]]. by lia. }
have [Pcode0 [Hrun0 _]] := executing_running Hin Hex.
have Htop' := Htop _ Hrun0 Hoffs.
have [w Hpos] : exists w, frame_pos_spec (~~ nilp gps') tpc w.
{ case: (dead_at Pcode0 (Z.to_nat (Pointer.offset ipc))) Htop'
    => Htop'.
  - case: Htop' => ad [w [Hpos _]]. by exists w.
  - case: Htop' => w [Hpos _]. by exists w. }
have [PcodeT [HrunT HinT HdeadT]] := frame_pos_running Hpos.
split.
- (* interface membership at the target *)
  exact: HinT.
- (* the new top's placement *)
  move: Hdeep HdeadT; rewrite /top_ok /deep_ok.
  case: gps' Htop Htop' {Hpos} => [|q rest] //= _ _ Hdeep HdeadT.
  move=> PcodeT' HrunT' _.
  have E : PcodeT' = PcodeT := running_code_uniq HrunT' HrunT.
  subst PcodeT'.
  rewrite (HdeadT isT).
  case: Hdeep => [[|ad ads'] Hcells] //=.
  case: Hcells => [[wq [Hposq Hcapq]] _].
  by exists ad, wq.
- (* the tail chain *)
  move: Hdeep; rewrite /deep_ok.
  case: gps' Htop Htop' {Hpos HdeadT} => [|q rest] //= _ _ Hdeep.
  case: Hdeep => [[|ad ads'] Hcells] //=.
  case: Hcells => _ Hrest.
  by exists ads'.
Qed.

(* ---- preservation: the cross-component return (IReturn pop) ---- *)
Lemma sinv_inst_pop_ret (bmap bmap2 : addr_map)
    (gps' : list Pointer.t)
    (imem imem2 : Memory.Memory.t)
    (iregs iregs2 : Intermediate.Register.t)
    (ipc tpc : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit)
    (mregs' : {fmap reg mt -> @ratom mt}) mpc' :
  Intermediate.GlobalEnv.executing G ipc IReturn ->
  (Pointer.component ipc == Pointer.component tpc) = false ->
  sinv_inst bmap (tpc :: gps') imem iregs ipc ms ->
  sinv_inst bmap2 gps' imem2 iregs2 tpc
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms) mregs' mpc' tt).
Proof.
move=> Hex Hneq [Hin Htop Hdeep].
have Hoffs : (0 <= Pointer.offset ipc)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]]. by lia. }
have [Pcode0 [Hrun0 _]] := executing_running Hin Hex.
have Htop' := Htop _ Hrun0 Hoffs.
have [w Hpos] : exists w, frame_pos_spec (~~ nilp gps') tpc w.
{ case: (dead_at Pcode0 (Z.to_nat (Pointer.offset ipc))) Htop'
    => Htop'.
  - case: Htop' => ad [w [Hpos _]]. by exists w.
  - case: Htop' => w [Hpos _]. by exists w. }
have [PcodeT [HrunT HinT HdeadT]] := frame_pos_running Hpos.
split.
- exact: HinT.
- move: Hdeep HdeadT; rewrite /top_ok /deep_ok.
  case: gps' Htop Htop' {Hpos} => [|q rest] //= _ _ Hdeep HdeadT.
  move=> PcodeT' HrunT' _.
  have E : PcodeT' = PcodeT := running_code_uniq HrunT' HrunT.
  subst PcodeT'.
  rewrite (HdeadT isT).
  case: Hdeep => [[|ad ads'] Hcells] //=.
  case: Hcells => [[wq [Hposq Hcapq]] _].
  by exists ad, wq.
- move: Hdeep; rewrite /deep_ok.
  case: gps' Htop Htop' {Hpos HdeadT} => [|q rest] //= _ _ Hdeep.
  case: Hdeep => [[|ad ads'] Hcells] //=.
  case: Hcells => _ Hrest.
  by exists ads'.
Qed.

(* ---- preservation: the intra-component call (IJal push) ---- *)
Lemma sinv_inst_push_jal (bmap : addr_map) (gps : list Pointer.t)
    (imem : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc tpc : Pointer.t) (l : nat)
    (ms : @Symbolic.state mt lrc_tags unit)
    (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id)
    (Pcode : Machine.code) mpc' :
  Intermediate.GlobalEnv.executing G ipc (IJal l) ->
  Intermediate.GlobalEnv.find_label_in_component G ipc l = Some tpc ->
  Intermediate.prog_procedures ilp (Pointer.component ipc)
    = Some Cprocs ->
  Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset ipc)%Z ->
  (gps <> [::] ->
   dead_at Pcode (Z.to_nat (Pointer.offset ipc)) = true) ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap (Pointer.inc ipc :: gps) imem
    (Intermediate.Register.set R_RA Undef iregs) tpc
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
       (setm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA))
          ((word_of_nat
              (side_flat_pos L P C pra prb (Pointer.component ipc) P0
                 Pcode (Z.to_nat (Pointer.offset ipc)).+1
               + size (initial_memory (mt := mt) pbW)))
             @LRC.InternalJump)) mpc' tt).
Proof.
case: ipc => [[cI bI] oI].
move=> Hex Hfind Hilp Hblk Hjnth Hoffs Hjd [Hin Htop Hdeep].
have Hrun : running_code (cI, bI, oI) Pcode by exists Cprocs, j, P0.
have [Ecomp [PcodeT [HrunT HofftT HlblT]]]
  := find_label_in_component_nth Hin Hfind.
have Hsh := running_shape Hrun.
have HshT := running_shape HrunT.
have Hnths := running_fetch Hin Hrun Hex.
move: Hnths => /= Hnths.
have HgetP0 : getm Cprocs P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact: (List.nth_error_In _ _ Hjnth). }
have HdeadT : dead_at PcodeT (Z.to_nat (Pointer.offset tpc)) = false.
{ case: (HrunT) => CprocsT [jT [PT [HAT HBT HCT]]].
  rewrite Ecomp /= in HAT.
  have Hilp' : Intermediate.prog_procedures ilp cI = Some Cprocs
    := Hilp.
  have ET : CprocsT = Cprocs.
  { move: HAT. rewrite Hilp'. by move=> [->]. }
  subst CprocsT.
  have HgetPT : getm Cprocs PT = Some PcodeT.
  { apply: BufferLayout.In_fmap_getm.
    exact: (List.nth_error_In _ _ HCT). }
  exact: (Hjal_target Hilp HgetP0 HgetPT Hnths HlblT). }
have Hne1 : IJal l <> IHalt by [].
have Hne2 : IJal l <> IReturn by [].
have Hne3 : IJal l <> IJump by [].
have [i' Hnext] := @cs_next _ Hsh _ _ Hnths Hne1 Hne2 Hne3.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ rewrite Z2Nat.inj_add //=. by rewrite PeanoNat.Nat.add_1_r. }
split.
- by rewrite Ecomp.
- rewrite /top_ok.
  move=> PcodeT' HrunT' _.
  have E := running_code_uniq HrunT' HrunT; subst PcodeT'.
  rewrite HdeadT.
  exists (word_of_nat
            (side_flat_pos L P C pra prb cI P0 Pcode
               (Z.to_nat oI).+1
             + size (initial_memory (mt := mt) pbW))).
  split.
  + exists Cprocs, j, P0, Pcode.
    split; last split.
    * split.
      -- exact: Hilp.
      -- exact: Hblk.
      -- exact: Hjnth.
      -- rewrite /=. by lia.
      -- rewrite /= Hoffi. reflexivity.
    * rewrite /= Hoffi. by exists i'.
    * rewrite /= Hoffi (dead_at_S Hnths) /=.
      move=> Hne. apply: Hjd => Egps. by rewrite Egps in Hne.
  + rewrite /= setmE eqxx /frame_tag Ecomp /= eqxx /=.
    reflexivity.
- rewrite /deep_ok /=.
  case: gps Htop Hdeep Hjd => [|p rest] Htop Hdeep Hjd.
  + by exists [::].
  + have Hdead : dead_at Pcode (Z.to_nat oI) = true by apply: Hjd.
    have Htop' := Htop _ Hrun Hoffs.
    rewrite /= Hdead in Htop'.
    case: Htop' => ad [w' [Hpos' Hcap']].
    case: Hdeep => ads0 Hcells0.
    exists (ad :: ads0) => /=.
    split; last exact Hcells0.
    exists w'.
    by split.
Qed.

(* ---- preservation: the cross-component call (ICall push) ---- *)
Lemma sinv_inst_push_call (bmap : addr_map) (gps : list Pointer.t)
    (imem : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc : Pointer.t) (C' : Component.id) (b : Block.id)
    (p : Procedure.id)
    (ms : @Symbolic.state mt lrc_tags unit)
    (mregs' : {fmap reg mt -> @ratom mt})
    (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id)
    (Pcode : Machine.code) mpc' :
  (Pointer.component ipc == C') = false ->
  C' \in domm (Intermediate.prog_interface ilp) ->
  Intermediate.GlobalEnv.executing G ipc (ICall C' p) ->
  Intermediate.prog_procedures ilp (Pointer.component ipc)
    = Some Cprocs ->
  Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset ipc)%Z ->
  getm mregs'
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA))
    = Some ((@word_of_nat (word_size mt)
               (side_flat_pos L P C pra prb (Pointer.component ipc) P0
                  Pcode (Z.to_nat (Pointer.offset ipc)).+1
                + size (initial_memory (mt := mt) pbW)))
              @(LRC.Ret (cross_frames (Pointer.component ipc) gps))) ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap (Pointer.inc ipc :: gps) imem
    (Intermediate.Register.invalidate iregs) (C', b, 0%Z)
    (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms) mregs' mpc' tt).
Proof.
case: ipc => [[cI bI] oI].
move=> Hne HC'in Hex Hilp Hblk Hjnth Hoffs Hra' [Hin Htop Hdeep].
move: Hne => /= Hne.
have Hrun : running_code (cI, bI, oI) Pcode by exists Cprocs, j, P0.
have Hsh := running_shape Hrun.
have Hnths := running_fetch Hin Hrun Hex.
move: Hnths => /= Hnths.
have Hdead : dead_at Pcode (Z.to_nat oI) = true
  := cs_call_dead Hsh Hnths.
have Hne1 : ICall C' p <> IHalt by [].
have Hne2 : ICall C' p <> IReturn by [].
have Hne3 : ICall C' p <> IJump by [].
have [i' Hnext] := @cs_next _ Hsh _ _ Hnths Hne1 Hne2 Hne3.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ rewrite Z2Nat.inj_add //=. by rewrite PeanoNat.Nat.add_1_r. }
split.
- exact: HC'in.
- rewrite /top_ok.
  move=> PcodeT' HrunT' _.
  rewrite /= dead_at0.
  exists (word_of_nat
            (side_flat_pos L P C pra prb cI P0 Pcode
               (Z.to_nat oI).+1
             + size (initial_memory (mt := mt) pbW))).
  split.
  + exists Cprocs, j, P0, Pcode.
    split; last split.
    * split.
      -- exact: Hilp.
      -- exact: Hblk.
      -- exact: Hjnth.
      -- rewrite /=. by lia.
      -- rewrite /= Hoffi. reflexivity.
    * rewrite /= Hoffi. by exists i'.
    * rewrite /= Hoffi (dead_at_S Hnths) /=. move=> _. exact: Hdead.
  + rewrite /frame_tag /= Hne.
    exact: Hra'.
- rewrite /deep_ok /=.
  case: gps Htop Hdeep Hra' => [|q rest] Htop Hdeep Hra'.
  + by exists [::].
  + have Htop' := Htop _ Hrun Hoffs.
    rewrite /= Hdead in Htop'.
    case: Htop' => ad [w' [Hpos' Hcap']].
    case: Hdeep => ads0 Hcells0.
    exists (ad :: ads0) => /=.
    split; last exact Hcells0.
    exists w'.
    by split.
Qed.

(* ---- extraction: the live capability at an IJump site ---- *)
Lemma sinv_inst_frame_jump (bmap : addr_map) (gps' : list Pointer.t)
    (tpc ipc : Pointer.t) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (Cprocs : NMap Machine.code) :
  sinv_inst bmap (tpc :: gps') imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc IJump ->
  Pointer.component tpc = Pointer.component ipc ->
  Intermediate.prog_procedures ilp (Pointer.component ipc)
    = Some Cprocs ->
  exists j' P0' Pcode',
    [/\ Pointer.block tpc
          = proc_nb0 ilp (Pointer.component ipc) + j',
        List.nth_error (elementsm Cprocs) j' = Some (P0', Pcode'),
        (0 <= Pointer.offset tpc)%Z,
        getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA))
        = Some ((word_of_nat
                   (side_flat_pos L P C pra prb
                      (Pointer.component ipc) P0' Pcode'
                      (Z.to_nat (Pointer.offset tpc))
                    + size (initial_memory (mt := mt) pbW)))
                  @LRC.InternalJump)
      & exists i'',
          List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
          = Some i''].
Proof.
move=> [Hin Htop Hdeep] Hex Hcmp Hilp.
have Hoffs : (0 <= Pointer.offset ipc)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]]. by lia. }
have [Pcode0 [Hrun0 Hnth0]] := executing_running Hin Hex.
have Hsh := running_shape Hrun0.
have Hlive : dead_at Pcode0 (Z.to_nat (Pointer.offset ipc)) = false
  := cs_jump_live Hsh Hnth0.
have Htop' := Htop _ Hrun0 Hoffs.
rewrite Hlive in Htop'.
case: Htop' => w [Hpos Hra].
case: Hpos
  => CprocsT [j' [P0' [Pcode' [[HA HB HC HD] [HE [[i'' Hi''] _]]]]]].
have EC : CprocsT = Cprocs.
{ move: HA. rewrite Hcmp Hilp. by case. }
subst CprocsT.
exists j', P0', Pcode'.
split.
- by rewrite -Hcmp.
- exact: HC.
- exact: HD.
- rewrite Hra HE /frame_tag Hcmp eqxx.
  reflexivity.
- by exists i''.
Qed.

(* ---- extraction: the live capability at an IReturn site ---- *)
Lemma sinv_inst_frame_ret (bmap : addr_map) (gps' : list Pointer.t)
    (tpc ipc : Pointer.t) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  sinv_inst bmap (tpc :: gps') imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc IReturn ->
  (Pointer.component ipc == Pointer.component tpc) = false ->
  exists Cprocs' j' P0' Pcode',
    [/\ Intermediate.prog_procedures ilp (Pointer.component tpc)
          = Some Cprocs',
        Pointer.block tpc
          = proc_nb0 ilp (Pointer.component tpc) + j',
        List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode'),
        (0 <= Pointer.offset tpc)%Z /\
        getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA))
        = Some ((word_of_nat
                   (side_flat_pos L P C pra prb
                      (Pointer.component tpc) P0' Pcode'
                      (Z.to_nat (Pointer.offset tpc))
                    + size (initial_memory (mt := mt) pbW)))
                  @(LRC.Ret (cross_frames (Pointer.component tpc)
                               gps')))
      & exists i'',
          List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
          = Some i''].
Proof.
move=> [Hin Htop Hdeep] Hex Hneq.
have Hoffs : (0 <= Pointer.offset ipc)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]]. by lia. }
have [Pcode0 [Hrun0 Hnth0]] := executing_running Hin Hex.
have Hsh := running_shape Hrun0.
have Hlive : dead_at Pcode0 (Z.to_nat (Pointer.offset ipc)) = false
  := cs_ret_live Hsh Hnth0.
have Htop' := Htop _ Hrun0 Hoffs.
rewrite Hlive in Htop'.
case: Htop' => w [Hpos Hra].
case: Hpos
  => CprocsT [j' [P0' [Pcode' [[HA HB HC HD] [HE [[i'' Hi''] _]]]]]].
have Hne' : (Pointer.component tpc == Pointer.component ipc) = false.
{ by rewrite eq_sym. }
exists CprocsT, j', P0', Pcode'.
split.
- exact: HA.
- exact: HB.
- exact: HC.
- split; first exact: HD.
  rewrite Hra HE /frame_tag Hne'.
  reflexivity.
- by exists i''.
Qed.

(* ---- preservation: the allocation (IAlloc) ---- *)
Lemma sinv_inst_alloc (bmap : addr_map) (gps : list Pointer.t)
    (imem imem' : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc : Pointer.t) (rptr rsize : register) (szZ : Z)
    (bI : Block.id) (base' : nat)
    (ms : @Symbolic.state mt lrc_tags unit)
    (mem' : {fmap mword mt -> matom})
    (mregs' : {fmap reg mt -> @ratom mt}) mpc' :
  Intermediate.GlobalEnv.executing G ipc (IAlloc rptr rsize) ->
  rptr <> R_RA ->
  Intermediate.Register.get rsize iregs = Int szZ ->
  Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
    = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
  (forall w a, getm (Symbolic.mem ms) w = Some a ->
               getm mem' w = Some a) ->
  getm mregs'
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA))
  = getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt)
         (Intermediate.Register.to_nat R_RA)) ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst (amap_set bmap (Pointer.component ipc) bI base') gps imem'
    (Intermediate.Register.set rptr
       (Ptr (Pointer.component ipc, bI, 0%Z)) iregs)
    (Pointer.inc ipc)
    (@Symbolic.State mt lrc_tags _ mem' mregs' mpc' tt).
Proof.
case: ipc => [[cI bIp] oI].
move=> Hex Hrptr Hsz HA Hmono Hres [Hin Htop Hdeep].
have Hoffs : (0 <= oI)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]].
  move: Hge => /= Hge. by lia. }
have [Pcode0 [Hrun0 Hnth0]] := executing_running Hin Hex.
move: Hnth0 => /= Hnth0.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ rewrite Z2Nat.inj_add //=. by rewrite PeanoNat.Nat.add_1_r. }
split; first exact: Hin.
- rewrite /top_ok.
  case: gps Htop Hdeep => [|p rest] //= Htop _.
  move=> Pcode' Hrun' _.
  have Hrun'' : running_code (cI, bIp, oI) Pcode'.
  { case: Hrun' => Cx [jx [Px [HAx HBx HCx]]].
    by exists Cx, jx, Px. }
  have E := running_code_uniq Hrun'' Hrun0; subst Pcode'.
  rewrite /= Hoffi (dead_at_S Hnth0) /=.
  have Htop' := Htop _ Hrun0 Hoffs.
  case: (dead_at Pcode0 (Z.to_nat oI)) Htop' => Htop'.
  + case: Htop' => ad [w [Hpos Hcap]].
    exists ad, w.
    split; first exact Hpos.
    case: Hcap => c0 [e Hget].
    exists c0, e.
    exact: (Hmono _ _ Hget).
  + case: Htop' => w [Hpos Hra].
    exists w.
    split; first exact Hpos.
    rewrite /= Hres.
    exact: Hra.
- rewrite /deep_ok.
  case: gps Htop Hdeep => [|p rest] //= _ [ads0 Hcells0].
  exists ads0.
  exact: (frames_cells_grow Hmono Hcells0).
Qed.

Lemma frame_tag_not_inv (cur : Component.id) (p : Pointer.t)
    (rest : list Pointer.t) :
  frame_tag cur p rest <> LRC.Invalidated.
Proof. rewrite /frame_tag. by case: eqP. Qed.

(* store survival with an {Other, Invalidated} old tag — live caps carry
   InternalJump/Ret, disjoint from both *)
Lemma frames_cells_store2 (cur : Component.id) (gps : list Pointer.t)
    (ads : list (mword mt)) (mmem : {fmap mword mt -> matom})
    (addr : mword mt) (w oldv : mword mt) (c0 : Component.id)
    (ent : option (Procedure.id * seq Component.id))
    (oldvt vt' : LRC.value_tag) :
  getm mmem addr = Some (oldv@(LRC.MTag oldvt c0 ent false)) ->
  oldvt = LRC.Other \/ oldvt = LRC.Invalidated ->
  frames_cells cur gps ads mmem ->
  frames_cells cur gps ads
    (setm mmem addr (w@(LRC.MTag vt' c0 ent false))).
Proof.
move=> Hold Hovt.
elim: gps cur ads => [|p rest IH] cur [|ad ads'] //=.
move=> [[wf [Hpos [cf [ef Hget]]]] Hrest].
split; last exact: (IH _ _ Hrest).
exists wf; split; first exact Hpos.
exists cf, ef.
rewrite setmE.
case: eqP => [Ead | _]; last exact Hget.
exfalso.
rewrite Ead Hold in Hget.
have /= Evt := congr1 (omap (fun a : matom => LRC.vtag (taga a))) Hget.
case: Evt => Evt.
case: Hovt => Hovt; rewrite Hovt in Evt.
- have HA := frame_tag_address cur p rest.
  by rewrite -Evt in HA.
- exact: (frame_tag_not_inv (esym Evt)).
Qed.

(* ---- preservation: the push-R_RA store (IStore _ R_RA) ---- *)
Lemma sinv_inst_store_ra (bmap : addr_map) (gps : list Pointer.t)
    (imem imem' : Memory.Memory.t) (iregs : Intermediate.Register.t)
    (ipc : Pointer.t) (r1 : register) (bp : Block.id) (op : Z)
    (base : nat) (w2 : mword mt) (ts : LRC.value_tag)
    (oldv : mword mt) (oldvt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id))
    (ms : @Symbolic.state mt lrc_tags unit) mpc' :
  Intermediate.GlobalEnv.executing G ipc (IStore r1 R_RA) ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  Memory.Memory.store imem (Pointer.component ipc, bp, op)
    (Intermediate.Register.get R_RA iregs) = Some imem' ->
  amap_get bmap (Pointer.component ipc) bp = Some base ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA)) = Some (w2@ts) ->
  getm (Symbolic.mem ms)
    (@word_of_nat (word_size mt) (base + Z.to_nat op))
    = Some (oldv@(LRC.MTag oldvt (Pointer.component ipc) ent false)) ->
  oldvt = LRC.Other \/ oldvt = LRC.Invalidated ->
  sinv_inst bmap gps imem iregs ipc ms ->
  sinv_inst bmap gps imem' iregs (Pointer.inc ipc)
    (@Symbolic.State mt lrc_tags _
       (setm (Symbolic.mem ms)
          (@word_of_nat (word_size mt) (base + Z.to_nat op))
          (w2@(LRC.MTag ts (Pointer.component ipc) ent false)))
       (setm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA))
          (w2@(if LRC.is_address ts then LRC.Invalidated
               else LRC.Other)))
       mpc' tt).
Proof.
case: ipc => [[cI bIp] oI].
move=> Hex Hptr Hstore Hamap Hra Hcell Hovt [Hin Htop Hdeep].
have Hoffs : (0 <= oI)%Z.
{ case: Hex => ? [? [_ [_ [Hge _]]]].
  move: Hge => /= Hge. by lia. }
have [Pcode0 [Hrun0 Hnth0]] := executing_running Hin Hex.
move: Hnth0 => /= Hnth0.
have Hsh := running_shape Hrun0.
have Hlive : dead_at Pcode0 (Z.to_nat oI) = false
  := cs_storera_live Hsh Hnth0.
have Hoffi : Z.to_nat (oI + 1) = (Z.to_nat oI).+1.
{ rewrite Z2Nat.inj_add //=. by rewrite PeanoNat.Nat.add_1_r. }
split; first exact: Hin.
- rewrite /top_ok.
  case: gps Htop Hdeep => [|p rest] //= Htop _.
  move=> Pcode' Hrun' _.
  have Hrun'' : running_code (cI, bIp, oI) Pcode'.
  { case: Hrun' => Cx [jx [Px [HAx HBx HCx]]].
    by exists Cx, jx, Px. }
  have E := running_code_uniq Hrun'' Hrun0; subst Pcode'.
  rewrite /= Hoffi (dead_at_S Hnth0) /=.
  have Htop' := Htop _ Hrun0 Hoffs.
  rewrite Hlive in Htop'.
  case: Htop' => w [Hpos Hra'].
  have Ew : w2 = w /\ ts = frame_tag cI p rest.
  { move: Hra'. rewrite /= Hra. case=> -> ->. by split. }
  case: Ew => Ew Ets.
  exists (@word_of_nat (word_size mt) (base + Z.to_nat op)), w.
  split; first exact Hpos.
  exists cI, ent.
  rewrite setmE eqxx Ew Ets.
  reflexivity.
- rewrite /deep_ok.
  case: gps Htop Hdeep => [|p rest] //= _ [ads0 Hcells0].
  exists ads0.
  exact: (frames_cells_store2 _ _ Hcell Hovt Hcells0).
Qed.

(* ==================== the record assembly ==================== *)

(* the one remaining dynamic obligation: the pop-R_RA clause (the SP-tie
   strengthening campaign discharges it) *)
Hypothesis Hload_ra_inst :
  forall bmap gps imem iregs ipc ms r1 (bp : Block.id) (op : Z)
         (v : value) (base : nat) (w2 : mword mt)
         (cvt : LRC.value_tag)
         (ent : option (Procedure.id * seq Component.id)) mpc',
    lin_match L P C pra prb sinv_inst bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (ILoad r1 R_RA) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
    amap_get bmap (Pointer.component ipc) bp = Some base ->
    getm (Symbolic.mem ms)
      (@word_of_nat (word_size mt) (base + Z.to_nat op))
      = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
    (forall (tpc : Pointer.t) (gps' : list Pointer.t),
     gps = tpc :: gps' ->
     exists (Cprocs' : NMap Machine.code) (j' : nat)
            (P0' : Procedure.id) (Pcode' : Machine.code),
       [/\ Intermediate.prog_procedures ilp (Pointer.component tpc)
             = Some Cprocs',
           Pointer.block tpc
             = proc_nb0 ilp (Pointer.component tpc) + j',
           List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode'),
           (0 <= Pointer.offset tpc)%Z
         & w2 = @word_of_nat (word_size mt)
                  (side_flat_pos L P C pra prb (Pointer.component tpc)
                     P0' Pcode' (Z.to_nat (Pointer.offset tpc))
                   + size (initial_memory (mt := mt) pbW))]
       /\ (exists i'',
             List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
             = Some i'')
       /\ (~~ nilp gps' ->
           dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
       /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                 then LRC.InternalJump
                 else LRC.Ret (cross_frames (Pointer.component tpc)
                                 gps'))) ->
    sinv_inst bmap gps imem (Intermediate.Register.set R_RA v iregs)
      (Pointer.inc ipc)
      (@Symbolic.State mt lrc_tags _
         (setm (Symbolic.mem ms)
            (@word_of_nat (word_size mt) (base + Z.to_nat op))
            (w2@(LRC.MTag (if LRC.is_address cvt then LRC.Invalidated
                           else LRC.Other)
                   (Pointer.component ipc) ent false)))
         (setm (Symbolic.regs ms)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat R_RA)) (w2@cvt))
         mpc' tt).

Theorem sinv_inst_spec : sinv_spec L P C pra prb sinv_inst.
Proof.
constructor.
- (* nop *)
  move=> bmap gps imem iregs ipc ms mpc' Hex HS0.
  exact: (sinv_inst_skip _ Hex (fun _ => erefl) HS0).
- (* label *)
  move=> bmap gps imem iregs ipc l ms mpc' Hex HS0.
  exact: (sinv_inst_skip _ Hex (fun _ => erefl) HS0).
- (* const *)
  move=> bmap gps imem iregs ipc v0 r ms mpc' Hex Hra HS0.
  exact: (sinv_inst_reg_write _ _ _ _ _ Hex (fun _ => erefl) Hra HS0).
- (* mov *)
  move=> bmap gps imem iregs ipc r1 r2 w1 ms mpc' Hex Hra1 Hra2 Hw1
         HS0.
  exact: (sinv_inst_reg_write _ _ _ _ _ Hex (fun _ => erefl) Hra2 HS0).
- (* mov, invalidated source *)
  move=> bmap gps imem iregs ipc r1 r2 w1 ms mpc' Hex Hra1 Hra2 Hu1
         Hw1 HS0.
  exact: (sinv_inst_reg_write _ _ _ _ _ Hex (fun _ => erefl) Hra2 HS0).
- (* binop *)
  move=> bmap gps imem iregs ipc op r1 r2 r3 w1 w2 ms mpc' Hex Hra3
         Hw1 Hw2 HS0.
  exact: (sinv_inst_reg_write _ _ _ _ _ Hex (fun _ => erefl) Hra3 HS0).
- (* load *)
  move=> bmap gps imem iregs ipc r1 r2 bp op v base w ent ms mpc' Hex
         Hra2 Hget Hload Hamap Hcell HS0.
  apply: (sinv_inst_reg_write _ _ _ _ _ Hex _ Hra2 HS0).
  move=> dead.
  exact: (ra_dead_step_skip (i := ILoad r1 r2) Hra2 dead).
- (* load, invalidated cell *)
  move=> bmap gps imem iregs ipc r1 r2 bp op v base w ent ms mpc' Hex
         Hra2 Hget Hload Hu Hamap Hcell HS0.
  apply: (sinv_inst_reg_write _ _ _ _ _ Hex _ Hra2 HS0).
  move=> dead.
  exact: (ra_dead_step_skip (i := ILoad r1 r2) Hra2 dead).
- (* store *)
  move=> bmap gps imem imem' iregs ipc r1 r2 bp op base w oldv ent ms
         mpc' Hex Hra2 Hget Hstore Hamap Hw Hcell HS0.
  apply: (sinv_inst_store _ _ _ _ _ _ Hex _ Hcell HS0).
  move=> dead.
  exact: (ra_dead_step_skip (i := IStore r1 r2) Hra2 dead).
- (* store, invalidated source *)
  move=> bmap gps imem imem' iregs ipc r1 r2 bp op base w oldv ent
         ms mpc' Hex Hra2 Hu2 Hget Hstore Hamap Hw Hcell HS0.
  apply: (sinv_inst_store _ _ _ _ _ _ Hex _ Hcell HS0).
  move=> dead.
  exact: (ra_dead_step_skip (i := IStore r1 r2) Hra2 dead).
- (* alloc *)
  move=> bmap gps imem imem' iregs ipc rptr rsize szZ bI base' ms mem'
         mregs' mpc' Hex Hrptr Hsz HA Hmono Hres HS0.
  exact: (sinv_inst_alloc _ _ Hex Hrptr Hsz HA Hmono Hres HS0).
- (* bnz_z *)
  move=> bmap gps imem iregs ipc r l ms mpc' Hex Hz HS0.
  exact: (sinv_inst_skip _ Hex (fun _ => erefl) HS0).
- (* bnz_nz *)
  move=> bmap gps imem iregs ipc tpc r l zv ms mpc' Hex Hfind Hnz Hz
         HS0.
  exact: (sinv_inst_bnz_nz _ _ _ _ Hex Hfind HS0).
- (* pop_jump *)
  move=> bmap gps' imem iregs ipc tpc ms mpc' Hex Hcmp HS0.
  exact: (sinv_inst_pop_jump _ _ _ _ Hex Hcmp HS0).
- (* pop_ret *)
  move=> bmap gps' imem iregs ipc tpc ms mregs' mpc' Hex Hneq HS0.
  exact: (sinv_inst_pop_ret _ _ _ _ _ Hex Hneq HS0).
- (* push_jal *)
  move=> bmap gps imem iregs ipc tpc l ms Cprocs j P0 Pcode mpc' Hex
         Hfind Hilp Hblk Hjnth Hoff HS0.
  exact: (sinv_inst_push_jal _ Hex Hfind Hilp Hblk Hjnth Hoff HS0).
- (* push_call *)
  move=> bmap gps imem iregs ipc C' b ms mregs' mpc' Cprocs j P0 Pcode
         p Hne HCin Hex Hilp Hblk Hjnth Hoff Hra HS0.
  exact: (sinv_inst_push_call _ _ Hne HCin Hex Hilp Hblk Hjnth Hoff
            Hra HS0).
- (* frame_jump *)
  move=> bmap gps' tpc imem iregs ipc ms Hm Hex Hcmp Cprocs Hilp.
  exact: (sinv_inst_frame_jump (lm_stack Hm) Hex Hcmp Hilp).
- (* frame_ret *)
  move=> bmap gps' tpc imem iregs ipc ms Hm Hex Hneq.
  exact: (sinv_inst_frame_ret (lm_stack Hm) Hex Hneq).
- (* load_ra *)
  move=> bmap gps imem iregs ipc ms r1 bp op v base w2 cvt ent mpc'
         Hm Hex Hget Hload Hamap Hcell.
  by apply: Hload_ra_inst; eassumption.
- (* store_ra *)
  move=> bmap gps imem imem' iregs ipc ms r1 bp op base w2 ts oldv
         oldvt ent mpc' Hm Hex Hget Hstore Hamap Hra Hcell Hovt.
  exact: (sinv_inst_store_ra _ Hex Hget Hstore Hamap Hra Hcell Hovt
            (lm_stack Hm)).
Qed.

End LinInv.

(* every component's side is one of the two programs — feeds the
   [sr_ra] discharge through [compiled_side_ra_free] *)
Lemma side_of_cases (pra prb : Intermediate.program)
    (cid : Component.id) :
  side_of pra prb cid = pra \/ side_of pra prb cid = prb.
Proof.
rewrite /side_of.
case: (cid \in domm (Intermediate.prog_procedures pra)).
- by left.
- by right.
Qed.

(* ==================== wf/closedness discharges ==================== *)

(* the three domain bridges follow from well-formedness and closedness
   of the linked program; the spec then rests on the shape facts and the
   pop clause only *)
Theorem sinv_inst_spec_wf (L P C : nat)
    (pra prb : Intermediate.program) :
  Intermediate.well_formed_program (Intermediate.program_link pra prb) ->
  Intermediate.closed_program (Intermediate.program_link pra prb) ->
  (forall cid Cprocs P0 Pcode,
     Intermediate.prog_procedures (Intermediate.program_link pra prb)
       cid = Some Cprocs ->
     getm Cprocs P0 = Some Pcode ->
     code_shape Pcode) ->
  (forall cid Cprocs P1 Pcode1 o1 (l : label) P2 Pcode2 o2,
     Intermediate.prog_procedures (Intermediate.program_link pra prb)
       cid = Some Cprocs ->
     getm Cprocs P1 = Some Pcode1 ->
     getm Cprocs P2 = Some Pcode2 ->
     List.nth_error Pcode1 o1 = Some (IJal l) ->
     List.nth_error Pcode2 o2 = Some (ILabel l) ->
     dead_at Pcode2 o2 = false) ->
  (forall bmap gps imem iregs ipc ms r1 (bp : Block.id) (op : Z)
          (v : value) (base : nat) (w2 : mword mt)
          (cvt : LRC.value_tag)
          (ent : option (Procedure.id * seq Component.id)) mpc',
     lin_match L P C pra prb (sinv_inst L P C pra prb) bmap gps imem
       iregs ipc ms ->
     Intermediate.GlobalEnv.executing
       (Intermediate.GlobalEnv.prepare_global_env
          (Intermediate.program_link pra prb)) ipc (ILoad r1 R_RA) ->
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
              (Intermediate.program_link pra prb)
              (Pointer.component tpc) = Some Cprocs',
            Pointer.block tpc
              = proc_nb0 (Intermediate.program_link pra prb)
                  (Pointer.component tpc) + j',
            List.nth_error (elementsm Cprocs') j' = Some (P0', Pcode'),
            (0 <= Pointer.offset tpc)%Z
          & w2 = @word_of_nat (word_size mt)
                   (side_flat_pos L P C pra prb (Pointer.component tpc)
                      P0' Pcode' (Z.to_nat (Pointer.offset tpc))
                    + size (initial_memory (mt := mt)
                              (unionm (Intermediate.prog_buffers pra)
                                 (Intermediate.prog_buffers prb))))]
        /\ (exists i'',
              List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
              = Some i'')
        /\ (~~ nilp gps' ->
            dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
        /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                  then LRC.InternalJump
                  else LRC.Ret (cross_frames (Pointer.component tpc)
                                  gps'))) ->
     sinv_inst L P C pra prb bmap gps imem
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
  sinv_spec L P C pra prb (sinv_inst L P C pra prb).
Proof.
move=> Hwf Hcl Hshape Hjal Hload.
apply: sinv_inst_spec.
- (* main is interfaced *)
  have [mp [_ [Hget _]]] := Intermediate.cprog_main_existence Hcl.
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by rewrite mem_domm Hget.
- exact: Hshape.
- exact: Hjal.
- (* interface -> procedures *)
  move=> cid Hin.
  rewrite (Intermediate.wfprog_defined_procedures Hwf) mem_domm in Hin.
  case E: (Intermediate.prog_procedures _ cid) Hin => [Cprocs|] //.
  move=> _. by exists Cprocs.
- (* procedures -> interface *)
  move=> cid Hin.
  by rewrite (Intermediate.wfprog_defined_procedures Hwf).
- exact: Hload.
Qed.

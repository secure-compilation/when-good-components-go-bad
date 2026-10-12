(* Task #14 (I→Merged correctness): the MATCH RELATION.

   Relates Intermediate.CS states of the linked compiled pair to me-machine
   (Symbolic) states.  The settled clauses:
   - pc: the I pc (C, blk, off) decomposes through the genv (LinGenv: blk =
     proc_nb0 + j, the j-th procedure P of C), and the me pc word is
     pc0 + flat_pos of (C, P, off), tagged Level n C with n the number of
     cross-component frames on gps;
   - memory: [mem_rel] (LinMatch) through an address map extending the
     static one;
   - registers: pointwise [val_rel_b] with Other tags, EXCEPT R_RA (owned
     by the calling-convention clause);
   - code: the code region of the me memory is exactly the encoded program
     (LRC's STORE rule refuses is_code cells, so this is invariant);
   - stack: the gps ↔ (R_RA / stack cells / Level) correspondence — the
     calling-convention invariant of compiled code (in design; kept as a
     parameter of the record for now so the data-step diagram can begin). *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path fintype.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.LinPos.
Require Import MicroPolicies.Recomposition.LinGenv.
Require Import MicroPolicies.Recomposition.LinMem.
Require Import MicroPolicies.Recomposition.LinMatch.

Import Intermediate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ==================== determinate-run toolkit ==================== *)

Section DetStar.

Variable L : semantics.
Hypothesis DET : determinate L.

(* two runs from one state have prefix-comparable traces, with the
   residual run made explicit *)
Lemma star_traces_comp :
  forall s t1 s1, Star L s t1 s1 ->
  forall t2 s2, Star L s t2 s2 ->
  (exists t', t2 = t1 ** t' /\ Star L s1 t' s2)
  \/ (exists t', t1 = t2 ** t' /\ Star L s2 t' s1).
Proof.
  induction 1 as [s|s1 t1 s2 t2 s3 tw Hstep Hstar IH Ht]; intros t4 s4 H2.
  - left. exists t4. split; auto.
  - inversion H2 as [|s0 ta sa tb sb tc Hstep' Hstar' Htr']; subst.
    + right. exists (t1 ** t2). split; auto.
      eapply star_step; eauto.
    + assert (MT : match_traces t1 ta)
        by (eapply sd_determ_1; [exact DET | exact Hstep | exact Hstep']).
      assert (Eta : t1 = ta) by (inversion MT; auto).
      subst ta.
      assert (Esa : s2 = sa)
        by (eapply sd_determ_2; [exact DET | exact Hstep | exact Hstep']).
      subst sa.
      destruct (IH _ _ Hstar') as [[t' [Et' Hres]] | [t' [Et' Hres]]].
      * left. exists t'. split; auto. subst. traceEq.
      * right. exists t'. split; auto. subst. traceEq.
Qed.

(* a state with arbitrarily long silent runs *)
Definition silent_ray (s : Smallstep.state L) : Prop :=
  forall n : nat,
    exists (k : nat) (s' : Smallstep.state L),
      (n <= k)%coq_nat
      /\ starN (Smallstep.step L) (globalenv L) k s E0 s'.

Lemma silent_ray_shift :
  forall s s',
    silent_ray s ->
    Smallstep.step L (globalenv L) s E0 s' ->
    silent_ray s'.
Proof.
  intros s s' Hray Hstep n.
  destruct (Hray (S n)) as [k [s'' [Hk HN]]].
  destruct k as [|k]; [lia|].
  inversion HN as [|n0 s0 tw ta sa tb sb Hst1 HstN Htr]; subst.
  destruct (List.app_eq_nil _ _ (esym Htr)) as [Eta Etb].
  subst ta tb.
  assert (Esa : sa = s')
    by (eapply sd_determ_2; [exact DET | exact Hst1 | exact Hstep]).
  subst sa.
  exists k. eexists. split; [lia | exact HstN].
Qed.

(* any run out of a silent ray is silent and stays on the ray *)
Lemma silent_ray_absorb :
  forall s t s',
    Star L s t s' -> silent_ray s -> t = E0 /\ silent_ray s'.
Proof.
  induction 1 as [s|s1 t1 s2 t2 s3 tw Hstep Hstar IH Ht]; intros Hray.
  - split; auto.
  - destruct (Hray 1%coq_nat) as [k [sx [Hk HN]]].
    destruct k as [|k]; [lia|].
    inversion HN as [|n0 s0 tz ta sa tb sb Hst1 HstN Htr]; subst.
    destruct (List.app_eq_nil _ _ (esym Htr)) as [Eta Etb].
    subst ta tb.
    assert (MT : match_traces t1 E0)
      by (eapply sd_determ_1; [exact DET | exact Hstep | exact Hst1]).
    assert (Et1 : t1 = E0) by (inversion MT; auto).
    subst t1.
    assert (Esa : s2 = sa)
      by (eapply sd_determ_2; [exact DET | exact Hstep | exact Hst1]).
    subst sa.
    destruct (IH (silent_ray_shift Hray Hstep)) as [Et2 Hray3].
    subst. split; auto.
Qed.

(* silent counted runs compose *)
Lemma starN_silent_compose :
  forall n1 s s',
    starN (Smallstep.step L) (globalenv L) n1 s E0 s' ->
  forall n2 s'',
    starN (Smallstep.step L) (globalenv L) n2 s' E0 s'' ->
    starN (Smallstep.step L) (globalenv L) (n1 + n2)%coq_nat s E0 s''.
Proof.
  intros n1 s s' HN.
  remember E0 as tt0 eqn:Htt in HN.
  revert Htt.
  induction HN as [|n s0 tw ta sa tb sb Hst HstN IH Htr];
    intros Htt n2 s'' HN2.
  - exact HN2.
  - rewrite Htr in Htt.
    destruct (List.app_eq_nil _ _ Htt) as [Eta Etb].
    subst ta tb.
    simpl. econstructor;
      [exact Hst | exact (IH (erefl _) _ _ HN2) | auto].
Qed.

(* a stuck state ends every run immediately *)
Lemma star_nostep_refl :
  forall s t s', Star L s t s' -> Nostep L s -> t = E0 /\ s' = s.
Proof.
  intros s t s' Hstar Hns.
  inversion Hstar as [|sa ta sb tb sc tw Hstep Hrest Htr]; subst.
  - split; auto.
  - exfalso. exact (Hns _ _ Hstep).
Qed.

(* a silent ray contradicts stuckness *)
Lemma ray_nostep_absurd :
  forall s, silent_ray s -> Nostep L s -> False.
Proof.
  intros s Hray Hns.
  destruct (Hray 1%coq_nat) as [k [s' [Hk HN]]].
  destruct k as [|k]; [lia|].
  inversion HN as [|n0 s0 tw ta sa tb sb Hst HstN Htr]; subst.
  exact (Hns _ _ Hst).
Qed.

End DetStar.

Section LinSim.

(* the canonical label-scheme bounds and the two compiled sides *)
Variables L P C : nat.
Variables pra prb : Intermediate.program.

(* the linked Intermediate program and its genv *)
Let ilp : Intermediate.program := Intermediate.program_link pra prb.
Let G : global_env := prepare_global_env ilp.

(* the linked me-side code and memory layout *)
Let codeW : @Merged.code mt := lin_code L P C pra ++ lin_code L P C prb.
Let pbW : NMap {fmap Block.id -> nat + seq value} :=
  unionm (Intermediate.prog_buffers pra) (Intermediate.prog_buffers prb).
Let pc0 : nat := size (initial_memory (mt := mt) pbW).

(* flat position of instruction [o] of procedure (C0,P0), side-aware:
   left-side components at their positions, right-side shifted *)
Definition side_flat_pos (C0 : Component.id) (P0 : Procedure.id)
    (Pcode : Machine.code) (o : nat) : nat :=
  if C0 \in domm (Intermediate.prog_procedures pra)
  then flat_pos pra C0 P0 Pcode o
  else size (lin_code L P C pra) + flat_pos prb C0 P0 Pcode o.

(* the source program owning component C0 *)
Definition side_of (C0 : Component.id) : Intermediate.program :=
  if C0 \in domm (Intermediate.prog_procedures pra) then pra else prb.

(* number of cross-component frames of a gps (consecutive same-component
   frames come from IJal; component changes come from ICall) *)
Fixpoint cross_frames (cur : Component.id) (gps : list Pointer.t) : nat :=
  match gps with
  | [::] => 0
  | p :: gps' =>
      if Pointer.component p == cur
      then cross_frames cur gps'
      else (cross_frames (Pointer.component p) gps').+1
  end.

(* the code region of the me memory is the encoded program *)
Definition code_region_ok (mmem : {fmap mword mt -> matom}) : Prop :=
  forall (w : mword mt) (a : matom),
    encode_code codeW pc0 w = Some a ->
    getm mmem w = Some a.

(* the pc clause: the I pc decomposes through the genv and lands at its
   flat position, tagged with the running component at the gps's level *)
Definition pc_rel (gps : list Pointer.t) (ipc : Pointer.t)
    (mpc : atom (mword mt) (tag_type lrc_tags Symbolic.P)) : Prop :=
  exists (Cprocs_src : NMap Machine.code) (j : nat)
         (P0 : Procedure.id) (Pcode : Machine.code),
    [/\ Intermediate.prog_procedures ilp (Pointer.component ipc)
          = Some Cprocs_src,
        Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j,
        List.nth_error (elementsm Cprocs_src) j = Some (P0, Pcode),
        (0 <= Pointer.offset ipc)%Z
      & vala mpc
        = @word_of_nat (word_size mt)
            (side_flat_pos (Pointer.component ipc) P0 Pcode
               (Z.to_nat (Pointer.offset ipc)) + pc0)
        /\ taga mpc
           = LRC.Level (cross_frames (Pointer.component ipc) gps)
               (Pointer.component ipc)].

(* registers except R_RA: related values, Other tags *)
Definition regs_rel_no_ra (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall r : register,
    r <> R_RA ->
    exists a : @ratom mt,
      [/\ getm mregs (@word_of_nat (reg_field_size mt)
                        (Intermediate.Register.to_nat r)) = Some a,
          val_rel_b bmap (Intermediate.Register.get r iregs) (vala a)
        & taga a = Other].

(* THE match relation, parameterized by the calling-convention stack
   invariant [SINV] (gps vs the me state) — instantiated once the R_RA
   discipline is formalized *)
(* the call-surviving register relation: a register is either strongly
   related with an Other tag, or its I-side value is Undef (in which case
   the me-side tag is unconstrained — post-invalidation state) *)
Definition regs_rel_w (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall r : register,
    r <> R_RA ->
    exists a : @ratom mt,
      getm mregs (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r)) = Some a
      /\ ((taga a = Other
           /\ val_rel_b bmap (Intermediate.Register.get r iregs) (vala a))
          \/ (Intermediate.Register.get r iregs = Undef
              /\ (taga a = LRC.Other \/ taga a = LRC.Invalidated))).

(* the me register file is total on the machine's working keys (the 11
   clear-list registers plus ra) — Jump/Jal's clear-lists need them *)
Definition reg_keys : seq nat := [:: 1; 0; 2; 3; 4; 5; 6; 7; 16; 17; 18; 19].

Definition regs_total (mregs : {fmap reg mt -> @ratom mt}) : Prop :=
  forall k : nat,
    k \in reg_keys ->
    exists a : @ratom mt,
      getm mregs (word.as_word (ssrint.Posz k)) = Some a.

Record lin_match
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map)
    (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t)
    (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) : Prop := LinMatch {
  lm_pc : pc_rel gps ipc (Symbolic.pc ms);
  lm_mem : mem_rel bmap imem (Symbolic.mem ms);
  lm_regs : regs_rel_w bmap iregs (Symbolic.regs ms);
  lm_code : code_region_ok (Symbolic.mem ms);
  lm_stack : SINV bmap gps imem iregs ipc ms;
  lm_total : regs_total (Symbolic.regs ms)
}.

(* totality survives any register write *)
Lemma regs_total_set (mregs : {fmap reg mt -> @ratom mt})
    (key : reg mt) (a : @ratom mt) :
  regs_total mregs -> regs_total (setm mregs key a).
Proof.
move=> Htot k Hk; rewrite setmE.
case: eqP => _; [by eexists | exact: Htot].
Qed.

(* placed later, after as_won_eqE (see regs_total_reg0 below) *)

(* ==================== register plumbing ==================== *)

(* register indices are small and distinct as 5-bit words *)
Lemma to_nat_lt32 (r : register) : Intermediate.Register.to_nat r < 32.
Proof. by case: r. Qed.

Lemma to_nat_inj (r r' : register) :
  Intermediate.Register.to_nat r = Intermediate.Register.to_nat r' ->
  r = r'.
Proof. by case: r; case: r'. Qed.

Lemma reg_key_eqE (r r' : register) :
  (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r)
   == word_of_nat (Intermediate.Register.to_nat r'))
  = (Intermediate.Register.to_nat r == Intermediate.Register.to_nat r').
Proof.
by rewrite won_eqE // small_lt_reg // to_nat_lt32.
Qed.

(* reading a related register *)
Lemma regs_rel_get (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) :
  regs_rel_no_ra bmap iregs mregs ->
  r <> R_RA ->
  exists w : mword mt,
    [/\ getm mregs (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
          = Some (w@LRC.Other)
      & val_rel_b bmap (Intermediate.Register.get r iregs) w].
Proof.
move=> Hrel Hra.
have [a [Hget Hval Htag]] := Hrel r Hra.
exists (vala a).
split=> //.
by rewrite -Htag; case: a Hget Hval Htag.
Qed.

(* an update on a present key succeeds *)
Lemma updm_from_get (T : ordType) (S : Type) (m : {fmap T -> S})
    (k : T) (a v : S) :
  getm m k = Some a ->
  updm m k v = Some (setm m k v).
Proof. by rewrite /updm => ->. Qed.

(* writing related values (with Other tags) preserves the relation *)
Lemma regs_rel_set (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register)
    (v : value) (w : mword mt) :
  regs_rel_no_ra bmap iregs mregs ->
  val_rel_b bmap v w ->
  regs_rel_no_ra bmap (Intermediate.Register.set r v iregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r))
       (w@LRC.Other)).
Proof.
move=> Hrel Hval r' Hra'.
rewrite /Intermediate.Register.get /Intermediate.Register.set !setmE.
rewrite reg_key_eqE.
case Er: (Intermediate.Register.to_nat r'
          == Intermediate.Register.to_nat r).
- by exists (w@LRC.Other); split.
- have [a [Hget Hval' Htag]] := Hrel r' Hra'.
  by exists a; split.
Qed.

(* writes to R_RA's slot are invisible to the no-RA relation *)
Lemma regs_rel_set_ra (bmap : addr_map)
    (iregs : Intermediate.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (a : @ratom mt) :
  regs_rel_no_ra bmap iregs mregs ->
  regs_rel_no_ra bmap iregs
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat R_RA)) a).
Proof.
move=> Hrel r' Hra'.
rewrite setmE reg_key_eqE.
case Er: (Intermediate.Register.to_nat r'
          == Intermediate.Register.to_nat R_RA).
- by move/eqP/to_nat_inj: Er => Er; case: Hra'.
- exact: Hrel.
Qed.

(* the call-surviving register relation: a register is either strongly
   related with an Other tag, or its I-side value is Undef (in which case
   the me-side tag is unconstrained — post-invalidation state) *)
Lemma regs_rel_w_of (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) :
  regs_rel_no_ra bmap iregs mregs -> regs_rel_w bmap iregs mregs.
Proof.
move=> Hrel r Hra.
have [a [Hget Hval Htag]] := Hrel r Hra.
by exists a; split=> //; left.
Qed.

(* at use sites the CS rules pin a non-Undef shape, recovering strength *)
Lemma regs_rel_w_get (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) :
  regs_rel_w bmap iregs mregs ->
  r <> R_RA ->
  Intermediate.Register.get r iregs <> Undef ->
  exists w : mword mt,
    [/\ getm mregs (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
          = Some (w@LRC.Other)
      & val_rel_b bmap (Intermediate.Register.get r iregs) w].
Proof.
move=> Hrel Hra Hnu.
have [a [Hget [[Htag Hval]|[Hu _]]]] := Hrel r Hra; last by [].
exists (vala a); split=> //.
by rewrite -Htag; case: a Hget Htag Hval.
Qed.

(* the Undef-tolerant fetch: every non-RA register has a register-file
   class atom (Other or Invalidated), related to the I value (Undef
   relates freely), and DEFINED values pin the Other tag — the entry
   point for the tag-parametric Mov/Store diagram cases *)
Lemma regs_rel_w_get_any (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) :
  regs_rel_w bmap iregs mregs ->
  r <> R_RA ->
  exists (w : mword mt) (t : LRC.value_tag),
    [/\ getm mregs (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
          = Some (w@t),
        val_rel_b bmap (Intermediate.Register.get r iregs) w,
        t = LRC.Other \/ t = LRC.Invalidated
      & Intermediate.Register.get r iregs <> Undef -> t = LRC.Other].
Proof.
move=> Hrel Hra.
have [a [Hget [[Htag Hval]|[Hu Ht]]]] := Hrel r Hra.
- case: a Hget Htag Hval => w t /= Hget Htag Hval.
  subst t.
  exists w, LRC.Other.
  by split=> //; left.
- case: a Hget Ht => w t /= Hget Ht.
  exists w, t.
  rewrite Hu.
  by split.
Qed.

(* writing related values (Other tags) preserves the weak relation *)
Lemma regs_rel_w_set (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (r : register)
    (v : value) (w : mword mt) :
  regs_rel_w bmap iregs mregs ->
  val_rel_b bmap v w ->
  regs_rel_w bmap (Intermediate.Register.set r v iregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r))
       (w@LRC.Other)).
Proof.
move=> Hrel Hval r' Hra'.
rewrite /Intermediate.Register.get /Intermediate.Register.set !setmE.
rewrite reg_key_eqE.
case Er: (Intermediate.Register.to_nat r'
          == Intermediate.Register.to_nat r).
- by exists (w@LRC.Other); split=> //; left; split.
- have [a [Hget Hd]] := Hrel r' Hra'.
  by exists a; split.
Qed.

(* setting Undef on the I side absorbs any me-side atom of a
   register-file tag class (Other or Invalidated) *)
Lemma regs_rel_w_set_undef (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (a : @ratom mt) :
  taga a = LRC.Other \/ taga a = LRC.Invalidated ->
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap (Intermediate.Register.set r Undef iregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) a).
Proof.
move=> Ht Hrel r' Hra'.
rewrite /Intermediate.Register.get /Intermediate.Register.set !setmE.
rewrite reg_key_eqE.
case Er: (Intermediate.Register.to_nat r'
          == Intermediate.Register.to_nat r).
- exists a; split=> //; right.
  by split.
- have [a' [Hget Hd]] := Hrel r' Hra'.
  by exists a'; split.
Qed.

Lemma regs_rel_w_set_ra (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (a : @ratom mt) :
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap iregs
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat R_RA)) a).
Proof.
move=> Hrel r' Hra'.
rewrite setmE reg_key_eqE.
case Er: (Intermediate.Register.to_nat r'
          == Intermediate.Register.to_nat R_RA).
- by move/eqP/to_nat_inj: Er => Er; case: Hra'.
- exact: Hrel.
Qed.

Lemma won_as_eqE (i j : nat) :
  i < 32 -> j < 32 ->
  ((@word_of_nat (reg_field_size mt) i) == word.as_word (ssrint.Posz j))
  = (i == j).
Proof.
move=> Hi Hj.
have -> : (word.as_word (ssrint.Posz j) : word (reg_field_size mt))
          = word_of_nat j by [].
by rewrite won_eqE // small_lt_reg.
Qed.

(* the invalidation thread of a cross call/return: ra rewritten, the ten
   clear registers invalidated, rcom untouched — matches the I side's
   Register.invalidate (Undef everywhere but R_COM) *)
Lemma regs_rel_w_invalidate (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt})
    (rav : mword mt) (rat : LRC.value_tag)
    (w0 w2 w3 w5 w6 w7 w16 w17 w18 w19 : mword mt) :
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap (Intermediate.Register.invalidate iregs)
    (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm
       mregs
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat R_RA)) (rav@rat))
       (word.as_word (ssrint.Posz 0)) (w0@LRC.Invalidated))
       (word.as_word (ssrint.Posz 2)) (w2@LRC.Invalidated))
       (word.as_word (ssrint.Posz 3)) (w3@LRC.Invalidated))
       (word.as_word (ssrint.Posz 5)) (w5@LRC.Invalidated))
       (word.as_word (ssrint.Posz 6)) (w6@LRC.Invalidated))
       (word.as_word (ssrint.Posz 7)) (w7@LRC.Invalidated))
       (word.as_word (ssrint.Posz 16)) (w16@LRC.Invalidated))
       (word.as_word (ssrint.Posz 17)) (w17@LRC.Invalidated))
       (word.as_word (ssrint.Posz 18)) (w18@LRC.Invalidated))
       (word.as_word (ssrint.Posz 19)) (w19@LRC.Invalidated)).
Proof.
move=> Hrel r' Hra'.
have Hra4 : (ra : reg mt) = word.as_word (ssrint.Posz 4) by [].
rewrite /Intermediate.Register.invalidate /Intermediate.Register.get
  mkfmapE.
case: r' Hra' => Hra' /=; rewrite ?Hra4 !setmE !won_as_eqE //=.
- (* R_ONE *)
  by exists (w0@LRC.Invalidated); split=> //; right; split=> //; right.
- (* R_COM *)
  have Hcr : R_COM <> R_RA by [].
  have [a [Hget Hd]] := Hrel R_COM Hcr.
  by exists a; split.
- (* R_AUX1 *)
  by exists (w2@LRC.Invalidated); split=> //; right; split=> //; right.
- (* R_AUX2 *)
  by exists (w3@LRC.Invalidated); split=> //; right; split=> //; right.
- (* R_SP *)
  by exists (w5@LRC.Invalidated); split=> //; right; split=> //; right.
- (* R_ARG *)
  by exists (w6@LRC.Invalidated); split=> //; right; split=> //; right.
Qed.

(* ==================== address-map extension ==================== *)

(* extending the address map at a FRESH block preserves the value
   relation (existing pointers reference other blocks) *)
Lemma val_rel_b_ext (bmap : addr_map) (C0 : Component.id) (b : Block.id)
    (base : nat) (v : value) (w : mword mt) :
  amap_get bmap C0 b = None ->
  val_rel_b bmap v w ->
  val_rel_b (amap_set bmap C0 b base) v w.
Proof.
move=> Hfresh.
case: v => //= [[[c' b'] o']].
case=> base' [Hg Hw].
exists base'; split=> //.
rewrite amap_set_neq //.
move=> [E1 E2]; subst c' b'.
by rewrite Hfresh in Hg.
Qed.

Lemma regs_rel_w_ext (bmap : addr_map) (C0 : Component.id)
    (b : Block.id) (base : nat) iregs
    (mregs : {fmap reg mt -> @ratom mt}) :
  amap_get bmap C0 b = None ->
  regs_rel_w bmap iregs mregs ->
  regs_rel_w (amap_set bmap C0 b base) iregs mregs.
Proof.
move=> Hfresh Hrel r' Hra'.
have [a [Hget Hd]] := Hrel r' Hra'.
exists a; split=> //.
case: Hd => [[Htag Hval]|Hu]; [left|by right].
split=> //.
exact: val_rel_b_ext Hval.
Qed.

(* ==================== position bridges ==================== *)

(* word successor of an encoded position — exact, no bounds (modular) *)
Lemma won_S (n : nat) :
  addw (@word_of_nat (word_size mt) n) onew = word_of_nat n.+1.
Proof.
rewrite /word_of_nat.
have -> : (onew : mword mt) = word.as_word (ssrint.Posz 1) by [].
rewrite as_word_addwD.
by congr word.as_word; lia.
Qed.

(* flat position of the next instruction *)
Lemma flat_pos_S (pr : Intermediate.program) (c : Component.id)
    (p : Procedure.id) (Pcode : Machine.code) (o : nat) (i : Machine.instr) :
  List.nth_error Pcode o = Some i ->
  flat_pos pr c p Pcode o.+1 = flat_pos pr c p Pcode o + isize i.
Proof.
move=> Ho; rewrite /flat_pos (proc_off_S Ho); by rewrite !addnA.
Qed.

Lemma side_flat_pos_S (c : Component.id) (p : Procedure.id)
    (Pcode : Machine.code) (o : nat) (i : Machine.instr) :
  List.nth_error Pcode o = Some i ->
  side_flat_pos c p Pcode o.+1 = side_flat_pos c p Pcode o + isize i.
Proof.
move=> Ho; rewrite /side_flat_pos; case: ifP => _.
- by rewrite (flat_pos_S pra c p Ho).
- by rewrite (flat_pos_S prb c p Ho) addnA.
Qed.

(* ==================== the master fetch bridge ==================== *)

(* [pc_rel] + the I-side [executing] fact pin down the SOURCE-level
   procedure and offset: the genv block decomposes through
   [genv_procs_spec], the codes agree, and the running instruction sits at
   the source offset — everything the encoded-fetch lemmas consume *)
Lemma lm_fetch (gps : list Pointer.t) (ipc : Pointer.t)
    (mpc : atom (mword mt) (tag_type lrc_tags Symbolic.P))
    (i : Machine.instr) :
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  pc_rel gps ipc mpc ->
  Intermediate.GlobalEnv.executing G ipc i ->
  exists (Cprocs : NMap Machine.code) (P0 : Procedure.id)
         (Pcode : Machine.code) (j : nat),
    [/\ Intermediate.prog_procedures (side_of (Pointer.component ipc))
          (Pointer.component ipc) = Some Cprocs,
        getm Cprocs P0 = Some Pcode,
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)) = Some i,
        vala mpc
        = @word_of_nat (word_size mt)
            (side_flat_pos (Pointer.component ipc) P0 Pcode
               (Z.to_nat (Pointer.offset ipc)) + pc0)
      & taga mpc
        = LRC.Level (cross_frames (Pointer.component ipc) gps)
            (Pointer.component ipc)]
    /\ [/\ Intermediate.prog_procedures ilp (Pointer.component ipc)
             = Some Cprocs,
           Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j
         & List.nth_error (elementsm Cprocs) j = Some (P0, Pcode)].
Proof.
move=> Hin Hpc Hex.
case: Hpc => Cprocs_src [j [P0 [Pcode [Hilp Hblk Hnth Hoffpos [Hval Htag]]]]].
case: Hex => C_procs [P_code [HgC [HgB [_ Hfetch]]]].
have [CprocsB [HgB' Hfwd Hbwd]] := genv_procs_spec Hin Hilp.
rewrite /G in HgC.
have EC : C_procs = CprocsB by congruence.
subst C_procs.
have [j' [P' [Hb' Hnth']]] := Hbwd _ _ HgB.
have Ej : j = j'.
{ move: Hb'; rewrite Hblk => /addnI. by []. }
subst j'.
rewrite Hnth in Hnth'.
case: Hnth' => EP EPc; subst P' P_code.
have Hget : getm Cprocs_src P0 = Some Pcode.
{ apply: BufferLayout.In_fmap_getm. exact (List.nth_error_In _ _ Hnth). }
have Hun : Intermediate.prog_procedures ilp
           = unionm (Intermediate.prog_procedures pra)
                    (Intermediate.prog_procedures prb) by [].
have Hside : Intermediate.prog_procedures
               (side_of (Pointer.component ipc)) (Pointer.component ipc)
             = Some Cprocs_src.
{ rewrite /side_of.
  move: Hilp; rewrite Hun unionmE.
  case Hd: (Pointer.component ipc
            \in domm (Intermediate.prog_procedures pra)).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _). }
exists Cprocs_src, P0, Pcode, j.
by split; split.
Qed.

(* ==================== step-construction kernels ==================== *)

(* the me machine takes a silent Nop step whenever the pc cell decodes to
   Nop, is code-tagged with the running colour, and the next cell belongs
   to the same colour — the computational core shared by all silent cases *)
Lemma stepf_nop_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (vtp : LRC.value_tag)
    (entp : option (Procedure.id * seq Component.id))
    (nv : mword mt) (rc : @ratom mt) :
  decode_instr iw = Some (Types.Nop mt) ->
  getm mem pcv = Some (iw@(LRC.MTag vtp c entp true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom.
eapply Symbolic.step_nop.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  by [].
Qed.

(* the silent Const step: same kernel plus one register write *)
Lemma stepf_const_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (n : imm mt) (r : reg mt)
    (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Const n r) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r = Some (oldv@oldt) ->
  updm mregs r ((swcast n)@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hold Hupd.
eapply Symbolic.step_const.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hold.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hupd /=.
  by [].
Qed.

(* the silent Mov step: two register reads, one write; the moved value
   keeps its tag (Other sources stay Other) *)
Lemma stepf_mov_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 : mword mt) (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Mov r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mregs r2 = Some (oldv@oldt) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  updm mregs1 r2 (w1@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hupd1 Hupd2.
eapply Symbolic.step_mov.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hupd2 /=.
  by [].
Qed.

(* the Invalidated twin: LRC's MOV rule propagates the tag (the
   [is_not_invalid] guard is disabled), and [is_address Invalidated]
   makes the source rewrite ts' = Invalidated = ts, so the state shape
   is identical *)
Lemma stepf_mov_compute_inv (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 : mword mt) (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Mov r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Invalidated) ->
  getm mregs r2 = Some (oldv@oldt) ->
  updm mregs r1 (w1@LRC.Invalidated) = Some mregs1 ->
  updm mregs1 r2 (w1@LRC.Invalidated) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hupd1 Hupd2.
eapply Symbolic.step_mov.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hupd2 /=.
  by [].
Qed.

(* the silent Binop step: two Other-tagged reads, one write *)
Lemma stepf_binop_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (op : binop) (r1 r2 r3 : reg mt)
    (w1 w2 : mword mt) (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs2 mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Binop op r1 r2 r3) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mregs r2 = Some (w2@LRC.Other) ->
  getm mregs r3 = Some (oldv@oldt) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  getm mregs1 r2 = Some (w2@LRC.Other) ->
  updm mregs1 r2 (w2@LRC.Other) = Some mregs2 ->
  updm mregs2 r3 ((binop_denote op w1 w2)@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hr3 Hupd1 Hr2' Hupd2 Hupd3.
eapply Symbolic.step_binop.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- exact: Hr3.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hr2' /= Hupd2 /= Hupd3 /=.
  by [].
Qed.

(* the silent Load step: own-colour data cell, Other-tagged pointer;
   the loaded value's tag moves to the register, the cell keeps Other *)
Lemma stepf_load_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 w2 : mword mt)
    (ent' : option (Procedure.id * seq Component.id))
    (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt})
    (mem1 : {fmap mword mt -> matom}) :
  decode_instr iw = Some (Types.Load r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mem w1 = Some (w2@(LRC.MTag LRC.Other c ent' false)) ->
  getm mregs r2 = Some (oldv@oldt) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  updm mem w1 (w2@(LRC.MTag LRC.Other c ent' false)) = Some mem1 ->
  updm mregs1 r2 (w2@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem1 mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hm1 Hr2 Hupd1 Hupdm Hupd2.
eapply Symbolic.step_load.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hm1.
- exact: Hr2.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hm1 /= Hupdm /= Hupd2 /=.
  by [].
Qed.

(* the silent Store step: own-colour data target, Other-tagged pointer and
   source; the source tag moves into the cell *)
Lemma stepf_store_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 w2 : mword mt)
    (ent' : option (Procedure.id * seq Component.id))
    (oldv : mword mt) (oldvt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  decode_instr iw = Some (Types.Store r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mregs r2 = Some (w2@LRC.Other) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  getm mregs1 r2 = Some (w2@LRC.Other) ->
  updm mregs1 r2 (w2@LRC.Other) = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag LRC.Other c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
eapply Symbolic.step_store.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- exact: Hm1.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hr2' /= Hupd2 /= Hupdm /=.
  by [].
Qed.

(* the Invalidated-source Store twin: the stored register carries an
   Invalidated tag (a cross-invalidated Undef on the I side); LRC's
   STORE accepts it, [is_address Invalidated] keeps the register tag,
   and [switch_val] moves Invalidated into the cell *)
Lemma stepf_store_compute_inv (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 w2 : mword mt)
    (ent' : option (Procedure.id * seq Component.id))
    (oldv : mword mt) (oldvt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  decode_instr iw = Some (Types.Store r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mregs r2 = Some (w2@LRC.Invalidated) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  getm mregs1 r2 = Some (w2@LRC.Invalidated) ->
  updm mregs1 r2 (w2@LRC.Invalidated) = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag LRC.Invalidated c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
eapply Symbolic.step_store.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- exact: Hm1.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hr2' /= Hupd2 /= Hupdm /=.
  by [].
Qed.

(* tag-generic Load: the cell's value tag is arbitrary and moves into the
   destination register; the cell is retagged by [switch_val] (invalidated
   when the moved tag is an address capability).  This is the variant the
   compiled pop-R_RA sites need. *)
Lemma stepf_load_any_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 w2 : mword mt)
    (cvt : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (oldv : mword mt) (oldt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt})
    (mem1 : {fmap mword mt -> matom}) :
  decode_instr iw = Some (Types.Load r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mem w1 = Some (w2@(LRC.MTag cvt c ent' false)) ->
  getm mregs r2 = Some (oldv@oldt) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  updm mem w1
    (w2@(LRC.MTag (if LRC.is_address cvt then LRC.Invalidated
                   else LRC.Other) c ent' false)) = Some mem1 ->
  updm mregs1 r2 (w2@cvt) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem1 mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hm1 Hr2 Hupd1 Hupdm Hupd2.
eapply Symbolic.step_load.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hm1.
- exact: Hr2.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hm1 /= Hupdm /= Hupd2 /=.
  by [].
Qed.

(* tag-generic Store: the source register's value tag is arbitrary and
   moves into the cell; the register is retagged by [switch_val]
   (invalidated when the moved tag is an address capability).  This is
   the variant the compiled push-R_RA sites need. *)
Lemma stepf_store_any_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 w2 : mword mt)
    (ts : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (oldv : mword mt) (oldvt : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  decode_instr iw = Some (Types.Store r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@LRC.Other) ->
  getm mregs r2 = Some (w2@ts) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs r1 (w1@LRC.Other) = Some mregs1 ->
  getm mregs1 r2 = Some (w2@ts) ->
  updm mregs1 r2
    (w2@(if LRC.is_address ts then LRC.Invalidated else LRC.Other))
    = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag ts c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
eapply Symbolic.step_store.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- exact: Hm1.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hr2' /= Hupd2 /= Hupdm /=.
  by [].
Qed.

(* the silent Bnz step, fall-through variant (tested register is zero) *)
Lemma stepf_bnz_z_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r : reg mt) (n : imm mt) (w : mword mt)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Bnz r n) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r = Some (w@LRC.Other) ->
  (w == 0%w) = true ->
  updm mregs r (w@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr Hw Hupd.
eapply Symbolic.step_bnz.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr.
- rewrite Hw.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr /= Hupd /=.
  by [].
Qed.

(* the silent Bnz step, taken-branch variant (tested register nonzero);
   target = pcv + swcast n, whose cell must be own-coloured *)
Lemma stepf_bnz_nz_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r : reg mt) (n : imm mt) (w : mword mt)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Bnz r n) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv (swcast n))
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r = Some (w@LRC.Other) ->
  (w == 0%w) = false ->
  updm mregs r (w@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv (swcast n))@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr Hw Hupd.
eapply Symbolic.step_bnz.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr.
- rewrite Hw.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr /= Hupd /=.
  by [].
Qed.

(* writing back the exact atom already stored leaves the map unchanged;
   turns the 13 register write-backs of Jump/Jal into no-ops *)
Lemma updm_id (T : ordType) (S : Type) (m : {fmap T -> S}) (k : T) (v : S) :
  getm m k = Some v -> updm m k v = Some m.
Proof.
move=> Hget; rewrite /updm Hget; congr Some.
by apply/eq_fmap=> k'; rewrite setmE; case: eqP => [->|//]; rewrite Hget.
Qed.

(* the silent intra-component Jump step: jump register tagged InternalJump,
   target cell own-coloured; every write-back is an identity *)
Lemma stepf_jump_intra_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r : reg mt) (w : mword mt)
    (rav : mword mt) (rat : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag) :
  decode_instr iw = Some (Types.Jump r) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem w = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r = Some (w@LRC.InternalJump) ->
  getm mregs ra = Some (rav@rat) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs (w@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Htgt Hrcom Hr Hra
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19.
eapply Symbolic.step_jump.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr.
- exact: Hra.
- rewrite /Symbolic.reg_clear_list /Symbolic.reg_list /=.
  rewrite Hc1 /= Hc0 /= Hc2 /= Hc3 /= Hc5 /= Hc6 /= Hc7 /=.
  rewrite Hc16 /= Hc17 /= Hc18 /= Hc19 /=.
  reflexivity.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Htgt /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite /LRC.check_belong /LRC.belong /= !eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hra /= (updm_id Hra) /=.
  rewrite Hr /= (updm_id Hr) /=.
  rewrite Hc1 /= (updm_id Hc1) /=.
  rewrite Hc0 /= (updm_id Hc0) /=.
  rewrite Hc2 /= (updm_id Hc2) /=.
  rewrite Hc3 /= (updm_id Hc3) /=.
  rewrite Hc5 /= (updm_id Hc5) /=.
  rewrite Hc6 /= (updm_id Hc6) /=.
  rewrite Hc7 /= (updm_id Hc7) /=.
  rewrite Hc16 /= (updm_id Hc16) /=.
  rewrite Hc17 /= (updm_id Hc17) /=.
  rewrite Hc18 /= (updm_id Hc18) /=.
  rewrite Hc19 /= (updm_id Hc19) /=.
  by [].
Qed.

(* the silent intra-component Jal step: return-address cell (pc+1) and target
   cell own-coloured; ra := pc+1 tagged InternalJump, clear write-backs are
   identities on the post-write register map *)
Lemma stepf_jal_intra_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (jimm : imm mt)
    (vret : mword mt) (vtret : LRC.value_tag)
    (entret : option (Procedure.id * seq Component.id)) (iscret : bool)
    (old : mword mt) (told : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (mregs1 : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Jal jimm) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (vret@(LRC.MTag vtret c entret iscret)) ->
  getm mem (swcast jimm) = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra ((addw pcv onew)@LRC.InternalJump) = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs1 (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs1 (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs1 (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs1 (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs1 (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs1 (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs1 (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs1 (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs1 (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs1
       ((swcast jimm)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC HRAcell Htgt Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd
  Hd1 Hd0 Hd2 Hd3 Hd5 Hd6 Hd7 Hd16 Hd17 Hd18 Hd19.
eapply Symbolic.step_jal.
- reflexivity.
- exact: HPC.
- exact: HRAcell.
- exact: Hdec.
- exact: Hold.
- rewrite /Symbolic.reg_clear_list /Symbolic.reg_list /=.
  rewrite Hc1 /= Hc0 /= Hc2 /= Hc3 /= Hc5 /= Hc6 /= Hc7 /=.
  rewrite Hc16 /= Hc17 /= Hc18 /= Hc19 /=.
  reflexivity.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Htgt /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite /LRC.check_belong /LRC.belong /= !eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite HRAcell /= (updm_id HRAcell) /=.
  rewrite Hupd /=.
  rewrite Hd1 /= (updm_id Hd1) /=.
  rewrite Hd0 /= (updm_id Hd0) /=.
  rewrite Hd2 /= (updm_id Hd2) /=.
  rewrite Hd3 /= (updm_id Hd3) /=.
  rewrite Hd5 /= (updm_id Hd5) /=.
  rewrite Hd6 /= (updm_id Hd6) /=.
  rewrite Hd7 /= (updm_id Hd7) /=.
  rewrite Hd16 /= (updm_id Hd16) /=.
  rewrite Hd17 /= (updm_id Hd17) /=.
  rewrite Hd18 /= (updm_id Hd18) /=.
  rewrite Hd19 /= (updm_id Hd19) /=.
  by [].
Qed.

(* the evented cross-component Jal step (ECall): target cell is a foreign
   entry point listing the caller; ra := pc+1 tagged Ret lvl, rcom stays
   Other, all other registers are invalidated *)
Lemma stepf_jal_cross_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c c' : Component.id)
    (iw : mword mt) (jimm : imm mt)
    (vret : mword mt) (vtret : LRC.value_tag)
    (entret : option (Procedure.id * seq Component.id)) (iscret : bool)
    (old : mword mt) (told : LRC.value_tag)
    (vt : LRC.value_tag) (p : Procedure.id) (cl : seq Component.id)
    (isc : bool)
    (nv : mword mt) (rcv : mword mt) (rct : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (w0 w2 w3 w5 w6 w7 w16 w17 w18 w19 : mword mt)
    (u0 u2 u3 u5 u6 u7 u16 u17 u18 u19 : LRC.value_tag)
    (mregs1 mregs2 mregs3 mregs4 mregs5 mregs6 mregs7 mregs8 mregs9
       mregs10 mregs11 : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Jal jimm) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (vret@(LRC.MTag vtret c entret iscret)) ->
  getm mem (swcast jimm)
    = Some (nv@(LRC.MTag vt c' (Some (p, cl)) isc)) ->
  (c == c') = false ->
  mem_seq cl c = true ->
  getm mregs rcom = Some (rcv@rct) ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra ((addw pcv onew)@(LRC.Ret lvl)) = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (w0@u0) ->
  updm mregs1 (word.as_word (ssrint.Posz 0)) (w0@LRC.Invalidated)
    = Some mregs2 ->
  getm mregs2 (word.as_word (ssrint.Posz 2)) = Some (w2@u2) ->
  updm mregs2 (word.as_word (ssrint.Posz 2)) (w2@LRC.Invalidated)
    = Some mregs3 ->
  getm mregs3 (word.as_word (ssrint.Posz 3)) = Some (w3@u3) ->
  updm mregs3 (word.as_word (ssrint.Posz 3)) (w3@LRC.Invalidated)
    = Some mregs4 ->
  getm mregs4 (word.as_word (ssrint.Posz 5)) = Some (w5@u5) ->
  updm mregs4 (word.as_word (ssrint.Posz 5)) (w5@LRC.Invalidated)
    = Some mregs5 ->
  getm mregs5 (word.as_word (ssrint.Posz 6)) = Some (w6@u6) ->
  updm mregs5 (word.as_word (ssrint.Posz 6)) (w6@LRC.Invalidated)
    = Some mregs6 ->
  getm mregs6 (word.as_word (ssrint.Posz 7)) = Some (w7@u7) ->
  updm mregs6 (word.as_word (ssrint.Posz 7)) (w7@LRC.Invalidated)
    = Some mregs7 ->
  getm mregs7 (word.as_word (ssrint.Posz 16)) = Some (w16@u16) ->
  updm mregs7 (word.as_word (ssrint.Posz 16)) (w16@LRC.Invalidated)
    = Some mregs8 ->
  getm mregs8 (word.as_word (ssrint.Posz 17)) = Some (w17@u17) ->
  updm mregs8 (word.as_word (ssrint.Posz 17)) (w17@LRC.Invalidated)
    = Some mregs9 ->
  getm mregs9 (word.as_word (ssrint.Posz 18)) = Some (w18@u18) ->
  updm mregs9 (word.as_word (ssrint.Posz 18)) (w18@LRC.Invalidated)
    = Some mregs10 ->
  getm mregs10 (word.as_word (ssrint.Posz 19)) = Some (w19@u19) ->
  updm mregs10 (word.as_word (ssrint.Posz 19)) (w19@LRC.Invalidated)
    = Some mregs11 ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs11
       ((swcast jimm)@(LRC.Level lvl.+1 c')) tt)
    (Some (Events.ECall c p (Symbolic.convert (word.int_of_word rcv)) c')).
Proof.
move=> Hdec HPC HRAcell Htgt Hneq Hentry Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd Hd1
  Hd0 Hu0 Hd2 Hu2 Hd3 Hu3 Hd5 Hu5 Hd6 Hu6 Hd7 Hu7
  Hd16 Hu16 Hd17 Hu17 Hd18 Hu18 Hd19 Hu19.
eapply Symbolic.step_jal.
- reflexivity.
- exact: HPC.
- exact: HRAcell.
- exact: Hdec.
- exact: Hold.
- rewrite /Symbolic.reg_clear_list /Symbolic.reg_list /=.
  rewrite Hc1 /= Hc0 /= Hc2 /= Hc3 /= Hc5 /= Hc6 /= Hc7 /=.
  rewrite Hc16 /= Hc17 /= Hc18 /= Hc19 /=.
  reflexivity.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Htgt /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite /LRC.check_belong /LRC.belong /= !eqxx /=.
  rewrite Hneq /=.
  rewrite Hentry /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite HRAcell /= (updm_id HRAcell) /=.
  rewrite Hupd /=.
  rewrite Hd1 /= (updm_id Hd1) /=.
  rewrite Hd0 /= Hu0 /=.
  rewrite Hd2 /= Hu2 /=.
  rewrite Hd3 /= Hu3 /=.
  rewrite Hd5 /= Hu5 /=.
  rewrite Hd6 /= Hu6 /=.
  rewrite Hd7 /= Hu7 /=.
  rewrite Hd16 /= Hu16 /=.
  rewrite Hd17 /= Hu17 /=.
  rewrite Hd18 /= Hu18 /=.
  rewrite Hd19 /= Hu19 /=.
  by [].
Qed.

(* the evented cross-component Jump step (ERet): jump register tagged
   Ret lvl at level lvl.+1, target cell foreign; ra and the jump register
   are invalidated, rcom stays Other, all other registers invalidated *)
Lemma stepf_jump_cross_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c c' : Component.id)
    (iw : mword mt) (r : reg mt) (w : mword mt)
    (rav : mword mt) (rat : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rcv : mword mt) (rct : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (wr2 : mword mt) (ur2 : LRC.value_tag)
    (x1 : mword mt)
    (w0 w2 w3 w5 w6 w7 w16 w17 w18 w19 : mword mt)
    (u0 u2 u3 u5 u6 u7 u16 u17 u18 u19 : LRC.value_tag)
    (mregsA mregsB mregs2 mregs3 mregs4 mregs5 mregs6 mregs7 mregs8
       mregs9 mregs10 mregs11 : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Jump r) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem w = Some (nv@(LRC.MTag vt c' ent isc)) ->
  (c == c') = false ->
  getm mregs rcom = Some (rcv@rct) ->
  getm mregs r = Some (w@(LRC.Ret lvl)) ->
  getm mregs ra = Some (rav@rat) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra (rav@LRC.Invalidated) = Some mregsA ->
  getm mregsA r = Some (wr2@ur2) ->
  updm mregsA r (wr2@LRC.Invalidated) = Some mregsB ->
  getm mregsB (word.as_word (ssrint.Posz 1)) = Some (x1@LRC.Other) ->
  getm mregsB (word.as_word (ssrint.Posz 0)) = Some (w0@u0) ->
  updm mregsB (word.as_word (ssrint.Posz 0)) (w0@LRC.Invalidated)
    = Some mregs2 ->
  getm mregs2 (word.as_word (ssrint.Posz 2)) = Some (w2@u2) ->
  updm mregs2 (word.as_word (ssrint.Posz 2)) (w2@LRC.Invalidated)
    = Some mregs3 ->
  getm mregs3 (word.as_word (ssrint.Posz 3)) = Some (w3@u3) ->
  updm mregs3 (word.as_word (ssrint.Posz 3)) (w3@LRC.Invalidated)
    = Some mregs4 ->
  getm mregs4 (word.as_word (ssrint.Posz 5)) = Some (w5@u5) ->
  updm mregs4 (word.as_word (ssrint.Posz 5)) (w5@LRC.Invalidated)
    = Some mregs5 ->
  getm mregs5 (word.as_word (ssrint.Posz 6)) = Some (w6@u6) ->
  updm mregs5 (word.as_word (ssrint.Posz 6)) (w6@LRC.Invalidated)
    = Some mregs6 ->
  getm mregs6 (word.as_word (ssrint.Posz 7)) = Some (w7@u7) ->
  updm mregs6 (word.as_word (ssrint.Posz 7)) (w7@LRC.Invalidated)
    = Some mregs7 ->
  getm mregs7 (word.as_word (ssrint.Posz 16)) = Some (w16@u16) ->
  updm mregs7 (word.as_word (ssrint.Posz 16)) (w16@LRC.Invalidated)
    = Some mregs8 ->
  getm mregs8 (word.as_word (ssrint.Posz 17)) = Some (w17@u17) ->
  updm mregs8 (word.as_word (ssrint.Posz 17)) (w17@LRC.Invalidated)
    = Some mregs9 ->
  getm mregs9 (word.as_word (ssrint.Posz 18)) = Some (w18@u18) ->
  updm mregs9 (word.as_word (ssrint.Posz 18)) (w18@LRC.Invalidated)
    = Some mregs10 ->
  getm mregs10 (word.as_word (ssrint.Posz 19)) = Some (w19@u19) ->
  updm mregs10 (word.as_word (ssrint.Posz 19)) (w19@LRC.Invalidated)
    = Some mregs11 ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl.+1 c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs11 (w@(LRC.Level lvl c')) tt)
    (Some (Events.ERet c (Symbolic.convert (word.int_of_word rcv)) c')).
Proof.
move=> Hdec HPC Htgt Hneq Hrcom Hr Hra
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19
  HuA HdB HuB Hd1
  Hd0 Hu0 Hd2 Hu2 Hd3 Hu3 Hd5 Hu5 Hd6 Hu6 Hd7 Hu7
  Hd16 Hu16 Hd17 Hu17 Hd18 Hu18 Hd19 Hu19.
eapply Symbolic.step_jump.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr.
- exact: Hra.
- rewrite /Symbolic.reg_clear_list /Symbolic.reg_list /=.
  rewrite Hc1 /= Hc0 /= Hc2 /= Hc3 /= Hc5 /= Hc6 /= Hc7 /=.
  rewrite Hc16 /= Hc17 /= Hc18 /= Hc19 /=.
  reflexivity.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Htgt /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite /LRC.check_belong /LRC.belong /= Hneq /= !eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hra /= HuA /=.
  rewrite HdB /= HuB /=.
  rewrite Hd1 /= (updm_id Hd1) /=.
  rewrite Hd0 /= Hu0 /=.
  rewrite Hd2 /= Hu2 /=.
  rewrite Hd3 /= Hu3 /=.
  rewrite Hd5 /= Hu5 /=.
  rewrite Hd6 /= Hu6 /=.
  rewrite Hd7 /= Hu7 /=.
  rewrite Hd16 /= Hu16 /=.
  rewrite Hd17 /= Hu17 /=.
  rewrite Hd18 /= Hu18 /=.
  rewrite Hd19 /= Hu19 /=.
  by [].
Qed.

(* the silent SERVICE step through the alloc syscall: pc is the (unmapped)
   alloc address, the monitor runs alloc_fun; the post-state shape is
   characterized separately by alloc_fun_shape *)
Lemma stepf_syscall_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (lvl : nat) (c : Component.id)
    (rc : @ratom mt)
    (st2 : @Symbolic.state mt LRC.lrc_tags unit) :
  getm mem (word_of_nat Merged.alloc_label) = None ->
  getm mregs rcom = Some rc ->
  LRC.alloc_fun (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat Merged.alloc_label)@(LRC.Level lvl c)) tt)
    = Some st2 ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat Merged.alloc_label)@(LRC.Level lvl c)) tt)
    st2 None.
Proof.
move=> HPC Hrcom Halloc.
eapply Symbolic.step_syscall.
- reflexivity.
- exact: HPC.
- by rewrite /Merged.table mkfmapE /= eqxx.
- rewrite /Symbolic.run_syscall /Symbolic.evi Hrcom /=.
  rewrite Halloc /=.
  by [].
Qed.

(* ==================== side-uniform encoded fetch ==================== *)

(* the linked fetch, dispatching on the side owning component [c] *)
Lemma side_encoded_fetch (c : Component.id) (Cprocs : NMap Machine.code)
    (p : Procedure.id) (Pcode : Machine.code) (o : nat) (i : Machine.instr)
    (k : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c i)) k = Some cell ->
  exists v : matom,
    [/\ encode_code codeW pc0
          (word_of_nat ((side_flat_pos c p Pcode o + k) + pc0)) = Some v,
        taga v = cell.2
      & Types.decode_instr (vala v)
        = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                  (pc0 + (side_flat_pos c p Pcode o + k)))].
Proof.
rewrite /side_of /side_flat_pos.
case Hd: (c \in domm (Intermediate.prog_procedures pra)) => /=;
  move=> Hb HC HP Ho Hk Hcell.
- have [v [Hv [Ht Hdec]]] := link_encoded_fetch_l Hb HC HP Ho Hk Hcell.
  by exists v; split.
- have [v [Hv [Ht Hdec]]] := link_encoded_fetch_r Hb HC HP Ho Hk Hcell.
  have Ea : size (lin_code L P C pra) + (flat_pos prb c p Pcode o + k)
            = (size (lin_code L P C pra) + flat_pos prb c p Pcode o) + k
    by rewrite addnA.
  rewrite Ea in Hv Hdec.
  by exists v; split.
Qed.

(* every instruction's first cell carries the plain code tag *)
Lemma cell_exp0 (msz0 : NMap (NMap nat)) (c : Component.id)
    (i : Machine.instr) :
  exists mi : @Merged.instr mt,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) msz0
         (instr_to_transitional c i)) 0
    = Some (mi, def_mem_tag c true).
Proof.
case: i => *; try by eexists.
by rewrite /instr_to_transitional; case: (Nat.eqb _ _); eexists.
Qed.

(* ==================== diagram wrappers ==================== *)

(* INop: one silent me-step, pc advances one cell *)
Lemma sim_nop (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some INop ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c INop)) 0
    = Some (MrNop, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 INop) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_nop_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
Qed.

(* ILabel: encodes to MrLabel, decodes to Nop — same silent step *)
Lemma sim_label (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (l : nat) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ILabel l))) 0
    = Some (MrLabel (can_upd L c l), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (ILabel l)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_nop_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
Qed.

(* IConst: one silent me-step writing the converted immediate *)
Lemma sim_const (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (v0 : imvalue) (r : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (oldv : mword mt) (oldt : LRC.value_tag)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IConst v0 r) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r))
    ((swcast (convert_value (mt := mt)
        (memory_lengths (Intermediate.prog_buffers (side_of c))) v0))
       @LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hold Hupd.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IConst v0 r))) 0
    = Some (MrConst
              (convert_value (mt := mt)
                 (memory_lengths (Intermediate.prog_buffers (side_of c))) v0)
              r,
            def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IConst v0 r)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_const_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hold.
- exact Hupd.
Qed.

(* IMov: one silent me-step copying r1 into r2 *)
Lemma sim_mov (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IMov r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl r1)))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl r2)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inl r1))) (w1@LRC.Other)
    = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inl r2))) (w1@LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IMov r1 r2))) 0
    = Some (MrMov (inl r1) (inl r2), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IMov r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_mov_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* the Invalidated twin of [sim_mov] — the entry wrapper's
   [IMov R_SP R_AUX1] on a freshly invalidated register file *)
Lemma sim_mov_inv (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IMov r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl r1)))
    = Some (w1@LRC.Invalidated) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl r2)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inl r1)))
    (w1@LRC.Invalidated) = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inl r2)))
    (w1@LRC.Invalidated) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IMov r1 r2))) 0
    = Some (MrMov (inl r1) (inl r2), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IMov r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_mov_compute_inv.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* IBinOp: one silent me-step computing the operation *)
Lemma sim_binop (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (op : Values.binop) (r1 r2 r3 : Machine.register)
    (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldt : LRC.value_tag)
    (mregs1 mregs2 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IBinOp op r1 r2 r3) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r3))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  getm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2)) (w2@LRC.Other)
    = Some mregs2 ->
  updm mregs2 (word_of_nat (Intermediate.Register.to_nat r3))
    ((binop_denote (Merged.binop_trans op) w1 w2)@LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hr3 Hupd1 Hr2' Hupd2 Hupd3.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IBinOp op r1 r2 r3))) 0
    = Some (MrBinop op r1 r2 r3, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IBinOp op r1 r2 r3)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_binop_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hr3.
- exact Hupd1.
- exact Hr2'.
- exact Hupd2.
- exact Hupd3.
Qed.

(* ILoad: one silent me-step through an own-colour data cell *)
Lemma sim_load (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldt : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (mregs1 mregs' : {fmap reg mt -> @ratom mt})
    (mem1 : {fmap mword mt -> matom}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (ILoad r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mem w1 = Some (w2@(LRC.MTag LRC.Other c ent' false)) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  updm mem w1 (w2@(LRC.MTag LRC.Other c ent' false)) = Some mem1 ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2)) (w2@LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem1 mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hm1 Hr2 Hupd1 Hupdm Hupd2.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ILoad r1 r2))) 0
    = Some (MrLoad r1 r2, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (ILoad r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_load_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hm1.
- exact Hr2.
- exact Hupd1.
- exact Hupdm.
- exact Hupd2.
Qed.

(* IStore: one silent me-step writing an own-colour data cell *)
Lemma sim_store (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldvt : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IStore r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  getm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2)) (w2@LRC.Other)
    = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag LRC.Other c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IStore r1 r2))) 0
    = Some (MrStore r1 r2, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IStore r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_store_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hm1.
- exact Hupd1.
- exact Hr2'.
- exact Hupd2.
- exact Hupdm.
Qed.

(* the Invalidated-source Store twin of [sim_store] *)
Lemma sim_store_inv (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldvt : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IStore r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Invalidated) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  getm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Invalidated) ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    (w2@LRC.Invalidated) = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag LRC.Invalidated c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IStore r1 r2))) 0
    = Some (MrStore r1 r2, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IStore r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_store_compute_inv.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hm1.
- exact Hupd1.
- exact Hr2'.
- exact Hupd2.
- exact Hupdm.
Qed.

(* ILoad, tag-generic: the loaded cell's value tag moves into the
   destination register; the cell is invalidated when the tag is an
   address capability (compiled pop-R_RA) *)
Lemma sim_load_any (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldt : LRC.value_tag)
    (cvt : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (mregs1 mregs' : {fmap reg mt -> @ratom mt})
    (mem1 : {fmap mword mt -> matom}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (ILoad r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mem w1 = Some (w2@(LRC.MTag cvt c ent' false)) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  updm mem w1
    (w2@(LRC.MTag (if LRC.is_address cvt then LRC.Invalidated
                   else LRC.Other) c ent' false)) = Some mem1 ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2)) (w2@cvt)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem1 mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hm1 Hr2 Hupd1 Hupdm Hupd2.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ILoad r1 r2))) 0
    = Some (MrLoad r1 r2, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (ILoad r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_load_any_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hm1.
- exact Hr2.
- exact Hupd1.
- exact Hupdm.
- exact Hupd2.
Qed.

(* IStore, tag-generic: the source register's value tag moves into the
   cell; the register is invalidated when the tag is an address
   capability (compiled push-R_RA) *)
Lemma sim_store_any (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r1 r2 : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 w2 oldv : mword mt) (oldvt : LRC.value_tag)
    (ts : LRC.value_tag)
    (ent' : option (Procedure.id * seq Component.id))
    (mregs1 mregs2 : {fmap reg mt -> @ratom mt})
    (mem' : {fmap mword mt -> matom}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IStore r1 r2) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@ts) ->
  getm mem w1 = Some (oldv@(LRC.MTag oldvt c ent' false)) ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r1)) (w1@LRC.Other)
    = Some mregs1 ->
  getm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    = Some (w2@ts) ->
  updm mregs1 (word_of_nat (Intermediate.Register.to_nat r2))
    (w2@(if LRC.is_address ts then LRC.Invalidated else LRC.Other))
    = Some mregs2 ->
  updm mem w1 (w2@(LRC.MTag ts c ent' false)) = Some mem' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem' mregs2
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hm1 Hupd1 Hr2' Hupd2 Hupdm.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IStore r1 r2))) 0
    = Some (MrStore r1 r2, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IStore r1 r2)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_store_any_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hm1.
- exact Hupd1.
- exact Hr2'.
- exact Hupd2.
- exact Hupdm.
Qed.

(* IBnz, untaken branch (register is zero): silent fall-through *)
Lemma sim_bnz_z (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r : Machine.register) (l : nat) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w : mword mt)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IBnz r l) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r))
    = Some (w@LRC.Other) ->
  (w == 0%w) = true ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r)) (w@LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr Hw Hupd.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IBnz r l))) 0
    = Some (MrBnz r (can_upd L c l), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IBnz r l)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_bnz_z_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr.
- exact Hw.
- exact Hupd.
Qed.

(* ==================== word-cast bridges ==================== *)

Lemma valw_won (k n : nat) :
  eqtype.val (@word_of_nat k n) = n %% 2 ^ k :> nat.
Proof. by rewrite /word_of_nat WordExtra.valw_as_word. Qed.

Lemma word_of_natDall (k a b : nat) :
  (@word_of_nat k a + @word_of_nat k b)%w = @word_of_nat k (a + b).
Proof.
apply: WordExtra.word_nat_inj. rewrite /addw.
move: (valw_won k a) (valw_won k b) => Ea Eb. rewrite Ea Eb.
rewrite (valw_won k (a + b)) WordExtra.valw_as_word. by rewrite modnDm.
Qed.

(* the unsigned imm→word cast is the identity on in-range positions *)
Lemma swcast_won_id (x : nat) :
  x < 2 ^ imm_size mt ->
  @swcast _ (word_size mt) (@word_of_nat (imm_size mt) x)
  = @word_of_nat (word_size mt) x.
Proof.
move=> Hx. by rewrite /swcast /word_of_nat (as_wordK Hx).
Qed.

Lemma addw_won_swcast (a b : nat) :
  b < 2 ^ imm_size mt ->
  (@word_of_nat (word_size mt) a
   + @swcast _ (word_size mt) (@word_of_nat (imm_size mt) b))%w
  = @word_of_nat (word_size mt) (a + b).
Proof.
move=> Hb. by rewrite (swcast_won_id Hb) word_of_natDall.
Qed.

(* IJump: the intra-component stack return — jumps through R_RA, whose tag
   must be InternalJump; the target cell is own-coloured *)
Lemma sim_jump_intra (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (w : mword mt)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some IJump ->
  code_region_ok mem ->
  getm mem w = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat R_RA))
    = Some (w@LRC.InternalJump) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs (w@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Hcode Htgt Hrcom Hr
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c IJump)) 0
    = Some (MrJump R_RA, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 IJump) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
eapply stepf_jump_intra_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- exact Htgt.
- exact Hrcom.
- exact Hr.
- exact Hr.
- exact Hc1.
- exact Hc0.
- exact Hc2.
- exact Hc3.
- exact Hc5.
- exact Hc6.
- exact Hc7.
- exact Hc16.
- exact Hc17.
- exact Hc18.
- exact Hc19.
Qed.

(* IReturn: the cross-component return — jumps through R_RA (tagged
   Ret lvl at level lvl.+1) into a foreign component, emitting ERet;
   everything but rcom is invalidated *)
Lemma sim_return (NC : nat) (c c' : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (w : mword mt)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rcv : mword mt) (rct : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt)
    (rav : mword mt) (rat : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (wr2 : mword mt) (ur2 : LRC.value_tag)
    (x1 : mword mt)
    (w0 w2 w3 w5 w6 w7 w16 w17 w18 w19 : mword mt)
    (u0 u2 u3 u5 u6 u7 u16 u17 u18 u19 : LRC.value_tag)
    (mregsA mregsB mregs2 mregs3 mregs4 mregs5 mregs6 mregs7 mregs8
       mregs9 mregs10 mregs11 : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some IReturn ->
  code_region_ok mem ->
  getm mem w = Some (nv@(LRC.MTag vt c' ent isc)) ->
  (c == c') = false ->
  getm mregs rcom = Some (rcv@rct) ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat R_RA))
    = Some (w@(LRC.Ret lvl)) ->
  getm mregs ra = Some (rav@rat) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra (rav@LRC.Invalidated) = Some mregsA ->
  getm mregsA (word_of_nat (Intermediate.Register.to_nat R_RA))
    = Some (wr2@ur2) ->
  updm mregsA (word_of_nat (Intermediate.Register.to_nat R_RA))
    (wr2@LRC.Invalidated) = Some mregsB ->
  getm mregsB (word.as_word (ssrint.Posz 1)) = Some (x1@LRC.Other) ->
  getm mregsB (word.as_word (ssrint.Posz 0)) = Some (w0@u0) ->
  updm mregsB (word.as_word (ssrint.Posz 0)) (w0@LRC.Invalidated)
    = Some mregs2 ->
  getm mregs2 (word.as_word (ssrint.Posz 2)) = Some (w2@u2) ->
  updm mregs2 (word.as_word (ssrint.Posz 2)) (w2@LRC.Invalidated)
    = Some mregs3 ->
  getm mregs3 (word.as_word (ssrint.Posz 3)) = Some (w3@u3) ->
  updm mregs3 (word.as_word (ssrint.Posz 3)) (w3@LRC.Invalidated)
    = Some mregs4 ->
  getm mregs4 (word.as_word (ssrint.Posz 5)) = Some (w5@u5) ->
  updm mregs4 (word.as_word (ssrint.Posz 5)) (w5@LRC.Invalidated)
    = Some mregs5 ->
  getm mregs5 (word.as_word (ssrint.Posz 6)) = Some (w6@u6) ->
  updm mregs5 (word.as_word (ssrint.Posz 6)) (w6@LRC.Invalidated)
    = Some mregs6 ->
  getm mregs6 (word.as_word (ssrint.Posz 7)) = Some (w7@u7) ->
  updm mregs6 (word.as_word (ssrint.Posz 7)) (w7@LRC.Invalidated)
    = Some mregs7 ->
  getm mregs7 (word.as_word (ssrint.Posz 16)) = Some (w16@u16) ->
  updm mregs7 (word.as_word (ssrint.Posz 16)) (w16@LRC.Invalidated)
    = Some mregs8 ->
  getm mregs8 (word.as_word (ssrint.Posz 17)) = Some (w17@u17) ->
  updm mregs8 (word.as_word (ssrint.Posz 17)) (w17@LRC.Invalidated)
    = Some mregs9 ->
  getm mregs9 (word.as_word (ssrint.Posz 18)) = Some (w18@u18) ->
  updm mregs9 (word.as_word (ssrint.Posz 18)) (w18@LRC.Invalidated)
    = Some mregs10 ->
  getm mregs10 (word.as_word (ssrint.Posz 19)) = Some (w19@u19) ->
  updm mregs10 (word.as_word (ssrint.Posz 19)) (w19@LRC.Invalidated)
    = Some mregs11 ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))
          @(LRC.Level lvl.+1 c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs11 (w@(LRC.Level lvl c')) tt)
    (Some (Events.ERet c (Symbolic.convert (word.int_of_word rcv)) c')).
Proof.
move=> Hb HC HP Ho Hcode Htgt Hneq Hrcom Hr Hra
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19
  HuA HdB HuB Hd1
  Hd0 Hu0 Hd2 Hu2 Hd3 Hu3 Hd5 Hu5 Hd6 Hu6 Hd7 Hu7
  Hd16 Hu16 Hd17 Hu17 Hd18 Hu18 Hd19 Hu19.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c IReturn)) 0
    = Some (MrJump R_RA, def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 IReturn) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
eapply stepf_jump_cross_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- exact Htgt.
- exact Hneq.
- exact Hrcom.
- exact Hr.
- exact Hra.
- exact Hc1.
- exact Hc0.
- exact Hc2.
- exact Hc3.
- exact Hc5.
- exact Hc6.
- exact Hc7.
- exact Hc16.
- exact Hc17.
- exact Hc18.
- exact Hc19.
- exact HuA.
- exact HdB.
- exact HuB.
- exact Hd1.
- exact Hd0.
- exact Hu0.
- exact Hd2.
- exact Hu2.
- exact Hd3.
- exact Hu3.
- exact Hd5.
- exact Hu5.
- exact Hd6.
- exact Hu6.
- exact Hd7.
- exact Hu7.
- exact Hd16.
- exact Hu16.
- exact Hd17.
- exact Hu17.
- exact Hd18.
- exact Hu18.
- exact Hd19.
- exact Hu19.
Qed.

(* ==================== the alloc five-cell sequence ==================== *)

(* no cell of the linked code defines [alloc_label] (all emitted labels are
   odd), so the resolver falls through to the syscall address *)
Lemma link_no_alloc :
  findopt (is_label_def Merged.alloc_label) codeW = None.
Proof.
apply: findopt_notIn_None => x HIn.
have [HIn'|HIn'] := List.in_app_or _ _ _ HIn.
- exact: (findopt_None_notIn (lin_low_no_alloc L P C pra) HIn').
- exact: (findopt_None_notIn (lin_low_no_alloc L P C prb) HIn').
Qed.

(* the capability Mov: the source's value tag — whatever it is — MOVES
   to the destination, the source is retagged by the MOV rule
   (invalidated when the tag is an address capability; LRC's MOV output
   [ts'; ts]) *)
Lemma stepf_mov_jump_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (r1 r2 : reg mt)
    (w1 oldv : mword mt) (oldt : LRC.value_tag)
    (ts : LRC.value_tag)
    (vt : LRC.value_tag)
    (ent : option (Procedure.id * seq Component.id)) (isc : bool)
    (nv : mword mt) (rc : @ratom mt)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Mov r1 r2) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (nv@(LRC.MTag vt c ent isc)) ->
  getm mregs rcom = Some rc ->
  getm mregs r1 = Some (w1@ts) ->
  getm mregs r2 = Some (oldv@oldt) ->
  updm mregs r1
    (w1@(if LRC.is_address ts then LRC.Invalidated else LRC.Other))
    = Some mregs1 ->
  updm mregs1 r2 (w1@ts) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((addw pcv onew)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC Hnext Hrcom Hr1 Hr2 Hupd1 Hupd2.
eapply Symbolic.step_mov.
- reflexivity.
- exact: HPC.
- exact: Hdec.
- exact: Hr1.
- exact: Hr2.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnext /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite eqxx /=.
  rewrite /LRC.check_belong /LRC.belong eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite Hr1 /= Hupd1 /= Hupd2 /=.
  by [].
Qed.

(* the service Jal: the target address is UNMAPPED (the syscall table
   address), so tni = None and belong accepts — a silent intra-style Jal *)
Lemma stepf_jal_service_compute (NC : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (pcv : mword mt) (lvl : nat) (c : Component.id)
    (iw : mword mt) (jimm : imm mt)
    (vret : mword mt) (vtret : LRC.value_tag)
    (entret : option (Procedure.id * seq Component.id)) (iscret : bool)
    (old : mword mt) (told : LRC.value_tag)
    (rc : @ratom mt)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (mregs1 : {fmap reg mt -> @ratom mt}) :
  decode_instr iw = Some (Types.Jal jimm) ->
  getm mem pcv = Some (iw@(def_mem_tag c true)) ->
  getm mem (addw pcv onew)
    = Some (vret@(LRC.MTag vtret c entret iscret)) ->
  getm mem (swcast jimm) = None ->
  getm mregs rcom = Some rc ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra ((addw pcv onew)@LRC.InternalJump) = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs1 (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs1 (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs1 (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs1 (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs1 (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs1 (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs1 (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs1 (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs1 (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs (pcv@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs1
       ((swcast jimm)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hdec HPC HRAcell Hnone Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd
  Hd1 Hd0 Hd2 Hd3 Hd5 Hd6 Hd7 Hd16 Hd17 Hd18 Hd19.
eapply Symbolic.step_jal.
- reflexivity.
- exact: HPC.
- exact: HRAcell.
- exact: Hdec.
- exact: Hold.
- rewrite /Symbolic.reg_clear_list /Symbolic.reg_list /=.
  rewrite Hc1 /= Hc0 /= Hc2 /= Hc3 /= Hc5 /= Hc6 /= Hc7 /=.
  rewrite Hc16 /= Hc17 /= Hc18 /= Hc19 /=.
  reflexivity.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite Hnone /=.
  rewrite /Symbolic.next_state /=.
  rewrite /Symbolic.evi Hrcom /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /=.
  rewrite /LRC.check_belong /LRC.belong /= !eqxx /=.
  rewrite /Symbolic.next_state_do_updates /=.
  rewrite HRAcell /= (updm_id HRAcell) /=.
  rewrite Hupd /=.
  rewrite Hd1 /= (updm_id Hd1) /=.
  rewrite Hd0 /= (updm_id Hd0) /=.
  rewrite Hd2 /= (updm_id Hd2) /=.
  rewrite Hd3 /= (updm_id Hd3) /=.
  rewrite Hd5 /= (updm_id Hd5) /=.
  rewrite Hd6 /= (updm_id Hd6) /=.
  rewrite Hd7 /= (updm_id Hd7) /=.
  rewrite Hd16 /= (updm_id Hd16) /=.
  rewrite Hd17 /= (updm_id Hd17) /=.
  rewrite Hd18 /= (updm_id Hd18) /=.
  rewrite Hd19 /= (updm_id Hd19) /=.
  by [].
Qed.

(* ---- the five positional steps of IAlloc ---- *)

(* cell 0: rsize → R_SC_ARG1 (data mov) *)
Lemma sim_alloc_mov1 (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl rsize)))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG1)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inl rsize))) (w1@LRC.Other)
    = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG1)))
    (w1@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 0) + pc0))
          @(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 1) + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hk0 : 0 < isize (IAlloc rptr rsize) by [].
have Hk1 : 1 < isize (IAlloc rptr rsize) by [].
have Hcell0 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 0
    = Some (MrMov (inl rsize) (inr Merged.R_SC_ARG1), def_mem_tag c true)
  by [].
have Hcell1 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 1
    = Some (MrMov (inl R_RA) (inr Merged.R_SC_ARG3), def_mem_tag c true)
  by [].
have [v [Hv Ht Hdec]] := side_encoded_fetch Hb HC HP Ho Hk0 Hcell0.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [v' [Hv' Ht' _]] := side_encoded_fetch Hb HC HP Ho Hk1 Hcell1.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat ((side_flat_pos c P0 Pcode o + 0) + pc0)) onew
           = @word_of_nat (word_size mt)
               ((side_flat_pos c P0 Pcode o + 1) + pc0).
{ rewrite won_S; congr word_of_nat; by lia. }
rewrite -Epc.
eapply stepf_mov_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* cell 1: R_RA → R_SC_ARG3 (capability mov, R_RA invalidated) *)
Lemma sim_alloc_mov2 (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt t4 : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl R_RA)))
    = Some (w1@t4) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inl R_RA)))
    (w1@(if LRC.is_address t4 then LRC.Invalidated else LRC.Other))
    = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
    (w1@t4) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 1) + pc0))
          @(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 2) + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hk1 : 1 < isize (IAlloc rptr rsize) by [].
have Hk2 : 2 < isize (IAlloc rptr rsize) by [].
have Hcell1 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 1
    = Some (MrMov (inl R_RA) (inr Merged.R_SC_ARG3), def_mem_tag c true)
  by [].
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 2
    = Some (MrJal Merged.alloc_label, def_mem_tag c true)
  by [].
have [v [Hv Ht Hdec]] := side_encoded_fetch Hb HC HP Ho Hk1 Hcell1.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [v' [Hv' Ht' _]] := side_encoded_fetch Hb HC HP Ho Hk2 Hcell2.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat ((side_flat_pos c P0 Pcode o + 1) + pc0)) onew
           = @word_of_nat (word_size mt)
               ((side_flat_pos c P0 Pcode o + 2) + pc0).
{ rewrite won_S; congr word_of_nat; by lia. }
rewrite -Epc.
eapply stepf_mov_jump_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* cell 2: Jal to the (unmapped) alloc service address *)
Lemma sim_alloc_jal (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt)
    (old : mword mt) (told : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (mregs1 : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  code_region_ok mem ->
  getm mem (word_of_nat Merged.alloc_label) = None ->
  getm mregs rcom = Some rc ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra
    ((word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0))
       @LRC.InternalJump)
    = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs1 (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs1 (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs1 (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs1 (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs1 (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs1 (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs1 (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs1 (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs1 (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 2) + pc0))
          @(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs1
       ((word_of_nat Merged.alloc_label)@(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Hcode Hnone Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd
  Hd1 Hd0 Hd2 Hd3 Hd5 Hd6 Hd7 Hd16 Hd17 Hd18 Hd19.
have Hk2 : 2 < isize (IAlloc rptr rsize) by [].
have Hk3 : 3 < isize (IAlloc rptr rsize) by [].
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 2
    = Some (MrJal Merged.alloc_label, def_mem_tag c true)
  by [].
have Hcell3 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 3
    = Some (MrMov (inr Merged.R_SC_ARG3) (inl R_RA), def_mem_tag c true)
  by [].
have [v [Hv Ht Hdec]] := side_encoded_fetch Hb HC HP Ho Hk2 Hcell2.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [v' [Hv' Ht' _]] := side_encoded_fetch Hb HC HP Ho Hk3 Hcell3.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
move: Hdec => /= Hdec.
have Hres : code_label_pos codeW pc0 Merged.alloc_label
              (pc0 + (side_flat_pos c P0 Pcode o + 2))
            = Merged.alloc_label.
{ by rewrite /code_label_pos link_no_alloc eqxx. }
rewrite Hres in Hdec.
have Halt : Merged.alloc_label < 2 ^ imm_size mt.
{ by rewrite imm_size_mt /Merged.alloc_label ltn_exp2l. }
have Etgt : @swcast _ (word_size mt)
              (@word_of_nat (imm_size mt) Merged.alloc_label)
            = @word_of_nat (word_size mt) Merged.alloc_label.
{ exact: (swcast_won_id Halt). }
have Epc : addw (word_of_nat ((side_flat_pos c P0 Pcode o + 2) + pc0)) onew
           = @word_of_nat (word_size mt)
               ((side_flat_pos c P0 Pcode o + 3) + pc0).
{ rewrite won_S; congr word_of_nat; by lia. }
rewrite -Etgt.
eapply stepf_jal_service_compute.
- exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- rewrite Etgt. exact Hnone.
- exact Hrcom.
- exact Hold.
- exact Hc1.
- exact Hc0.
- exact Hc2.
- exact Hc3.
- exact Hc5.
- exact Hc6.
- exact Hc7.
- exact Hc16.
- exact Hc17.
- exact Hc18.
- exact Hc19.
- rewrite Epc. exact Hupd.
- exact Hd1.
- exact Hd0.
- exact Hd2.
- exact Hd3.
- exact Hd5.
- exact Hd6.
- exact Hd7.
- exact Hd16.
- exact Hd17.
- exact Hd18.
- exact Hd19.
Qed.

(* cell 3: R_SC_ARG3 → R_RA (capability mov back) *)
Lemma sim_alloc_mov4 (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt t4 : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
    = Some (w1@t4) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl R_RA)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
    (w1@(if LRC.is_address t4 then LRC.Invalidated else LRC.Other))
    = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inl R_RA)))
    (w1@t4) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0))
          @(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 4) + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hk3 : 3 < isize (IAlloc rptr rsize) by [].
have Hk4 : 4 < isize (IAlloc rptr rsize) by [].
have Hcell3 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 3
    = Some (MrMov (inr Merged.R_SC_ARG3) (inl R_RA), def_mem_tag c true)
  by [].
have Hcell4 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 4
    = Some (MrMov (inr Merged.R_SC_RET) (inl rptr), def_mem_tag c true)
  by [].
have [v [Hv Ht Hdec]] := side_encoded_fetch Hb HC HP Ho Hk3 Hcell3.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [v' [Hv' Ht' _]] := side_encoded_fetch Hb HC HP Ho Hk4 Hcell4.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0)) onew
           = @word_of_nat (word_size mt)
               ((side_flat_pos c P0 Pcode o + 4) + pc0).
{ rewrite won_S; congr word_of_nat; by lia. }
rewrite -Epc.
eapply stepf_mov_jump_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* cell 4: R_SC_RET → rptr (data mov); pc leaves the alloc block *)
Lemma sim_alloc_mov5 (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register) (i' : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w1 oldv : mword mt) (oldt : LRC.value_tag)
    (mregs1 mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  List.nth_error Pcode o.+1 = Some i' ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_RET)))
    = Some (w1@LRC.Other) ->
  getm mregs (word_of_nat (Merged.to_nat_bis (inl rptr)))
    = Some (oldv@oldt) ->
  updm mregs (word_of_nat (Merged.to_nat_bis (inr Merged.R_SC_RET)))
    (w1@LRC.Other) = Some mregs1 ->
  updm mregs1 (word_of_nat (Merged.to_nat_bis (inl rptr)))
    (w1@LRC.Other) = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat ((side_flat_pos c P0 Pcode o + 4) + pc0))
          @(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' Hcode Hrcom Hr1 Hr2 Hupd1 Hupd2.
have Hk4 : 4 < isize (IAlloc rptr rsize) by [].
have Hcell4 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IAlloc rptr rsize))) 4
    = Some (MrMov (inr Merged.R_SC_RET) (inl rptr), def_mem_tag c true)
  by [].
have [v [Hv Ht Hdec]] := side_encoded_fetch Hb HC HP Ho Hk4 Hcell4.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Epc : addw (word_of_nat ((side_flat_pos c P0 Pcode o + 4) + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
rewrite -Epc.
eapply stepf_mov_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- exact Hrcom.
- exact Hr1.
- exact Hr2.
- exact Hupd1.
- exact Hupd2.
Qed.

(* ==================== body-label statics ==================== *)

Section BodyStatics.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).
Hypothesis Huniq_a : forall cid Cprocs0 l0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.
Hypothesis Huniq_b : forall cid Cprocs0 l0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.

(* body-label resolution through the link, side-uniform *)
Lemma side_label_pos_body (c : Component.id) (l : nat)
    (Cprocs : NMap Machine.code) (Pcode : Machine.code)
    (p : Procedure.id) (o : nat) (pc00 default : nat) :
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  code_label_pos codeW pc00 (can_upd L c l) default
  = pc00 + (side_flat_pos c p Pcode o + 0).
Proof.
rewrite /side_of /side_flat_pos.
case Hd: (c \in domm (Intermediate.prog_procedures pra)) => /=;
  move=> HC HP Ho.
- rewrite (link_label_pos_body_l P Hlab_a Hcomp_a Hlab_b Hdisj HC HP Ho
             (fun Cp H => Huniq_a l H) pc00 default).
  by [].
- rewrite (link_label_pos_body_r P Hlab_a Hlab_b Hcomp_b Hdisj HC HP Ho
             (fun Cp H => Huniq_b l H) pc00 default).
  by lia.
Qed.

(* ---- entry-label layer (ICall targets) ---- *)

(* the flat position of procedure (c,p)'s ENTRY cell, side-aware *)
Definition side_entry_pos (c : Component.id) (p : Procedure.id) : nat :=
  if c \in domm (Intermediate.prog_procedures pra)
  then comp_base (intermediate_to_transitional pra) c
       + (proc_base pra c p + 0)
  else size (lin_code L P C pra)
       + (comp_base (intermediate_to_transitional prb) c
          + (proc_base prb c p + 0)).

(* entry-label resolution through the link, side-uniform *)
Lemma side_label_pos_entry (c : Component.id) (p : Procedure.id)
    (Cprocs : NMap Machine.code) (Pcode : Machine.code)
    (pc00 default : nat) :
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  code_label_pos codeW pc00 (can_make L P C (c, p)) default
  = pc00 + side_entry_pos c p.
Proof.
have -> : can_make L P C (c, p) = mk_entry L P C c p by [].
rewrite /side_of /side_entry_pos.
case Hd: (c \in domm (Intermediate.prog_procedures pra)) => /=;
  move=> HC HP.
- by rewrite (link_label_pos_entry_l Hlab_a Hproc_a Hcomp_a Hlab_b Hproc_b
                Hcomp_b Hdisj HC HP pc00 default).
- by rewrite (link_label_pos_entry_r Hlab_a Hproc_a Hcomp_a Hlab_b Hproc_b
                Hcomp_b Hdisj HC HP pc00 default).
Qed.

(* the encoded ENTRY cell: a Nop carrying [head_tag] (colour, entry point,
   allowed callers) *)
Lemma side_entry_encoded_fetch (c : Component.id) (p : Procedure.id)
    (Cprocs : NMap Machine.code) (Pcode : Machine.code) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  exists v : matom,
    [/\ encode_code codeW pc0
          (word_of_nat (side_entry_pos c p + pc0)) = Some v,
        taga v = head_tag (side_of c) c p
      & Types.decode_instr (vala v) = Some (Types.Nop mt)].
Proof.
have auxl : forall (Cp : NMap Machine.code) (Pc : Machine.code),
    pc0 + size codeW < 2 ^ word_size mt ->
    Intermediate.prog_procedures pra c = Some Cp ->
    getm Cp p = Some Pc ->
    exists v : matom,
      [/\ encode_code codeW pc0
            (word_of_nat ((comp_base (intermediate_to_transitional pra) c
                           + (proc_base pra c p + 0)) + pc0)) = Some v,
          taga v = head_tag pra c p
        & Types.decode_instr (vala v) = Some (Types.Nop mt)].
{ move=> Cp Pc Hb HC HP.
  have Hn := link_entry_nth_l L P C prb HC HP.
  have [v [Hv [Ht Hval]]] := encode_code_fetch Hb Hn.
  exists v; split=> //.
  rewrite Hval /encode_instr_mp.
  rewrite encodeK /=.
  by []. }
have auxr : forall (Cp : NMap Machine.code) (Pc : Machine.code),
    pc0 + size codeW < 2 ^ word_size mt ->
    Intermediate.prog_procedures prb c = Some Cp ->
    getm Cp p = Some Pc ->
    exists v : matom,
      [/\ encode_code codeW pc0
            (word_of_nat ((size (lin_code L P C pra)
                           + (comp_base (intermediate_to_transitional prb) c
                              + (proc_base prb c p + 0))) + pc0)) = Some v,
          taga v = head_tag prb c p
        & Types.decode_instr (vala v) = Some (Types.Nop mt)].
{ move=> Cp Pc Hb HC HP.
  have Hn := link_entry_nth_r L P C pra HC HP.
  have [v [Hv [Ht Hval]]] := encode_code_fetch Hb Hn.
  exists v; split=> //.
  rewrite Hval /encode_instr_mp.
  rewrite encodeK /=.
  by []. }
move=> Hb; move: Hb.
rewrite /side_of /side_entry_pos.
case Hd: (c \in domm (Intermediate.prog_procedures pra)) => Hb HC HP.
- exact (auxl _ _ Hb HC HP).
- exact (auxr _ _ Hb HC HP).
Qed.

(* the entry stutter: from the entry cell to offset 0 of the procedure —
   one silent Nop step inside the (already switched) component *)
Lemma sim_entry_nop (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (p : Procedure.id) (Pcode : Machine.code)
    (i0 : Machine.instr)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs p = Some Pcode ->
  List.nth_error Pcode 0 = Some i0 ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_entry_pos c p + pc0))@(LRC.Level lvl c)) tt)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c p Pcode 0 + pc0))@(LRC.Level lvl c))
       tt)
    None.
Proof.
move=> Hb HC HP Ho0 Hcode Hrcom.
have [v [Hv Ht Hdec]] := side_entry_encoded_fetch Hb HC HP.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi0 Hcell0] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i0.
have [v0 [Hv0 Ht0 _]]
  := side_encoded_fetch Hb HC HP Ho0 (isize_gt0 i0) Hcell0.
rewrite addn0 in Hv0.
case: v0 Hv0 Ht0 => nv ntag Hv0 /= Ht0; subst ntag.
have Epc : addw (word_of_nat (side_entry_pos c p + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c p Pcode 0 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite /side_entry_pos /side_flat_pos /flat_pos /proc_off take0.
  by case Hd: (c \in domm (Intermediate.prog_procedures pra)) => /=; lia. }
rewrite -Epc.
eapply stepf_nop_compute.
- move: Hdec => /= Hdec. exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv0).
- exact Hrcom.
Qed.

(* IJal: intra-component call to the body label [l] (unique in [c]);
   ra := pc+1 tagged InternalJump, target = the label cell *)
Lemma sim_jal (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (l : nat) (i' : Machine.instr)
    (pt : Procedure.id) (Ptcode : Machine.code) (ot : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt)
    (old : mword mt) (told : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (mregs1 : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IJal l) ->
  List.nth_error Pcode o.+1 = Some i' ->
  getm Cprocs pt = Some Ptcode ->
  List.nth_error Ptcode ot = Some (ILabel l) ->
  pc0 + (side_flat_pos c pt Ptcode ot + 0) < 2 ^ imm_size mt ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra
    ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@LRC.InternalJump)
    = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs1 (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs1 (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs1 (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs1 (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs1 (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs1 (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs1 (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs1 (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs1 (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs1
       ((word_of_nat (side_flat_pos c pt Ptcode ot + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho Ho' HPt Hot Himm Hcode Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd
  Hd1 Hd0 Hd2 Hd3 Hd5 Hd6 Hd7 Hd16 Hd17 Hd18 Hd19.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IJal l))) 0
    = Some (MrJal (can_upd L c l), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IJal l)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
have Hcellt : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ILabel l))) 0
    = Some (MrLabel (can_upd L c l), def_mem_tag c true) by [].
have [vt [Hvt Htt _]]
  := side_encoded_fetch Hb HC HPt Hot (isize_gt0 (ILabel l)) Hcellt.
rewrite addn0 in Hvt.
case: vt Hvt Htt => tv ttag Hvt /= Htt; subst ttag.
move: Hdec => /= Hdec.
rewrite (side_label_pos_body _ _ HC HPt Hot) in Hdec.
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
have Etgt : @swcast _ (word_size mt)
              (@word_of_nat (imm_size mt)
                 (pc0 + (side_flat_pos c pt Ptcode ot + 0)))
            = @word_of_nat (word_size mt)
                (side_flat_pos c pt Ptcode ot + pc0).
{ rewrite (swcast_won_id Himm); congr word_of_nat; by lia. }
rewrite -Etgt.
eapply stepf_jal_intra_compute.
- exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- rewrite Etgt.
  exact (Hcode _ _ Hvt).
- exact Hrcom.
- exact Hold.
- exact Hc1.
- exact Hc0.
- exact Hc2.
- exact Hc3.
- exact Hc5.
- exact Hc6.
- exact Hc7.
- exact Hc16.
- exact Hc17.
- exact Hc18.
- exact Hc19.
- rewrite Epc. exact Hupd.
- exact Hd1.
- exact Hd0.
- exact Hd2.
- exact Hd3.
- exact Hd5.
- exact Hd6.
- exact Hd7.
- exact Hd16.
- exact Hd17.
- exact Hd18.
- exact Hd19.
Qed.

(* ICall: the evented cross-component call — Jal to the callee's entry
   cell, which lists the caller among its allowed callers; ra := pc+1
   tagged Ret lvl, rcom survives, everything else is invalidated *)
Lemma sim_call (NC : nat) (c c' : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (p : Procedure.id) (i' : Machine.instr)
    (Cprocs' : NMap Machine.code) (Pcode' : Machine.code)
    (cl : seq Component.id)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rcv : mword mt) (rct : LRC.value_tag)
    (old : mword mt) (told : LRC.value_tag)
    (v1 v0 v2 v3 v5 v6 v7 v16 v17 v18 v19 : mword mt)
    (t0 t2 t3 t5 t6 t7 t16 t17 t18 t19 : LRC.value_tag)
    (w0 w2 w3 w5 w6 w7 w16 w17 w18 w19 : mword mt)
    (u0 u2 u3 u5 u6 u7 u16 u17 u18 u19 : LRC.value_tag)
    (mregs1 mregs2 mregs3 mregs4 mregs5 mregs6 mregs7 mregs8 mregs9
       mregs10 mregs11 : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (ICall c' p) ->
  List.nth_error Pcode o.+1 = Some i' ->
  Intermediate.prog_procedures (side_of c') c' = Some Cprocs' ->
  getm Cprocs' p = Some Pcode' ->
  (c == c') = false ->
  head_tag (side_of c') c' p = LRC.MTag LRC.Other c' (Some (p, cl)) true ->
  mem_seq cl c = true ->
  pc0 + side_entry_pos c' p < 2 ^ imm_size mt ->
  code_region_ok mem ->
  getm mregs rcom = Some (rcv@rct) ->
  getm mregs ra = Some (old@told) ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 16)) = Some (v16@t16) ->
  getm mregs (word.as_word (ssrint.Posz 17)) = Some (v17@t17) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  getm mregs (word.as_word (ssrint.Posz 19)) = Some (v19@t19) ->
  updm mregs ra
    ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))@(LRC.Ret lvl))
    = Some mregs1 ->
  getm mregs1 (word.as_word (ssrint.Posz 1)) = Some (v1@LRC.Other) ->
  getm mregs1 (word.as_word (ssrint.Posz 0)) = Some (w0@u0) ->
  updm mregs1 (word.as_word (ssrint.Posz 0)) (w0@LRC.Invalidated)
    = Some mregs2 ->
  getm mregs2 (word.as_word (ssrint.Posz 2)) = Some (w2@u2) ->
  updm mregs2 (word.as_word (ssrint.Posz 2)) (w2@LRC.Invalidated)
    = Some mregs3 ->
  getm mregs3 (word.as_word (ssrint.Posz 3)) = Some (w3@u3) ->
  updm mregs3 (word.as_word (ssrint.Posz 3)) (w3@LRC.Invalidated)
    = Some mregs4 ->
  getm mregs4 (word.as_word (ssrint.Posz 5)) = Some (w5@u5) ->
  updm mregs4 (word.as_word (ssrint.Posz 5)) (w5@LRC.Invalidated)
    = Some mregs5 ->
  getm mregs5 (word.as_word (ssrint.Posz 6)) = Some (w6@u6) ->
  updm mregs5 (word.as_word (ssrint.Posz 6)) (w6@LRC.Invalidated)
    = Some mregs6 ->
  getm mregs6 (word.as_word (ssrint.Posz 7)) = Some (w7@u7) ->
  updm mregs6 (word.as_word (ssrint.Posz 7)) (w7@LRC.Invalidated)
    = Some mregs7 ->
  getm mregs7 (word.as_word (ssrint.Posz 16)) = Some (w16@u16) ->
  updm mregs7 (word.as_word (ssrint.Posz 16)) (w16@LRC.Invalidated)
    = Some mregs8 ->
  getm mregs8 (word.as_word (ssrint.Posz 17)) = Some (w17@u17) ->
  updm mregs8 (word.as_word (ssrint.Posz 17)) (w17@LRC.Invalidated)
    = Some mregs9 ->
  getm mregs9 (word.as_word (ssrint.Posz 18)) = Some (w18@u18) ->
  updm mregs9 (word.as_word (ssrint.Posz 18)) (w18@LRC.Invalidated)
    = Some mregs10 ->
  getm mregs10 (word.as_word (ssrint.Posz 19)) = Some (w19@u19) ->
  updm mregs10 (word.as_word (ssrint.Posz 19)) (w19@LRC.Invalidated)
    = Some mregs11 ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs11
       ((word_of_nat (side_entry_pos c' p + pc0))@(LRC.Level lvl.+1 c'))
       tt)
    (Some (Events.ECall c p (Symbolic.convert (word.int_of_word rcv)) c')).
Proof.
move=> Hb HC HP Ho Ho' HC' HP' Hneq Hhead Hentry Himm Hcode Hrcom Hold
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18 Hc19 Hupd Hd1
  Hd0 Hu0 Hd2 Hu2 Hd3 Hu3 Hd5 Hu5 Hd6 Hu6 Hd7 Hu7
  Hd16 Hu16 Hd17 Hu17 Hd18 Hu18 Hd19 Hu19.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ICall c' p))) 0
    = Some (MrJal (can_make L P C (c', p)), def_mem_tag c true).
{ by rewrite /instr_to_transitional; case: (Nat.eqb _ _). }
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (ICall c' p)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
(* the return cell at o.+1 *)
have [mi' Hcell'] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers (side_of c))) c i'.
have [v' [Hv' Ht' _]]
  := side_encoded_fetch Hb HC HP Ho' (isize_gt0 i') Hcell'.
rewrite addn0 in Hv'.
case: v' Hv' Ht' => nv ntag Hv' /= Ht'; subst ntag.
(* the callee's entry cell *)
have [ve [Hve Hte _]] := side_entry_encoded_fetch Hb HC' HP'.
case: ve Hve Hte => ev etag Hve /= Hte; subst etag.
rewrite Hhead in Hve.
(* resolve the entry label inside the decoded Jal *)
move: Hdec => /= Hdec.
rewrite (side_label_pos_entry _ _ HC' HP') in Hdec.
(* pc bridges *)
have Epc : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0)) onew
           = @word_of_nat (word_size mt)
               (side_flat_pos c P0 Pcode o.+1 + pc0).
{ rewrite won_S; congr word_of_nat.
  rewrite (side_flat_pos_S c P0 Ho) /=; by lia. }
have Etgt : @swcast _ (word_size mt)
              (@word_of_nat (imm_size mt) (pc0 + side_entry_pos c' p))
            = @word_of_nat (word_size mt) (side_entry_pos c' p + pc0).
{ rewrite (swcast_won_id Himm); congr word_of_nat; by lia. }
rewrite -Etgt.
eapply stepf_jal_cross_compute.
- exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Epc. exact (Hcode _ _ Hv').
- rewrite Etgt. exact (Hcode _ _ Hve).
- exact Hneq.
- exact Hentry.
- exact Hrcom.
- exact Hold.
- exact Hc1.
- exact Hc0.
- exact Hc2.
- exact Hc3.
- exact Hc5.
- exact Hc6.
- exact Hc7.
- exact Hc16.
- exact Hc17.
- exact Hc18.
- exact Hc19.
- rewrite Epc. exact Hupd.
- exact Hd1.
- exact Hd0.
- exact Hu0.
- exact Hd2.
- exact Hu2.
- exact Hd3.
- exact Hu3.
- exact Hd5.
- exact Hu5.
- exact Hd6.
- exact Hu6.
- exact Hd7.
- exact Hu7.
- exact Hd16.
- exact Hu16.
- exact Hd17.
- exact Hu17.
- exact Hd18.
- exact Hu18.
- exact Hd19.
- exact Hu19.
Qed.

(* IBnz, taken branch: relative forward jump to the body label [l] *)
Lemma sim_bnz_nz (NC : nat) (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (r : Machine.register) (l : nat)
    (pt : Procedure.id) (Ptcode : Machine.code) (ot : nat)
    (mem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt) (w : mword mt)
    (mregs' : {fmap reg mt -> @ratom mt}) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IBnz r l) ->
  getm Cprocs pt = Some Ptcode ->
  List.nth_error Ptcode ot = Some (ILabel l) ->
  side_flat_pos c P0 Pcode o <= side_flat_pos c pt Ptcode ot ->
  (pc0 + (side_flat_pos c pt Ptcode ot + 0))
    - (pc0 + side_flat_pos c P0 Pcode o) < 2 ^ imm_size mt ->
  code_region_ok mem ->
  getm mregs rcom = Some rc ->
  getm mregs (word_of_nat (Intermediate.Register.to_nat r))
    = Some (w@LRC.Other) ->
  (w == 0%w) = false ->
  updm mregs (word_of_nat (Intermediate.Register.to_nat r)) (w@LRC.Other)
    = Some mregs' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags _ mem mregs
       ((word_of_nat (side_flat_pos c P0 Pcode o + pc0))@(LRC.Level lvl c))
       tt)
    (@Symbolic.State mt lrc_tags _ mem mregs'
       ((word_of_nat (side_flat_pos c pt Ptcode ot + pc0))
          @(LRC.Level lvl c)) tt)
    None.
Proof.
move=> Hb HC HP Ho HPt Hot Hfwd Himm Hcode Hrcom Hr Hw Hupd.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (IBnz r l))) 0
    = Some (MrBnz r (can_upd L c l), def_mem_tag c true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb HC HP Ho (isize_gt0 (IBnz r l)) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
have Hcellt : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers (side_of c)))
       (instr_to_transitional c (ILabel l))) 0
    = Some (MrLabel (can_upd L c l), def_mem_tag c true) by [].
have [vt [Hvt Htt _]]
  := side_encoded_fetch Hb HC HPt Hot (isize_gt0 (ILabel l)) Hcellt.
rewrite addn0 in Hvt.
case: vt Hvt Htt => tv ttag Hvt /= Htt; subst ttag.
move: Hdec => /= Hdec.
rewrite (side_label_pos_body _ _ HC HPt Hot) in Hdec.
have Etgt : addw (word_of_nat (side_flat_pos c P0 Pcode o + pc0))
              (@swcast _ (word_size mt)
                 (@word_of_nat (imm_size mt)
                    ((pc0 + (side_flat_pos c pt Ptcode ot + 0))
                     - (pc0 + side_flat_pos c P0 Pcode o))))
            = @word_of_nat (word_size mt)
                (side_flat_pos c pt Ptcode ot + pc0).
{ rewrite (addw_won_swcast (side_flat_pos c P0 Pcode o + pc0) Himm).
  congr word_of_nat; by lia. }
rewrite -Etgt.
eapply stepf_bnz_nz_compute.
- exact Hdec.
- exact (Hcode _ _ Hv).
- rewrite Etgt.
  exact (Hcode _ _ Hvt).
- exact Hrcom.
- exact Hr.
- exact Hw.
- exact Hupd.
Qed.

End BodyStatics.

(* ==================== diagram cases ==================== *)

(* the machine's rcom register IS R_COM's key — via VM computation: the
   kernel's lazy conversion diverges on this innocuous-looking fact *)
Lemma rcom_key : (rcom : reg mt)
  = @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat R_COM).
Proof. by vm_compute. Qed.

(* the me address of a related pointer IS the flat position word — bridges
   val_rel_b's Ptr clause to mr_load's address spelling *)
Lemma won_addz (base : nat) (off : Z) :
  (0 <= off)%Z ->
  word.as_word
    (ssrint.intZmod.addz (Merged.encode_int off) (ssrint.Posz base))
  = @word_of_nat (word_size mt) (base + Z.to_nat off).
Proof.
move=> Hoff.
rewrite /word_of_nat; congr word.as_word.
by case: off Hoff => [|p|p] //= Hoff; lia.
Qed.

(* the integer-immediate value relation: an in-range non-negative
   constant is written as the same word on both sides (the fit condition
   is the standard trace-value assumption) *)
Lemma val_rel_imm_int (bmap : addr_map) (msz0 : NMap (NMap nat)) (z : Z) :
  (0 <= z)%Z -> Z.to_nat z < 2 ^ imm_size mt ->
  val_rel_b bmap (imm_to_val (IInt z))
    (swcast (convert_value (mt := mt) msz0 (IInt z))).
Proof.
move=> Hz Hfit /=.
have -> : Merged.encode_int z = ssrint.Posz (Z.to_nat z).
{ case: z Hz {Hfit} => [|p|p] //= Hz.
  by congr ssrint.Posz; lia. }
exact (swcast_won_id Hfit).
Qed.

(* the event-value roundtrip: the me machine reads back exactly the
   I-side integer, for non-negative values fitting the SIGNED word range
   (int_of_word reads the top bit as a sign) *)
Lemma event_value_roundtrip (z : Z) :
  (0 <= z)%Z -> Z.to_nat z < 2 ^ (word_size mt).-1 ->
  Symbolic.convert
    (word.int_of_word
       (word.as_word (Merged.encode_int z) : mword mt)) = z.
Proof.
move=> Hz Hfit.
have -> : Merged.encode_int z = ssrint.Posz (Z.to_nat z).
{ case: z Hz {Hfit} => [|p|p] //= Hz.
  by congr ssrint.Posz; lia. }
have Hlt : Z.to_nat z < 2 ^ (word_size mt).
{ apply: (leq_trans Hfit).
  by rewrite leq_exp2l //; case: (word_size mt). }
rewrite /word.int_of_word !(as_wordK Hlt) ifT //.
rewrite /Symbolic.convert.
by lia.
Qed.

Lemma as_wordD_nat (a b : nat) :
  addw (word.as_word (ssrint.Posz a)) (word.as_word (ssrint.Posz b))
  = (word.as_word (ssrint.Posz (a + b)) : mword mt).
Proof. exact (word_of_natDall (word_size mt) a b). Qed.

(* integer addition relates unconditionally on non-negative operands
   (word addition is modular; encode_int is Posz∘Z.to_nat on ≥ 0) *)
Lemma binop_rel_add_int (bmap : addr_map) (z1 z2 : Z)
    (w1 w2 : mword mt) :
  (0 <= z1)%Z -> (0 <= z2)%Z ->
  val_rel_b bmap (Int z1) w1 ->
  val_rel_b bmap (Int z2) w2 ->
  val_rel_b bmap (eval_binop Add (Int z1) (Int z2))
    (binop_denote (Merged.binop_trans Add) w1 w2).
Proof.
move=> Hz1 Hz2 /= -> -> /=.
have E1 : Merged.encode_int z1 = ssrint.Posz (Z.to_nat z1).
{ by case: z1 Hz1 => [|p|p] //= _; congr ssrint.Posz; lia. }
have E2 : Merged.encode_int z2 = ssrint.Posz (Z.to_nat z2).
{ by case: z2 Hz2 => [|p|p] //= _; congr ssrint.Posz; lia. }
have E12 : Merged.encode_int (z1 + z2)
           = ssrint.Posz (Z.to_nat (z1 + z2)).
{ have Hz12 : (0 <= z1 + z2)%Z by lia.
  by case: (z1 + z2)%Z Hz12 => [|p|p] //= _; congr ssrint.Posz; lia. }
rewrite E1 E2 E12 as_wordD_nat.
congr word.as_word; congr ssrint.Posz.
by lia.
Qed.

Lemma word_of_natMall (k a b : nat) :
  mulw (@word_of_nat k a) (@word_of_nat k b) = @word_of_nat k (a * b).
Proof.
apply: WordExtra.word_nat_inj. rewrite /mulw.
move: (valw_won k a) (valw_won k b) => Ea Eb. rewrite Ea Eb.
rewrite (valw_won k (a * b)) WordExtra.valw_as_word. by rewrite modnMm.
Qed.

Lemma as_wordM_nat (a b : nat) :
  mulw (word.as_word (ssrint.Posz a)) (word.as_word (ssrint.Posz b))
  = (word.as_word (ssrint.Posz (a * b)) : mword mt).
Proof. exact (word_of_natMall (word_size mt) a b). Qed.

Lemma binop_rel_mul_int (bmap : addr_map) (z1 z2 : Z)
    (w1 w2 : mword mt) :
  (0 <= z1)%Z -> (0 <= z2)%Z ->
  val_rel_b bmap (Int z1) w1 ->
  val_rel_b bmap (Int z2) w2 ->
  val_rel_b bmap (eval_binop Mul (Int z1) (Int z2))
    (binop_denote (Merged.binop_trans Mul) w1 w2).
Proof.
move=> Hz1 Hz2 /= -> -> /=.
have E1 : Merged.encode_int z1 = ssrint.Posz (Z.to_nat z1).
{ by case: z1 Hz1 => [|p|p] //= _; congr ssrint.Posz; lia. }
have E2 : Merged.encode_int z2 = ssrint.Posz (Z.to_nat z2).
{ by case: z2 Hz2 => [|p|p] //= _; congr ssrint.Posz; lia. }
have E12 : Merged.encode_int (z1 * z2)
           = ssrint.Posz (Z.to_nat (z1 * z2)).
{ have Hz12 : (0 <= z1 * z2)%Z by lia.
  by case: (z1 * z2)%Z Hz12 => [|p|p] //= _; congr ssrint.Posz; lia. }
rewrite E1 E2 E12 as_wordM_nat.
congr word.as_word; congr ssrint.Posz.
by lia.
Qed.

(* integer equality relates under the word-size fit (collision freedom) *)
Lemma binop_rel_eq_int (bmap : addr_map) (z1 z2 : Z)
    (w1 w2 : mword mt) :
  (0 <= z1)%Z -> (0 <= z2)%Z ->
  Z.to_nat z1 < 2 ^ word_size mt -> Z.to_nat z2 < 2 ^ word_size mt ->
  val_rel_b bmap (Int z1) w1 ->
  val_rel_b bmap (Int z2) w2 ->
  val_rel_b bmap (eval_binop Eq (Int z1) (Int z2))
    (binop_denote (Merged.binop_trans Eq) w1 w2).
Proof.
move=> Hz1 Hz2 Hf1 Hf2 /= -> -> /=.
have E1 : Merged.encode_int z1 = ssrint.Posz (Z.to_nat z1).
{ by case: z1 Hz1 {Hf1} => [|p|p] //= _; congr ssrint.Posz; lia. }
have E2 : Merged.encode_int z2 = ssrint.Posz (Z.to_nat z2).
{ by case: z2 Hz2 {Hf2} => [|p|p] //= _; congr ssrint.Posz; lia. }
rewrite E1 E2 (won_eqE Hf1 Hf2).
have -> : (Z.to_nat z1 == Z.to_nat z2) = (z1 =? z2)%Z.
{ case: (Z.eqb_spec z1 z2) => Ez.
  - by rewrite Ez eqxx.
  - by apply/negbTE/negP => /eqP; lia. }
by case: (z1 =? z2)%Z.
Qed.

(* as_word cancels val (the canonical nat base of a word) *)
Lemma won_valK (w : mword mt) :
  @word_of_nat (word_size mt) (eqtype.val w) = w.
Proof.
apply: WordExtra.word_nat_inj.
by rewrite valw_won modn_small.
Qed.

(* the fresh block's base word: won (val max).+1 = max + 1 *)
Lemma won_val_S (w : mword mt) :
  @word_of_nat (word_size mt) ((eqtype.val w).+1)
  = (w + word.as_word (ssrint.Posz 1))%w.
Proof.
by rewrite -won_S won_valK.
Qed.

Lemma word_of_natBall (k a b : nat) :
  b <= a -> a < 2 ^ k ->
  subw (@word_of_nat k a) (@word_of_nat k b) = @word_of_nat k (a - b).
Proof.
move=> Hba Ha.
have H2k : 0 < 2 ^ k by rewrite expn_gt0.
apply: WordExtra.word_nat_inj.
rewrite /subw /addw /oppw.
move: (valw_won k a) (valw_won k b) => Ea Eb.
rewrite Ea Eb.
move: (@WordExtra.valw_as_word k (2 ^ k - b %% 2 ^ k)) => Eo.
rewrite Eo.
rewrite (valw_won k (a - b)) WordExtra.valw_as_word.
have Hb : b < 2 ^ k by lia.
rewrite (modn_small Ha) (modn_small Hb).
case: (posnP b) => [Eb0 | Hbpos].
- by rewrite Eb0 subn0 modnn addn0 subn0 (modn_small Ha).
- have Hlt : 2 ^ k - b < 2 ^ k by lia.
  rewrite (modn_small Hlt).
  have -> : a + (2 ^ k - b) = (a - b) + 2 ^ k by lia.
  by rewrite modnDr.
Qed.

Lemma binop_rel_minus_int (bmap : addr_map) (z1 z2 : Z)
    (w1 w2 : mword mt) :
  (0 <= z2)%Z -> (z2 <= z1)%Z ->
  Z.to_nat z1 < 2 ^ word_size mt ->
  val_rel_b bmap (Int z1) w1 ->
  val_rel_b bmap (Int z2) w2 ->
  val_rel_b bmap (eval_binop Minus (Int z1) (Int z2))
    (binop_denote (Merged.binop_trans Minus) w1 w2).
Proof.
move=> Hz2 Hz21 Hf1 /= -> -> /=.
have Hz1 : (0 <= z1)%Z by lia.
have E1 : Merged.encode_int z1 = ssrint.Posz (Z.to_nat z1).
{ by case: z1 Hz1 {Hz21 Hf1} => [|p|p] //= _; congr ssrint.Posz; lia. }
have E2 : Merged.encode_int z2 = ssrint.Posz (Z.to_nat z2).
{ by case: z2 Hz2 {Hz21} => [|p|p] //= _; congr ssrint.Posz; lia. }
have E12 : Merged.encode_int (z1 - z2)
           = ssrint.Posz (Z.to_nat (z1 - z2)).
{ have Hz12 : (0 <= z1 - z2)%Z by lia.
  by case: (z1 - z2)%Z Hz12 => [|p|p] //= _; congr ssrint.Posz; lia. }
rewrite E1 E2 E12.
have Hle : Z.to_nat z2 <= Z.to_nat z1 by lia.
have -> := word_of_natBall Hle Hf1.
congr word.as_word; congr ssrint.Posz.
by lia.
Qed.

(* TODO(Leq case): the word Ord is the subtype (val) order but the
   conversion through the pcancel-HB chain diverges at exact-time; an
   ord_wonE bridge needs a dedicated extraction lemma for [Ord of _ by <:]
   (e.g. via Ord.leq's cancel-instance equation) — then binop_rel_leq_int
   is a clone of binop_rel_eq_int. *)

(* pc_rel advances with Pointer.inc (same block decomposition) *)
Lemma pc_rel_inc (gps : list Pointer.t) (ipc : Pointer.t)
    (mpc : atom (mword mt) (tag_type lrc_tags Symbolic.P))
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component ipc) = Some Cprocs ->
  Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset ipc)%Z ->
  vala mpc = @word_of_nat (word_size mt)
               (side_flat_pos (Pointer.component ipc) P0 Pcode
                  (Z.to_nat (Pointer.offset ipc)).+1 + pc0) ->
  taga mpc = LRC.Level (cross_frames (Pointer.component ipc) gps)
               (Pointer.component ipc) ->
  pc_rel gps (Pointer.inc ipc) mpc.
Proof.
move=> Hilp Hblk Hjnth Hoff Hval Htag.
have HoffE : Pointer.offset (Pointer.inc ipc)
             = (Pointer.offset ipc + 1)%Z.
{ by case: ipc {Hilp Hblk Hoff Hval Htag} => [[? ?] ?]. }
have HtoS : Z.to_nat (Pointer.offset ipc + 1)
            = (Z.to_nat (Pointer.offset ipc)).+1.
{ by lia. }
exists Cprocs, j, P0, Pcode.
rewrite !Pointer.inc_preserves_component !Pointer.inc_preserves_block.
rewrite HoffE HtoS.
split.
- exact Hilp.
- exact Hblk.
- exact Hjnth.
- by lia.
- by split.
Qed.

(* pc_rel at an arbitrary target pointer sharing ipc's component and
   block (intra-procedure jumps: taken branches, Jal landings) *)
Lemma pc_rel_at (gps : list Pointer.t) (ipc tpc : Pointer.t)
    (mpc : atom (mword mt) (tag_type lrc_tags Symbolic.P))
    (Cprocs : NMap Machine.code) (j : nat)
    (P0 : Procedure.id) (Pcode : Machine.code) :
  Intermediate.prog_procedures ilp (Pointer.component ipc) = Some Cprocs ->
  Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  Pointer.component tpc = Pointer.component ipc ->
  Pointer.block tpc = Pointer.block ipc ->
  (0 <= Pointer.offset tpc)%Z ->
  vala mpc = @word_of_nat (word_size mt)
               (side_flat_pos (Pointer.component ipc) P0 Pcode
                  (Z.to_nat (Pointer.offset tpc)) + pc0) ->
  taga mpc = LRC.Level (cross_frames (Pointer.component ipc) gps)
               (Pointer.component ipc) ->
  pc_rel gps tpc mpc.
Proof.
move=> Hilp Hblk Hjnth Hcomp Hblk' Hoff Hval Htag.
exists Cprocs, j, P0, Pcode.
rewrite Hcomp Hblk'.
split.
- exact Hilp.
- exact Hblk.
- exact Hjnth.
- exact Hoff.
- by split.
Qed.

(* the machine's ra register IS R_RA's key — VM-certified like rcom_key *)
Lemma ra_key4 : (ra : reg mt)
  = @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat R_RA).
Proof. by vm_compute. Qed.

(* raw as_word key comparison (both spellings), 5-bit registers *)
Lemma as_eqE (i j : nat) :
  i < 32 -> j < 32 ->
  ((word.as_word (ssrint.Posz i) : reg mt) == word.as_word (ssrint.Posz j))
  = (i == j).
Proof. move=> Hi Hj. exact (won_as_eqE Hi Hj). Qed.

(* the I-side R_RA clobber is invisible to the no-RA relation *)
Lemma regs_rel_w_iset_ra (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (v : value) :
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap (Intermediate.Register.set R_RA v iregs) mregs.
Proof.
move=> Hrel r' Hra'.
have [a [Hget Hd]] := Hrel r' Hra'.
exists a; split=> //.
rewrite /Intermediate.Register.get /Intermediate.Register.set setmE.
have -> : (Intermediate.Register.to_nat r'
           == Intermediate.Register.to_nat R_RA) = false.
{ by apply/negbTE/negP => /eqP /to_nat_inj E; exact: Hra' E. }
by move: Hd; rewrite /Intermediate.Register.get.
Qed.

(* getm through a setm at ra's slot, other working keys unchanged *)
Lemma getm_set_ra_other (mregs : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (k : nat) :
  k < 32 -> (k == 4) = false ->
  getm (setm mregs
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA)) x)
    (word.as_word (ssrint.Posz k))
  = getm mregs (word.as_word (ssrint.Posz k)).
Proof.
move=> Hk Hk4.
rewrite setmE.
have -> : ((word.as_word (ssrint.Posz k) : reg mt)
           == @word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA)) = false.
{ by rewrite (as_eqE Hk (isT : 4 < 32)) Hk4. }
by [].
Qed.

(* reading BACK the ra key just set (both spellings) *)
Lemma getm_set_ra_self (mregs : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) :
  getm (setm mregs
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA)) x)
    (word.as_word (ssrint.Posz 4)) = Some x.
Proof.
rewrite setmE.
have -> : ((word.as_word (ssrint.Posz 4) : reg mt)
           == @word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA)) = true.
{ by rewrite (as_eqE (isT : 4 < 32) (isT : 4 < 32)). }
by [].
Qed.

(* INop: one silent me-step, lin_match reassembled at Pointer.inc ipc.
   Premises beyond the match: the SINV clause is pc-insensitive, and the
   instruction is not last in its procedure (compiledness). *)
Lemma diag_nop (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                  (Symbolic.regs ms) mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)) = Some INop ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc INop ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have HoffE : Pointer.offset (Pointer.inc ipc)
             = (Pointer.offset ipc + 1)%Z.
{ by case: ipc {HS Hm Hin Hex Hpc Hval Htag Hside HgetP Hnth Hterm Hblk
                Hilp Hoff Hnth' Hstack} => [[? ?] ?]. }
have HtoS : Z.to_nat (Pointer.offset ipc + 1)
            = (Z.to_nat (Pointer.offset ipc)).+1.
{ by lia. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Htot.
subst pcv pct.
exists (@Symbolic.State mt lrc_tags _ mmem mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_nop;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (exact Hregs).
  + abstract (exact Hcode).
  + abstract (exact: (HS _ Hstack)).
  + abstract (exact Htot).
Qed.

(* ILabel: same silent diagram as INop *)
Lemma diag_label (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) (l : nat) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                  (Symbolic.regs ms) mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (ILabel l) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILabel l) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Htot.
subst pcv pct.
exists (@Symbolic.State mt lrc_tags _ mmem mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_label;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (exact Hregs).
  + abstract (exact Hcode).
  + abstract (exact: (HS _ Hstack)).
  + abstract (exact Htot).
Qed.

(* IConst: silent step writing the converted immediate; the value relation
   for the immediate and the SINV stability are explicit premises *)
Lemma diag_const (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (v0 : imvalue) (r : Machine.register) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r <> R_RA ->
  Intermediate.Register.set r (imm_to_val v0) iregs = iregs' ->
  val_rel_b bmap (imm_to_val v0)
    (swcast (convert_value (mt := mt)
       (memory_lengths (Intermediate.prog_buffers
          (side_of (Pointer.component ipc)))) v0)) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r (imm_to_val v0) iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r))
           ((swcast (convert_value (mt := mt)
               (memory_lengths (Intermediate.prog_buffers
                  (side_of (Pointer.component ipc)))) v0))@LRC.Other))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IConst v0 r) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IConst v0 r) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra Hset Hvrel HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have [aold [Hold _]] := Hregs r Hrra.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hold Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hold Htot.
subst pcv pct.
case: aold Hold => oldv oldt Hold.
have Hupd := updm_from_get
  ((swcast (convert_value (mt := mt)
      (memory_lengths (Intermediate.prog_buffers
         (side_of (Pointer.component ipc)))) v0))@LRC.Other) Hold.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r))
     ((swcast (convert_value (mt := mt)
         (memory_lengths (Intermediate.prog_buffers
            (side_of (Pointer.component ipc)))) v0))@LRC.Other))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_const;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hold
    | exact Hupd]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset; exact (regs_rel_w_set r Hregs Hvrel)).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IBinOp: silent step; the sources' Other-tags and the result value
   relation are explicit premises (BinOp has no I-side shape premise, so
   Other-ness comes from the compiled read-after-write invariant later) *)
Lemma diag_binop (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (op : Values.binop) (r1 r2 r3 : Machine.register)
    (w1 w2 : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r3 <> R_RA ->
  Intermediate.Register.set r3
    (eval_binop op (Intermediate.Register.get r1 iregs)
       (Intermediate.Register.get r2 iregs)) iregs = iregs' ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  val_rel_b bmap
    (eval_binop op (Intermediate.Register.get r1 iregs)
       (Intermediate.Register.get r2 iregs))
    (binop_denote (Merged.binop_trans op) w1 w2) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r3
           (eval_binop op (Intermediate.Register.get r1 iregs)
              (Intermediate.Register.get r2 iregs)) iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r3))
           ((binop_denote (Merged.binop_trans op) w1 w2)@LRC.Other))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IBinOp op r1 r2 r3) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBinOp op r1 r2 r3) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra3 Hset Hs1 Hs2 Hvres HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have [a3 [Hold3 _]] := Hregs r3 Hrra3.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hs2 Hold3 Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hs2 Hold3 Htot.
subst pcv pct.
case: a3 Hold3 => oldv oldt Hold3.
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_id Hs2.
have Hupd3 := updm_from_get
  ((binop_denote (Merged.binop_trans op) w1 w2)@LRC.Other) Hold3.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r3))
     ((binop_denote (Merged.binop_trans op) w1 w2)@LRC.Other))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_binop;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hs2
    | exact Hold3 | exact Hupd1 | exact Hs2 | exact Hupd2
    | exact Hupd3]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset; exact (regs_rel_w_set r3 Hregs Hvres)).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IMov, strong case: the source register is Other-tagged and related;
   the writeback is an identity, the destination write a single setm *)
Lemma diag_mov_strong (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (w1 : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r2 <> R_RA ->
  Intermediate.Register.set r2 (Intermediate.Register.get r1 iregs) iregs
    = iregs' ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Other) ->
  val_rel_b bmap (Intermediate.Register.get r1 iregs) w1 ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r2
           (Intermediate.Register.get r1 iregs) iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2)) (w1@LRC.Other))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IMov r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IMov r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra2 Hset Hs1 Hvrel HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have [a2 [Hold2 _]] := Hregs r2 Hrra2.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hold2 Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hold2 Htot.
subst pcv pct.
case: a2 Hold2 => oldv oldt Hold2.
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_from_get (w1@LRC.Other) Hold2.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r2)) (w1@LRC.Other))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_mov;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1
    | exact Hold2 | exact Hupd1 | exact Hupd2]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset; exact (regs_rel_w_set r2 Hregs Hvrel)).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IMov, Invalidated case: the source register was cross-invalidated,
   so its I value is Undef; the tag propagates to the destination *)
Lemma diag_mov_inv (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (w1 : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r2 <> R_RA ->
  Intermediate.Register.get r1 iregs = Undef ->
  Intermediate.Register.set r2 (Intermediate.Register.get r1 iregs) iregs
    = iregs' ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r1))
    = Some (w1@LRC.Invalidated) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r2
           (Intermediate.Register.get r1 iregs) iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2)) (w1@LRC.Invalidated))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IMov r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IMov r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra2 Hu1 Hset Hs1 HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have [a2 [Hold2 _]] := Hregs r2 Hrra2.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hold2 Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hold2 Htot.
subst pcv pct.
case: a2 Hold2 => oldv oldt Hold2.
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_from_get (w1@LRC.Invalidated) Hold2.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r2)) (w1@LRC.Invalidated))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_mov_inv;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1
    | exact Hold2 | exact Hupd1 | exact Hupd2]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset Hu1;
      have Ht : LRC.Invalidated = LRC.Other
                \/ LRC.Invalidated = LRC.Invalidated;
      [by right
      | exact: (@regs_rel_w_set_undef bmap iregs mregs r2
                  (w1@LRC.Invalidated) Ht Hregs)]).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IBnz, untaken: silent fall-through, registers unchanged (identity
   writeback); the zero test on the me word is an explicit premise *)
Lemma diag_bnz_z (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r : Machine.register) (l : nat) (w : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r))
    = Some (w@LRC.Other) ->
  (w == 0%w) = true ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                  (Symbolic.regs ms) mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IBnz r l) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hs Hw HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs Htot.
subst pcv pct.
have Hupd := updm_id Hs.
exists (@Symbolic.State mt lrc_tags _ mmem mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_bnz_z;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs | exact Hw
    | exact Hupd]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (exact Hregs).
  + abstract (exact Hcode).
  + abstract (exact: (HS _ Hstack)).
  + abstract (exact Htot).
Qed.

(* a pure tag rewrite of one data cell (same word, colour, entry,
   code-flag) preserves the memory relation — [switch_val]'s cell
   retagging on RA-moving loads *)
Lemma mem_rel_retag (bmap : addr_map) (imem : Memory.Memory.t)
    (mmem : {fmap mword mt -> matom}) (k : mword mt) (w : mword mt)
    (vt vt' : LRC.value_tag) (c0 : Component.id)
    (e : option (Procedure.id * seq Component.id)) :
  mem_rel bmap imem mmem ->
  getm mmem k = Some (w@(LRC.MTag vt c0 e false)) ->
  mem_rel bmap imem (setm mmem k (w@(LRC.MTag vt' c0 e false))).
Proof.
move=> [ML MF MI] Hcell.
constructor.
- move=> C0 b0 off0 v0 Hl0.
  have [base0 [a0 [H1 H2 H3 H4 H5]]] := ML _ _ _ _ Hl0.
  exists base0.
  rewrite setmE.
  case Ew: (@word_of_nat (word_size mt) (base0 + Z.to_nat off0) == k).
  + move/eqP: Ew => Ew.
    rewrite Ew Hcell in H2.
    case: H2 => Ea; subst a0.
    exists (w@(LRC.MTag vt' c0 e false)).
    by split.
  + exists a0. by split.
- exact: MF.
- exact: MI.
Qed.

(* ILoad: silent step through an own-component data cell; the cell's
   Other-vtag (buffer/stack separation) and SINV stability are premises *)
Lemma diag_load (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (bp : Block.id) (op : Z) (v : value) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA -> r2 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
  Intermediate.Register.set r2 v iregs = iregs' ->
  (forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Other) ->
  (forall base w ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                     false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem (Intermediate.Register.set r2 v iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2)) (w@LRC.Other))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (ILoad r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hrra2 Hptr Hoffp Hload Hset Hvtag HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hload.
have Eb : base' = base by congruence.
subst base'.
have Hvt := Hvtag _ _ Hamap Hcell.
have [a2 [Hold2 _]] := Hregs r2 Hrra2.
clear Hm Hmrl.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hcell Hvt
  Hold2 Hvtag Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hcell Hvt Hold2 Hvtag Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc Hvt => w2 atag /= Hcell Hvrel Hcol Hisc Hvt.
case: atag Hcell Hcol Hisc Hvt
  => avt ac aent aisc /= Hcell Hcol Hisc Hvt.
subst avt ac aisc.
subst w1.
case: a2 Hold2 => oldv oldt Hold2.
have Hupd1 := updm_id Hs1.
have Hupdm := updm_id Hcell.
have Hupd2 := updm_from_get (w2@LRC.Other) Hold2.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r2)) (w2@LRC.Other))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_load;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hcell
    | exact Hold2 | exact Hupd1 | exact Hupdm | exact Hupd2]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset; exact (regs_rel_w_set r2 Hregs Hvrel)).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ _ _ _ Hamap Hcell Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* ILoad of an Invalidated data cell (a stored cross-invalidated Undef,
   e.g. the reloaded saved-SP slot): the tag moves into the destination
   register and the cell is re-tagged Invalidated (unchanged) *)
Lemma diag_load_inv (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (bp : Block.id) (op : Z) (v : value) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA -> r2 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
  v = Undef ->
  Intermediate.Register.set r2 v iregs = iregs' ->
  (forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Invalidated) ->
  (forall base w ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w@(LRC.MTag LRC.Invalidated (Pointer.component ipc) ent
                     false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem (Intermediate.Register.set r2 v iregs)
        (Pointer.inc ipc) (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
        (setm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2)) (w@LRC.Invalidated))
        mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (ILoad r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hrra2 Hptr Hoffp Hload Hu Hset Hvtag HS Hterm
  Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hload.
have Eb : base' = base by congruence.
subst base'.
have Hvt := Hvtag _ _ Hamap Hcell.
have [a2 [Hold2 _]] := Hregs r2 Hrra2.
clear Hm Hmrl.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hcell Hvt
  Hold2 Hvtag Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hcell Hvt Hold2 Hvtag Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc Hvt => w2 atag /= Hcell Hvrel Hcol Hisc Hvt.
case: atag Hcell Hcol Hisc Hvt
  => avt ac aent aisc /= Hcell Hcol Hisc Hvt.
subst avt ac aisc.
subst w1.
case: a2 Hold2 => oldv oldt Hold2.
have Hupd1 := updm_id Hs1.
have Hupdm := updm_id Hcell.
have Hupd2 := updm_from_get (w2@LRC.Invalidated) Hold2.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat r2)) (w2@LRC.Invalidated))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_load_any;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hcell
    | exact Hold2 | exact Hupd1 | exact Hupdm | exact Hupd2]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset Hu;
      have Ht : LRC.Invalidated = LRC.Other
                \/ LRC.Invalidated = LRC.Invalidated;
      [by right
      | exact: (@regs_rel_w_set_undef bmap iregs mregs r2
                  (w2@LRC.Invalidated) Ht Hregs)]).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset; exact: (HS _ _ _ _ Hamap Hcell Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IStore: silent step writing an own-component data cell; the me memory
   changes by one setm; the code region survives because the target cell
   is a data cell while encoded cells are code-tagged *)
Lemma diag_store (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (bp : Block.id) (op : Z)
    (w2 : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.store imem (Pointer.component ipc, bp, op)
    (Intermediate.Register.get r2 iregs) = Some imem' ->
  loadable imem (Pointer.component ipc, bp, op) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Other) ->
  val_rel_b bmap (Intermediate.Register.get r2 iregs) w2 ->
  (forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Other) ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  (forall base w oldv ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r2)) = Some (w@LRC.Other) ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (oldv@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                        false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
        (setm (Symbolic.mem ms)
           (@word_of_nat (word_size mt) (base + Z.to_nat op))
           (w@(LRC.MTag LRC.Other (Pointer.component ipc) ent false)))
        (Symbolic.regs ms) mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IStore r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem' iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hptr Hoffp Hstore Hloadable Hs2 Hvr2 Hvtag Hct HS
  Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: Hloadable => vold Hloadold.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hloadold.
have Eb : base' = base by congruence.
subst base'.
have Hvt := Hvtag _ _ Hamap Hcell.
have Hmem' := mem_rel_store
  (tg := LRC.MTag LRC.Other (Pointer.component ipc) (entry (taga a))
           false)
  Hmem Hstore Hamap Hvr2 (erefl _) (erefl _).
clear Hm Hmrl.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hs2 Hcell Hvt
  Hvtag Hmem' Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hs2 Hcell Hvt Hvtag Hmem' Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc Hvt Hmem'
  => vo atag /= Hcell Hvrel Hcol Hisc Hvt Hmem'.
case: atag Hcell Hcol Hisc Hvt Hmem'
  => avt ac aent aisc /= Hcell Hcol Hisc Hvt Hmem'.
subst avt ac aisc.
subst w1.
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_id Hs2.
have Hupdm := updm_from_get
  (w2@(LRC.MTag LRC.Other (Pointer.component ipc) aent false)) Hcell.
exists (@Symbolic.State mt lrc_tags _
  (setm mmem
     (@word_of_nat (word_size mt) (base + Z.to_nat op))
     (w2@(LRC.MTag LRC.Other (Pointer.component ipc) aent false)))
  mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_store;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hs2
    | exact Hcell | exact Hupd1 | exact Hs2 | exact Hupd2
    | exact Hupdm]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem').
  + abstract (exact Hregs).
  + (* code region survives: the target is a data cell *)
    abstract (
      move=> w a Henc;
      rewrite setmE;
      case: eqP => [Ew | _];
      [ exfalso;
        move: (Hcode _ _ Henc); rewrite Ew Hcell;
        case=> Ea; move: (Hct _ _ Henc); rewrite -Ea /=; by []
      | exact: (Hcode _ _ Henc) ]).
  + abstract (exact: (HS _ _ _ _ _ Hamap Hs2 Hcell Hstack)).
  + abstract (exact Htot).
Qed.

(* IStore of a cross-invalidated register (Undef on the I side): the
   Invalidated tag moves into the cell; the old cell tag is arbitrary *)
Lemma diag_store_inv (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 r2 : Machine.register) (bp : Block.id) (op : Z)
    (w2 : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.store imem (Pointer.component ipc, bp, op)
    (Intermediate.Register.get r2 iregs) = Some imem' ->
  loadable imem (Pointer.component ipc, bp, op) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r2))
    = Some (w2@LRC.Invalidated) ->
  val_rel_b bmap (Intermediate.Register.get r2 iregs) w2 ->
  (forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Other) ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  (forall base w oldv ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r2)) = Some (w@LRC.Invalidated) ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (oldv@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                        false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
        (setm (Symbolic.mem ms)
           (@word_of_nat (word_size mt) (base + Z.to_nat op))
           (w@(LRC.MTag LRC.Invalidated (Pointer.component ipc) ent
                 false)))
        (Symbolic.regs ms) mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IStore r1 r2) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem' iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hptr Hoffp Hstore Hloadable Hs2 Hvr2 Hvtag Hct HS
  Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: Hloadable => vold Hloadold.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hloadold.
have Eb : base' = base by congruence.
subst base'.
have Hvt := Hvtag _ _ Hamap Hcell.
have Hmem' := mem_rel_store
  (tg := LRC.MTag LRC.Invalidated (Pointer.component ipc)
           (entry (taga a)) false)
  Hmem Hstore Hamap Hvr2 (erefl _) (erefl _).
clear Hm Hmrl.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hs2 Hcell
  Hvt Hvtag Hmem' Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hs2 Hcell Hvt Hvtag Hmem' Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc Hvt Hmem'
  => vo atag /= Hcell Hvrel Hcol Hisc Hvt Hmem'.
case: atag Hcell Hcol Hisc Hvt Hmem'
  => avt ac aent aisc /= Hcell Hcol Hisc Hvt Hmem'.
subst avt ac aisc.
subst w1.
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_id Hs2.
have Hupdm := updm_from_get
  (w2@(LRC.MTag LRC.Invalidated (Pointer.component ipc) aent false))
  Hcell.
exists (@Symbolic.State mt lrc_tags _
  (setm mmem
     (@word_of_nat (word_size mt) (base + Z.to_nat op))
     (w2@(LRC.MTag LRC.Invalidated (Pointer.component ipc) aent
            false)))
  mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_store_inv;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hs2
    | exact Hcell | exact Hupd1 | exact Hs2 | exact Hupd2
    | exact Hupdm]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem').
  + abstract (exact Hregs).
  + abstract (
      move=> w a Henc;
      rewrite setmE;
      case: eqP => [Ew | _];
      [ exfalso;
        move: (Hcode _ _ Henc); rewrite Ew Hcell;
        case=> Ea; move: (Hct _ _ Henc); rewrite -Ea /=; by []
      | exact: (Hcode _ _ Henc) ]).
  + abstract (exact: (HS _ _ _ _ _ Hamap Hs2 Hcell Hstack)).
  + abstract (exact Htot).
Qed.

(* ILoad into R_RA (the compiled pop-R_RA site): the cell's value tag —
   whatever it is — moves into R_RA and the cell is retagged by
   [switch_val].  R_RA is outside [regs_rel_w], the cell's word does not
   change, so the match relation survives with only the SINV-threading
   premise position-conditioned. *)
Lemma diag_load_ra (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 : Machine.register) (bp : Block.id) (op : Z) (v : value) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
  Intermediate.Register.set R_RA v iregs = iregs' ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  (forall base w2 cvt ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem (Intermediate.Register.set R_RA v iregs)
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
           mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (ILoad r1 R_RA) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILoad r1 R_RA) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs' (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hptr Hoffp Hload Hset Hct HS Hterm Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hload.
have Eb : base' = base by congruence.
subst base'.
have [aold Hold] := Htot 4 isT.
clear Hm Hmrl.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hcell Hold
  Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hcell Hold Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc => w2 atag /= Hcell Hvrel Hcol Hisc.
case: atag Hcell Hcol Hisc
  => avt ac aent aisc /= Hcell Hcol Hisc.
subst ac aisc.
subst w1.
case: aold Hold => oldv oldt Hold.
have Hold' : getm mregs
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA)) = Some (oldv@oldt)
  := Hold.
have Hupd1 := updm_id Hs1.
have Hupdm := updm_from_get
  (w2@(LRC.MTag (if LRC.is_address avt then LRC.Invalidated
                 else LRC.Other) (Pointer.component ipc) aent false))
  Hcell.
have Hupd2 := updm_from_get (w2@avt) Hold'.
exists (@Symbolic.State mt lrc_tags _
  (setm mmem
     (@word_of_nat (word_size mt) (base + Z.to_nat op))
     (w2@(LRC.MTag (if LRC.is_address avt then LRC.Invalidated
                    else LRC.Other) (Pointer.component ipc) aent false)))
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat R_RA)) (w2@avt))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_load_any;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hcell
    | exact Hold' | exact Hupd1 | exact Hupdm | exact Hupd2]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact: (mem_rel_retag _ Hmem Hcell)).
  + abstract (rewrite -Hset;
      exact: (regs_rel_w_set_ra _ (regs_rel_w_iset_ra v Hregs))).
  + (* code region survives: the target is a data cell *)
    abstract (
      move=> w a Henc;
      rewrite setmE;
      case: eqP => [Ew | _];
      [ exfalso;
        move: (Hcode _ _ Henc); rewrite Ew Hcell;
        case=> Ea; move: (Hct _ _ Henc); rewrite -Ea /=; by []
      | exact: (Hcode _ _ Henc) ]).
  + abstract (rewrite -Hset; exact: (HS _ _ _ _ _ Hamap Hcell Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* IStore of R_RA (the compiled push-R_RA site): R_RA's value tag —
   whatever it is — moves into the cell and R_RA is retagged by
   [switch_val].  The I side stores Undef (the I-side R_RA is clobbered
   by IJal), which relates to any word, so the match relation survives. *)
Lemma diag_store_ra (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r1 : Machine.register) (bp : Block.id) (op : Z) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  r1 <> R_RA ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  (0 <= op)%Z ->
  Memory.Memory.store imem (Pointer.component ipc, bp, op)
    (Intermediate.Register.get R_RA iregs) = Some imem' ->
  loadable imem (Pointer.component ipc, bp, op) ->
  Intermediate.Register.get R_RA iregs = Undef ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  (forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Other \/ vtag (taga a) = LRC.Invalidated) ->
  (forall base w2 ts oldv oldvt ent mpc',
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_RA)) = Some (w2@ts) ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (oldv@(LRC.MTag oldvt (Pointer.component ipc) ent false)) ->
      oldvt = LRC.Other \/ oldvt = LRC.Invalidated ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
           (setm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
              (w2@(LRC.MTag ts (Pointer.component ipc) ent false)))
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
              (w2@(if LRC.is_address ts then LRC.Invalidated
                   else LRC.Other)))
           mpc' tt)) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IStore r1 R_RA) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IStore r1 R_RA) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem' iregs (Pointer.inc ipc) ms'.
Proof.
move=> Hb Hin Hrra1 Hptr Hoffp Hstore Hloadable HraU Hct Hvt2 HS Hterm
  Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Hnund : Intermediate.Register.get r1 iregs <> Undef.
{ by rewrite Hptr. }
have [w1 [Hs1 Hvr1]] := regs_rel_w_get Hregs Hrra1 Hnund.
rewrite Hptr in Hvr1.
case: Hvr1 => base [Hamap Hw1].
rewrite (won_addz base Hoffp) in Hw1.
case: Hloadable => vold Hloadold.
case: (Hmem) => Hmrl _ _.
have [base' [a [Hamap' Hcell Hvrel Hcol Hisc]]] := Hmrl _ _ _ _ Hloadold.
have Eb : base' = base by congruence.
subst base'.
have Hovt := Hvt2 _ _ Hamap Hcell.
have [ara Hra] := Htot 4 isT.
clear Hm Hmrl Hvt2.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs1 Hcell Hra Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs1 Hcell Hra Htot.
subst pcv pct.
case: a Hcell Hvrel Hcol Hisc Hovt
  => vo atag /= Hcell Hvrel Hcol Hisc Hovt.
case: atag Hcell Hcol Hisc Hovt
  => avt ac aent aisc /= Hcell Hcol Hisc Hovt.
subst ac aisc.
subst w1.
have Hovt' : avt = LRC.Other \/ avt = LRC.Invalidated := Hovt.
case: ara Hra => w2 ts Hra.
have Hra' : getm mregs
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA)) = Some (w2@ts)
  := Hra.
have Hvr2 : val_rel_b bmap (Intermediate.Register.get R_RA iregs) w2.
{ by rewrite HraU. }
have Hmem' := mem_rel_store
  (tg := LRC.MTag ts (Pointer.component ipc) aent false)
  Hmem Hstore Hamap Hvr2 (erefl _) (erefl _).
have Hupd1 := updm_id Hs1.
have Hupd2 := updm_from_get
  (w2@(if LRC.is_address ts then LRC.Invalidated else LRC.Other)) Hra'.
have Hupdm := updm_from_get
  (w2@(LRC.MTag ts (Pointer.component ipc) aent false)) Hcell.
exists (@Symbolic.State mt lrc_tags _
  (setm mmem
     (@word_of_nat (word_size mt) (base + Z.to_nat op))
     (w2@(LRC.MTag ts (Pointer.component ipc) aent false)))
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat R_RA))
     (w2@(if LRC.is_address ts then LRC.Invalidated else LRC.Other)))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_store_any;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact Hcode | rewrite rcom_key; exact Hrc | exact Hs1 | exact Hra'
    | exact Hcell | exact Hupd1 | exact Hra' | exact Hupd2
    | exact Hupdm]).
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact Hmem').
  + abstract (exact: (regs_rel_w_set_ra _ Hregs)).
  + (* code region survives: the target is a data cell *)
    abstract (
      move=> w a Henc;
      rewrite setmE;
      case: eqP => [Ew | _];
      [ exfalso;
        move: (Hcode _ _ Henc); rewrite Ew Hcell;
        case=> Ea; move: (Hct _ _ Henc); rewrite -Ea /=; by []
      | exact: (Hcode _ _ Henc) ]).
  + abstract (exact: (HS _ _ _ _ _ _ _ Hamap Hra' Hcell Hovt' Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

(* ==================== control-flow diagram cases ==================== *)

Section DiagStatics.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).
Hypothesis Huniq_a : forall cid Cprocs0 l0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.
Hypothesis Huniq_b : forall cid Cprocs0 l0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.

(* IBnz, taken: silent jump to the label's position [tpc] in the same
   procedure; the label/forward/fit facts come pinned to the match's
   procedure code *)
Lemma diag_bnz_nz (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc tpc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (r : Machine.register) (l : nat) (w : mword mt) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  Pointer.component tpc = Pointer.component ipc ->
  Pointer.block tpc = Pointer.block ipc ->
  (0 <= Pointer.offset tpc)%Z ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r))
    = Some (w@LRC.Other) ->
  (w == 0%w) = false ->
  (forall Cprocs (j : nat) P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      Pointer.block ipc
        = proc_nb0 ilp (Pointer.component ipc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IBnz r l) ->
      [/\ List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
            = Some (ILabel l),
          side_flat_pos (Pointer.component ipc) P0 Pcode
            (Z.to_nat (Pointer.offset ipc))
          <= side_flat_pos (Pointer.component ipc) P0 Pcode
               (Z.to_nat (Pointer.offset tpc))
        & (pc0 + (side_flat_pos (Pointer.component ipc) P0 Pcode
                    (Z.to_nat (Pointer.offset tpc)) + 0))
          - (pc0 + side_flat_pos (Pointer.component ipc) P0 Pcode
                     (Z.to_nat (Pointer.offset ipc)))
          < 2 ^ imm_size mt]) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                  (Symbolic.regs ms) mpc' tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps imem iregs tpc ms'.
Proof.
move=> Hb Hin Hcomp' Hblk' Hofft Hs Hw Hlabel HS Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [HPt Hfwd Himm] := Hlabel _ _ _ _ Hside HgetP Hblk Hjnth Hnth.
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
clear Hm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Hs Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Hs Htot.
subst pcv pct.
have Hupd := updm_id Hs.
exists (@Symbolic.State mt lrc_tags _ mmem mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset tpc)) + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply (sim_bnz_nz Hlab_a Hcomp_a Hlab_b Hcomp_b Hdisj
    Huniq_a Huniq_b);
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact HgetP
    | exact HPt | exact Hfwd | exact Himm | exact Hcode
    | rewrite rcom_key; exact Hrc | exact Hs | exact Hw | exact Hupd]).
- constructor => /=.
  + abstract (apply: (pc_rel_at Hilp Hblk Hjnth Hcomp' Hblk' Hofft);
      by []).
  + abstract (exact Hmem).
  + abstract (exact Hregs).
  + abstract (exact Hcode).
  + abstract (exact: (HS _ Hstack)).
  + abstract (exact Htot).
Qed.

End DiagStatics.

(* IJump: the intra-component stack return — pops the gps to [tpc]; the
   R_RA fact and the frame's decomposition are the SINV clause, taken
   here as the [Hframe] premise *)
Lemma diag_jump (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps gps' : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc tpc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  gps = tpc :: gps' ->
  Pointer.component tpc = Pointer.component ipc ->
  (forall Cprocs,
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
                       (side_flat_pos (Pointer.component ipc) P0' Pcode'
                          (Z.to_nat (Pointer.offset tpc)) + pc0))
                      @LRC.InternalJump)
          & exists i'',
              List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
              = Some i'']) ->
  (forall mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps' imem iregs tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                   (Symbolic.regs ms) mpc' tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc IJump ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap gps' imem iregs tpc ms'.
Proof.
move=> Hb Hin Hgps Hcomp' Hframe HS Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [j' [P0' [Pcode' [Hblk' Hjnth' Hofft HRA [i'' Hnth'']]]]]
  := Hframe _ Hilp.
have HgetP' : getm Cprocs P0' = Some Pcode'.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ Hjnth'). }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Elvl : cross_frames (Pointer.component ipc) gps
            = cross_frames (Pointer.component ipc) gps'.
{ by rewrite Hgps /= Hcomp' eqxx. }
(* the target cell *)
have [mit Hcellt] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers
     (side_of (Pointer.component ipc)))) (Pointer.component ipc) i''.
have [vt [Hvt Htt _]]
  := side_encoded_fetch Hb Hside HgetP' Hnth'' (isize_gt0 i'') Hcellt.
rewrite addn0 in Hvt.
clear Hm Hframe.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Htot HRA
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Htot HRA.
subst pcv pct.
case: vt Hvt Htt => nvt nttag Hvt /= Htt; subst nttag.
(* the eleven clear registers from totality *)
have [a1 Hc1] := Htot 1 isT.
have [a0 Hc0] := Htot 0 isT.
have [a2 Hc2] := Htot 2 isT.
have [a3 Hc3] := Htot 3 isT.
have [a5 Hc5] := Htot 5 isT.
have [a6 Hc6] := Htot 6 isT.
have [a7 Hc7] := Htot 7 isT.
have [a16 Hc16] := Htot 16 isT.
have [a17 Hc17] := Htot 17 isT.
have [a18 Hc18] := Htot 18 isT.
have [a19 Hc19] := Htot 19 isT.
case: a1 Hc1 => v1 t1 Hc1.
case: a0 Hc0 => v0 t0 Hc0.
case: a2 Hc2 => v2 t2 Hc2.
case: a3 Hc3 => v3 t3 Hc3.
case: a5 Hc5 => v5 t5 Hc5.
case: a6 Hc6 => v6 t6 Hc6.
case: a7 Hc7 => v7 t7 Hc7.
case: a16 Hc16 => v16 t16 Hc16.
case: a17 Hc17 => v17 t17 Hc17.
case: a18 Hc18 => v18 t18 Hc18.
case: a19 Hc19 => v19 t19 Hc19.
exists (@Symbolic.State mt lrc_tags _ mmem mregs
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0' Pcode'
      (Z.to_nat (Pointer.offset tpc)) + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply sim_jump_intra;
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hcode
    | exact (Hcode _ _ Hvt) | rewrite rcom_key; exact Hrc | exact HRA
    | exact Hc1 | exact Hc0 | exact Hc2 | exact Hc3 | exact Hc5
    | exact Hc6 | exact Hc7 | exact Hc16 | exact Hc17 | exact Hc18
    | exact Hc19]).
- constructor => /=.
  + abstract (
      exists Cprocs, j', P0', Pcode';
      rewrite Hcomp';
      split;
      [ exact Hilp | exact Hblk' | exact Hjnth' | exact Hofft
      | rewrite -Elvl; by split ]).
  + abstract (exact Hmem).
  + abstract (exact Hregs).
  + abstract (exact Hcode).
  + abstract (exact: (HS _ Hstack)).
  + abstract (exact Htot).
Qed.

(* IHalt: final-state correspondence — the me pc sits on the encoded
   Halt cell, which is code-tagged *)
Lemma diag_halt
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc IHalt ->
  exists (iw : mword mt) (itag : mem_tag),
    [/\ getm (Symbolic.mem ms) (vala (Symbolic.pc ms)) = Some (iw@itag),
        Types.decode_instr iw = Some (Types.Halt mt)
      & is_code itag = true].
Proof.
move=> Hb Hin Hm Hex.
case: (Hm) => Hpc _ _ Hcode _ _.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] _]]]]]
  := lm_fetch Hin Hpc Hex.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L)
       (memory_lengths (Intermediate.prog_buffers
          (side_of (Pointer.component ipc))))
       (instr_to_transitional (Pointer.component ipc) IHalt)) 0
    = Some (MrHalt, def_mem_tag (Pointer.component ipc) true) by [].
have [v [Hv Ht Hdec]]
  := side_encoded_fetch Hb Hside HgetP Hnth (isize_gt0 IHalt) Hcell.
rewrite addn0 in Hv Hdec.
case: v Hv Ht Hdec => iw itag Hv /= Ht Hdec; subst itag.
clear Hm.
case: ms Hpc Hcode Hval Htag
  => mmem mregs [pcv pct] [] Hpc Hcode /= Hval Htag.
subst pcv pct.
exists iw, (def_mem_tag (Pointer.component ipc) true).
split.
- exact (Hcode _ _ Hv).
- move: Hdec => /= Hdec. exact Hdec.
- by [].
Qed.

(* stepping a getm over a setm at a distinct literal working key *)
Lemma getm_set_other (mregs : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (i k : nat) :
  i < 32 -> k < 32 -> (k == i) = false ->
  getm (setm mregs (word.as_word (ssrint.Posz i)) x)
    (word.as_word (ssrint.Posz k))
  = getm mregs (word.as_word (ssrint.Posz k)).
Proof. move=> Hi Hk Hki. by rewrite setmE as_eqE // Hki. Qed.

(* IReturn: the evented cross-component return — pops [tpc] (a foreign
   frame), emits ERet, invalidates everything but rcom; the frame facts
   and the event-value correspondence are premises (SINV + fit) *)
Lemma diag_return (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps gps' : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc tpc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) (ret_arg : Z) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  gps = tpc :: gps' ->
  (Pointer.component ipc == Pointer.component tpc) = false ->
  Intermediate.Register.get R_COM iregs = Int ret_arg ->
  (forall w t,
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
      Symbolic.convert (word.int_of_word w) = ret_arg) ->
  (exists Cprocs' j' P0' Pcode',
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
                     (side_flat_pos (Pointer.component tpc) P0' Pcode'
                        (Z.to_nat (Pointer.offset tpc)) + pc0))
                    @(LRC.Ret (cross_frames (Pointer.component tpc)
                                 gps')))
        & exists i'',
            List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
            = Some i'']) ->
  (forall mregs' mpc',
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps' imem (Intermediate.Register.invalidate iregs) tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
                   mregs' mpc' tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc IReturn ->
  exists ms',
    step_me (NC := NC) ms ms'
      (Some (Events.ERet (Pointer.component ipc) ret_arg
               (Pointer.component tpc)))
    /\ lin_match SINV bmap gps' imem
         (Intermediate.Register.invalidate iregs) tpc ms'.
Proof.
move=> Hb Hin Hgps Hneq Hcom Hevent Hframe HS Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
case: Hframe => Cprocs' [j'] [P0'] [Pcode']
  [Hilp' Hblk' Hjnth' [Hofft HRA] [i'' Hnth'']].
have HgetP' : getm Cprocs' P0' = Some Pcode'.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ Hjnth'). }
have Hside' : Intermediate.prog_procedures
                (side_of (Pointer.component tpc)) (Pointer.component tpc)
              = Some Cprocs'.
{ move: Hilp'.
  have -> : Intermediate.prog_procedures ilp
            = unionm (Intermediate.prog_procedures pra)
                     (Intermediate.prog_procedures prb) by [].
  rewrite /side_of unionmE.
  case Hd: (Pointer.component tpc
            \in domm (Intermediate.prog_procedures pra)).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _). }
have Hnund : Intermediate.Register.get R_COM iregs <> Undef.
{ by rewrite Hcom. }
have Hcr : R_COM <> R_RA by [].
have [rcv [Hrcv _]] := regs_rel_w_get Hregs Hcr Hnund.
have Hev := Hevent _ _ Hrcv.
have Elvl : cross_frames (Pointer.component ipc) gps
            = (cross_frames (Pointer.component tpc) gps').+1.
{ rewrite Hgps /=.
  by rewrite eq_sym Hneq. }
rewrite Elvl in Htag.
(* the target cell *)
have [mit Hcellt] := cell_exp0
  (memory_lengths (Intermediate.prog_buffers
     (side_of (Pointer.component tpc)))) (Pointer.component tpc) i''.
have [vt [Hvt Htt _]]
  := side_encoded_fetch Hb Hside' HgetP' Hnth'' (isize_gt0 i'') Hcellt.
rewrite addn0 in Hvt.
clear Hm Hevent.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrcv HRA Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrcv HRA Htot.
subst pcv pct.
case: vt Hvt Htt => nvt nttag Hvt /= Htt; subst nttag.
have [a0 Hc0] := Htot 0 isT.
have [a2 Hc2] := Htot 2 isT.
have [a3 Hc3] := Htot 3 isT.
have [a5 Hc5] := Htot 5 isT.
have [a6 Hc6] := Htot 6 isT.
have [a7 Hc7] := Htot 7 isT.
have [a16 Hc16] := Htot 16 isT.
have [a17 Hc17] := Htot 17 isT.
have [a18 Hc18] := Htot 18 isT.
have [a19 Hc19] := Htot 19 isT.
case: a0 Hc0 => v0 t0 Hc0.
case: a2 Hc2 => v2 t2 Hc2.
case: a3 Hc3 => v3 t3 Hc3.
case: a5 Hc5 => v5 t5 Hc5.
case: a6 Hc6 => v6 t6 Hc6.
case: a7 Hc7 => v7 t7 Hc7.
case: a16 Hc16 => v16 t16 Hc16.
case: a17 Hc17 => v17 t17 Hc17.
case: a18 Hc18 => v18 t18 Hc18.
case: a19 Hc19 => v19 t19 Hc19.
have Hc1' : getm mregs (word.as_word (ssrint.Posz 1))
            = Some (rcv@LRC.Other).
{ exact Hrcv. }
have HRA' : getm mregs
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
            = Some ((word_of_nat
                       (side_flat_pos (Pointer.component tpc) P0' Pcode'
                          (Z.to_nat (Pointer.offset tpc)) + pc0))
                      @(LRC.Ret (cross_frames (Pointer.component tpc)
                                   gps'))).
{ exact HRA. }
(* the invalidation thread *)
have HuA := updm_from_get
  ((word_of_nat (side_flat_pos (Pointer.component tpc) P0' Pcode'
      (Z.to_nat (Pointer.offset tpc)) + pc0))@LRC.Invalidated) HRA'.
set raK := @word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat R_RA).
have HdB : getm (setm mregs raK
             ((word_of_nat (side_flat_pos (Pointer.component tpc) P0'
                 Pcode' (Z.to_nat (Pointer.offset tpc)) + pc0))
                @LRC.Invalidated)) raK
           = Some ((word_of_nat (side_flat_pos (Pointer.component tpc)
                      P0' Pcode' (Z.to_nat (Pointer.offset tpc)) + pc0))
                     @LRC.Invalidated).
{ by rewrite setmE eqxx. }
have HuB := updm_from_get
  ((word_of_nat (side_flat_pos (Pointer.component tpc) P0' Pcode'
      (Z.to_nat (Pointer.offset tpc)) + pc0))@LRC.Invalidated) HdB.
rewrite setmxx in HuB.
have Hd1 : getm (setm mregs raK
             ((word_of_nat (side_flat_pos (Pointer.component tpc) P0'
                 Pcode' (Z.to_nat (Pointer.offset tpc)) + pc0))
                @LRC.Invalidated)) (word.as_word (ssrint.Posz 1))
           = Some (rcv@LRC.Other).
{ by rewrite /raK getm_set_ra_other. }
have Hd0 : getm (setm mregs raK
             ((word_of_nat (side_flat_pos (Pointer.component tpc) P0'
                 Pcode' (Z.to_nat (Pointer.offset tpc)) + pc0))
                @LRC.Invalidated)) (word.as_word (ssrint.Posz 0))
           = Some (v0@t0).
{ by rewrite /raK getm_set_ra_other. }
have Hu0 := updm_from_get (v0@LRC.Invalidated) Hd0.
set M1 := setm mregs raK _ in Hd1 Hd0 Hu0 HdB HuB.
set M2 := setm M1 _ _ in Hu0.
have Hd2 : getm M2 (word.as_word (ssrint.Posz 2)) = Some (v2@t2).
{ by rewrite /M2 /M1 getm_set_other // /raK getm_set_ra_other. }
have Hu2 := updm_from_get (v2@LRC.Invalidated) Hd2.
set M3 := setm M2 _ _ in Hu2.
have Hd3 : getm M3 (word.as_word (ssrint.Posz 3)) = Some (v3@t3).
{ by rewrite /M3 /M2 /M1 !getm_set_other // /raK getm_set_ra_other. }
have Hu3 := updm_from_get (v3@LRC.Invalidated) Hd3.
set M4 := setm M3 _ _ in Hu3.
have Hd5 : getm M4 (word.as_word (ssrint.Posz 5)) = Some (v5@t5).
{ by rewrite /M4 /M3 /M2 /M1 !getm_set_other // /raK getm_set_ra_other. }
have Hu5 := updm_from_get (v5@LRC.Invalidated) Hd5.
set M5 := setm M4 _ _ in Hu5.
have Hd6 : getm M5 (word.as_word (ssrint.Posz 6)) = Some (v6@t6).
{ by rewrite /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu6 := updm_from_get (v6@LRC.Invalidated) Hd6.
set M6 := setm M5 _ _ in Hu6.
have Hd7 : getm M6 (word.as_word (ssrint.Posz 7)) = Some (v7@t7).
{ by rewrite /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu7 := updm_from_get (v7@LRC.Invalidated) Hd7.
set M7 := setm M6 _ _ in Hu7.
have Hd16 : getm M7 (word.as_word (ssrint.Posz 16)) = Some (v16@t16).
{ by rewrite /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu16 := updm_from_get (v16@LRC.Invalidated) Hd16.
set M8 := setm M7 _ _ in Hu16.
have Hd17 : getm M8 (word.as_word (ssrint.Posz 17)) = Some (v17@t17).
{ by rewrite /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu17 := updm_from_get (v17@LRC.Invalidated) Hd17.
set M9 := setm M8 _ _ in Hu17.
have Hd18 : getm M9 (word.as_word (ssrint.Posz 18)) = Some (v18@t18).
{ by rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu18 := updm_from_get (v18@LRC.Invalidated) Hd18.
set M10 := setm M9 _ _ in Hu18.
have Hd19 : getm M10 (word.as_word (ssrint.Posz 19)) = Some (v19@t19).
{ by rewrite /M10 /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu19 := updm_from_get (v19@LRC.Invalidated) Hd19.
rewrite -Hev.
eexists.
split.
- eapply sim_return.
  + exact Hb.
  + exact Hside.
  + exact HgetP.
  + exact Hnth.
  + exact Hcode.
  + exact (Hcode _ _ Hvt).
  + exact Hneq.
  + rewrite rcom_key. exact Hrcv.
  + exact HRA'.
  + rewrite ra_key4. exact HRA'.
  + exact Hc1'.
  + exact Hc0.
  + exact Hc2.
  + exact Hc3.
  + exact Hc5.
  + exact Hc6.
  + exact Hc7.
  + exact Hc16.
  + exact Hc17.
  + exact Hc18.
  + exact Hc19.
  + rewrite ra_key4. exact HuA.
  + exact HdB.
  + exact HuB.
  + exact Hd1.
  + exact Hd0.
  + exact Hu0.
  + exact Hd2.
  + exact Hu2.
  + exact Hd3.
  + exact Hu3.
  + exact Hd5.
  + exact Hu5.
  + exact Hd6.
  + exact Hu6.
  + exact Hd7.
  + exact Hu7.
  + exact Hd16.
  + exact Hu16.
  + exact Hd17.
  + exact Hu17.
  + exact Hd18.
  + exact Hu18.
  + exact Hd19.
  + exact Hu19.
- constructor => /=.
  + exists Cprocs', j', P0', Pcode'.
    split.
    * exact Hilp'.
    * exact Hblk'.
    * exact Hjnth'.
    * exact Hofft.
    * by split.
  + exact Hmem.
  + apply: (regs_rel_w_invalidate _ _ _ _ _ _ _ _ _ _ _ _ Hregs).
  + exact Hcode.
  + exact: (HS _ _ Hstack).
  + do !apply: regs_total_set.
    exact Htot.
Qed.

Section DiagStaticsCall.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).

(* ICall: TWO me-steps — the evented cross Jal onto the callee's entry
   cell, then the silent entry stutter to offset 0; registers invalidated
   but rcom, ra minted with the Ret capability *)
Lemma diag_call (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (C' : Component.id) (p : Procedure.id) (b : Block.id)
    (call_arg : Z) (cl : seq Component.id) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  (Pointer.component ipc == C') = false ->
  Intermediate.Register.get R_COM iregs = Int call_arg ->
  (forall w t,
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
      Symbolic.convert (word.int_of_word w) = call_arg) ->
  head_tag (side_of C') C' p = LRC.MTag LRC.Other C' (Some (p, cl)) true ->
  mem_seq cl (Pointer.component ipc) = true ->
  C' \in domm (Intermediate.prog_interface ilp) ->
  pc0 + side_entry_pos C' p < 2 ^ imm_size mt ->
  (exists CprocsC jc Pcode',
      [/\ Intermediate.prog_procedures ilp C' = Some CprocsC,
          b = proc_nb0 ilp C' + jc,
          List.nth_error (elementsm CprocsC) jc = Some (p, Pcode')
        & exists i0, List.nth_error Pcode' 0 = Some i0]) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (ICall C' p) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  (forall mregs' mpc' (Cprocs : NMap Machine.code) (j : nat)
          (P0 : Procedure.id) (Pcode : Machine.code),
      C' \in domm (Intermediate.prog_interface ilp) ->
      Intermediate.prog_procedures ilp (Pointer.component ipc)
        = Some Cprocs ->
      Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      (0 <= Pointer.offset ipc)%Z ->
      getm mregs'
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_RA))
        = Some ((@word_of_nat (word_size mt)
                   (side_flat_pos (Pointer.component ipc) P0 Pcode
                      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
                  @(LRC.Ret (cross_frames (Pointer.component ipc)
                               gps))) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap (Pointer.inc ipc :: gps) imem
        (Intermediate.Register.invalidate iregs) (C', b, 0%Z)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms) mregs' mpc'
           tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ICall C' p) ->
  exists ms1 ms2,
    [/\ step_me (NC := NC) ms ms1
          (Some (Events.ECall (Pointer.component ipc) p call_arg C')),
        step_me (NC := NC) ms1 ms2 None
      & lin_match SINV bmap (Pointer.inc ipc :: gps) imem
          (Intermediate.Register.invalidate iregs) (C', b, 0%Z) ms2].
Proof.
move=> Hb Hin Hneq Hcom Hevent Hhead Hentry HC'in Himm Hcallee Hterm HS
  Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
case: Hcallee => CprocsC [jc] [Pcode'] [HilpC HblkC HjnthC [i0 Hnth0]].
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have HgetPC : getm CprocsC p = Some Pcode'.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ HjnthC). }
have HsideC : Intermediate.prog_procedures (side_of C') C'
              = Some CprocsC.
{ move: HilpC.
  have -> : Intermediate.prog_procedures ilp
            = unionm (Intermediate.prog_procedures pra)
                     (Intermediate.prog_procedures prb) by [].
  rewrite /side_of unionmE.
  case Hd: (C' \in domm (Intermediate.prog_procedures pra)).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _).
  - by move: Hd; rewrite mem_domm;
      case: (Intermediate.prog_procedures pra _). }
have Hnund : Intermediate.Register.get R_COM iregs <> Undef.
{ by rewrite Hcom. }
have Hcr : R_COM <> R_RA by [].
have [rcv [Hrcv _]] := regs_rel_w_get Hregs Hcr Hnund.
have Hev := Hevent _ _ Hrcv.
have Elvl : cross_frames C' (Pointer.inc ipc :: gps)
            = (cross_frames (Pointer.component ipc) gps).+1.
{ by rewrite /= Pointer.inc_preserves_component Hneq. }
clear Hm Hevent Hterm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrcv Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrcv Htot.
subst pcv pct.
have [a4 Hc4] := Htot 4 isT.
have [a0 Hc0] := Htot 0 isT.
have [a2 Hc2] := Htot 2 isT.
have [a3 Hc3] := Htot 3 isT.
have [a5 Hc5] := Htot 5 isT.
have [a6 Hc6] := Htot 6 isT.
have [a7 Hc7] := Htot 7 isT.
have [a16 Hc16] := Htot 16 isT.
have [a17 Hc17] := Htot 17 isT.
have [a18 Hc18] := Htot 18 isT.
have [a19 Hc19] := Htot 19 isT.
case: a4 Hc4 => v4 t4 Hc4.
case: a0 Hc0 => v0 t0 Hc0.
case: a2 Hc2 => v2 t2 Hc2.
case: a3 Hc3 => v3 t3 Hc3.
case: a5 Hc5 => v5 t5 Hc5.
case: a6 Hc6 => v6 t6 Hc6.
case: a7 Hc7 => v7 t7 Hc7.
case: a16 Hc16 => v16 t16 Hc16.
case: a17 Hc17 => v17 t17 Hc17.
case: a18 Hc18 => v18 t18 Hc18.
case: a19 Hc19 => v19 t19 Hc19.
have Hc1' : getm mregs (word.as_word (ssrint.Posz 1))
            = Some (rcv@LRC.Other).
{ exact Hrcv. }
have Hc4' : getm mregs
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA)) = Some (v4@t4).
{ exact Hc4. }
(* the invalidation thread, ra minted with the Ret capability *)
pose reta : @ratom mt
  := ((@word_of_nat (word_size mt)
         (side_flat_pos (Pointer.component ipc) P0 Pcode
            (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
        @(LRC.Ret (cross_frames (Pointer.component ipc) gps))).
pose raK := @word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat R_RA).
have HuA := updm_from_get reta Hc4'.
have Hd1 : getm (setm mregs raK reta) (word.as_word (ssrint.Posz 1))
           = Some (rcv@LRC.Other).
{ by rewrite /raK getm_set_ra_other. }
have Hd0 : getm (setm mregs raK reta) (word.as_word (ssrint.Posz 0))
           = Some (v0@t0).
{ by rewrite /raK getm_set_ra_other. }
have Hu0 := updm_from_get (v0@LRC.Invalidated) Hd0.
set M1 := setm mregs raK reta in Hd1 Hd0 Hu0.
set M2 := setm M1 _ _ in Hu0.
have Hd2 : getm M2 (word.as_word (ssrint.Posz 2)) = Some (v2@t2).
{ by rewrite /M2 /M1 getm_set_other // /raK getm_set_ra_other. }
have Hu2 := updm_from_get (v2@LRC.Invalidated) Hd2.
set M3 := setm M2 _ _ in Hu2.
have Hd3 : getm M3 (word.as_word (ssrint.Posz 3)) = Some (v3@t3).
{ by rewrite /M3 /M2 /M1 !getm_set_other // /raK getm_set_ra_other. }
have Hu3 := updm_from_get (v3@LRC.Invalidated) Hd3.
set M4 := setm M3 _ _ in Hu3.
have Hd5 : getm M4 (word.as_word (ssrint.Posz 5)) = Some (v5@t5).
{ by rewrite /M4 /M3 /M2 /M1 !getm_set_other // /raK getm_set_ra_other. }
have Hu5 := updm_from_get (v5@LRC.Invalidated) Hd5.
set M5 := setm M4 _ _ in Hu5.
have Hd6 : getm M5 (word.as_word (ssrint.Posz 6)) = Some (v6@t6).
{ by rewrite /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu6 := updm_from_get (v6@LRC.Invalidated) Hd6.
set M6 := setm M5 _ _ in Hu6.
have Hd7 : getm M6 (word.as_word (ssrint.Posz 7)) = Some (v7@t7).
{ by rewrite /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu7 := updm_from_get (v7@LRC.Invalidated) Hd7.
set M7 := setm M6 _ _ in Hu7.
have Hd16 : getm M7 (word.as_word (ssrint.Posz 16)) = Some (v16@t16).
{ by rewrite /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu16 := updm_from_get (v16@LRC.Invalidated) Hd16.
set M8 := setm M7 _ _ in Hu16.
have Hd17 : getm M8 (word.as_word (ssrint.Posz 17)) = Some (v17@t17).
{ by rewrite /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu17 := updm_from_get (v17@LRC.Invalidated) Hd17.
set M9 := setm M8 _ _ in Hu17.
have Hd18 : getm M9 (word.as_word (ssrint.Posz 18)) = Some (v18@t18).
{ by rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu18 := updm_from_get (v18@LRC.Invalidated) Hd18.
set M10 := setm M9 _ _ in Hu18.
have Hd19 : getm M10 (word.as_word (ssrint.Posz 19)) = Some (v19@t19).
{ by rewrite /M10 /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1 !getm_set_other //
     /raK getm_set_ra_other. }
have Hu19 := updm_from_get (v19@LRC.Invalidated) Hd19.
set M11 := setm M10 _ _ in Hu19.
(* rcom survives the whole thread *)
have Hrc11 : getm M11 (word.as_word (ssrint.Posz 1))
             = Some (rcv@LRC.Other).
{ by rewrite /M11 /M10 /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1
     !getm_set_other // /raK getm_set_ra_other. }
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have HraM11' : getm M11 (word.as_word (ssrint.Posz 4)) = Some reta.
{ have F11 : getm M11 (word.as_word (ssrint.Posz 4))
             = getm M10 (word.as_word (ssrint.Posz 4))
    by rewrite /M11 getm_set_other.
  have F10 : getm M10 (word.as_word (ssrint.Posz 4))
             = getm M9 (word.as_word (ssrint.Posz 4))
    by rewrite /M10 getm_set_other.
  have F9 : getm M9 (word.as_word (ssrint.Posz 4))
            = getm M8 (word.as_word (ssrint.Posz 4))
    by rewrite /M9 getm_set_other.
  have F8 : getm M8 (word.as_word (ssrint.Posz 4))
            = getm M7 (word.as_word (ssrint.Posz 4))
    by rewrite /M8 getm_set_other.
  have F7 : getm M7 (word.as_word (ssrint.Posz 4))
            = getm M6 (word.as_word (ssrint.Posz 4))
    by rewrite /M7 getm_set_other.
  have F6 : getm M6 (word.as_word (ssrint.Posz 4))
            = getm M5 (word.as_word (ssrint.Posz 4))
    by rewrite /M6 getm_set_other.
  have F5 : getm M5 (word.as_word (ssrint.Posz 4))
            = getm M4 (word.as_word (ssrint.Posz 4))
    by rewrite /M5 getm_set_other.
  have F4 : getm M4 (word.as_word (ssrint.Posz 4))
            = getm M3 (word.as_word (ssrint.Posz 4))
    by rewrite /M4 getm_set_other.
  have F3 : getm M3 (word.as_word (ssrint.Posz 4))
            = getm M2 (word.as_word (ssrint.Posz 4))
    by rewrite /M3 getm_set_other.
  have F2 : getm M2 (word.as_word (ssrint.Posz 4))
            = getm M1 (word.as_word (ssrint.Posz 4))
    by rewrite /M2 getm_set_other.
  by rewrite F11 F10 F9 F8 F7 F6 F5 F4 F3 F2 /M1 /raK
     getm_set_ra_self. }
have HraM11 : getm M11
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_RA)) = Some reta.
{ exact HraM11'. }
rewrite -Hev.
exists (@Symbolic.State mt lrc_tags _ mmem M11
  ((word_of_nat (side_entry_pos C' p + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps).+1 C')) tt).
eexists.
split.
- eapply (sim_call Hlab_a Hcomp_a Hlab_b Hcomp_b Hproc_a Hproc_b).
  + exact Hdisj.
  + exact Hb.
  + exact Hside.
  + exact HgetP.
  + exact Hnth.
  + exact Hnth'.
  + exact HsideC.
  + exact HgetPC.
  + exact Hneq.
  + exact Hhead.
  + exact Hentry.
  + exact Himm.
  + exact Hcode.
  + rewrite rcom_key. exact Hrcv.
  + rewrite ra_key4. exact Hc4'.
  + exact Hc1'.
  + exact Hc0.
  + exact Hc2.
  + exact Hc3.
  + exact Hc5.
  + exact Hc6.
  + exact Hc7.
  + exact Hc16.
  + exact Hc17.
  + exact Hc18.
  + exact Hc19.
  + rewrite ra_key4. exact HuA.
  + exact Hd1.
  + exact Hd0.
  + exact Hu0.
  + exact Hd2.
  + exact Hu2.
  + exact Hd3.
  + exact Hu3.
  + exact Hd5.
  + exact Hu5.
  + exact Hd6.
  + exact Hu6.
  + exact Hd7.
  + exact Hu7.
  + exact Hd16.
  + exact Hu16.
  + exact Hd17.
  + exact Hu17.
  + exact Hd18.
  + exact Hu18.
  + exact Hd19.
  + exact Hu19.
- eapply sim_entry_nop.
  + exact Hdisj.
  + exact Hb.
  + exact HsideC.
  + exact HgetPC.
  + exact Hnth0.
  + exact Hcode.
  + rewrite rcom_key. exact Hrc11.
- constructor => /=.
  + exists CprocsC, jc, p, Pcode'.
    split.
    * exact HilpC.
    * exact HblkC.
    * exact HjnthC.
    * by [].
    * rewrite Elvl. by split.
  + exact Hmem.
  + apply: regs_rel_w_invalidate.
    exact Hregs.
  + exact Hcode.
  + exact: (HS _ _ _ _ _ _ HC'in Hilp Hblk Hjnth Hoff HraM11 Hstack).
  + do !apply: regs_total_set.
    exact Htot.
Qed.

End DiagStaticsCall.

(* the syscall_ret register's key, VM-certified like rcom/ra *)
Lemma sret_key : (syscall_ret : reg mt) = word.as_word (ssrint.Posz 16).
Proof. by vm_compute. Qed.

(* key-spelling bridges for the alloc sequence's registers *)
Lemma key17E : @word_of_nat (reg_field_size mt)
                 (Merged.to_nat_bis (inr Merged.R_SC_ARG1))
               = word.as_word (ssrint.Posz 17).
Proof. by []. Qed.

Lemma key19E : @word_of_nat (reg_field_size mt)
                 (Merged.to_nat_bis (inr Merged.R_SC_ARG3))
               = word.as_word (ssrint.Posz 19).
Proof. by []. Qed.

Lemma key16E : @word_of_nat (reg_field_size mt)
                 (Merged.to_nat_bis (inr Merged.R_SC_RET))
               = word.as_word (ssrint.Posz 16).
Proof. by []. Qed.

Lemma key4E : @word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inl R_RA))
              = word.as_word (ssrint.Posz 4).
Proof. by []. Qed.

(* I-side register indices are < 7: walks over syscall-register writes *)
Lemma to_nat_lt7 (r : register) : Intermediate.Register.to_nat r < 7.
Proof. by case: r. Qed.

Lemma ra_key4b : (ra : reg mt)
  = @word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl R_RA)).
Proof. by vm_compute. Qed.

Lemma to_nat_bis_lt32 (kb : register + Merged.sys_reg) :
  Merged.to_nat_bis kb < 32.
Proof. by case: kb => [r|s]; [case: r | case: s]. Qed.

(* getm through a setm at a to_nat_bis-spelled key, distinct raw key *)
Lemma getm_set_bis_other (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (kb : register + Merged.sys_reg) (k : nat) :
  k < 32 -> (k == Merged.to_nat_bis kb) = false ->
  getm (setm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          x)
    (word.as_word (ssrint.Posz k))
  = getm m (word.as_word (ssrint.Posz k)).
Proof.
move=> Hk Hne.
rewrite setmE.
have -> : ((word.as_word (ssrint.Posz k) : reg mt)
           == @word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          = false.
{ rewrite eq_sym (won_as_eqE (to_nat_bis_lt32 kb) Hk).
  by rewrite eq_sym Hne. }
by [].
Qed.

(* getm through a setm, both keys to_nat_bis-spelled and distinct *)
Lemma getm_set_bis_bis (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (kb kb' : register + Merged.sys_reg) :
  (Merged.to_nat_bis kb' == Merged.to_nat_bis kb) = false ->
  getm (setm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          x)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb'))
  = getm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb')).
Proof.
move=> Hne.
rewrite setmE.
rewrite (won_eqE (small_lt_reg (to_nat_bis_lt32 kb'))
                 (small_lt_reg (to_nat_bis_lt32 kb))).
by rewrite Hne.
Qed.

Lemma as_won_eqE (k i : nat) :
  k < 32 -> i < 32 ->
  ((word.as_word (ssrint.Posz k) : reg mt)
   == @word_of_nat (reg_field_size mt) i) = (k == i).
Proof. move=> Hk Hi. by rewrite eq_sym (won_as_eqE Hi Hk) eq_sym. Qed.

(* the me machine's initial register file is total on the working keys:
   getm walks decided at the 5-bit KEY level only (32-bit values are
   never normalized — vm_compute would explode on the unary 2^32) *)
Lemma regs_total_reg0 : regs_total Merged.reg0.
Proof.
move=> k; rewrite /reg_keys !inE => Hk.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
case/orP: Hk => [/eqP ->|Hk];
  first by rewrite /Merged.reg0 mkfmapE /=
             !as_won_eqE //=; eexists.
by move/eqP: Hk => ->; rewrite /Merged.reg0 mkfmapE /=
     !as_won_eqE //=; eexists.
Qed.

(* the raw key HITS the to_nat_bis-spelled setm *)
Lemma getm_set_bis_hit (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (kb : register + Merged.sys_reg) (k : nat) :
  k < 32 -> (k == Merged.to_nat_bis kb) = true ->
  getm (setm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          x)
    (word.as_word (ssrint.Posz k))
  = Some x.
Proof.
move=> Hk Hke.
by rewrite setmE (as_won_eqE Hk (to_nat_bis_lt32 kb)) Hke.
Qed.

(* walking a to_nat_bis-spelled read over a RAW-keyed setm *)
Lemma getm_set_raw_other_bis (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (j : nat) (kb : register + Merged.sys_reg) :
  j < 32 -> (Merged.to_nat_bis kb == j) = false ->
  getm (setm m (word.as_word (ssrint.Posz j)) x)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
  = getm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb)).
Proof.
move=> Hj Hne.
by rewrite setmE (won_as_eqE (to_nat_bis_lt32 kb) Hj) Hne.
Qed.

Lemma getm_set_raw_hit_bis (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (j : nat) (kb : register + Merged.sys_reg) :
  j < 32 -> (Merged.to_nat_bis kb == j) = true ->
  getm (setm m (word.as_word (ssrint.Posz j)) x)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
  = Some x.
Proof.
move=> Hj Hke.
by rewrite setmE (won_as_eqE (to_nat_bis_lt32 kb) Hj) Hke.
Qed.

Lemma getm_set_raw_rcom (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (j : nat) :
  j < 32 -> (1 == j) = false ->
  getm (setm m (word.as_word (ssrint.Posz j)) x) rcom = getm m rcom.
Proof.
move=> Hj Hne.
rewrite setmE rcom_key (won_as_eqE (to_nat_lt32 R_COM) Hj).
by rewrite Hne -rcom_key.
Qed.

(* same, reading rcom (register 1) *)
Lemma getm_set_bis_rcom (m : {fmap reg mt -> @ratom mt})
    (x : @ratom mt) (kb : register + Merged.sys_reg) :
  (1 == Merged.to_nat_bis kb) = false ->
  getm (setm m (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          x) rcom
  = getm m rcom.
Proof.
move=> Hne.
rewrite setmE.
have -> : ((rcom : reg mt)
           == @word_of_nat (reg_field_size mt) (Merged.to_nat_bis kb))
          = false.
{ rewrite rcom_key
    (won_eqE (small_lt_reg (to_nat_lt32 R_COM))
             (small_lt_reg (to_nat_bis_lt32 kb))).
  exact Hne. }
by [].
Qed.

(* an I-register key never collides with a syscall-register key (≥ 16) *)
Lemma won_reg_neq_hi (r : register) (k : nat) :
  16 <= k < 32 ->
  ((@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r)
    : reg mt) == word.as_word (ssrint.Posz k)) = false.
Proof.
move=> /andP [Hlo Hhi].
rewrite won_as_eqE ?to_nat_lt32 //.
apply/negbTE/negP => /eqP E.
have := to_nat_lt7 r.
rewrite E => Hk7.
by lia.
Qed.

(* writes to syscall-register slots (raw keys ≥ 16) are invisible to the
   I-register relation *)
Lemma regs_rel_w_set_hi (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) (k : nat) (a : @ratom mt) :
  16 <= k < 32 ->
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap iregs (setm mregs (word.as_word (ssrint.Posz k)) a).
Proof.
move=> Hk Hrel r' Hra'.
have [a' [Hget Hd]] := Hrel r' Hra'.
exists a'; split=> //.
by rewrite setmE (won_reg_neq_hi r' Hk).
Qed.

(* same for the to_nat_bis-spelled syscall keys *)
Lemma regs_rel_w_set_bis_hi (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt})
    (s : Merged.sys_reg) (a : @ratom mt) :
  regs_rel_w bmap iregs mregs ->
  regs_rel_w bmap iregs
    (setm mregs
       (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inr s)))
       a).
Proof.
move=> Hrel r' Hra'.
have [a' [Hget Hd]] := Hrel r' Hra'.
exists a'; split=> //.
rewrite setmE.
have -> : ((@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat r') : reg mt)
           == @word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inr s))) = false.
{ rewrite (won_eqE (small_lt_reg (to_nat_lt32 r'))
                   (small_lt_reg (to_nat_bis_lt32 (inr s)))).
  apply/negbTE/negP => /eqP E.
  have H7 := to_nat_lt7 r'.
  by case: s E => /= E; rewrite E in H7. }
by [].
Qed.

(* nor with ra's key, when the register is not R_RA *)
Lemma won_reg_neq_ra (r : register) :
  r <> R_RA ->
  ((@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r)
    : reg mt)
   == @word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat R_RA)) = false.
Proof.
move=> Hne.
rewrite reg_key_eqE.
by apply/negbTE/negP => /eqP /to_nat_inj E; exact: Hne E.
Qed.

(* the six-me-step chain of IAlloc.  The syscall result [st4] and the
   code-region fact for its (grown) memory are premises; the final state
   is characterized through st4's fields and the fresh block's [max]. *)
Lemma diag_alloc_steps (NC : nat)
    (c : Component.id) (lvl : nat)
    (Cprocs : NMap Machine.code) (P0 : Procedure.id) (Pcode : Machine.code)
    (o : nat) (rptr rsize : Machine.register) (i' : Machine.instr)
    (mmem : {fmap mword mt -> matom}) (mregs : {fmap reg mt -> @ratom mt})
    (rc : @ratom mt)
    (wsz : mword mt) (v4 : mword mt) (t4 : LRC.value_tag)
    (a1 a3 a16 aptr : @ratom mt)
    (v1 v0 v2 v3 v5 v6 v7 v18 : mword mt)
    (t1 t0 t2 t3 t5 t6 t7 t18 : LRC.value_tag)
    (st4 : @Symbolic.state mt LRC.lrc_tags unit) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures (side_of c) c = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some (IAlloc rptr rsize) ->
  List.nth_error Pcode o.+1 = Some i' ->
  rptr <> R_RA ->
  getm mregs (word.as_word (ssrint.Posz 1)) = Some (v1@t1) ->
  getm mregs (word.as_word (ssrint.Posz 0)) = Some (v0@t0) ->
  getm mregs (word.as_word (ssrint.Posz 2)) = Some (v2@t2) ->
  getm mregs (word.as_word (ssrint.Posz 3)) = Some (v3@t3) ->
  getm mregs (word.as_word (ssrint.Posz 5)) = Some (v5@t5) ->
  getm mregs (word.as_word (ssrint.Posz 6)) = Some (v6@t6) ->
  getm mregs (word.as_word (ssrint.Posz 7)) = Some (v7@t7) ->
  getm mregs (word.as_word (ssrint.Posz 18)) = Some (v18@t18) ->
  code_region_ok mmem ->
  code_region_ok (Symbolic.mem st4) ->
  getm mmem (word_of_nat Merged.alloc_label) = None ->
  getm mregs rcom = Some rc ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inl rsize))) = Some (wsz@LRC.Other) ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inr Merged.R_SC_ARG1))) = Some a1 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inl R_RA)))
    = Some (v4@t4) ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inr Merged.R_SC_ARG3))) = Some a3 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inr Merged.R_SC_RET))) = Some a16 ->
  getm mregs (@word_of_nat (reg_field_size mt)
                (Merged.to_nat_bis (inl rptr))) = Some aptr ->
  LRC.alloc_fun (NC := NC)
    (@Symbolic.State mt lrc_tags _ mmem
       (setm (setm (setm (setm mregs
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inr Merged.R_SC_ARG1))) (wsz@LRC.Other))
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inl R_RA)))
             (v4@(if LRC.is_address t4 then LRC.Invalidated
                  else LRC.Other)))
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
          (v4@t4))
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inl R_RA)))
          ((word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0))
             @LRC.InternalJump))
       ((word_of_nat Merged.alloc_label)@(LRC.Level lvl c)) tt)
    = Some st4 ->
  exists (max : mword mt) (len : nat)
         (ms1 ms2 ms3 ms5 : @Symbolic.state mt LRC.lrc_tags unit),
    [/\ 0 < len,
        Symbolic.mem st4
        = unionm mmem
            (mkfmap (mkseq (fun n =>
               ((max + as_word (ssrint.Posz (n + 1)))%w,
                (as_word (ssrint.Posz 0))@(LRC.def_mem_tag c false))) len)),
        Symbolic.regs st4
        = setm (setm (setm (setm (setm mregs
            (@word_of_nat (reg_field_size mt)
               (Merged.to_nat_bis (inr Merged.R_SC_ARG1))) (wsz@LRC.Other))
            (@word_of_nat (reg_field_size mt)
               (Merged.to_nat_bis (inl R_RA)))
             (v4@(if LRC.is_address t4 then LRC.Invalidated
                  else LRC.Other)))
            (@word_of_nat (reg_field_size mt)
               (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
            (v4@t4))
            (@word_of_nat (reg_field_size mt)
               (Merged.to_nat_bis (inl R_RA)))
            ((word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0))
               @LRC.InternalJump))
            (word.as_word (ssrint.Posz 16))
            ((max + as_word (ssrint.Posz 1))%w@LRC.Other)
      & [/\ step_me (NC := NC)
              (@Symbolic.State mt lrc_tags _ mmem mregs
                 ((word_of_nat ((side_flat_pos c P0 Pcode o + 0) + pc0))
                    @(LRC.Level lvl c)) tt) ms1 None,
            step_me (NC := NC) ms1 ms2 None,
            step_me (NC := NC) ms2 ms3 None /\
            step_me (NC := NC) ms3 st4 None,
            step_me (NC := NC) st4 ms5 None
          & step_me (NC := NC) ms5
              (@Symbolic.State mt lrc_tags _ (Symbolic.mem st4)
                 (setm (setm (setm (Symbolic.regs st4)
                    (@word_of_nat (reg_field_size mt)
                       (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
                    (v4@(if LRC.is_address t4 then LRC.Invalidated
                         else LRC.Other)))
                    (@word_of_nat (reg_field_size mt)
                       (Merged.to_nat_bis (inl R_RA)))
                    (v4@t4))
                    (@word_of_nat (reg_field_size mt)
                       (Merged.to_nat_bis (inl rptr)))
                    ((max + as_word (ssrint.Posz 1))%w@LRC.Other))
                 ((word_of_nat (side_flat_pos c P0 Pcode o.+1 + pc0))
                    @(LRC.Level lvl c)) tt) None]].
Proof.
move=> Hb HC HP Ho Ho' Hrra Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc18 Hcode
  Hcode4 Hnone Hrc Hsz Ha1 Hra Ha3 Ha16 Haptr Hafun.
case: a1 Ha1 => v17 t17 Ha1.
case: a3 Ha3 => v19a t19a Ha3.
case: a16 Ha16 => v16a t16a Ha16.
case: aptr Haptr => vpa tpa Haptr.
set K17b := @word_of_nat (reg_field_size mt)
              (Merged.to_nat_bis (inr Merged.R_SC_ARG1)) in Hafun.
set K4b := @word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inl R_RA)) in Hafun.
set K19b := @word_of_nat (reg_field_size mt)
              (Merged.to_nat_bis (inr Merged.R_SC_ARG3)) in Hafun.
set KRPT := @word_of_nat (reg_field_size mt)
              (Merged.to_nat_bis (inl rptr)) in Hafun.
set reta := ((word_of_nat ((side_flat_pos c P0 Pcode o + 3) + pc0))
               @LRC.InternalJump) in Hafun.
set t4inv := (if LRC.is_address t4 then LRC.Invalidated else LRC.Other)
  in Hafun |- *.
set N1 := setm mregs K17b (wsz@LRC.Other) in Hafun.
set N2 := setm N1 K4b (v4@t4inv) in Hafun.
set N3 := setm N2 K19b (v4@t4) in Hafun.
set N4 := setm N3 K4b reta in Hafun.
(* chain updm facts *)
have HuA1 : updm mregs K17b (wsz@LRC.Other) = Some N1.
{ by rewrite (updm_from_get _ Ha1). }
have H1_4 : getm N1 K4b = Some (v4@t4).
{ by rewrite /N1 getm_set_bis_bis. }
have H1_19 : getm N1 K19b = Some (v19a@t19a).
{ by rewrite /N1 getm_set_bis_bis. }
have HuA2 : updm N1 K4b (v4@t4inv) = Some N2.
{ by rewrite (updm_from_get _ H1_4). }
have H2_19 : getm N2 K19b = Some (v19a@t19a).
{ by rewrite /N2 getm_set_bis_bis // /N1 getm_set_bis_bis. }
have HuA3 : updm N2 K19b (v4@t4) = Some N3.
{ by rewrite (updm_from_get _ H2_19). }
have H3ra : getm N3 K4b = Some (v4@t4inv).
{ by rewrite /N3 getm_set_bis_bis // /N2 setmE eqxx. }
have HuA4 : updm N3 K4b reta = Some N4.
{ by rewrite (updm_from_get _ H3ra). }
(* clear-list facts on N3 and N4 *)
have H3_1 : getm N3 (word.as_word (ssrint.Posz 1)) = Some (v1@t1).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_0 : getm N3 (word.as_word (ssrint.Posz 0)) = Some (v0@t0).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_2 : getm N3 (word.as_word (ssrint.Posz 2)) = Some (v2@t2).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_3 : getm N3 (word.as_word (ssrint.Posz 3)) = Some (v3@t3).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_5 : getm N3 (word.as_word (ssrint.Posz 5)) = Some (v5@t5).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_6 : getm N3 (word.as_word (ssrint.Posz 6)) = Some (v6@t6).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_7 : getm N3 (word.as_word (ssrint.Posz 7)) = Some (v7@t7).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_16 : getm N3 (word.as_word (ssrint.Posz 16)) = Some (v16a@t16a).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_17 : getm N3 (word.as_word (ssrint.Posz 17))
             = Some (wsz@LRC.Other).
{ rewrite /N3 getm_set_bis_other //.
  rewrite /N2 getm_set_bis_other //.
  by rewrite /N1 getm_set_bis_hit. }
have H3_18 : getm N3 (word.as_word (ssrint.Posz 18)) = Some (v18@t18).
{ by rewrite /N3 /N2 /N1 !getm_set_bis_other. }
have H3_19 : getm N3 (word.as_word (ssrint.Posz 19))
             = Some (v4@t4).
{ by rewrite /N3 getm_set_bis_hit. }
have H4_1 : getm N4 (word.as_word (ssrint.Posz 1)) = Some (v1@t1).
{ by rewrite /N4 getm_set_bis_other. }
have H4_0 : getm N4 (word.as_word (ssrint.Posz 0)) = Some (v0@t0).
{ by rewrite /N4 getm_set_bis_other. }
have H4_2 : getm N4 (word.as_word (ssrint.Posz 2)) = Some (v2@t2).
{ by rewrite /N4 getm_set_bis_other. }
have H4_3 : getm N4 (word.as_word (ssrint.Posz 3)) = Some (v3@t3).
{ by rewrite /N4 getm_set_bis_other. }
have H4_5 : getm N4 (word.as_word (ssrint.Posz 5)) = Some (v5@t5).
{ by rewrite /N4 getm_set_bis_other. }
have H4_6 : getm N4 (word.as_word (ssrint.Posz 6)) = Some (v6@t6).
{ by rewrite /N4 getm_set_bis_other. }
have H4_7 : getm N4 (word.as_word (ssrint.Posz 7)) = Some (v7@t7).
{ by rewrite /N4 getm_set_bis_other. }
have H4_16 : getm N4 (word.as_word (ssrint.Posz 16)) = Some (v16a@t16a).
{ by rewrite /N4 getm_set_bis_other. }
have H4_17 : getm N4 (word.as_word (ssrint.Posz 17))
             = Some (wsz@LRC.Other).
{ by rewrite /N4 getm_set_bis_other. }
have H4_18 : getm N4 (word.as_word (ssrint.Posz 18)) = Some (v18@t18).
{ by rewrite /N4 getm_set_bis_other. }
have H4_19 : getm N4 (word.as_word (ssrint.Posz 19))
             = Some (v4@t4).
{ by rewrite /N4 getm_set_bis_other. }
(* rcom through the chain *)
have Hrc1 : getm N1 rcom = Some rc.
{ by rewrite /N1 getm_set_bis_rcom. }
have Hrc3 : getm N3 rcom = Some rc.
{ by rewrite /N3 /N2 !getm_set_bis_rcom. }
have Hrc4 : getm N4 rcom = Some rc.
{ by rewrite /N4 getm_set_bis_rcom. }
(* the syscall's shape *)
have [c4 [len [max [rav [regs5 SH]]]]] := alloc_fun_shape Hafun.
case: SH => [[Hrav Hpc4]] Hc4 [Hlen Hbnd] [Hupd5 Hregs4] Hmem4.
move: Hc4 => /= Hc4; subst c4.
have Hrav' : getm N4 (ra : reg mt) = Some rav := Hrav.
rewrite ra_key4b -/K4b /N4 setmE eqxx in Hrav'.
case: Hrav' => Erav; subst rav.
have Hupd5' : updm N4 (syscall_ret : reg mt)
                ((max + as_word (ssrint.Posz 1))%w@LRC.Other)
              = Some regs5 := Hupd5.
rewrite sret_key in Hupd5'.
move: Hupd5'; rewrite /updm H4_16 /= => -[Eregs5]; subst regs5.
set N5 := setm N4 (word.as_word (ssrint.Posz 16))
            ((max + as_word (ssrint.Posz 1))%w@LRC.Other) in Eregs5.
(* destructure the syscall's result state *)
clear Hupd5 Hrav.
case: st4 Hpc4 Eregs5 Hmem4 Hcode4 Hafun
  => m4 r4 [p4v p4t] [] /= Hpc4 Eregs5 Hmem4 Hcode4 Hafun.
case: Hpc4 => E1 E2; subst p4v p4t.
subst r4.
(* mov4/mov5 facts *)
have Hrc5 : getm N5 rcom = Some rc.
{ by rewrite /N5 getm_set_raw_rcom. }
have H5_19 : getm N5 K19b = Some (v4@t4).
{ by rewrite /N5 getm_set_raw_other_bis // /N4 getm_set_bis_bis. }
have H5_4 : getm N5 K4b = Some reta.
{ rewrite /N5 getm_set_raw_other_bis //.
  by rewrite /N4 setmE eqxx. }
have Hu56 : updm N5 K19b (v4@t4inv)
            = Some (setm N5 K19b (v4@t4inv)).
{ by rewrite (updm_from_get _ H5_19). }
set N6 := setm N5 K19b (v4@t4inv) in Hu56.
have H6_4 : getm N6 K4b = Some reta.
{ by rewrite /N6 getm_set_bis_bis. }
have Hu67 : updm N6 K4b (v4@t4)
            = Some (setm N6 K4b (v4@t4)).
{ by rewrite (updm_from_get _ H6_4). }
set N7 := setm N6 K4b (v4@t4) in Hu67.
have Hrc7 : getm N7 rcom = Some rc.
{ by rewrite /N7 /N6 !getm_set_bis_rcom. }
have H7_16 : getm N7
               (@word_of_nat (reg_field_size mt)
                  (Merged.to_nat_bis (inr Merged.R_SC_RET)))
             = Some ((max + as_word (ssrint.Posz 1))%w@LRC.Other).
{ by rewrite /N7 /N6 !getm_set_bis_bis // /N5 getm_set_raw_hit_bis. }
have Hrp4 : (Merged.to_nat_bis (inl rptr)
             == Merged.to_nat_bis (inl R_RA)) = false.
{ apply/negbTE/negP => /eqP /= E.
  have E2 : Intermediate.Register.to_nat rptr
            = Intermediate.Register.to_nat R_RA := E.
  by move: (to_nat_inj E2) => E'; exact: Hrra E'. }
have Hrp19 : (Merged.to_nat_bis (inl rptr)
              == Merged.to_nat_bis (inr Merged.R_SC_ARG3)) = false.
{ apply/negbTE/negP => /eqP /= E.
  have H7' := to_nat_lt7 rptr.
  by rewrite E in H7'. }
have Hrp17 : (Merged.to_nat_bis (inl rptr)
              == Merged.to_nat_bis (inr Merged.R_SC_ARG1)) = false.
{ apply/negbTE/negP => /eqP /= E.
  have H7' := to_nat_lt7 rptr.
  by rewrite E in H7'. }
have Hrp16 : (Merged.to_nat_bis (inl rptr) == 16) = false.
{ apply/negbTE/negP => /eqP /= E.
  have H7' := to_nat_lt7 rptr.
  by rewrite E in H7'. }
have H7_rp : getm N7 KRPT = Some (vpa@tpa).
{ by rewrite /N7 getm_set_bis_bis // /N6 getm_set_bis_bis //
     /N5 getm_set_raw_other_bis // /N4 getm_set_bis_bis //
     /N3 getm_set_bis_bis // /N2 getm_set_bis_bis //
     /N1 getm_set_bis_bis. }
have Hu78 : updm N7 KRPT ((max + as_word (ssrint.Posz 1))%w@LRC.Other)
            = Some (setm N7 KRPT
                      ((max + as_word (ssrint.Posz 1))%w@LRC.Other)).
{ by rewrite (updm_from_get _ H7_rp). }
(* assemble *)
exists max, len.
do 4!eexists.
split; [exact Hlen | exact Hmem4 | by [] |].
split.
- eapply sim_alloc_mov1.
  + exact Hb.
  + exact HC.
  + exact HP.
  + exact Ho.
  + exact Hcode.
  + exact Hrc.
  + exact Hsz.
  + exact Ha1.
  + exact (updm_id Hsz).
  + exact HuA1.
- eapply sim_alloc_mov2.
  + exact Hb.
  + exact HC.
  + exact HP.
  + exact Ho.
  + exact Hcode.
  + exact Hrc1.
  + exact H1_4.
  + exact H1_19.
  + exact HuA2.
  + exact HuA3.
- split.
  + eapply sim_alloc_jal.
    * exact Hb.
    * exact HC.
    * exact HP.
    * exact Ho.
    * exact Hcode.
    * exact Hnone.
    * exact Hrc3.
    * rewrite ra_key4b -/K4b. exact H3ra.
    * exact H3_1.
    * exact H3_0.
    * exact H3_2.
    * exact H3_3.
    * exact H3_5.
    * exact H3_6.
    * exact H3_7.
    * exact H3_16.
    * exact H3_17.
    * exact H3_18.
    * exact H3_19.
    * rewrite ra_key4b -/K4b. exact HuA4.
    * exact H4_1.
    * exact H4_0.
    * exact H4_2.
    * exact H4_3.
    * exact H4_5.
    * exact H4_6.
    * exact H4_7.
    * exact H4_16.
    * exact H4_17.
    * exact H4_18.
    * exact H4_19.
  + eapply stepf_syscall_compute.
    * exact Hnone.
    * exact Hrc4.
    * exact Hafun.
- eapply sim_alloc_mov4.
  + exact Hb.
  + exact HC.
  + exact HP.
  + exact Ho.
  + exact Hcode4.
  + exact Hrc5.
  + exact H5_19.
  + exact H5_4.
  + exact Hu56.
  + exact Hu67.
- eapply sim_alloc_mov5.
  + exact Hb.
  + exact HC.
  + exact HP.
  + exact Ho.
  + exact Ho'.
  + exact Hcode4.
  + exact Hrc7.
  + exact H7_16.
  + exact H7_rp.
  + exact (updm_id H7_16).
  + exact Hu78.
Qed.

(* IAlloc: the full diagram case — six me-steps and the lin_match
   reassembly over the extended address map; the syscall success, the
   post-memory relation (freshness) and SINV stability are premises *)
Lemma diag_alloc (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem imem' : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit)
    (rptr rsize : Machine.register) (szZ : Z) (bI : Block.id)
    (wsz v4 : mword mt) (t4 : LRC.value_tag)
    (st4 : @Symbolic.state mt LRC.lrc_tags unit) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  rptr <> R_RA ->
  Intermediate.Register.get rsize iregs = Int szZ ->
  Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
    = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
  Intermediate.Register.set rptr
    (Ptr (Pointer.component ipc, bI, 0%Z)) iregs = iregs' ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl rsize)))
    = Some (wsz@LRC.Other) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl R_RA)))
    = Some (v4@t4) ->
  getm (Symbolic.mem ms) (word_of_nat Merged.alloc_label) = None ->
  code_region_ok (Symbolic.mem st4) ->
  amap_get bmap (Pointer.component ipc) bI = None ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IAlloc rptr rsize) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
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
                  ((side_flat_pos (Pointer.component ipc) P0 Pcode
                      (Z.to_nat (Pointer.offset ipc)) + 3) + pc0))
                 @LRC.InternalJump))
           ((word_of_nat Merged.alloc_label)
              @(LRC.Level (cross_frames (Pointer.component ipc) gps)
                  (Pointer.component ipc))) tt)
      = Some st4) ->
  (forall (max : mword mt) (len : nat),
      0 < len ->
      Symbolic.mem st4
      = unionm (Symbolic.mem ms)
          (mkfmap (mkseq (fun n =>
             ((max + as_word (ssrint.Posz (n + 1)))%w,
              (as_word (ssrint.Posz 0))
                @(LRC.def_mem_tag (Pointer.component ipc) false))) len)) ->
      mem_rel (amap_set bmap (Pointer.component ipc) bI
                 ((eqtype.val max).+1)) imem' (Symbolic.mem st4)) ->
  (forall mregs' mpc' (base' : nat),
      getm mregs'
        (@word_of_nat (reg_field_size mt)
           (Merged.to_nat_bis (inl R_RA)))
      = getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inl R_RA))) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV (amap_set bmap (Pointer.component ipc) bI base') gps imem'
        (Intermediate.Register.set rptr
           (Ptr (Pointer.component ipc, bI, 0%Z)) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem st4)
                  mregs' mpc' tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IAlloc rptr rsize) ->
  exists (max : mword mt) (len : nat)
         (ms1 ms2 ms3 ms5 msF : @Symbolic.state mt LRC.lrc_tags unit),
    [/\ step_me (NC := NC) ms ms1 None,
        step_me (NC := NC) ms1 ms2 None,
        step_me (NC := NC) ms2 ms3 None /\
        step_me (NC := NC) ms3 st4 None,
        step_me (NC := NC) st4 ms5 None /\
        step_me (NC := NC) ms5 msF None
      & lin_match SINV
          (amap_set bmap (Pointer.component ipc) bI ((eqtype.val max).+1))
          gps imem' iregs' (Pointer.inc ipc) msF].
Proof.
move=> Hb Hin Hrra Hsize Halloc Hset Hwsz HR4 Hnone Hcode4 Hfresh
  Hterm Hafun Hmemrel HS Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have HafunI := Hafun _ _ _ Hside HgetP Hnth.
have [aptr [Haptr _]] := Hregs rptr Hrra.
clear Hm Hafun Hterm.
have [a1 Hc1] := Htot 1 isT.
have [a0 Hc0] := Htot 0 isT.
have [a2 Hc2] := Htot 2 isT.
have [a3' Hc3] := Htot 3 isT.
have [a5 Hc5] := Htot 5 isT.
have [a6 Hc6] := Htot 6 isT.
have [a7 Hc7] := Htot 7 isT.
have [a16 Hc16] := Htot 16 isT.
have [a17 Hc17] := Htot 17 isT.
have [a18 Hc18] := Htot 18 isT.
have [a19 Hc19] := Htot 19 isT.
case: a1 Hc1 => v1 t1 Hc1.
case: a0 Hc0 => v0 t0 Hc0.
case: a2 Hc2 => v2 t2 Hc2.
case: a3' Hc3 => v3 t3 Hc3.
case: a5 Hc5 => v5 t5 Hc5.
case: a6 Hc6 => v6 t6 Hc6.
case: a7 Hc7 => v7 t7 Hc7.
case: a18 Hc18 => v18 t18 Hc18.
case: ms Hpc Hmem Hregs Hcode Hstack Htot Hval Htag Hwsz HR4 Hnone
  HafunI Hmemrel HS Haptr Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc16 Hc17 Hc18
  Hc19
  => mmem mregs [pcv pct] [] Hpc Hmem Hregs Hcode Hstack Htot /= Hval
     Htag Hwsz HR4 Hnone HafunI Hmemrel HS Haptr Hc1 Hc0 Hc2 Hc3 Hc5
     Hc6 Hc7 Hc16 Hc17 Hc18 Hc19.
subst pcv pct.
have Hrc : getm mregs rcom = Some (v1@t1).
{ rewrite rcom_key. exact Hc1. }
have Ha1s : getm mregs
              (@word_of_nat (reg_field_size mt)
                 (Merged.to_nat_bis (inr Merged.R_SC_ARG1)))
            = Some a17 := Hc17.
have Ha3s : getm mregs
              (@word_of_nat (reg_field_size mt)
                 (Merged.to_nat_bis (inr Merged.R_SC_ARG3)))
            = Some a19 := Hc19.
have Ha16s : getm mregs
               (@word_of_nat (reg_field_size mt)
                  (Merged.to_nat_bis (inr Merged.R_SC_RET)))
             = Some a16 := Hc16.
have Haptrs : getm mregs
                (@word_of_nat (reg_field_size mt)
                   (Merged.to_nat_bis (inl rptr))) = Some aptr := Haptr.
have STEPS := diag_alloc_steps Hb Hside HgetP Hnth Hnth' Hrra
  Hc1 Hc0 Hc2 Hc3 Hc5 Hc6 Hc7 Hc18 Hcode Hcode4 Hnone Hrc Hwsz Ha1s
  HR4 Ha3s Ha16s Haptrs HafunI.
case: STEPS
  => max [len [ms1 [ms2 [ms3 [ms5
     [Hlen Hmem4 Hregs4 [S1 S2 [S3 S4] S5 S6]]]]]]].
have Hvalptr : val_rel_b
    (amap_set bmap (Pointer.component ipc) bI ((eqtype.val max).+1))
    (Ptr (Pointer.component ipc, bI, 0%Z))
    ((max + as_word (ssrint.Posz 1))%w).
{ exists ((eqtype.val max).+1).
  split; first exact: amap_set_eq.
  have -> : ssrint.intZmod.addz (Merged.encode_int 0)
              (ssrint.Posz ((eqtype.val max).+1))
            = ssrint.Posz ((eqtype.val max).+1) by [].
  exact (esym (won_val_S max)). }
rewrite addn0 in S1.
exists max, len, ms1, ms2, ms3, ms5.
eexists.
split.
- exact S1.
- exact S2.
- by split; [exact S3 | exact S4].
- by split; [exact S5 | exact S6].
- constructor => /=.
  + abstract (apply: (pc_rel_inc Hilp Hblk Hjnth Hoff); by []).
  + abstract (exact (Hmemrel _ _ Hlen Hmem4)).
  + abstract (
      rewrite Hregs4 -Hset;
      apply: (regs_rel_w_set rptr); last exact Hvalptr;
      apply: regs_rel_w_set_ra;
      apply: regs_rel_w_set_hi; first by [];
      apply: regs_rel_w_set_hi; first by [];
      apply: regs_rel_w_set_ra;
      apply: regs_rel_w_set_hi; first by [];
      apply: regs_rel_w_set_ra;
      apply: regs_rel_w_set_hi; first by [];
      exact: (regs_rel_w_ext _ Hfresh Hregs)).
  + abstract (exact Hcode4).
  + abstract (
      rewrite -Hset;
      apply: (HS _ _ _ _ Hstack);
      rewrite (getm_set_bis_bis _ _ (kb := inl rptr) (kb' := inl R_RA));
      [ by rewrite setmE eqxx HR4
      | by apply/negbTE/negP => /eqP /to_nat_inj E;
           apply: Hrra; rewrite E ]).
  + abstract (rewrite Hregs4; do !apply: regs_total_set; exact Htot).
Qed.

Section DiagStaticsJal.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).
Hypothesis Huniq_a : forall cid Cprocs0 l0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.
Hypothesis Huniq_b : forall cid Cprocs0 l0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.

(* IJal: pushes inc ipc onto the gps, clobbers R_RA (Undef on the I side,
   the InternalJump return capability on the me side), jumps to label [l]
   at [tpc]; the label decomposition comes pinned to the ilp lookup *)
Lemma diag_jal (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs iregs' : Intermediate.Register.t) (ipc tpc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) (l : nat) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Pointer.component ipc \in domm (Intermediate.prog_interface ilp) ->
  Pointer.component tpc = Pointer.component ipc ->
  Intermediate.Register.set R_RA Undef iregs = iregs' ->
  (forall Cprocs,
      Intermediate.prog_procedures ilp (Pointer.component ipc)
        = Some Cprocs ->
      exists jt pt Ptcode,
        [/\ Pointer.block tpc
              = proc_nb0 ilp (Pointer.component ipc) + jt,
            List.nth_error (elementsm Cprocs) jt = Some (pt, Ptcode),
            (0 <= Pointer.offset tpc)%Z,
            List.nth_error Ptcode (Z.to_nat (Pointer.offset tpc))
              = Some (ILabel l)
          & pc0 + (side_flat_pos (Pointer.component ipc) pt Ptcode
                     (Z.to_nat (Pointer.offset tpc)) + 0)
            < 2 ^ imm_size mt]) ->
  (forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IJal l) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc)).+1
        = Some i') ->
  (forall (Cprocs : NMap Machine.code) (j : nat) (P0 : Procedure.id)
          (Pcode : Machine.code) mpc',
      Intermediate.prog_procedures ilp (Pointer.component ipc)
        = Some Cprocs ->
      Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      (0 <= Pointer.offset ipc)%Z ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap (Pointer.inc ipc :: gps) imem
        (Intermediate.Register.set R_RA Undef iregs) tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
              ((word_of_nat
                  (side_flat_pos (Pointer.component ipc) P0 Pcode
                     (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
                 @LRC.InternalJump)) mpc' tt)) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IJal l) ->
  exists ms',
    step_me (NC := NC) ms ms' None
    /\ lin_match SINV bmap (Pointer.inc ipc :: gps) imem iregs' tpc ms'.
Proof.
move=> Hb Hin Hcomp' Hset Hlabel Hterm HS Hm Hex.
case: (Hm) => Hpc Hmem Hregs Hcode Hstack Htot.
have [Cprocs [P0 [Pcode [j
  [[Hside HgetP Hnth Hval Htag] [Hilp Hblk Hjnth]]]]]]
  := lm_fetch Hin Hpc Hex.
have [jt [pt [Ptcode [Hblkt Hjntht Hofft HPt Himm]]]] := Hlabel _ Hilp.
have [i' Hnth'] := Hterm _ _ _ Hside HgetP Hnth.
have HgetPt : getm Cprocs pt = Some Ptcode.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ Hjntht). }
have Hoff : (0 <= Pointer.offset ipc)%Z.
{ by case: Hpc => ? [? [? [? [_ _ _ Hoffpos _]]]]. }
have Hcr : R_COM <> R_RA by [].
have [rca [Hrc _]] := Hregs R_COM Hcr.
have Elvl : cross_frames (Pointer.component ipc) (Pointer.inc ipc :: gps)
            = cross_frames (Pointer.component ipc) gps.
{ by rewrite /= Pointer.inc_preserves_component eqxx. }
clear Hm Hlabel Hterm.
case: ms HS Hpc Hmem Hregs Hcode Hstack Hval Htag Hrc Htot
  => mmem mregs [pcv pct] [] HS Hpc Hmem Hregs Hcode Hstack /= Hval
     Htag Hrc Htot.
subst pcv pct.
have [a1 Hc1] := Htot 1 isT.
have [a0 Hc0] := Htot 0 isT.
have [a2 Hc2] := Htot 2 isT.
have [a3 Hc3] := Htot 3 isT.
have [a4 Hc4] := Htot 4 isT.
have [a5 Hc5] := Htot 5 isT.
have [a6 Hc6] := Htot 6 isT.
have [a7 Hc7] := Htot 7 isT.
have [a16 Hc16] := Htot 16 isT.
have [a17 Hc17] := Htot 17 isT.
have [a18 Hc18] := Htot 18 isT.
have [a19 Hc19] := Htot 19 isT.
case: a1 Hc1 => v1 t1 Hc1.
case: a0 Hc0 => v0 t0 Hc0.
case: a2 Hc2 => v2 t2 Hc2.
case: a3 Hc3 => v3 t3 Hc3.
case: a4 Hc4 => v4 t4 Hc4.
case: a5 Hc5 => v5 t5 Hc5.
case: a6 Hc6 => v6 t6 Hc6.
case: a7 Hc7 => v7 t7 Hc7.
case: a16 Hc16 => v16 t16 Hc16.
case: a17 Hc17 => v17 t17 Hc17.
case: a18 Hc18 => v18 t18 Hc18.
case: a19 Hc19 => v19 t19 Hc19.
have Hc4' : getm mregs
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA)) = Some (v4@t4).
{ exact Hc4. }
have Hupd := updm_from_get
  ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))@LRC.InternalJump) Hc4'.
exists (@Symbolic.State mt lrc_tags _ mmem
  (setm mregs
     (@word_of_nat (reg_field_size mt)
        (Intermediate.Register.to_nat R_RA))
     ((word_of_nat (side_flat_pos (Pointer.component ipc) P0 Pcode
         (Z.to_nat (Pointer.offset ipc)).+1 + pc0))@LRC.InternalJump))
  ((word_of_nat (side_flat_pos (Pointer.component ipc) pt Ptcode
      (Z.to_nat (Pointer.offset tpc)) + pc0))
     @(LRC.Level (cross_frames (Pointer.component ipc) gps)
         (Pointer.component ipc))) tt).
split.
- abstract (eapply (sim_jal Hlab_a Hcomp_a Hlab_b Hcomp_b Hdisj
    Huniq_a Huniq_b);
    [exact Hb | exact Hside | exact HgetP | exact Hnth | exact Hnth'
    | exact HgetPt | exact HPt | exact Himm | exact Hcode
    | rewrite rcom_key; exact Hrc
    | rewrite ra_key4; exact Hc4'
    | exact Hc1 | exact Hc0 | exact Hc2 | exact Hc3 | exact Hc5
    | exact Hc6 | exact Hc7 | exact Hc16 | exact Hc17 | exact Hc18
    | exact Hc19
    | rewrite ra_key4; exact Hupd
    | rewrite getm_set_ra_other //; exact Hc1
    | rewrite getm_set_ra_other //; exact Hc0
    | rewrite getm_set_ra_other //; exact Hc2
    | rewrite getm_set_ra_other //; exact Hc3
    | rewrite getm_set_ra_other //; exact Hc5
    | rewrite getm_set_ra_other //; exact Hc6
    | rewrite getm_set_ra_other //; exact Hc7
    | rewrite getm_set_ra_other //; exact Hc16
    | rewrite getm_set_ra_other //; exact Hc17
    | rewrite getm_set_ra_other //; exact Hc18
    | rewrite getm_set_ra_other //; exact Hc19]).
- constructor => /=.
  + abstract (
      exists Cprocs, jt, pt, Ptcode;
      rewrite Hcomp';
      split;
      [ exact Hilp | exact Hblkt | exact Hjntht | exact Hofft
      | rewrite Elvl; by split ]).
  + abstract (exact Hmem).
  + abstract (rewrite -Hset;
      exact (regs_rel_w_set_ra _ (regs_rel_w_iset_ra Undef Hregs))).
  + abstract (exact Hcode).
  + abstract (rewrite -Hset;
      exact: (HS _ _ _ _ _ Hilp Hblk Hjnth Hoff Hstack)).
  + abstract (apply: regs_total_set; exact Htot).
Qed.

End DiagStaticsJal.

(* ==================== the SINV specification ==================== *)

(* Position classes of compiled code (shared vocabulary with the
   instance): [dead_at c o] scans the first [o] instructions of [c] and
   reports whether position [o] sits inside a call window — after a
   push-R_RA ([IStore _ R_RA]) up to and including the matching pop-R_RA
   ([ILoad _ R_RA]) — where the return capability is parked in the
   frame's stack cell rather than live in R_RA. *)
Definition ra_dead_step (i : Machine.instr) (dead : bool) : bool :=
  match i with
  | IStore _ r2 => match r2 with R_RA => true | _ => dead end
  | ILoad _ r2 => match r2 with R_RA => false | _ => dead end
  | _ => dead
  end.

Fixpoint ra_dead_scan (c : Machine.code) (dead : bool) (o : nat)
  : bool :=
  match o, c with
  | 0, _ => dead
  | _.+1, [::] => dead
  | o'.+1, i :: c' => ra_dead_scan c' (ra_dead_step i dead) o'
  end.

Definition dead_at (c : Machine.code) (o : nat) : bool :=
  ra_dead_scan c false o.

(* the exact obligations the fifteen diagram cases impose on the
   calling-convention invariant: any SINV satisfying this record makes
   the whole diagram work.  Each preservation clause carries the joint
   step's FULL data (the instruction, the exact I-side update, the exact
   me-side write-back), so a positional instance can track the stack
   discipline; the frame-extraction clauses are what the control-transfer
   cases consume. *)
Record sinv_spec
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
  : Prop := SinvSpec {
  ss_nop : forall bmap gps imem iregs (ipc : Pointer.t) ms mpc',
      Intermediate.GlobalEnv.executing G ipc INop ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (Symbolic.regs ms) mpc' tt);
  ss_label : forall bmap gps imem iregs (ipc : Pointer.t) (l : nat) ms
                    mpc',
      Intermediate.GlobalEnv.executing G ipc (ILabel l) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (Symbolic.regs ms) mpc' tt);
  ss_const : forall bmap gps imem iregs (ipc : Pointer.t) (v0 : imvalue)
                    (r : register) ms mpc',
      Intermediate.GlobalEnv.executing G ipc (IConst v0 r) ->
      r <> R_RA ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r (imm_to_val v0) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r))
              ((swcast (convert_value (mt := mt)
                  (memory_lengths (Intermediate.prog_buffers
                     (side_of (Pointer.component ipc)))) v0))@LRC.Other))
           mpc' tt);
  ss_mov : forall bmap gps imem iregs (ipc : Pointer.t)
                  (r1 r2 : register) (w1 : mword mt)
                  (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (IMov r1 r2) ->
      r1 <> R_RA -> r2 <> R_RA ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r1)) = Some (w1@LRC.Other) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r2
           (Intermediate.Register.get r1 iregs) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r2)) (w1@LRC.Other))
           mpc' tt);
  ss_mov_inv : forall bmap gps imem iregs (ipc : Pointer.t)
                  (r1 r2 : register) (w1 : mword mt)
                  (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (IMov r1 r2) ->
      r1 <> R_RA -> r2 <> R_RA ->
      Intermediate.Register.get r1 iregs = Undef ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r1))
        = Some (w1@LRC.Invalidated) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r2
           (Intermediate.Register.get r1 iregs) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r2))
              (w1@LRC.Invalidated))
           mpc' tt);
  ss_binop : forall bmap gps imem iregs (ipc : Pointer.t)
                    (op : Values.binop)
                    (r1 r2 r3 : register) (w1 w2 : mword mt)
                    (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (IBinOp op r1 r2 r3) ->
      r3 <> R_RA ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r1)) = Some (w1@LRC.Other) ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r2)) = Some (w2@LRC.Other) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem
        (Intermediate.Register.set r3
           (eval_binop op (Intermediate.Register.get r1 iregs)
              (Intermediate.Register.get r2 iregs)) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r3))
              ((binop_denote (Merged.binop_trans op) w1 w2)@LRC.Other))
           mpc' tt);
  ss_load : forall bmap gps imem iregs (ipc : Pointer.t)
                   (r1 r2 : register) (bp : Block.id) (op : Z)
                   (v : value) (base : nat) (w : mword mt)
                   (ent : option (Procedure.id * seq Component.id))
                   (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
      r2 <> R_RA ->
      Intermediate.Register.get r1 iregs
        = Ptr (Pointer.component ipc, bp, op) ->
      Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                     false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem (Intermediate.Register.set r2 v iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r2)) (w@LRC.Other))
           mpc' tt);
  ss_load_inv : forall bmap gps imem iregs (ipc : Pointer.t)
                   (r1 r2 : register) (bp : Block.id) (op : Z)
                   (v : value) (base : nat) (w : mword mt)
                   (ent : option (Procedure.id * seq Component.id))
                   (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
      r2 <> R_RA ->
      Intermediate.Register.get r1 iregs
        = Ptr (Pointer.component ipc, bp, op) ->
      Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
      v = Undef ->
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w@(LRC.MTag LRC.Invalidated (Pointer.component ipc) ent
                     false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem (Intermediate.Register.set r2 v iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r2)) (w@LRC.Invalidated))
           mpc' tt);
  ss_store : forall bmap gps imem imem' iregs (ipc : Pointer.t)
                    (r1 r2 : register) (bp : Block.id) (op : Z)
                    (base : nat) (w oldv : mword mt)
                    (ent : option (Procedure.id * seq Component.id))
                    (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
      r2 <> R_RA ->
      Intermediate.Register.get r1 iregs
        = Ptr (Pointer.component ipc, bp, op) ->
      Memory.Memory.store imem (Pointer.component ipc, bp, op)
        (Intermediate.Register.get r2 iregs) = Some imem' ->
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r2)) = Some (w@LRC.Other) ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (oldv@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                        false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
           (setm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
              (w@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                    false)))
           (Symbolic.regs ms) mpc' tt);
  ss_store_inv : forall bmap gps imem imem' iregs (ipc : Pointer.t)
                    (r1 r2 : register) (bp : Block.id) (op : Z)
                    (base : nat) (w oldv : mword mt)
                    (ent : option (Procedure.id * seq Component.id))
                    (ms : @Symbolic.state mt lrc_tags unit) mpc',
      Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
      r2 <> R_RA ->
      Intermediate.Register.get r2 iregs = Undef ->
      Intermediate.Register.get r1 iregs
        = Ptr (Pointer.component ipc, bp, op) ->
      Memory.Memory.store imem (Pointer.component ipc, bp, op)
        (Intermediate.Register.get r2 iregs) = Some imem' ->
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r2))
        = Some (w@LRC.Invalidated) ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (oldv@(LRC.MTag LRC.Other (Pointer.component ipc) ent
                        false)) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
           (setm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
              (w@(LRC.MTag LRC.Invalidated (Pointer.component ipc) ent
                    false)))
           (Symbolic.regs ms) mpc' tt);
  ss_alloc : forall bmap gps imem imem' iregs (ipc : Pointer.t)
                    (rptr rsize : register) (szZ : Z) (bI : Block.id)
                    (base' : nat)
                    (ms : @Symbolic.state mt lrc_tags unit) mem' mregs'
                    mpc',
      Intermediate.GlobalEnv.executing G ipc (IAlloc rptr rsize) ->
      rptr <> R_RA ->
      Intermediate.Register.get rsize iregs = Int szZ ->
      Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
        = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
      (forall w a, getm (Symbolic.mem ms) w = Some a ->
                   getm mem' w = Some a) ->
      getm mregs'
        (@word_of_nat (reg_field_size mt)
           (Merged.to_nat_bis (inl R_RA)))
      = getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Merged.to_nat_bis (inl R_RA))) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV (amap_set bmap (Pointer.component ipc) bI base') gps imem'
        (Intermediate.Register.set rptr
           (Ptr (Pointer.component ipc, bI, 0%Z)) iregs)
        (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ mem' mregs' mpc' tt);
  ss_bnz_z : forall bmap gps imem iregs (ipc : Pointer.t) (r : register)
                    (l : nat) ms mpc',
      Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
      Intermediate.Register.get r iregs = Int 0 ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (Symbolic.regs ms) mpc' tt);
  ss_bnz_nz : forall bmap gps imem iregs (ipc tpc : Pointer.t)
                     (r : register) (l : nat) (zv : Z) ms mpc',
      Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
      Intermediate.GlobalEnv.find_label_in_procedure G ipc l
        = Some tpc ->
      Intermediate.Register.get r iregs = Int zv ->
      (zv <> 0)%Z ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap gps imem iregs tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (Symbolic.regs ms) mpc' tt);
  ss_pop_jump : forall bmap gps' imem iregs (ipc tpc : Pointer.t) ms
                       mpc',
      Intermediate.GlobalEnv.executing G ipc IJump ->
      Pointer.component tpc = Pointer.component ipc ->
      SINV bmap (tpc :: gps') imem iregs ipc ms ->
      SINV bmap gps' imem iregs tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (Symbolic.regs ms) mpc' tt);
  ss_pop_ret : forall bmap gps' imem iregs (ipc tpc : Pointer.t) ms
                      mregs' mpc',
      Intermediate.GlobalEnv.executing G ipc IReturn ->
      (Pointer.component ipc == Pointer.component tpc) = false ->
      SINV bmap (tpc :: gps') imem iregs ipc ms ->
      SINV bmap gps' imem (Intermediate.Register.invalidate iregs) tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           mregs' mpc' tt);
  ss_push_jal : forall bmap gps imem iregs (ipc tpc : Pointer.t)
                       (l : nat) ms
                       (Cprocs : NMap Machine.code) (j : nat)
                       (P0 : Procedure.id) (Pcode : Machine.code) mpc',
      Intermediate.GlobalEnv.executing G ipc (IJal l) ->
      Intermediate.GlobalEnv.find_label_in_component G ipc l = Some tpc ->
      Intermediate.prog_procedures ilp (Pointer.component ipc)
        = Some Cprocs ->
      Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      (0 <= Pointer.offset ipc)%Z ->
      (gps <> [::] ->
       dead_at Pcode (Z.to_nat (Pointer.offset ipc)) = true) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap (Pointer.inc ipc :: gps) imem
        (Intermediate.Register.set R_RA Undef iregs) tpc
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms)
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
              ((word_of_nat
                  (side_flat_pos (Pointer.component ipc) P0 Pcode
                     (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
                 @LRC.InternalJump)) mpc' tt);
  ss_push_call : forall bmap gps imem iregs (ipc : Pointer.t)
                        (C' : Component.id) (b : Block.id)
                        (ms : @Symbolic.state mt lrc_tags unit)
                        (mregs' : {fmap reg mt -> @ratom mt}) mpc'
                        (Cprocs : NMap Machine.code) (j : nat)
                        (P0 : Procedure.id) (Pcode : Machine.code)
                        (p : Procedure.id),
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
                   (side_flat_pos (Pointer.component ipc) P0 Pcode
                      (Z.to_nat (Pointer.offset ipc)).+1 + pc0))
                  @(LRC.Ret (cross_frames (Pointer.component ipc)
                               gps))) ->
      SINV bmap gps imem iregs ipc ms ->
      SINV bmap (Pointer.inc ipc :: gps) imem
        (Intermediate.Register.invalidate iregs) (C', b, 0%Z)
        (@Symbolic.State mt lrc_tags _ (Symbolic.mem ms) mregs' mpc'
           tt);
  (* EXTRACTION clauses — position-conditioned via the matched pc *)
  ss_frame_jump : forall bmap gps' tpc imem iregs ipc ms,
      lin_match SINV bmap (tpc :: gps') imem iregs ipc ms ->
      Intermediate.GlobalEnv.executing G ipc IJump ->
      Pointer.component tpc = Pointer.component ipc ->
      forall Cprocs,
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
                         (side_flat_pos (Pointer.component ipc) P0'
                            Pcode' (Z.to_nat (Pointer.offset tpc))
                          + pc0))@LRC.InternalJump)
            & exists i'',
                List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
                = Some i''];
  ss_frame_ret : forall bmap gps' tpc imem iregs ipc ms,
      lin_match SINV bmap (tpc :: gps') imem iregs ipc ms ->
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
                       (side_flat_pos (Pointer.component tpc) P0' Pcode'
                          (Z.to_nat (Pointer.offset tpc)) + pc0))
                      @(LRC.Ret (cross_frames (Pointer.component tpc)
                                   gps')))
          & exists i'',
              List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
              = Some i''];
  (* RA-transport clauses — the compiled pop/push-R_RA sites move the
     capability between R_RA and a stack cell via [switch_val] *)
  ss_load_ra : forall bmap gps imem iregs ipc ms r1 (bp : Block.id)
                      (op : Z) (v : value) (base : nat) (w2 : mword mt)
                      (cvt : LRC.value_tag)
                      (ent : option (Procedure.id * seq Component.id))
                      mpc',
      lin_match SINV bmap gps imem iregs ipc ms ->
      Intermediate.GlobalEnv.executing G ipc (ILoad r1 R_RA) ->
      Intermediate.Register.get r1 iregs
        = Ptr (Pointer.component ipc, bp, op) ->
      Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op))
        = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
      (* the loaded slot holds the top frame's capability (run-level:
         compiled pops read exactly the pushed slot) *)
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
                    (side_flat_pos (Pointer.component tpc) P0' Pcode'
                       (Z.to_nat (Pointer.offset tpc)) + pc0)]
         /\ (exists i'',
               List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
               = Some i'')
         /\ (~~ nilp gps' ->
             dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
         /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                   then LRC.InternalJump
                   else LRC.Ret (cross_frames (Pointer.component tpc)
                                   gps'))) ->
      SINV bmap gps imem (Intermediate.Register.set R_RA v iregs)
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
           mpc' tt);
  ss_store_ra : forall bmap gps imem imem' iregs ipc ms r1
                       (bp : Block.id)
                       (op : Z) (base : nat) (w2 : mword mt)
                       (ts : LRC.value_tag) (oldv : mword mt)
                       (oldvt : LRC.value_tag)
                       (ent : option (Procedure.id * seq Component.id))
                       mpc',
      lin_match SINV bmap gps imem iregs ipc ms ->
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
      SINV bmap gps imem' iregs (Pointer.inc ipc)
        (@Symbolic.State mt lrc_tags _
           (setm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
              (w2@(LRC.MTag ts (Pointer.component ipc) ent false)))
           (setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
              (w2@(if LRC.is_address ts then LRC.Invalidated
                   else LRC.Other)))
           mpc' tt)
}.

(* ==================== the assembled step diagram ==================== *)

(* silent multi-step closure of the me machine *)
Inductive me_sstar (NC : nat)
  : @Symbolic.state mt lrc_tags unit
    -> @Symbolic.state mt lrc_tags unit -> Prop :=
| me_sstar_refl : forall s, me_sstar NC s s
| me_sstar_step : forall s s' s'',
    step_me (NC := NC) s s' None -> me_sstar NC s' s'' ->
    me_sstar NC s s''.

(* trace-indexed me step, CompCert-style (mirrors RSCDefs' step shape) *)
Definition step_t (NC : nat)
    (s : @Symbolic.state mt lrc_tags unit) (t : Events.trace)
    (s' : @Symbolic.state mt lrc_tags unit) : Prop :=
  match t with
  | [::] => step_me (NC := NC) s s' None
  | [:: e] => step_me (NC := NC) s s' (Some e)
  | _ => False
  end.

(* the silent star embeds into the trace-indexed star *)
Lemma me_sstar_star (NC : nat)
    (ms msF : @Symbolic.state mt lrc_tags unit) :
  me_sstar NC ms msF ->
  star (fun _ : unit => step_t NC) tt ms Events.E0 msF.
Proof.
elim=> [s|s s' s'' Hst _ IH].
- exact: star_refl.
- have St : step_t NC s Events.E0 s' := Hst.
  by eapply star_step; [exact St | exact IH | ].
Qed.

(* CS steps carry at most one event *)
Lemma cs_step_trace (s1 s2 : CS.state) (e : Events.trace) :
  CS.step G s1 e s2 ->
  e = Events.E0 \/ exists ev, e = [:: ev].
Proof.
move=> Hst; case: Hst => *; try (by left); by right; eexists.
Qed.

(* a related zero is the zero word (discharges Obnz_z's conclusion) *)
Lemma val_rel_int0 (bmap : addr_map) (w : mword mt) :
  val_rel_b bmap (Int 0) w -> (w == 0%w) = true.
Proof.
move=> -> /=.
by apply/eqP.
Qed.

(* the running component lies in the linked procedure domain *)
Lemma lm_pc_domm
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
        -> Intermediate.Register.t -> Pointer.t
        -> @Symbolic.state mt lrc_tags unit -> Prop)
    (bmap : addr_map) (gps : CS.stack) (imem : Memory.Memory.t)
    (iregs : Intermediate.Register.t) (ipc : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  lin_match SINV bmap gps imem iregs ipc ms ->
  Pointer.component ipc \in domm (Intermediate.prog_procedures ilp).
Proof.
case=> -[Cp [j [P0 [Pc [HP _ _ _ _]]]]] _ _ _ _ _.
by rewrite mem_domm HP.
Qed.

(* ---- discharges of the DiagAll/InitMatch side conditions ---- *)

(* the domm side condition follows from well-formedness *)
Lemma wf_procs_iface :
  Intermediate.well_formed_program ilp ->
  forall cid,
    cid \in domm (Intermediate.prog_procedures ilp) ->
    cid \in domm (Intermediate.prog_interface ilp).
Proof.
move=> Hwf cid.
by rewrite (Intermediate.wfprog_defined_procedures Hwf).
Qed.

(* the main-procedure premises follow from well-formedness (main on the
   left side) *)
Lemma wf_main_procs :
  Intermediate.well_formed_program ilp ->
  Intermediate.prog_main ilp = true ->
  Component.main \in domm (Intermediate.prog_procedures pra) ->
  exists CprocsM,
    Intermediate.prog_procedures pra Component.main = Some CprocsM
    /\ Procedure.main \in domm CprocsM.
Proof.
move=> Hwf Hmain HmL.
have Hm' : Intermediate.prog_main ilp by rewrite Hmain.
have [mp [Hget Hin]] := Intermediate.wfprog_main_existence Hwf Hm'.
case/dommP: HmL => CprocsM HgetA.
move: Hget; rewrite /ilp /Intermediate.program_link /= unionmE HgetA /=.
case=> ?; subst mp.
by exists CprocsM; split.
Qed.

(* the mirrored main lookup: main owned by the right side *)
Lemma wf_main_procs_r :
  Intermediate.well_formed_program ilp ->
  Intermediate.prog_main ilp = true ->
  Component.main \notin domm (Intermediate.prog_procedures pra) ->
  exists CprocsM,
    Intermediate.prog_procedures prb Component.main = Some CprocsM
    /\ Procedure.main \in domm CprocsM.
Proof.
move=> Hwf Hmain HmL.
have Hm' : Intermediate.prog_main ilp by rewrite Hmain.
have [mp [Hget Hin]] := Intermediate.wfprog_main_existence Hwf Hm'.
have HgA : Intermediate.prog_procedures pra Component.main = None.
{ by apply/dommPn. }
move: Hget; rewrite /ilp /Intermediate.program_link /= unionmE HgA /=.
move=> Hget.
by exists mp; split.
Qed.

(* index of the least key: id 0 sorts first *)
Lemma index0_sorted (l : seq nat) :
  sorted Ord.lt l -> 0 \in l -> seq.index 0 l = 0.
Proof.
case: l => [|a l] //= Hpath.
rewrite inE => /orP[/eqP Ea | Hin].
- by rewrite -Ea eqxx.
- have Hall : all (Ord.lt a) l
    := order_path_min (@Ord.lt_trans _) Hpath.
  move/allP: Hall => /(_ _ Hin) /andP[Hle Hne].
  exfalso.
  clear Hpath Hin.
  case: a Hle Hne => [|a'] Hle Hne.
  + by rewrite eqxx in Hne.
  + by move: Hle.
Qed.

(* the main procedure (id 0) has base offset 0 in its component *)
Lemma proc_base_main (pr : Intermediate.program)
    (c : Component.id) (Cprocs : NMap Machine.code) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Procedure.main \in domm Cprocs ->
  proc_base pr c Procedure.main = 0.
Proof.
move=> HC Hin.
rewrite /proc_base /comp_procs HC /=.
have -> : seq.index Procedure.main (domm Cprocs) = 0.
{ apply: index0_sorted; last exact: Hin.
  by move: Hin; case: (domm Cprocs) => s Hs _. }
by rewrite take0.
Qed.

(* the encoded code cells are code-tagged (discharges Oenc) *)
Lemma encode_is_code :
  Intermediate.well_formed_program pra ->
  Intermediate.well_formed_program prb ->
  forall (w : mword mt) (a : matom),
    encode_code codeW pc0 w = Some a -> is_code (taga a) = true.
Proof.
move=> Hwfa Hwfb w a Henc.
have [n [Ew [Hn Hnth]]] := encode_code_nth_inv Henc.
have [i [t [Hcell [Etag Eval]]]] := encode_code_foldr_nth Hnth.
rewrite Etag.
have HIn : List.In (i, t) codeW := List.nth_error_In _ _ Hcell.
have [HIna|HInb] := List.in_app_or _ _ _ HIn.
- by have [Hic _] := lin_low_tags HIna.
- by have [Hic _] := lin_low_tags HInb.
Qed.

(* compiled code never touches R_RA through the data-register forms;
   the vestigial push/pop R_RA transport (IStore/ILoad on the RA slot)
   is handled by dedicated variants later *)
(* decidable R_RA test on registers (7 constructors) *)
Lemma reg_ra_dec (r : Machine.register) : r = R_RA \/ r <> R_RA.
Proof. by case: r; [right|right|right|right|left|right|right]. Qed.

Definition ra_free_instr (i : Machine.instr) : Prop :=
  match i with
  | IConst _ r => r <> R_RA
  | IMov r1 r2 => r1 <> R_RA /\ r2 <> R_RA
  | IBinOp _ r1 r2 r3 => [/\ r1 <> R_RA, r2 <> R_RA & r3 <> R_RA]
  (* the moved register of Load/Store MAY be R_RA — the compiled
     pop/push-R_RA sites; only the address register is constrained *)
  | ILoad r1 r2 => r1 <> R_RA
  | IStore r1 r2 => r1 <> R_RA
  | IBnz r _ => r <> R_RA
  | IAlloc rptr rsize => rptr <> R_RA /\ rsize <> R_RA
  | _ => True
  end.

(* I-side reachability from the linked program's initial state — the
   anchor that makes run-invariant oracles (operand definedness, R_RA
   clobberedness, value fits) dischargeable by an instance: they only
   need to hold along actual runs, not for arbitrary matched states *)
Definition ireach (s : CS.state) : Prop :=
  exists t, star CS.step G (CS.initial_machine_state ilp) t s.

Lemma ireach_init : ireach (CS.initial_machine_state ilp).
Proof. exists Events.E0. exact: star_refl. Qed.

Lemma ireach_step (s s' : CS.state) (e : Events.trace) :
  ireach s -> CS.step G s e s' -> ireach s'.
Proof.
move=> [t Hst] Hstep.
exists (t ** e).
eapply star_trans; [exact Hst| |by []].
by apply: star_one.
Qed.

Lemma ireach_star (s s' : CS.state) (t : Events.trace) :
  ireach s -> star CS.step G s t s' -> ireach s'.
Proof.
move=> [t0 Hst] Hstar.
exists (t0 ** t).
by eapply star_trans; [exact Hst | exact Hstar |].
Qed.

Section DiagAll.

(* ---- the label-scheme statics (union of the per-case sections) ---- *)
Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).
Hypothesis Huniq_a : forall cid Cprocs0 l0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.
Hypothesis Huniq_b : forall cid Cprocs0 l0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
       | p' <- domm Cprocs0] <= 1.

(* the linked program's procedure components are interfaced *)
Hypothesis Hdomm : forall cid,
  cid \in domm (Intermediate.prog_procedures ilp) ->
  cid \in domm (Intermediate.prog_interface ilp).

(* the flat code image fits in the word space *)
Hypothesis Hb : pc0 + size codeW < 2 ^ word_size mt.

Variable NC : nat.
Variable SINV : addr_map -> list Pointer.t -> Memory.Memory.t
                -> Intermediate.Register.t -> Pointer.t
                -> @Symbolic.state mt lrc_tags unit -> Prop.
Hypothesis Hspec : sinv_spec SINV.

(* -------- the compiledness / fit / freshness oracle -------- *)

(* non-terminal instructions have a successor cell *)
Hypothesis Onext : forall cid Cprocs P0 Pcode o i,
  Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  i <> IHalt -> i <> IReturn -> i <> IJump ->
  exists i', List.nth_error Pcode o.+1 = Some i'.

(* compiled data-register forms avoid R_RA *)
Hypothesis Ora : forall cid Cprocs P0 Pcode o i,
  Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  ra_free_instr i.

(* the encoded code cells are code-tagged *)
Hypothesis Oenc : forall w a,
  encode_code codeW pc0 w = Some a -> is_code (taga a) = true.

(* along compiled runs a binop's operand registers carry Other tags on
   the me side (LRC's BINOP rule demands [is_other] on both): the
   compiled push/pop binops read freshly written R_SP/R_ONE and user
   binops read reloaded user values — never a cross-invalidated
   register *)
Hypothesis Otag : forall bmap gps imem iregs ipc ms Cprocs P0 Pcode
    op r1 r2 r3,
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.prog_procedures (side_of (Pointer.component ipc))
    (Pointer.component ipc) = Some Cprocs ->
  getm Cprocs P0 = Some Pcode ->
  List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
    = Some (IBinOp op r1 r2 r3) ->
  (forall a, getm (Symbolic.regs ms)
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r1)) = Some a ->
     taga a = LRC.Other)
  /\ (forall a, getm (Symbolic.regs ms)
       (@word_of_nat (reg_field_size mt)
          (Intermediate.Register.to_nat r2)) = Some a ->
     taga a = LRC.Other).

(* at compiled pop-R_RA sites the loaded slot holds the top frame's
   capability *)
Hypothesis Oload_ra : forall bmap gps imem iregs ipc ms r1
       (bp : Block.id) (op : Z) (v : value) (base : nat)
       (w2 : mword mt) (cvt : LRC.value_tag)
       (ent : option (Procedure.id * seq Component.id)),
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILoad r1 R_RA) ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
  amap_get bmap (Pointer.component ipc) bp = Some base ->
  getm (Symbolic.mem ms)
    (@word_of_nat (word_size mt) (base + Z.to_nat op))
    = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
  forall (tpc : Pointer.t) (gps' : list Pointer.t),
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
                 (side_flat_pos (Pointer.component tpc) P0' Pcode'
                    (Z.to_nat (Pointer.offset tpc)) + pc0)]
      /\ (exists i'',
            List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
            = Some i'')
      /\ (~~ nilp gps' ->
          dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
      /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                then LRC.InternalJump
                else LRC.Ret (cross_frames (Pointer.component tpc)
                                gps')).

(* at compiled push-R_RA sites the I-side R_RA is clobbered (IJal sets
   it to Undef; pop reloads the pushed Undef; call/return invalidate) *)
Hypothesis Oraud : forall bmap gps imem iregs ipc ms r1,
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IStore r1 R_RA) ->
  Intermediate.Register.get R_RA iregs = Undef.

(* converted immediates relate *)
Hypothesis Oimm : forall bmap gps imem iregs ipc ms v0 r,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IConst v0 r) ->
  val_rel_b bmap (imm_to_val v0)
    (swcast (convert_value (mt := mt)
       (memory_lengths (Intermediate.prog_buffers
          (side_of (Pointer.component ipc)))) v0)).

(* binop results relate *)
Hypothesis Obinop : forall bmap gps imem iregs ipc ms op r1 r2 r3 w1 w2,
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBinOp op r1 r2 r3) ->
  val_rel_b bmap (Intermediate.Register.get r1 iregs) w1 ->
  val_rel_b bmap (Intermediate.Register.get r2 iregs) w2 ->
  val_rel_b bmap
    (eval_binop op (Intermediate.Register.get r1 iregs)
       (Intermediate.Register.get r2 iregs))
    (binop_denote (Merged.binop_trans op) w1 w2).

(* the branch scrutinee words mirror the zero test *)
Hypothesis Obnz_z : forall bmap gps imem iregs ipc ms r l w,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  Intermediate.Register.get r iregs = Int 0 ->
  val_rel_b bmap (Int 0) w ->
  (w == 0%w) = true.
Hypothesis Obnz_nz : forall bmap gps imem iregs ipc ms r l zv w,
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  Intermediate.Register.get r iregs = Int zv ->
  (zv <> 0)%Z ->
  val_rel_b bmap (Int zv) w ->
  (w == 0%w) = false.

(* the branch label facts: nonnegative target offset, the label cell,
   forward position, immediate fit *)
Hypothesis Obnz_lab : forall bmap gps imem iregs ipc tpc ms r l,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
  Intermediate.GlobalEnv.find_label_in_procedure G ipc l = Some tpc ->
  (0 <= Pointer.offset tpc)%Z /\
  (forall Cprocs (j : nat) P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component ipc))
        (Pointer.component ipc) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      Pointer.block ipc
        = proc_nb0 ilp (Pointer.component ipc) + j ->
      List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
        = Some (IBnz r l) ->
      [/\ List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
            = Some (ILabel l),
          side_flat_pos (Pointer.component ipc) P0 Pcode
            (Z.to_nat (Pointer.offset ipc))
          <= side_flat_pos (Pointer.component ipc) P0 Pcode
               (Z.to_nat (Pointer.offset tpc))
        & (pc0 + (side_flat_pos (Pointer.component ipc) P0 Pcode
                    (Z.to_nat (Pointer.offset tpc)) + 0))
          - (pc0 + side_flat_pos (Pointer.component ipc) P0 Pcode
                     (Z.to_nat (Pointer.offset ipc)))
          < 2 ^ imm_size mt]).

(* the jal label facts *)
Hypothesis Ojal_lab : forall bmap gps imem iregs ipc tpc ms l,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IJal l) ->
  Intermediate.GlobalEnv.find_label_in_component G ipc l = Some tpc ->
  forall Cprocs,
    Intermediate.prog_procedures ilp (Pointer.component ipc)
      = Some Cprocs ->
    exists jt pt Ptcode,
      [/\ Pointer.block tpc
            = proc_nb0 ilp (Pointer.component ipc) + jt,
          List.nth_error (elementsm Cprocs) jt = Some (pt, Ptcode),
          (0 <= Pointer.offset tpc)%Z,
          List.nth_error Ptcode (Z.to_nat (Pointer.offset tpc))
            = Some (ILabel l)
        & pc0 + (side_flat_pos (Pointer.component ipc) pt Ptcode
                   (Z.to_nat (Pointer.offset tpc)) + 0)
          < 2 ^ imm_size mt].

(* along compiled runs, a jal executing above a nonempty frame stack
   sits inside a call window (only the wrap-main stub's jal is naked,
   and it only ever runs at the bottom) *)
Hypothesis Ojal_dead : forall bmap gps imem iregs ipc ms l
       (Cprocs : NMap Machine.code) (j : nat)
       (P0 : Procedure.id) (Pcode : Machine.code),
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IJal l) ->
  Intermediate.prog_procedures ilp (Pointer.component ipc)
    = Some Cprocs ->
  Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
  List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
  (0 <= Pointer.offset ipc)%Z ->
  gps <> [::] ->
  dead_at Pcode (Z.to_nat (Pointer.offset ipc)) = true.

(* the loaded cells are plain data *)
Hypothesis Oload : forall bmap gps imem iregs ipc ms r1 r2 bp op v,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
  (0 <= op)%Z /\
  (r2 <> R_RA ->
   forall base a,
      amap_get bmap (Pointer.component ipc) bp = Some base ->
      getm (Symbolic.mem ms)
        (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
      vtag (taga a) = LRC.Other
      \/ (vtag (taga a) = LRC.Invalidated /\ v = Undef)).

(* the stored cells are plain data *)
Hypothesis Ostore : forall bmap gps imem imem' iregs ipc ms r1 r2 bp op,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
  Intermediate.Register.get r1 iregs
    = Ptr (Pointer.component ipc, bp, op) ->
  Memory.Memory.store imem (Pointer.component ipc, bp, op)
    (Intermediate.Register.get r2 iregs) = Some imem' ->
  [/\ (0 <= op)%Z,
      (r2 <> R_RA ->
       forall base a,
          amap_get bmap (Pointer.component ipc) bp = Some base ->
          getm (Symbolic.mem ms)
            (@word_of_nat (word_size mt) (base + Z.to_nat op))
          = Some a ->
          vtag (taga a) = LRC.Other)
    & (forall base a,
          amap_get bmap (Pointer.component ipc) bp = Some base ->
          getm (Symbolic.mem ms)
            (@word_of_nat (word_size mt) (base + Z.to_nat op))
          = Some a ->
          vtag (taga a) = LRC.Other
          \/ vtag (taga a) = LRC.Invalidated)].

(* the event argument words convert back to the traced integers *)
Hypothesis Oconv : forall bmap gps imem iregs ipc ms z w t,
  ireach (gps, imem, iregs, ipc) ->
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.Register.get R_COM iregs = Int z ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt)
       (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
  Symbolic.convert (word.int_of_word w) = z.

(* the call entry statics: head tag, import listing, entry fit,
   entry-point decomposition *)
Hypothesis Ocall : forall bmap gps imem iregs ipc ms C' p b,
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (ICall C' p) ->
  imported_procedure (genv_interface G) (Pointer.component ipc) C' p ->
  EntryPoint.get C' p (genv_entrypoints G) = Some b ->
  exists cl,
    [/\ head_tag (side_of C') C' p
          = LRC.MTag LRC.Other C' (Some (p, cl)) true,
        mem_seq cl (Pointer.component ipc) = true,
        pc0 + side_entry_pos C' p < 2 ^ imm_size mt
      & exists CprocsC jc Pcode',
          [/\ Intermediate.prog_procedures ilp C' = Some CprocsC,
              b = proc_nb0 ilp C' + jc,
              List.nth_error (elementsm CprocsC) jc = Some (p, Pcode')
            & exists i0, List.nth_error Pcode' 0 = Some i0]].

(* the alloc oracle: syscall dispatch cell absent, the syscall's
   result state, block freshness, and the produced memory's relation *)
Hypothesis Oalloc : forall bmap gps imem imem' iregs ipc ms
                           rptr rsize szZ bI wsz v4
                           (t4 : LRC.value_tag),
  lin_match SINV bmap gps imem iregs ipc ms ->
  Intermediate.GlobalEnv.executing G ipc (IAlloc rptr rsize) ->
  Intermediate.Register.get rsize iregs = Int szZ ->
  Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
    = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl rsize)))
    = Some (wsz@LRC.Other) ->
  getm (Symbolic.regs ms)
    (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl R_RA)))
    = Some (v4@t4) ->
  exists st4 : @Symbolic.state mt LRC.lrc_tags unit,
    [/\ getm (Symbolic.mem ms) (word_of_nat Merged.alloc_label) = None,
        code_region_ok (Symbolic.mem st4),
        amap_get bmap (Pointer.component ipc) bI = None,
        (forall Cprocs P0 Pcode,
            Intermediate.prog_procedures (side_of (Pointer.component ipc))
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
                        ((side_flat_pos (Pointer.component ipc) P0 Pcode
                            (Z.to_nat (Pointer.offset ipc)) + 3) + pc0))
                       @LRC.InternalJump))
                 ((word_of_nat Merged.alloc_label)
                    @(LRC.Level (cross_frames (Pointer.component ipc) gps)
                        (Pointer.component ipc))) tt)
            = Some st4)
      & (forall (max : mword mt) (len : nat),
            0 < len ->
            Symbolic.mem st4
            = unionm (Symbolic.mem ms)
                (mkfmap (mkseq (fun n =>
                   ((max + as_word (ssrint.Posz (n + 1)))%w,
                    (as_word (ssrint.Posz 0))
                      @(LRC.def_mem_tag (Pointer.component ipc) false)))
                   len)) ->
            mem_rel (amap_set bmap (Pointer.component ipc) bI
                       ((eqtype.val max).+1)) imem' (Symbolic.mem st4))
        /\ (forall w a,
              getm (Symbolic.mem ms) w = Some a ->
              getm (Symbolic.mem st4) w = Some a)].

(* -------- packaging helpers -------- *)

Local Lemma pack_silent (bmap' : addr_map) (gpsF : CS.stack)
    (imemF : Memory.Memory.t) (iregsF : Intermediate.Register.t)
    (ipcF : Pointer.t) (ms : @Symbolic.state mt lrc_tags unit) :
  (exists ms', step_me (NC := NC) ms ms' None
     /\ lin_match SINV bmap' gpsF imemF iregsF ipcF ms') ->
  exists (bmapx : addr_map)
         (ms1 msF : @Symbolic.state mt lrc_tags unit),
    [/\ step_me (NC := NC) ms ms1 None,
        me_sstar NC ms1 msF
      & lin_match SINV bmapx gpsF imemF iregsF ipcF msF].
Proof.
case=> ms' [S M]; exists bmap', ms', ms'; split=> //.
exact: me_sstar_refl.
Qed.

Local Lemma pack_event (ev : Events.event) (bmap' : addr_map)
    (gpsF : CS.stack) (imemF : Memory.Memory.t)
    (iregsF : Intermediate.Register.t) (ipcF : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  (exists ms', step_me (NC := NC) ms ms' (Some ev)
     /\ lin_match SINV bmap' gpsF imemF iregsF ipcF ms') ->
  exists (bmapx : addr_map)
         (ms1 msF : @Symbolic.state mt lrc_tags unit),
    [/\ step_me (NC := NC) ms ms1 (Some ev),
        me_sstar NC ms1 msF
      & lin_match SINV bmapx gpsF imemF iregsF ipcF msF].
Proof.
case=> ms' [S M]; exists bmap', ms', ms'; split=> //.
exact: me_sstar_refl.
Qed.

Local Lemma pack_call (ev : Events.event) (bmap' : addr_map)
    (gpsF : CS.stack) (imemF : Memory.Memory.t)
    (iregsF : Intermediate.Register.t) (ipcF : Pointer.t)
    (ms : @Symbolic.state mt lrc_tags unit) :
  (exists ms1 ms2,
     [/\ step_me (NC := NC) ms ms1 (Some ev),
         step_me (NC := NC) ms1 ms2 None
       & lin_match SINV bmap' gpsF imemF iregsF ipcF ms2]) ->
  exists (bmapx : addr_map)
         (ms1 msF : @Symbolic.state mt lrc_tags unit),
    [/\ step_me (NC := NC) ms ms1 (Some ev),
        me_sstar NC ms1 msF
      & lin_match SINV bmapx gpsF imemF iregsF ipcF msF].
Proof.
case=> ms1 [ms2 [S1 S2 M]]; exists bmap', ms1, ms2; split=> //.
by eapply me_sstar_step; [exact S2 | eapply me_sstar_refl].
Qed.

(* -------- the assembled diagram -------- *)

Theorem diag_all (bmap : addr_map) (s1 s2 : CS.state)
    (e : Events.trace) (ms : @Symbolic.state mt lrc_tags unit) :
  ireach s1 ->
  (let '(gps, imem, iregs, ipc) := s1 in
     lin_match SINV bmap gps imem iregs ipc ms) ->
  CS.step G s1 e s2 ->
  exists (bmap' : addr_map)
         (ms1 msF : @Symbolic.state mt lrc_tags unit),
    [/\ step_me (NC := NC) ms ms1 (ohead e),
        me_sstar NC ms1 msF
      & let '(gps2, imem2, iregs2, ipc2) := s2 in
          lin_match SINV bmap' gps2 imem2 iregs2 ipc2 msF].
Proof.
move=> Hreach Hm Hstep.
inversion Hstep; subst; clear Hstep.
- (* Nop *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  apply: pack_silent.
  eapply diag_nop; try eassumption.
  + move=> mpc' HS0; exact: (ss_nop Hspec mpc' Hex HS0).
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Label *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  apply: pack_silent.
  eapply diag_label; try eassumption.
  + move=> mpc' HS0; exact: (ss_label Hspec mpc' Hex HS0).
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Const *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hra : r <> R_RA := Ora Hside HgetP Hnth.
  apply: pack_silent.
  eapply diag_const; try eassumption.
  + reflexivity.
  + exact: (Oimm Hm Hex).
  + move=> mpc' HS0; exact: (ss_const Hspec mpc' Hex Hra HS0).
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Mov *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have [Hra1 Hra2] : r1 <> R_RA /\ r2 <> R_RA
    := Ora Hside HgetP Hnth.
  have [w1 [t1 [Hw1 Hv1 Ht1 Hpin]]]
    := regs_rel_w_get_any (lm_regs Hm) Hra1.
  case: Ht1 => Et1; subst t1.
  + (* Other-tagged source *)
    apply: pack_silent.
    eapply diag_mov_strong; try eassumption.
    * reflexivity.
    * move=> mpc' HS0; exact: (ss_mov Hspec mpc' Hex Hra1 Hra2 Hw1 HS0).
    * by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
  + (* Invalidated source: the I value is Undef *)
    have Hu1 : Intermediate.Register.get r1 regs0 = Undef.
    { case E: (Intermediate.Register.get r1 regs0) => [z|p|] //.
      - by have := Hpin ltac:(rewrite E; discriminate).
      - by have := Hpin ltac:(rewrite E; discriminate). }
    apply: pack_silent.
    eapply diag_mov_inv; try eassumption.
    * reflexivity.
    * move=> mpc' HS0;
        exact: (ss_mov_inv Hspec mpc' Hex Hra1 Hra2 Hu1 Hw1 HS0).
    * by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* BinOp *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have [Hra1 Hra2 Hra3] : [/\ r1 <> R_RA, r2 <> R_RA & r3 <> R_RA]
    := Ora Hside HgetP Hnth.
  have [Htag1 Htag2] := Otag Hreach Hm Hside HgetP Hnth.
  have [w1 [t1 [Hw1 Hv1 _ _]]]
    := regs_rel_w_get_any (lm_regs Hm) Hra1.
  have Et1 : t1 = LRC.Other := Htag1 _ Hw1.
  subst t1.
  have [w2 [t2 [Hw2 Hv2 _ _]]]
    := regs_rel_w_get_any (lm_regs Hm) Hra2.
  have Et2 : t2 = LRC.Other := Htag2 _ Hw2.
  subst t2.
  apply: pack_silent.
  eapply diag_binop with (r1 := r1) (r2 := r2) (w1 := w1) (w2 := w2);
    try eassumption.
  + rewrite /result; reflexivity.
  + exact: (Obinop Hreach Hm Hex Hv1 Hv2).
  + move=> mpc' HS0; exact: (ss_binop Hspec mpc' Hex Hra3 Hw1 Hw2 HS0).
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Load *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Ptr _ |- _ => move: Hg => HG
  end.
  match goal with
  | Hc : Pointer.component _ = Pointer.component _ |- _ =>
      move: Hc => HC
  end.
  match goal with
  | Hl : Memory.Memory.load _ _ = Some _ |- _ => move: Hl => HL
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hra1 : r1 <> R_RA := Ora Hside HgetP Hnth.
  case: ptr HG HC HL => [[cp bp] opz] HG /= HC HL; subst cp.
  have [Hoffp Hvtag0]
    := Oload Hm Hex HG HL.
  have [Era | Hra2] := reg_ra_dec r2.
  + (* pop-R_RA site: the cell's tag moves into R_RA *)
    subst r2.
    apply: pack_silent.
    eapply diag_load_ra with (r1 := r1); try eassumption.
    * reflexivity.
    * move=> base w2 cvt ent mpc' Hamap Hcell HS0.
      have HO := Oload_ra Hreach Hm Hex HG HL Hamap Hcell.
      exact: (ss_load_ra Hspec mpc' Hm Hex HG HL Hamap Hcell HO).
    * by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
  + (* fetch the cell to decide its tag class *)
    have Hmrl0 : forall C1 b1 o1 v1,
        Memory.Memory.load mem0 (C1, b1, o1) = Some v1 ->
        exists base a,
          [/\ amap_get bmap C1 b1 = Some base,
              getm (Symbolic.mem ms)
                (@word_of_nat (word_size mt) (base + Z.to_nat o1))
                = Some a,
              val_rel_b bmap v1 (vala a),
              color (taga a) = C1
            & is_code (taga a) = false].
    { by case: (lm_mem Hm). }
    have [base0 [a0 [Hamap0 Hcell0 _ _ _]]] := Hmrl0 _ _ _ _ HL.
    case: (Hvtag0 Hra2 _ _ Hamap0 Hcell0)
      => [Ho0 | [Hi0 Hu0]].
    * (* Other-tagged cell *)
      have Hvtag : forall base a,
          amap_get bmap (Pointer.component pc1) bp = Some base ->
          getm (Symbolic.mem ms)
            (@word_of_nat (word_size mt) (base + Z.to_nat opz))
            = Some a ->
          vtag (taga a) = LRC.Other.
      { move=> base a Ha Hg.
        have Eb : base = base0 by congruence.
        subst base.
        have Ea : a = a0 by congruence.
        by subst a. }
      apply: pack_silent.
      eapply diag_load with (r1 := r1); try eassumption.
      -- reflexivity.
      -- move=> base w ent mpc' Hamap1 Hcell1 HS0;
           exact: (ss_load Hspec mpc' Hex Hra2 HG HL Hamap1 Hcell1 HS0).
      -- by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
    * (* Invalidated cell: the loaded value is Undef *)
      have Hvtag : forall base a,
          amap_get bmap (Pointer.component pc1) bp = Some base ->
          getm (Symbolic.mem ms)
            (@word_of_nat (word_size mt) (base + Z.to_nat opz))
            = Some a ->
          vtag (taga a) = LRC.Invalidated.
      { move=> base a Ha Hg.
        have Eb : base = base0 by congruence.
        subst base.
        have Ea : a = a0 by congruence.
        by subst a. }
      apply: pack_silent.
      eapply diag_load_inv with (r1 := r1); try eassumption.
      -- reflexivity.
      -- move=> base w ent mpc' Hamap1 Hcell1 HS0;
           exact: (ss_load_inv Hspec mpc' Hex Hra2 HG HL Hu0 Hamap1
                     Hcell1 HS0).
      -- by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Store *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Ptr _ |- _ => move: Hg => HG
  end.
  match goal with
  | Hc : Pointer.component _ = Pointer.component _ |- _ =>
      move: Hc => HC
  end.
  match goal with
  | Hs : Memory.Memory.store _ _ _ = Some _ |- _ => move: Hs => HST
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hra1 : r1 <> R_RA := Ora Hside HgetP Hnth.
  case: ptr HG HC HST => [[cp bp] opz] HG /= HC HST; subst cp.
  have [Hoffp Hvtag0 Hvt2]
    := Ostore Hm Hex HG HST.
  have Hld : loadable mem0 (Pointer.component pc1, bp, opz)
    := Memory_store_loadable HST.
  have [Era | Hra2] := reg_ra_dec r2.
  + (* push-R_RA site: R_RA's tag moves into the cell *)
    subst r2.
    have HraU := Oraud Hreach Hm Hex.
    apply: pack_silent.
    eapply diag_store_ra with (r1 := r1); try eassumption.
    * move=> base w2 ts oldv oldvt ent mpc' Hamap Hra' Hcell Hovt HS0;
        exact: (ss_store_ra Hspec mpc' Hm Hex HG HST Hamap Hra' Hcell
                  Hovt).
    * by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
  + have [w2 [t2 [Hw2 Hv2 Ht2 Hpin2]]]
      := regs_rel_w_get_any (lm_regs Hm) Hra2.
    case: Ht2 => Et2; subst t2.
    * (* Other-tagged stored value *)
      have Hvtag := Hvtag0 Hra2.
      apply: pack_silent.
      eapply diag_store with (r1 := r1); try eassumption.
      -- move=> base w oldv ent mpc' Hamap0 Hw0 Hcell0 HS0;
           exact: (ss_store Hspec mpc' Hex Hra2 HG HST Hamap0 Hw0
                     Hcell0 HS0).
      -- by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
    * (* Invalidated stored value: the I value is Undef *)
      have Hu2 : Intermediate.Register.get r2 regs0 = Undef.
      { case E: (Intermediate.Register.get r2 regs0) => [z|p|] //.
        - by have := Hpin2 ltac:(rewrite E; discriminate).
        - by have := Hpin2 ltac:(rewrite E; discriminate). }
      have Hvtag := Hvtag0 Hra2.
      apply: pack_silent.
      eapply diag_store_inv with (r1 := r1); try eassumption.
      -- move=> base w oldv ent mpc' Hamap0 Hw0 Hcell0 HS0;
           exact: (ss_store_inv Hspec mpc' Hex Hra2 Hu2 HG HST Hamap0
                     Hw0 Hcell0 HS0).
      -- by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Jal *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hf : Intermediate.GlobalEnv.find_label_in_component _ _ _ = Some _
    |- _ => move: Hf => HF
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have Hcmp := esym (Intermediate.GlobalEnv.find_label_in_component_1
                       _ _ _ _ HF).
  have Hjl := Ojal_lab Hm Hex HF.
  apply: pack_silent.
  eapply diag_jal; try eassumption.
  + reflexivity.
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
  + move=> Cp0 j0 Q0 Qc0 mpc' Hilp0 Hblk0 Hjnth0 Hoff0 HS0;
      exact: (ss_push_jal Hspec mpc' Hex HF Hilp0 Hblk0 Hjnth0 Hoff0
                (Ojal_dead Hreach Hm Hex Hilp0 Hblk0 Hjnth0 Hoff0)
                HS0).
- (* Jump *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hc : Pointer.component _ = Pointer.component _ |- _ =>
      move: Hc => Hcmp
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have Hfj := ss_frame_jump Hspec Hm Hex Hcmp.
  apply: pack_silent.
  eapply diag_jump; try eassumption.
  + reflexivity.
  + move=> mpc' HS0; exact: (ss_pop_jump Hspec mpc' Hex Hcmp HS0).
- (* BnzNZ *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Int _ |- _ => move: Hg => HG
  end.
  match goal with
  | Hn : (_ <> _)%Z |- _ => move: Hn => Hnz
  end.
  match goal with
  | Hf : Intermediate.GlobalEnv.find_label_in_procedure _ _ _ = Some _
    |- _ => move: Hf => HF
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hra : r <> R_RA := Ora Hside HgetP Hnth.
  have Hdef : Intermediate.Register.get r regs0 <> Undef by rewrite HG.
  have [w [Hw Hv]] := regs_rel_w_get (lm_regs Hm) Hra Hdef.
  rewrite HG in Hv.
  have [Hcmp Hblk]
    := Intermediate.GlobalEnv.find_label_in_procedure_guarantees
         _ _ _ _ HF.
  have [Hofft Hbund] := Obnz_lab Hm Hex HF.
  have Hcmp' := esym Hcmp.
  have Hblk' := esym Hblk.
  have Hw0 := Obnz_nz Hreach Hm Hex HG Hnz Hv.
  apply: pack_silent.
  eapply diag_bnz_nz; try eassumption.
  move=> mpc' HS0; exact: (ss_bnz_nz Hspec mpc' Hex HF HG Hnz HS0).
- (* BnzZ *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Int _ |- _ => move: Hg => HG
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have Hra : r <> R_RA := Ora Hside HgetP Hnth.
  have Hdef : Intermediate.Register.get r regs0 <> Undef by rewrite HG.
  have [w [Hw Hv]] := regs_rel_w_get (lm_regs Hm) Hra Hdef.
  rewrite HG in Hv.
  have Hw0 := Obnz_z Hm Hex HG Hv.
  apply: pack_silent.
  eapply diag_bnz_z; try eassumption.
  + move=> mpc' HS0; exact: (ss_bnz_z Hspec mpc' Hex HG HS0).
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
- (* Alloc *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Int _ |- _ => move: Hg => HG
  end.
  match goal with
  | Ha : Memory.Memory.alloc _ _ _ = Some _ |- _ => move: Ha => HA
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have [Cp [Q0 [Qc [j0 [[Hside HgetP Hnth _ _] _]]]]]
    := lm_fetch Hin (lm_pc Hm) Hex.
  have [Hrptr Hrsz] : rptr <> R_RA /\ rsize <> R_RA
    := Ora Hside HgetP Hnth.
  have [bI EbI] : exists bI, ptr = (Pointer.component pc1, bI, 0%Z).
  { move: (HA); rewrite /Memory.Memory.alloc.
    case: (getm mem0 (Pointer.component pc1)) => [memC|] //.
    case: (ComponentMemory.alloc memC (Z.to_nat size)) => memC' b.
    by case=> _ <-; exists b. }
  subst ptr.
  have Hdef : Intermediate.Register.get rsize regs0 <> Undef
    by rewrite HG.
  have [wsz [Hwsz Hvsz]] := regs_rel_w_get (lm_regs Hm) Hrsz Hdef.
  have Hwsz' : getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl rsize)))
      = Some (wsz@LRC.Other) := Hwsz.
  have [a4 Hc4a] := lm_total Hm (isT : 4 \in reg_keys).
  case: a4 Hc4a => v4 t4 Hc4a.
  have Hv4 : getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl R_RA)))
      = Some (v4@t4) := Hc4a.
  have [st4 [H9 H10 H11 Hafun [Hmr Hmono]]]
    := Oalloc Hm Hex HG HA Hwsz' Hv4.
  have Hterm' : forall Cprocs P0 Pcode,
      Intermediate.prog_procedures (side_of (Pointer.component pc1))
        (Pointer.component pc1) = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode (Z.to_nat (Pointer.offset pc1))
        = Some (IAlloc rptr rsize) ->
      exists i',
        List.nth_error Pcode (Z.to_nat (Pointer.offset pc1)).+1
        = Some i'.
  { by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn). }
  have [max [len [ms1 [ms2 [ms3 [ms5 [msF
    [S1 S2 [S3 S4] [S5 S6] M]]]]]]]]
    := diag_alloc
         Hb Hin Hrptr HG HA erefl Hwsz' Hv4 H9 H10 H11 Hterm' Hafun Hmr
         (fun mregs' mpc' base' HraEq0 HS0 =>
            ss_alloc Hspec base' mpc' Hex Hrptr HG HA Hmono HraEq0 HS0)
         Hm Hex.
  exists (amap_set bmap (Pointer.component pc1) bI ((eqtype.val max).+1)),
    ms1, msF.
  split.
  + exact S1.
  + eapply me_sstar_step; first exact S2.
    eapply me_sstar_step; first exact S3.
    eapply me_sstar_step; first exact S4.
    eapply me_sstar_step; first exact S5.
    eapply me_sstar_step; first exact S6.
    eapply me_sstar_refl.
  + exact M.
- (* Call *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hn : _ <> _ |- _ => move: Hn => Hneq
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Int _ |- _ =>
      move: Hg => HRcom
  end.
  match goal with
  | Hi : imported_procedure _ _ _ _ |- _ => move: Hi => Himp
  end.
  match goal with
  | Hp : EntryPoint.get _ _ _ = Some _ |- _ => move: Hp => HEP
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have Hne : (Pointer.component pc1 == C') = false
    by apply/negbTE/eqP.
  have [cl [Hht Hmemseq Hfit Hentry]]
    := Ocall Hm Hex Himp HEP.
  have Hcv : forall w t,
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
      Symbolic.convert (word.int_of_word w) = call_arg.
  { move=> w t Hw; exact: (Oconv Hreach Hm HRcom Hw). }
  have HCin : C' \in domm (Intermediate.prog_interface ilp).
  { case: (Hentry) => CprocsX [jX] [PcodeX] [HilpX _ _ _].
    apply: Hdomm. by rewrite mem_domm HilpX. }
  apply: pack_call.
  eapply diag_call; try eassumption.
  + by move=> ??? Hs Hg Hn; apply: (Onext Hs Hg Hn).
  + move=> mregs' mpc' Cp0 j0 Q0 Qc0 HCin0 Hilp0 Hblk0 Hjnth0 Hoff0
           Hra0 HS0;
      exact: (ss_push_call Hspec b mpc' Hne HCin0 Hex Hilp0 Hblk0
                Hjnth0 Hoff0 Hra0 HS0).
- (* Return *)
  match goal with
  | He : Intermediate.GlobalEnv.executing _ _ _ |- _ => move: He => Hex
  end.
  match goal with
  | Hn : _ <> _ |- _ => move: Hn => Hneq
  end.
  match goal with
  | Hg : Intermediate.Register.get _ _ = Int _ |- _ =>
      move: Hg => HRcom
  end.
  have Hin := Hdomm (lm_pc_domm Hm).
  have Hne : (Pointer.component pc1 == Pointer.component pc') = false
    by apply/negbTE/eqP.
  have Hcv : forall w t,
      getm (Symbolic.regs ms)
        (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
      Symbolic.convert (word.int_of_word w) = ret_arg.
  { move=> w t Hw; exact: (Oconv Hreach Hm HRcom Hw). }
  have Hfr := ss_frame_ret Hspec Hm Hex Hne.
  apply: pack_event.
  eapply diag_return; try eassumption.
  + reflexivity.
  + move=> mregs' mpc' HS0;
      exact: (ss_pop_ret Hspec mregs' mpc' Hex Hne HS0).
Qed.

(* the diagram lifted to whole runs: every I star is mirrored by a
   trace-equal me star through lin_match *)
Theorem star_diag (s1 s2 : CS.state) (t : Events.trace)
    (bmap : addr_map) (ms : @Symbolic.state mt lrc_tags unit) :
  star CS.step G s1 t s2 ->
  ireach s1 ->
  (let '(gps, imem, iregs, ipc) := s1 in
     lin_match SINV bmap gps imem iregs ipc ms) ->
  exists (bmap' : addr_map)
         (msF : @Symbolic.state mt lrc_tags unit),
    star (fun _ : unit => step_t NC) tt ms t msF
    /\ (let '(gps2, imem2, iregs2, ipc2) := s2 in
        lin_match SINV bmap' gps2 imem2 iregs2 ipc2 msF).
Proof.
move=> Hstar; elim: Hstar bmap ms.
- move=> s bmap ms _ Hm.
  exists bmap, ms; split=> //; exact: star_refl.
- move=> sa t1 sb t2 sc tw Hstep Hstar' IH Et bmap ms Hreach Hm.
  have [bmap1 [ms1 [msF0 [S1 SS M1]]]] := diag_all Hreach Hm Hstep.
  have [bmapF [msF [Sstar MF]]] := IH _ _ (ireach_step Hreach Hstep) M1.
  exists bmapF, msF; split=> //.
  have [Et1 | [ev Et1]] := cs_step_trace Hstep; subst t1.
  + have St : step_t NC ms Events.E0 ms1 := S1.
    eapply star_step; [exact St| |by rewrite Et].
    eapply star_trans; [exact: (me_sstar_star SS) | exact Sstar |].
    reflexivity.
  + have St : step_t NC ms [:: ev] ms1 := S1.
    eapply star_step; [exact St| |by rewrite Et].
    eapply star_trans; [exact: (me_sstar_star SS) | exact Sstar |].
    reflexivity.
Qed.

(* ==================== initial states ==================== *)

(* the initial register file satisfies the weak relation *)
Lemma regs_rel_w_of_b (bmap : addr_map) iregs
    (mregs : {fmap reg mt -> @ratom mt}) :
  regs_rel_b bmap iregs mregs -> regs_rel_w bmap iregs mregs.
Proof.
move=> Hrel r _.
have [a [Hget Hval Htag]] := Hrel r.
by exists a; split=> //; left.
Qed.

(* the me machine's initial state is one silent entry stutter away from
   matching the I machine's initial state *)
Theorem match_initial (CprocsM : NMap Machine.code) (bM : Block.id) :
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures pra Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base pra Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  exists ms',
    step_me (NC := NC)
      (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
      ms' None
    /\ (let '(gps, imem, iregs, ipc) := CS.initial_machine_state ilp in
        lin_match SINV (static_amap pbW) gps imem iregs ipc ms').
Proof.
move=> Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0.
have HmainL : Component.main \in domm (Intermediate.prog_procedures pra)
  by rewrite mem_domm HmainP.
have Hilp : Intermediate.prog_procedures ilp Component.main
            = Some CprocsM.
{ by rewrite /ilp /Intermediate.program_link /= unionmE HmainP. }
have HinI : Component.main \in domm (Intermediate.prog_interface ilp).
{ apply: Hdomm. by rewrite mem_domm Hilp. }
have Hep' : EntryPoint.get Component.main Procedure.main
    (Intermediate.GlobalEnv.genv_entrypoints G) = Some bM.
{ move: Hep.
  rewrite /Intermediate.prepare_procedures_entrypoints /G
          /Intermediate.GlobalEnv.prepare_global_env.
  by case: (Intermediate.prepare_procedures_initial_memory ilp)
    => [[? ?] ?]. }
have [j [Pcode [HbM Hjnth]]] := genv_entry_spec HinI Hilp Hep'.
have HPc : getm CprocsM Procedure.main = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ Hjnth). }
have [i0 Hi0] := Hmain0 _ HPc.
have HsideC : Intermediate.prog_procedures (side_of Component.main)
    Component.main = Some CprocsM.
{ by rewrite /side_of HmainL. }
have Emp : find (fun '(_, tag) => color tag == Component.main) codeW
           = side_entry_pos Component.main Procedure.main.
{ rewrite find_pred_pairE.
  rewrite (find_color_link L P C prb HmainP Hp0).
  by rewrite /side_entry_pos HmainL Hpb0 !addn0. }
have [rca [Hrc _ _]] := init_regs_rel_b (static_amap pbW) R_COM.
rewrite /CS.initial_machine_state Hmain.
case E: (Intermediate.prepare_procedures_initial_memory ilp)
  => [[m1 p1] e1].
have Em1 : Intermediate.prepare_procedures_memory ilp = m1
  by rewrite /Intermediate.prepare_procedures_memory E.
have Ee1 : EntryPoint.get Component.main Procedure.main e1 = Some bM
  by move: Hep; rewrite /Intermediate.prepare_procedures_entrypoints E.
rewrite Ee1 /=.
exists (@Symbolic.State mt lrc_tags _
  (unionm (encode_code codeW pc0) (initial_memory (mt := mt) pbW))
  Merged.reg0
  ((word_of_nat
      (side_flat_pos Component.main Procedure.main Pcode 0 + pc0))
     @(LRC.Level 0 Component.main)) tt).
split.
- have -> : Merged.initial_state codeW pbW (Intermediate.prog_interface ilp)
    = @Symbolic.State mt lrc_tags _
        (unionm (encode_code codeW pc0) (initial_memory (mt := mt) pbW))
        Merged.reg0
        ((word_of_nat
            (side_entry_pos Component.main Procedure.main + pc0))
           @(LRC.Level 0 Component.main)) tt.
  { rewrite /Merged.initial_state; cbv zeta.
    by rewrite Emp [pc0 + _]addnC. }
  eapply sim_entry_nop; try eassumption.
  move=> w a Henc; by rewrite unionmE Henc.
- constructor => /=.
  + exists CprocsM, j, Procedure.main, Pcode.
    split.
    * exact Hilp.
    * exact HbM.
    * exact Hjnth.
    * by [].
    * by split.
  + rewrite -Em1.
    have Hsz' : size (linearize_bufs (Intermediate.prog_buffers ilp))
                + size codeW < 2 ^ word_size mt := Hsz.
    exact: (initial_mem_rel Hsz' Hptr).
  + exact: regs_rel_w_of_b (init_regs_rel_b _).
  + move=> w a Henc; by rewrite unionmE Henc.
  + exact: HS0.
  + exact: regs_total_reg0.
Qed.

(* the mirrored initial-states lemma: main owned by the RIGHT side *)
Theorem match_initial_r (CprocsM : NMap Machine.code) (bM : Block.id) :
  Intermediate.well_formed_program pra ->
  Component.main \notin domm (Intermediate.prog_interface pra) ->
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures prb Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base prb Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  exists ms',
    step_me (NC := NC)
      (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
      ms' None
    /\ (let '(gps, imem, iregs, ipc) := CS.initial_machine_state ilp in
        lin_match SINV (static_amap pbW) gps imem iregs ipc ms').
Proof.
move=> Hwfa HnotA Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0.
have HmainNotA : Component.main
    \notin domm (Intermediate.prog_procedures pra).
{ by rewrite -(Intermediate.wfprog_defined_procedures Hwfa). }
have HgA : Intermediate.prog_procedures pra Component.main = None.
{ by apply/dommPn. }
have Hilp : Intermediate.prog_procedures ilp Component.main
            = Some CprocsM.
{ by rewrite /ilp /Intermediate.program_link /= unionmE HgA HmainP. }
have HinI : Component.main \in domm (Intermediate.prog_interface ilp).
{ apply: Hdomm. by rewrite mem_domm Hilp. }
have Hep' : EntryPoint.get Component.main Procedure.main
    (Intermediate.GlobalEnv.genv_entrypoints G) = Some bM.
{ move: Hep.
  rewrite /Intermediate.prepare_procedures_entrypoints /G
          /Intermediate.GlobalEnv.prepare_global_env.
  by case: (Intermediate.prepare_procedures_initial_memory ilp)
    => [[? ?] ?]. }
have [j [Pcode [HbM Hjnth]]] := genv_entry_spec HinI Hilp Hep'.
have HPc : getm CprocsM Procedure.main = Some Pcode.
{ apply: BufferLayout.In_fmap_getm.
  exact (List.nth_error_In _ _ Hjnth). }
have [i0 Hi0] := Hmain0 _ HPc.
have HsideC : Intermediate.prog_procedures (side_of Component.main)
    Component.main = Some CprocsM.
{ by rewrite /side_of (negbTE HmainNotA). }
have Emp : find (fun '(_, tag) => color tag == Component.main) codeW
           = side_entry_pos Component.main Procedure.main.
{ rewrite find_pred_pairE.
  rewrite (find_color_link_r L P C Hwfa HnotA HmainP Hp0).
  by rewrite /side_entry_pos (negbTE HmainNotA) Hpb0 !addn0. }
have [rca [Hrc _ _]] := init_regs_rel_b (static_amap pbW) R_COM.
rewrite /CS.initial_machine_state Hmain.
case E: (Intermediate.prepare_procedures_initial_memory ilp)
  => [[m1 p1] e1].
have Em1 : Intermediate.prepare_procedures_memory ilp = m1
  by rewrite /Intermediate.prepare_procedures_memory E.
have Ee1 : EntryPoint.get Component.main Procedure.main e1 = Some bM
  by move: Hep; rewrite /Intermediate.prepare_procedures_entrypoints E.
rewrite Ee1 /=.
exists (@Symbolic.State mt lrc_tags _
  (unionm (encode_code codeW pc0) (initial_memory (mt := mt) pbW))
  Merged.reg0
  ((word_of_nat
      (side_flat_pos Component.main Procedure.main Pcode 0 + pc0))
     @(LRC.Level 0 Component.main)) tt).
split.
- have -> : Merged.initial_state codeW pbW (Intermediate.prog_interface ilp)
    = @Symbolic.State mt lrc_tags _
        (unionm (encode_code codeW pc0) (initial_memory (mt := mt) pbW))
        Merged.reg0
        ((word_of_nat
            (side_entry_pos Component.main Procedure.main + pc0))
           @(LRC.Level 0 Component.main)) tt.
  { rewrite /Merged.initial_state; cbv zeta.
    by rewrite Emp [pc0 + _]addnC. }
  eapply sim_entry_nop; try eassumption.
  move=> w a Henc; by rewrite unionmE Henc.
- constructor => /=.
  + exists CprocsM, j, Procedure.main, Pcode.
    split.
    * exact Hilp.
    * exact HbM.
    * exact Hjnth.
    * by [].
    * by split.
  + rewrite -Em1.
    have Hsz' : size (linearize_bufs (Intermediate.prog_buffers ilp))
                + size codeW < 2 ^ word_size mt := Hsz.
    exact: (initial_mem_rel Hsz' Hptr).
  + exact: regs_rel_w_of_b (init_regs_rel_b _).
  + move=> w a Henc; by rewrite unionmE Henc.
  + exact: HS0.
  + exact: regs_total_reg0.
Qed.

(* ==================== behaviour-level packaging ==================== *)

(* the MP-level program whose me semantics runs the linked linearized
   image *)
Definition Wlin : MicroPolicies.Recomposition.Definitions.program :=
  MicroPolicies.Recomposition.Definitions.Build_program
    (Intermediate.prog_interface ilp) codeW pbW true.

(* matched final states: an I halt lands the me machine on an encoded
   halt cell *)
Lemma match_final (bmap : addr_map) (s : CS.state)
    (ms : @Symbolic.state mt lrc_tags unit) :
  (let '(gps, imem, iregs, ipc) := s in
     lin_match SINV bmap gps imem iregs ipc ms) ->
  CS.final_state G s ->
  final_halt_code ms.
Proof.
case: s => [[[gps imem] iregs] ipc] Hm Hf.
have Hin := Hdomm (lm_pc_domm Hm).
have [iw [itag [Hget Hdec Hic]]] := diag_halt Hb Hin Hm Hf.
clear Hm Hf Hin.
case: ms Hget => m0 r0 [pcv pct] [] /= Hget.
rewrite /final_halt_code Hget /=.
by split.
Qed.

(* THE forward transfer, generic over how the initial match was
   established (main-left or main-right) *)
Theorem fwd_does_prefix_gen (m : finpref_behavior) :
  (exists ms',
     step_me (NC := NC)
       (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
       ms' None
     /\ (let '(gps, imem, iregs, ipc) := CS.initial_machine_state ilp in
         lin_match SINV (static_amap pbW) gps imem iregs ipc ms')) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem ilp) m ->
  does_prefix (me_sem NC Wlin) m.
Proof.
move=> [ms' [Sini Hmi]] Hnw Hdp.
have St : Smallstep.step (me_sem NC Wlin) tt
    (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
    Events.E0 ms' := Sini.
apply/(does_prefix_equiv (det_me_sem NC Wlin)).
move/(does_prefix_equiv (CS.determinacy ilp)): Hdp => Hdp.
case: m Hnw Hdp => t Hnw Hdp.
- (* FTerminates *)
  inversion Hdp as [| |s s' t0 Hini Hstar Hfin| |]; subst.
  move: Hini; rewrite /= /CS.initial_state => ?; subst s.
  have [bmapF [msF [Sme HmF]]] := star_diag Hstar ireach_init Hmi.
  have Sme' : star (prog_step_me NC) tt ms' t msF := Sme.
  eapply does_FTerminates.
  + reflexivity.
  + eapply star_step; [exact St | exact Sme' | by []].
  + exact: match_final HmF Hfin.
- (* FGoes_wrong *)
  by [].
- (* FTbc *)
  inversion Hdp as [s s' t0 Hini Hstar| | | |Hnoinit]; subst; last first.
  + by have := Hnoinit _ (erefl _).
  + move: Hini; rewrite /= /CS.initial_state => ?; subst s.
    have [bmapF [msF [Sme _]]] := star_diag Hstar ireach_init Hmi.
    have Sme' : star (prog_step_me NC) tt ms' t msF := Sme.
    eapply does_FTbc.
    * reflexivity.
    * eapply star_step; [exact St | exact Sme' | by []].
Qed.

(* the forward transfer, main on the left *)
Theorem fwd_does_prefix (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  Intermediate.well_formed_program ilp ->
  Intermediate.closed_program ilp ->
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures pra Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base pra Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem ilp) m ->
  does_prefix (me_sem NC Wlin) m.
Proof.
move=> Hwf Hcl Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0 Hnw Hdp.
exact: (fwd_does_prefix_gen
          (match_initial Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0)
          Hnw Hdp).
Qed.

(* the forward transfer, main on the right *)
Theorem fwd_does_prefix_r (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  Intermediate.well_formed_program pra ->
  Component.main \notin domm (Intermediate.prog_interface pra) ->
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures prb Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base prb Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem ilp) m ->
  does_prefix (me_sem NC Wlin) m.
Proof.
move=> Hwfa HnotA Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0 Hnw Hdp.
exact: (fwd_does_prefix_gen
          (match_initial_r Hwfa HnotA Hsz Hmain HmainP Hp0 Hep Hpb0
             Hmain0 Hptr HS0)
          Hnw Hdp).
Qed.

(* silent me stars counted *)
Lemma me_sstar_starN (ms msF : @Symbolic.state mt lrc_tags unit) :
  me_sstar NC ms msF ->
  exists j, starN (prog_step_me NC) tt j ms Events.E0 msF.
Proof.
elim=> [s|s s' s'' Hst _ [j IH]].
- by exists 0%coq_nat; constructor.
- have St : prog_step_me NC tt s Events.E0 s' := Hst.
  exists (S j).
  by eapply starN_step; [exact St | exact IH | ].
Qed.

(* the me image of a silent I divergence is an unbounded silent ray *)
Lemma diverge_ray (bmap : addr_map) (s : CS.state)
    (ms : @Symbolic.state mt lrc_tags unit) :
  ireach s ->
  (let '(gps, imem, iregs, ipc) := s in
     lin_match SINV bmap gps imem iregs ipc ms) ->
  Forever_silent (CS.sem ilp) s ->
  forall n : nat,
    exists (k : nat) (ms'' : @Symbolic.state mt lrc_tags unit),
      (n <= k)%coq_nat
      /\ starN (prog_step_me NC) tt k ms Events.E0 ms''.
Proof.
move=> Hreach Hm Hdiv n.
elim: n bmap s ms Hreach Hm Hdiv
  => [|n IH] bmap s ms Hreach Hm Hdiv.
- by exists 0%coq_nat, ms; split; [lia|constructor].
- inversion Hdiv as [s1x s2x HstepI HdivI]; subst.
  have [bmap1 [ms1 [msX [S1 SS M1]]]] := diag_all Hreach Hm HstepI.
  have [k [ms'' [Hk HN]]]
    := IH _ _ _ (ireach_step Hreach HstepI) M1 HdivI.
  have [j HssN] := me_sstar_starN SS.
  have St : prog_step_me NC tt ms Events.E0 ms1 := S1.
  exists (S (j + k)%coq_nat), ms''.
  split; [lia|].
  eapply starN_step; [exact St| |by []].
  exact: (starN_silent_compose (L := me_sem NC Wlin) HssN HN).
Qed.

(* THE determinism flip, generic over how the initial match was
   established (main-left or main-right) *)
Theorem bwd_improves_gen (m : finpref_behavior) :
  (exists ms',
     step_me (NC := NC)
       (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
       ms' None
     /\ (let '(gps, imem, iregs, ipc) := CS.initial_machine_state ilp in
         lin_match SINV (static_amap pbW) gps imem iregs ipc ms')) ->
  does_prefix (me_sem NC Wlin) m ->
  exists beh,
    program_behaves (CS.sem ilp) beh
    /\ (prefix m beh \/ behavior_improves_finpref beh m).
Proof.
move=> [ms' [Sini Hmi]] Hdp.
have St0 : Smallstep.step (me_sem NC Wlin) tt
    (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
    Events.E0 ms' := Sini.
have Ime : forall t2 s2,
    star CS.step G (CS.initial_machine_state ilp) t2 s2 ->
    exists (bmap2 : addr_map) (ms2 : @Symbolic.state mt lrc_tags unit),
      Star (me_sem NC Wlin)
        (Merged.initial_state codeW pbW (Intermediate.prog_interface ilp))
        t2 ms2
      /\ (let '(gps, imem, iregs, ipc) := s2 in
          lin_match SINV bmap2 gps imem iregs ipc ms2).
{ move=> t2 s2 Hst.
  have [bmap2 [ms2 [Sme Hm2]]] := star_diag Hst ireach_init Hmi.
  have Sme' : star (prog_step_me NC) tt ms' t2 ms2 := Sme.
  exists bmap2, ms2; split=> //.
  eapply star_step; [exact St0 | exact Sme' | by []]. }
have [beh Hbeh] := program_behaves_exists (CS.sem ilp).
exists beh; split; first exact Hbeh.
move/(does_prefix_equiv (det_me_sem NC Wlin)): Hdp => Hdp.
inversion Hbeh as [s0 beh0 Hini0 Hsb | Hnoinit0]; subst; last first.
- by have := Hnoinit0 (CS.initial_machine_state ilp) (erefl _).
- move: Hini0; rewrite /= /CS.initial_state => ?; subst s0.
  inversion Hsb as [tb sfin Hstb Hfin | tb sdiv Hstb Hdiv
                   | T Hreact | tb sw Hstb Hnostep Hnfin]; subst.
  + (* Terminates tb *)
    have [bmapF [msFI [SmeI HmF]]] := Ime _ _ Hstb.
    have HfinC : final_halt_code msFI := match_final HmF Hfin.
    have HnsI : Nostep (me_sem NC Wlin) msFI.
    { by apply: (sd_final_nostep (det_me_sem NC Wlin)); exact HfinC. }
    case: m Hdp => t Hdp.
    * (* FTerminates *)
      inversion Hdp as [| |sm0 sm t0 Hini2 Hsm Hfm| |]; subst.
      move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
      have Hns_m : Nostep (me_sem NC Wlin) sm.
      { by apply: (sd_final_nostep (det_me_sem NC Wlin)); exact Hfm. }
      destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
        as [[t' [Etr Hres]] | [t' [Etr Hres]]].
      -- have [Et' _] := star_nostep_refl Hres Hns_m.
         subst t'. left. by rewrite /= Etr E0_right.
      -- have [Et' _] := star_nostep_refl Hres HnsI.
         subst t'. left. by rewrite /= Etr E0_right.
    * (* FGoes_wrong *)
      inversion Hdp as [|sm0 sm t0 Hini2 Hsm Hns_m Hnf_m| | Hnoinit|];
        subst; last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ have [Et' Es'] := star_nostep_refl Hres Hns_m.
            subst t' msFI. by have := Hnf_m HfinC.
         ++ have [Et' Es'] := star_nostep_refl Hres HnsI.
            subst t' sm. by have := Hnf_m HfinC.
    * (* FTbc *)
      inversion Hdp as [sm0 sm t0 Hini2 Hsm| | | |Hnoinit]; subst;
        last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ left. rewrite /= Etr. by exists (Terminates t').
         ++ have [Et' _] := star_nostep_refl Hres HnsI.
            subst t'. left. rewrite /= Etr E0_right.
            exists (Terminates Events.E0). by rewrite /= E0_right.
  + (* Diverges tb *)
    have [bmapF [msD [SmeI HmD]]] := Ime _ _ Hstb.
    have HreachD : ireach sdiv by exists tb.
    have Hray : silent_ray (L := me_sem NC Wlin) msD.
    { move=> n.
      have [k [msz [Hk HN]]] := diverge_ray HreachD HmD Hdiv n.
      by exists k, msz; split; [exact Hk | exact HN]. }
    case: m Hdp => t Hdp.
    * (* FTerminates *)
      inversion Hdp as [| |sm0 sm t0 Hini2 Hsm Hfm| |]; subst.
      move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
      have Hns_m : Nostep (me_sem NC Wlin) sm.
      { by apply: (sd_final_nostep (det_me_sem NC Wlin)); exact Hfm. }
      destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
        as [[t' [Etr Hres]] | [t' [Etr Hres]]].
      -- have [Et' Es'] := star_nostep_refl Hres Hns_m.
         subst t' msD.
         by have := ray_nostep_absurd Hray Hns_m.
      -- have [_ Hray2] := silent_ray_absorb (det_me_sem NC Wlin)
                             Hres Hray.
         by have := ray_nostep_absurd Hray2 Hns_m.
    * (* FGoes_wrong *)
      inversion Hdp as [|sm0 sm t0 Hini2 Hsm Hns_m Hnf_m| | Hnoinit|];
        subst; last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ have [Et' Es'] := star_nostep_refl Hres Hns_m.
            subst t' msD.
            by have := ray_nostep_absurd Hray Hns_m.
         ++ have [_ Hray2] := silent_ray_absorb (det_me_sem NC Wlin)
                                Hres Hray.
            by have := ray_nostep_absurd Hray2 Hns_m.
    * (* FTbc *)
      inversion Hdp as [sm0 sm t0 Hini2 Hsm| | | |Hnoinit]; subst;
        last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ left. rewrite /= Etr. by exists (Diverges t').
         ++ have [Et' _] := silent_ray_absorb (det_me_sem NC Wlin)
                              Hres Hray.
            subst t'. left. rewrite /= Etr E0_right.
            exists (Diverges Events.E0). by rewrite /= E0_right.
  + (* Reacts T *)
    have F : forall (n : nat) (sF : CS.state) (TF : traceinf),
        forever_reactive CS.step G sF TF ->
        exists t' s',
          (n < length t')%coq_nat
          /\ behavior_prefix t' (Reacts TF)
          /\ star CS.step G sF t' s'.
    { elim=> [|n IHn] sF TF Hfor.
      - inversion Hfor as [sA sB t2 T2 Hst Hne Hf]; subst.
        exists t2, sB. split; [|split].
        + have Hlen0 : length t2 <> 0%coq_nat.
          { move=> Hz. apply: Hne. by apply List.length_zero_iff_nil. }
          lia.
        + by exists (Reacts T2).
        + exact Hst.
      - inversion Hfor as [sA sB t2 T2 Hst Hne Hf]; subst.
        have [t' [s' [Hlen [Hpref Hstar']]]] := IHn _ _ Hf.
        exists (t2 ** t'), s'. split; [|split].
        + rewrite List.app_length.
          have Hlen0 : length t2 <> 0%coq_nat.
          { move=> Hz. apply: Hne. by apply List.length_zero_iff_nil. }
          lia.
        + case: Hpref => beh' Ebeh'. exists beh'.
          by rewrite behavior_app_assoc -Ebeh'.
        + eapply star_trans; [exact Hst | exact Hstar' | by []]. }
    case: m Hdp => t Hdp.
    * (* FTerminates *)
      inversion Hdp as [| |sm0 sm t0 Hini2 Hsm Hfm| |]; subst.
      move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
      have Hns_m : Nostep (me_sem NC Wlin) sm.
      { by apply: (sd_final_nostep (det_me_sem NC Wlin)); exact Hfm. }
      have [t' [s' [Hlen [HprefT Hstar']]]] := F (length t) _ _ Hreact.
      have [bmapF [msR [SmeI _]]] := Ime _ _ Hstar'.
      destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
        as [[tx [Etr Hres]] | [tx [Etr Hres]]].
      -- have [Etx _] := star_nostep_refl Hres Hns_m.
         subst tx. rewrite E0_right in Etr. subst t'.
         by move: Hlen; lia.
      -- exfalso. subst t.
         move: Hlen. rewrite List.app_length. lia.
    * (* FGoes_wrong *)
      inversion Hdp as [|sm0 sm t0 Hini2 Hsm Hns_m Hnf_m| | Hnoinit|];
        subst; last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         have [t' [s' [Hlen [HprefT Hstar']]]] := F (length t) _ _ Hreact.
         have [bmapF [msR [SmeI _]]] := Ime _ _ Hstar'.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[tx [Etr Hres]] | [tx [Etr Hres]]].
         ++ have [Etx _] := star_nostep_refl Hres Hns_m.
            subst tx. rewrite E0_right in Etr. subst t'.
            by move: Hlen; lia.
         ++ exfalso. subst t.
            move: Hlen. rewrite List.app_length. lia.
    * (* FTbc *)
      inversion Hdp as [sm0 sm t0 Hini2 Hsm| | | |Hnoinit]; subst;
        last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         have [t' [s' [Hlen [HprefT Hstar']]]] := F (length t) _ _ Hreact.
         have [bmapF [msR [SmeI _]]] := Ime _ _ Hstar'.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[tx [Etr Hres]] | [tx [Etr Hres]]].
         ++ left. rewrite /=.
            case: HprefT => beh' Ebeh'. subst t'.
            exists (behavior_app tx beh').
            by rewrite -behavior_app_assoc.
         ++ exfalso. subst t.
            move: Hlen. rewrite List.app_length. lia.
  + (* Goes_wrong tb *)
    have [bmapF [msW [SmeI HmW]]] := Ime _ _ Hstb.
    case: m Hdp => t Hdp.
    * (* FTerminates *)
      inversion Hdp as [| |sm0 sm t0 Hini2 Hsm Hfm| |]; subst.
      move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
      have Hns_m : Nostep (me_sem NC Wlin) sm.
      { by apply: (sd_final_nostep (det_me_sem NC Wlin)); exact Hfm. }
      destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
        as [[t' [Etr Hres]] | [t' [Etr Hres]]].
      -- have [Et' _] := star_nostep_refl Hres Hns_m.
         subst t'. rewrite E0_right in Etr. subst tb.
         right. exists t. split; [reflexivity|].
         rewrite /=. exists Events.E0. by rewrite E0_right.
      -- right. exists tb. split; [reflexivity|].
         rewrite /=. by exists t'.
    * (* FGoes_wrong *)
      inversion Hdp as [|sm0 sm t0 Hini2 Hsm Hns_m Hnf_m| | Hnoinit|];
        subst; last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ have [Et' _] := star_nostep_refl Hres Hns_m.
            subst t'. rewrite E0_right in Etr. subst tb.
            by left.
         ++ right. exists tb. split; [reflexivity|].
            rewrite /=. by exists t'.
    * (* FTbc *)
      inversion Hdp as [sm0 sm t0 Hini2 Hsm| | | |Hnoinit]; subst;
        last first.
      -- by have := Hnoinit _ (erefl _).
      -- move: Hini2; rewrite /= /prog_initial => ?; subst sm0.
         destruct (star_traces_comp (det_me_sem NC Wlin) Hsm SmeI)
           as [[t' [Etr Hres]] | [t' [Etr Hres]]].
         ++ left. rewrite /= Etr. by exists (Goes_wrong t').
         ++ right. exists tb. split; [reflexivity|].
            rewrite /=. by exists t'.
Qed.

(* the determinism flip, main on the left *)
Theorem bwd_improves (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  Intermediate.well_formed_program ilp ->
  Intermediate.closed_program ilp ->
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures pra Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base pra Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  does_prefix (me_sem NC Wlin) m ->
  exists beh,
    program_behaves (CS.sem ilp) beh
    /\ (prefix m beh \/ behavior_improves_finpref beh m).
Proof.
move=> Hwf Hcl Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0 Hdp.
exact: (bwd_improves_gen
          (match_initial Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0)
          Hdp).
Qed.

(* the determinism flip, main on the right *)
Theorem bwd_improves_r (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  Intermediate.well_formed_program pra ->
  Component.main \notin domm (Intermediate.prog_interface pra) ->
  size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures prb Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  proc_base prb Component.main Procedure.main = 0 ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall bmap0 imem0 iregs0 ms0,
     SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0) ->
  does_prefix (me_sem NC Wlin) m ->
  exists beh,
    program_behaves (CS.sem ilp) beh
    /\ (prefix m beh \/ behavior_improves_finpref beh m).
Proof.
move=> Hwfa HnotA Hsz Hmain HmainP Hp0 Hep Hpb0 Hmain0 Hptr HS0 Hdp.
exact: (bwd_improves_gen
          (match_initial_r Hwfa HnotA Hsz Hmain HmainP Hp0 Hep Hpb0
             Hmain0 Hptr HS0)
          Hdp).
Qed.

End DiagAll.

(* ==================== the residual interface ==================== *)

(* Everything the simulation still ASSUMES, bundled per linked pair: the
   label-scheme statics, the calling-convention invariant with its spec,
   the finite-machine fits, and the undischarged per-run oracles
   (liveness, RA-freedom, label statics, value fits, the alloc bundle).
   KDynamics.v assumes this record and turns [H_bwd]/[bt_run] into
   theorems over it. *)
Record sim_residual (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
  : Prop := SimResidual {
  sr_lab_a : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures pra cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L;
  sr_comp_a : forall cid,
    cid \in domm (Intermediate.prog_procedures pra) -> cid < C;
  sr_lab_b : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures prb cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L;
  sr_comp_b : forall cid,
    cid \in domm (Intermediate.prog_procedures prb) -> cid < C;
  sr_proc_a : forall cid Cprocs Pid,
    Intermediate.prog_procedures pra cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P;
  sr_proc_b : forall cid Cprocs Pid,
    Intermediate.prog_procedures prb cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P;
  sr_disj :
    fdisjoint (domm (Intermediate.prog_procedures pra))
              (domm (Intermediate.prog_procedures prb));
  sr_uniq_a : forall cid Cprocs0 l0,
    Intermediate.prog_procedures pra cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1;
  sr_uniq_b : forall cid Cprocs0 l0,
    Intermediate.prog_procedures prb cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1;
  sr_spec : sinv_spec SINV;
  sr_fit_code : pc0 + size codeW < 2 ^ word_size mt;
  sr_fit_mem : size (linearize_bufs pbW) + size codeW < 2 ^ word_size mt;
  sr_init : forall (bM : Block.id) bmap0 imem0 iregs0 ms0,
      SINV bmap0 [::] imem0 iregs0 (Component.main, bM, 0%Z) ms0;
  sr_ra : forall cid Cprocs P0 Pcode o i,
    Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode o = Some i ->
    ra_free_instr i;
  (* the tag oracle replacing the old (FALSE) operand-definedness
     field: a binop's operand registers are Other-tagged on the me
     side (LRC's BINOP demands [is_other]); TRUE of compiled runs *)
  sr_tag_binop : forall bmap gps imem iregs ipc ms Cprocs P0 Pcode
      op r1 r2 r3,
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.prog_procedures (side_of (Pointer.component ipc))
      (Pointer.component ipc) = Some Cprocs ->
    getm Cprocs P0 = Some Pcode ->
    List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
      = Some (IBinOp op r1 r2 r3) ->
    (forall a, getm (Symbolic.regs ms)
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat r1)) = Some a ->
       taga a = LRC.Other)
    /\ (forall a, getm (Symbolic.regs ms)
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat r2)) = Some a ->
       taga a = LRC.Other);
  sr_load_ra : forall bmap gps imem iregs ipc ms r1
       (bp : Block.id) (op : Z) (v : value) (base : nat)
       (w2 : mword mt) (cvt : LRC.value_tag)
       (ent : option (Procedure.id * seq Component.id)),
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (ILoad r1 R_RA) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
    amap_get bmap (Pointer.component ipc) bp = Some base ->
    getm (Symbolic.mem ms)
      (@word_of_nat (word_size mt) (base + Z.to_nat op))
      = Some (w2@(LRC.MTag cvt (Pointer.component ipc) ent false)) ->
    forall (tpc : Pointer.t) (gps' : list Pointer.t),
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
                   (side_flat_pos (Pointer.component tpc) P0' Pcode'
                      (Z.to_nat (Pointer.offset tpc)) + pc0)]
        /\ (exists i'',
              List.nth_error Pcode' (Z.to_nat (Pointer.offset tpc))
              = Some i'')
        /\ (~~ nilp gps' ->
            dead_at Pcode' (Z.to_nat (Pointer.offset tpc)) = true)
        /\ cvt = (if Pointer.component tpc == Pointer.component ipc
                  then LRC.InternalJump
                  else LRC.Ret (cross_frames (Pointer.component tpc)
                                  gps'));
  sr_ra_undef : forall bmap gps imem iregs ipc ms r1,
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IStore r1 R_RA) ->
    Intermediate.Register.get R_RA iregs = Undef;
  sr_imm : forall bmap gps imem iregs ipc ms v0 r,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IConst v0 r) ->
    val_rel_b bmap (imm_to_val v0)
      (swcast (convert_value (mt := mt)
         (memory_lengths (Intermediate.prog_buffers
            (side_of (Pointer.component ipc)))) v0));
  sr_binop : forall bmap gps imem iregs ipc ms op r1 r2 r3 w1 w2,
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBinOp op r1 r2 r3) ->
    val_rel_b bmap (Intermediate.Register.get r1 iregs) w1 ->
    val_rel_b bmap (Intermediate.Register.get r2 iregs) w2 ->
    val_rel_b bmap
      (eval_binop op (Intermediate.Register.get r1 iregs)
         (Intermediate.Register.get r2 iregs))
      (binop_denote (Merged.binop_trans op) w1 w2);
  sr_bnz_nz : forall bmap gps imem iregs ipc ms r l zv w,
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int zv ->
    (zv <> 0)%Z ->
    val_rel_b bmap (Int zv) w ->
    (w == 0%w) = false;
  sr_bnz_lab : forall bmap gps imem iregs ipc tpc ms r l,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.GlobalEnv.find_label_in_procedure G ipc l = Some tpc ->
    (0 <= Pointer.offset tpc)%Z /\
    (forall Cprocs (j : nat) P0 Pcode,
        Intermediate.prog_procedures (side_of (Pointer.component ipc))
          (Pointer.component ipc) = Some Cprocs ->
        getm Cprocs P0 = Some Pcode ->
        Pointer.block ipc
          = proc_nb0 ilp (Pointer.component ipc) + j ->
        List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
        List.nth_error Pcode (Z.to_nat (Pointer.offset ipc))
          = Some (IBnz r l) ->
        [/\ List.nth_error Pcode (Z.to_nat (Pointer.offset tpc))
              = Some (ILabel l),
            side_flat_pos (Pointer.component ipc) P0 Pcode
              (Z.to_nat (Pointer.offset ipc))
            <= side_flat_pos (Pointer.component ipc) P0 Pcode
                 (Z.to_nat (Pointer.offset tpc))
          & (pc0 + (side_flat_pos (Pointer.component ipc) P0 Pcode
                      (Z.to_nat (Pointer.offset tpc)) + 0))
            - (pc0 + side_flat_pos (Pointer.component ipc) P0 Pcode
                       (Z.to_nat (Pointer.offset ipc)))
            < 2 ^ imm_size mt]);
  sr_jal_lab : forall bmap gps imem iregs ipc tpc ms l,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IJal l) ->
    Intermediate.GlobalEnv.find_label_in_component G ipc l = Some tpc ->
    forall Cprocs,
      Intermediate.prog_procedures ilp (Pointer.component ipc)
        = Some Cprocs ->
      exists jt pt Ptcode,
        [/\ Pointer.block tpc
              = proc_nb0 ilp (Pointer.component ipc) + jt,
            List.nth_error (elementsm Cprocs) jt = Some (pt, Ptcode),
            (0 <= Pointer.offset tpc)%Z,
            List.nth_error Ptcode (Z.to_nat (Pointer.offset tpc))
              = Some (ILabel l)
          & pc0 + (side_flat_pos (Pointer.component ipc) pt Ptcode
                     (Z.to_nat (Pointer.offset tpc)) + 0)
            < 2 ^ imm_size mt];
  sr_jal_dead : forall bmap gps imem iregs ipc ms l
       (Cprocs : NMap Machine.code) (j : nat)
       (P0 : Procedure.id) (Pcode : Machine.code),
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IJal l) ->
    Intermediate.prog_procedures ilp (Pointer.component ipc)
      = Some Cprocs ->
    Pointer.block ipc = proc_nb0 ilp (Pointer.component ipc) + j ->
    List.nth_error (elementsm Cprocs) j = Some (P0, Pcode) ->
    (0 <= Pointer.offset ipc)%Z ->
    gps <> [::] ->
    dead_at Pcode (Z.to_nat (Pointer.offset ipc)) = true;
  sr_load : forall bmap gps imem iregs ipc ms r1 r2 bp op v,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (ILoad r1 r2) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.load imem (Pointer.component ipc, bp, op) = Some v ->
    (0 <= op)%Z /\
    (r2 <> R_RA ->
     forall base a,
        amap_get bmap (Pointer.component ipc) bp = Some base ->
        getm (Symbolic.mem ms)
          (@word_of_nat (word_size mt) (base + Z.to_nat op)) = Some a ->
        vtag (taga a) = LRC.Other
        \/ (vtag (taga a) = LRC.Invalidated /\ v = Undef));
  sr_store : forall bmap gps imem imem' iregs ipc ms r1 r2 bp op,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IStore r1 r2) ->
    Intermediate.Register.get r1 iregs
      = Ptr (Pointer.component ipc, bp, op) ->
    Memory.Memory.store imem (Pointer.component ipc, bp, op)
      (Intermediate.Register.get r2 iregs) = Some imem' ->
    [/\ (0 <= op)%Z,
        (r2 <> R_RA ->
         forall base a,
            amap_get bmap (Pointer.component ipc) bp = Some base ->
            getm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
            = Some a ->
            vtag (taga a) = LRC.Other)
      & (forall base a,
            amap_get bmap (Pointer.component ipc) bp = Some base ->
            getm (Symbolic.mem ms)
              (@word_of_nat (word_size mt) (base + Z.to_nat op))
            = Some a ->
            vtag (taga a) = LRC.Other
            \/ vtag (taga a) = LRC.Invalidated)];
  sr_conv : forall bmap gps imem iregs ipc ms z w t,
    ireach (gps, imem, iregs, ipc) ->
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.Register.get R_COM iregs = Int z ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt)
         (Intermediate.Register.to_nat R_COM)) = Some (w@t) ->
    Symbolic.convert (word.int_of_word w) = z;
  sr_call : forall bmap gps imem iregs ipc ms C' p b,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (ICall C' p) ->
    imported_procedure (genv_interface G) (Pointer.component ipc) C' p ->
    EntryPoint.get C' p (genv_entrypoints G) = Some b ->
    exists cl,
      [/\ head_tag (side_of C') C' p
            = LRC.MTag LRC.Other C' (Some (p, cl)) true,
          mem_seq cl (Pointer.component ipc) = true,
          pc0 + side_entry_pos C' p < 2 ^ imm_size mt
        & exists CprocsC jc Pcode',
            [/\ Intermediate.prog_procedures ilp C' = Some CprocsC,
                b = proc_nb0 ilp C' + jc,
                List.nth_error (elementsm CprocsC) jc = Some (p, Pcode')
              & exists i0, List.nth_error Pcode' 0 = Some i0]];
  sr_alloc : forall bmap gps imem imem' iregs ipc ms
                    rptr rsize szZ bI wsz v4
                    (t4 : LRC.value_tag),
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IAlloc rptr rsize) ->
    Intermediate.Register.get rsize iregs = Int szZ ->
    Memory.Memory.alloc imem (Pointer.component ipc) (Z.to_nat szZ)
      = Some (imem', (Pointer.component ipc, bI, 0%Z)) ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl rsize)))
      = Some (wsz@LRC.Other) ->
    getm (Symbolic.regs ms)
      (@word_of_nat (reg_field_size mt) (Merged.to_nat_bis (inl R_RA)))
      = Some (v4@t4) ->
    exists st4 : @Symbolic.state mt LRC.lrc_tags unit,
      [/\ getm (Symbolic.mem ms) (word_of_nat Merged.alloc_label) = None,
          code_region_ok (Symbolic.mem st4),
          amap_get bmap (Pointer.component ipc) bI = None,
          (forall Cprocs P0 Pcode,
              Intermediate.prog_procedures
                (side_of (Pointer.component ipc))
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
                          ((side_flat_pos (Pointer.component ipc) P0 Pcode
                              (Z.to_nat (Pointer.offset ipc)) + 3) + pc0))
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
                        @(LRC.def_mem_tag (Pointer.component ipc) false)))
                     len)) ->
              mem_rel (amap_set bmap (Pointer.component ipc) bI
                         ((eqtype.val max).+1)) imem' (Symbolic.mem st4))
          /\ (forall w a,
                getm (Symbolic.mem ms) w = Some a ->
                getm (Symbolic.mem st4) w = Some a)]
}.

(* the label-scheme statics alone (dischargeable from [lin_ok] + wf +
   compiledness + linkability) *)
Record lin_statics : Prop := LinStatics {
  lst_lab_a : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures pra cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L;
  lst_comp_a : forall cid,
    cid \in domm (Intermediate.prog_procedures pra) -> cid < C;
  lst_lab_b : forall cid Cprocs Pid Pcode l0,
    Intermediate.prog_procedures prb cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L;
  lst_comp_b : forall cid,
    cid \in domm (Intermediate.prog_procedures prb) -> cid < C;
  lst_proc_a : forall cid Cprocs Pid,
    Intermediate.prog_procedures pra cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P;
  lst_proc_b : forall cid Cprocs Pid,
    Intermediate.prog_procedures prb cid = Some Cprocs ->
    Pid \in domm Cprocs -> Pid < P;
  lst_disj :
    fdisjoint (domm (Intermediate.prog_procedures pra))
              (domm (Intermediate.prog_procedures prb));
  lst_uniq_a : forall cid Cprocs0 l0,
    Intermediate.prog_procedures pra cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1;
  lst_uniq_b : forall cid Cprocs0 l0,
    Intermediate.prog_procedures prb cid = Some Cprocs0 ->
    sumn [seq count (ilab l0) (odflt [::] (getm Cprocs0 p'))
         | p' <- domm Cprocs0] <= 1
}.

(* the determinism flip, over the residual bundle *)
Theorem bwd_improves_res (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
    (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  sim_residual NC SINV ->
  Intermediate.well_formed_program ilp ->
  Intermediate.closed_program ilp ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures pra Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall cid Cprocs P0 Pcode o i,
      Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode o = Some i ->
      i <> IHalt -> i <> IReturn -> i <> IJump ->
      exists i', List.nth_error Pcode o.+1 = Some i') ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  does_prefix (me_sem NC Wlin) m ->
  exists beh,
    program_behaves (CS.sem ilp) beh
    /\ (prefix m beh \/ behavior_improves_finpref beh m).
Proof.
case=> Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b Rdisj Runiq_a
       Runiq_b Rspec Rfitc Rfitm Rinit Rra Rdef Rloadra Rraud Rimm
       Rbinop
       Rbnznz Rbnzlab Rjallab Rjaldead Rload Rstore Rconv Rcall Ralloc.
move=> Hwf Hcl Hmain HmainP Hp0 Hep Hmain0 Hptr Honext Hoenc Hdp.
have Hdomm := wf_procs_iface Hwf.
have Hpb0 := proc_base_main HmainP Hp0.
have Obz : forall bmap gps imem iregs ipc ms r l w,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int 0 ->
    val_rel_b bmap (Int 0) w ->
    (w == 0%w) = true.
{ move=> bmap gps imem iregs ipc ms r l w _ _ _ Hv.
  exact: val_rel_int0 Hv. }
exact: (bwd_improves Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b
          Rdisj Runiq_a Runiq_b Hdomm Rfitc Rspec Honext Rra Hoenc Rdef
          Rloadra
          Rraud Rimm Rbinop Obz Rbnznz Rbnzlab Rjallab Rjaldead Rload
          Rstore Rconv
          Rcall Ralloc Hwf Hcl Rfitm Hmain HmainP Hp0 Hep Hpb0 Hmain0
          Hptr (Rinit bM) Hdp).
Qed.

(* the determinism flip over the residual bundle, main on the right *)
Theorem bwd_improves_res_r (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
    (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  sim_residual NC SINV ->
  Intermediate.well_formed_program ilp ->
  Intermediate.well_formed_program pra ->
  Component.main \notin domm (Intermediate.prog_interface pra) ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures prb Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall cid Cprocs P0 Pcode o i,
      Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode o = Some i ->
      i <> IHalt -> i <> IReturn -> i <> IJump ->
      exists i', List.nth_error Pcode o.+1 = Some i') ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  does_prefix (me_sem NC Wlin) m ->
  exists beh,
    program_behaves (CS.sem ilp) beh
    /\ (prefix m beh \/ behavior_improves_finpref beh m).
Proof.
case=> Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b Rdisj Runiq_a
       Runiq_b Rspec Rfitc Rfitm Rinit Rra Rdef Rloadra Rraud Rimm
       Rbinop
       Rbnznz Rbnzlab Rjallab Rjaldead Rload Rstore Rconv Rcall Ralloc.
move=> Hwf Hwfa HnotA Hmain HmainP Hp0 Hep Hmain0 Hptr Honext Hoenc Hdp.
have Hdomm := wf_procs_iface Hwf.
have Hpb0 := proc_base_main HmainP Hp0.
have Obz : forall bmap gps imem iregs ipc ms r l w,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int 0 ->
    val_rel_b bmap (Int 0) w ->
    (w == 0%w) = true.
{ move=> bmap gps imem iregs ipc ms r l w _ _ _ Hv.
  exact: val_rel_int0 Hv. }
exact: (bwd_improves_r Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b
          Rdisj Runiq_a Runiq_b Hdomm Rfitc Rspec Honext Rra Hoenc Rdef
          Rloadra
          Rraud Rimm Rbinop Obz Rbnznz Rbnzlab Rjallab Rjaldead Rload
          Rstore Rconv
          Rcall Ralloc Hwfa HnotA Rfitm Hmain HmainP Hp0 Hep Hpb0
          Hmain0 Hptr (Rinit bM) Hdp).
Qed.

(* the forward transfer, over the residual bundle *)
Theorem fwd_does_prefix_res (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
    (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  sim_residual NC SINV ->
  Intermediate.well_formed_program ilp ->
  Intermediate.closed_program ilp ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures pra Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall cid Cprocs P0 Pcode o i,
      Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode o = Some i ->
      i <> IHalt -> i <> IReturn -> i <> IJump ->
      exists i', List.nth_error Pcode o.+1 = Some i') ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem ilp) m ->
  does_prefix (me_sem NC Wlin) m.
Proof.
case=> Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b Rdisj Runiq_a
       Runiq_b Rspec Rfitc Rfitm Rinit Rra Rdef Rloadra Rraud Rimm
       Rbinop
       Rbnznz Rbnzlab Rjallab Rjaldead Rload Rstore Rconv Rcall Ralloc.
move=> Hwf Hcl Hmain HmainP Hp0 Hep Hmain0 Hptr Honext Hoenc Hnw Hdp.
have Hdomm := wf_procs_iface Hwf.
have Hpb0 := proc_base_main HmainP Hp0.
have Obz : forall bmap gps imem iregs ipc ms r l w,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int 0 ->
    val_rel_b bmap (Int 0) w ->
    (w == 0%w) = true.
{ move=> bmap gps imem iregs ipc ms r l w _ _ _ Hv.
  exact: val_rel_int0 Hv. }
exact: (fwd_does_prefix Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b
          Rdisj Runiq_a Runiq_b Hdomm Rfitc Rspec Honext Rra Hoenc Rdef
          Rloadra
          Rraud Rimm Rbinop Obz Rbnznz Rbnzlab Rjallab Rjaldead Rload
          Rstore Rconv
          Rcall Ralloc Hwf Hcl Rfitm Hmain HmainP Hp0 Hep Hpb0 Hmain0
          Hptr (Rinit bM) Hnw Hdp).
Qed.

(* the forward transfer over the residual bundle, main on the right *)
Theorem fwd_does_prefix_res_r (NC : nat)
    (SINV : addr_map -> list Pointer.t -> Memory.Memory.t
            -> Intermediate.Register.t -> Pointer.t
            -> @Symbolic.state mt lrc_tags unit -> Prop)
    (CprocsM : NMap Machine.code) (bM : Block.id)
    (m : finpref_behavior) :
  sim_residual NC SINV ->
  Intermediate.well_formed_program ilp ->
  Intermediate.well_formed_program pra ->
  Component.main \notin domm (Intermediate.prog_interface pra) ->
  Intermediate.prog_main ilp = true ->
  Intermediate.prog_procedures prb Component.main = Some CprocsM ->
  Procedure.main \in domm CprocsM ->
  EntryPoint.get Component.main Procedure.main
    (Intermediate.prepare_procedures_entrypoints ilp) = Some bM ->
  (forall Pcode, getm CprocsM Procedure.main = Some Pcode ->
     exists i0, List.nth_error Pcode 0 = Some i0) ->
  (forall C0 b off c' b' o',
     Memory.Memory.load (Intermediate.prepare_procedures_memory ilp)
       (C0, b, off) = Some (Ptr (c', b', o')) ->
     exists bm', Intermediate.prog_buffers ilp c' = Some bm'
       /\ b' \in domm bm') ->
  (forall cid Cprocs P0 Pcode o i,
      Intermediate.prog_procedures (side_of cid) cid = Some Cprocs ->
      getm Cprocs P0 = Some Pcode ->
      List.nth_error Pcode o = Some i ->
      i <> IHalt -> i <> IReturn -> i <> IJump ->
      exists i', List.nth_error Pcode o.+1 = Some i') ->
  (forall w a, encode_code codeW pc0 w = Some a ->
      is_code (taga a) = true) ->
  not_wrong_finpref m ->
  does_prefix (CS.sem ilp) m ->
  does_prefix (me_sem NC Wlin) m.
Proof.
case=> Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b Rdisj Runiq_a
       Runiq_b Rspec Rfitc Rfitm Rinit Rra Rdef Rloadra Rraud Rimm
       Rbinop
       Rbnznz Rbnzlab Rjallab Rjaldead Rload Rstore Rconv Rcall Ralloc.
move=> Hwf Hwfa HnotA Hmain HmainP Hp0 Hep Hmain0 Hptr Honext Hoenc
       Hnw Hdp.
have Hdomm := wf_procs_iface Hwf.
have Hpb0 := proc_base_main HmainP Hp0.
have Obz : forall bmap gps imem iregs ipc ms r l w,
    lin_match SINV bmap gps imem iregs ipc ms ->
    Intermediate.GlobalEnv.executing G ipc (IBnz r l) ->
    Intermediate.Register.get r iregs = Int 0 ->
    val_rel_b bmap (Int 0) w ->
    (w == 0%w) = true.
{ move=> bmap gps imem iregs ipc ms r l w _ _ _ Hv.
  exact: val_rel_int0 Hv. }
exact: (fwd_does_prefix_r Rlab_a Rcomp_a Rlab_b Rcomp_b Rproc_a Rproc_b
          Rdisj Runiq_a Runiq_b Hdomm Rfitc Rspec Honext Rra Hoenc Rdef
          Rloadra
          Rraud Rimm Rbinop Obz Rbnznz Rbnzlab Rjallab Rjaldead Rload
          Rstore Rconv
          Rcall Ralloc Hwfa HnotA Rfitm Hmain HmainP Hp0 Hep Hpb0
          Hmain0 Hptr (Rinit bM) Hnw Hdp).
Qed.

End LinSim.
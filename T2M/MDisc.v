(** * T2M — the dynamic tag-discipline invariant [disc_inv].

    Consumes the static per-component class maps [MM c] (each passing
    [comp_ok]): [svat]/[exec_sv] read a pc's class value with its
    [vstep] transfer, [dinv]/[disc_inv] state the register/frame/phase
    invariant, and the [dinv_*] lemmas transport it along [TS.step].             *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import T2M.MSig.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section Disc.

Variable cde : Transitional.code.
Variable MM : Component.id -> seq sv.
Hypothesis HMM : forall c S,
  getm cde c = Some S -> comp_ok (c, 1, 0%Z) S (MM c).

Hypothesis Hcst : forall pc iv r tg c p,
  Transitional.executing cde pc (TrConst iv r) tg c ->
  iv = IPtr p ->
  p = (c, 0, 0%Z) \/
  ((p = (c, 1, 0%Z) \/ p = (c, 1, 1%Z)) /\ (r = R_AUX1 \/ r = R_AUX2)).

Hypothesis Huniq : forall (c : Component.id) (S : TS.tcode) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  getm cde c = Some S ->
  nth_error S m = Some (TrLabel (inl l), t1) ->
  nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.

(* the state's class value at a pc *)
Definition svat (pc : Pointer.t) : option sv :=
  nth_error (MM (Pointer.component pc)) (Z.to_nat (Pointer.offset pc)).

(* an executing instruction has a class value, a defined transfer, and
   (unless terminal) the successor carries the transferred value *)
Lemma exec_sv (pc : Pointer.t) (i : Transitional.instr)
    (tg : mem_tag) (c : Component.id) :
  Transitional.executing cde pc i tg c ->
  exists v v',
    [/\ svat pc = Some v,
        vstep (c, 1, 0%Z) v i = Some v'
      & ~~ terminal i ->
        exists w, svat (Pointer.inc pc) = Some w /\ sv_le v' w].
Proof.
case=> C_code [Ec [Eg [Eo En]]].
have Hok : comp_ok (c, 1, 0%Z) C_code (MM c) := HMM Eg.
have [v [v' [Ev Evs Hsucc]]] := vc_at_inv Hok En.
exists v, v'.
rewrite /svat Ec Ev.
split=> // Hnt.
have [w [Ew Eww]] := Hsucc Hnt.
have EcI : Pointer.component (Pointer.inc pc) = c.
{ by case: (pc) Ec => [[c0 b0] o0] /= ->. }
have EoI : Z.to_nat (Pointer.offset (Pointer.inc pc))
           = (Z.to_nat (Pointer.offset pc)).+1.
{ case: (pc) Eo => [[c0 b0] o0] /= Eo. by lia. }
rewrite EcI EoI Ew.
by exists w.
Qed.

(* [find_label]'s result is a position holding the label *)
Lemma find_label_some (S : seq (Transitional.instr * mem_tag))
    (l : label) (o : Z) :
  Transitional.find_label S l = Some o ->
  (0 <= o)%Z /\
  exists tg, nth_error S (Z.to_nat o) = Some (TrLabel (inl l), tg).
Proof.
suff Hgen : forall (S0 : seq (Transitional.instr * mem_tag))
    (o0 : Z), (0 <= o0)%Z ->
    (fix aux (c : seq (Transitional.instr * mem_tag)) (o1 : Z)
       {struct c} : option Z :=
       match c with
       | [::] => None
       | (TrLabel (inl l'), _) :: c' =>
           if Nat.eqb l l' then Some o1 else aux c' (1 + o1)%Z
       | _ :: c' => aux c' (1 + o1)%Z
       end) S0 o0 = Some o ->
    (o0 <= o)%Z /\
    exists tg, nth_error S0 (Z.to_nat (o - o0))
               = Some (TrLabel (inl l), tg).
{ rewrite /Transitional.find_label.
  case: S => [|x S'] //= H.
  have [Ho [tg Htg]] := Hgen (x :: S') 0%Z (Z.le_refl 0) H.
  split; first by lia.
  exists tg. by rewrite Z.sub_0_r in Htg. }
elim=> [|[i tg0] S0 IH] o0 Ho0 //=.
case: i => [|lab|iv r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0|r|l0
           |pl|] /=;
  try (move=> HR;
       have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR;
       split; [by lia| exists tg1];
       rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
       [exact: Htg | by lia]).
case: lab => [l'|pl'] /=; last first.
{ move=> HR.
  have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR.
  split; [by lia| exists tg1].
  rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
    [exact: Htg | by lia]. }
case E: (Nat.eqb l l').
- move=> [Eo]. subst o.
  split; first by lia.
  exists tg0.
  rewrite (_ : Z.to_nat (o0 - o0) = 0); last by lia.
  move/PeanoNat.Nat.eqb_eq: E => E.
  by rewrite /= E.
- move=> HR.
  have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR.
  split; [by lia| exists tg1].
  rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
    [exact: Htg | by lia].
Qed.

(* the Bnz target carries a weakening of the branch-site value *)
Lemma bnz_target (pc pc' : Pointer.t) (l : label) (tg : mem_tag)
    (c : Component.id) (r : register) (v : sv) :
  Transitional.executing cde pc (TrBnz r l) tg c ->
  svat pc = Some v ->
  Transitional.find_label_in_comp cde c l = Some pc' ->
  Pointer.component pc' = c /\
  exists w, svat pc' = Some w /\ sv_le v w.
Proof.
case=> C_code [Ec [Eg [Eo En]]] Ev.
rewrite /Transitional.find_label_in_comp Eg.
case Efl: (Transitional.find_label C_code l) => [o|] // -[Epc'].
have [Ho [tg' Htg]] := find_label_some Efl.
have Hok : comp_ok (c, 1, 0%Z) C_code (MM c) := HMM Eg.
have Hvc := comp_ok_at Hok En.
move: Hvc. rewrite /vc_at En.
have EvM : nth_error (MM c) (Z.to_nat (Pointer.offset pc)) = Some v.
{ move: Ev. by rewrite /svat Ec. }
rewrite EvM.
case EV: (vstep _ _ _) => [v'|] //.
case/andP => _ /hasP [m Hm /andP [Hlat HmM]].
move: Hlat. rewrite /lbl_at.
case Enm: (nth_error C_code m) => [[[|[l1|pl1]|iv0 r0|? ?|? ? ? ?|? ?
  |? ?|? ?|? ?|?|?|?|] tgm]|] //.
move/PeanoNat.Nat.eqb_eq => El1. subst l1.
have Em : Z.to_nat o = m := Huniq Eg Htg Enm.
move: HmM.
case EwM: (nth_error (MM c) m) => [w|] // Hw.
split; first by rewrite -Epc'.
exists w. split=> //.
rewrite /svat -Epc' /=.
by rewrite Em EwM.
Qed.

(* the internal-Jal target is the procedure label carrying [sv0_one] *)
Lemma jal_target (pc pc' : Pointer.t) (l : label) (tg : mem_tag)
    (c : Component.id) (v : sv) :
  Transitional.executing cde pc (TrJalNat l) tg c ->
  svat pc = Some v ->
  Transitional.find_label_in_comp cde c l = Some pc' ->
  Pointer.component pc' = c /\ svat pc' = Some sv0_one.
Proof.
case=> C_code [Ec [Eg [Eo En]]] Ev.
rewrite /Transitional.find_label_in_comp Eg.
case Efl: (Transitional.find_label C_code l) => [o|] // -[Epc'].
have [Ho [tg' Htg]] := find_label_some Efl.
have Hok : comp_ok (c, 1, 0%Z) C_code (MM c) := HMM Eg.
have Hvc := comp_ok_at Hok En.
move: Hvc. rewrite /vc_at En.
have EvM : nth_error (MM c) (Z.to_nat (Pointer.offset pc)) = Some v.
{ move: Ev. by rewrite /svat Ec. }
rewrite EvM.
case EV: (vstep _ _ _) => [v'|] //.
case/andP => _ /hasP [m Hm /andP [Hlat HmM]].
move: Hlat. rewrite /lbl_at.
case Enm: (nth_error C_code m) => [[[|[l1|pl1]|iv0 r0|? ?|? ? ? ?|? ?
  |? ?|? ?|? ?|?|?|?|] tgm]|] //.
move/PeanoNat.Nat.eqb_eq => El1. subst l1.
have Em : Z.to_nat o = m := Huniq Eg Htg Enm.
move: HmM.
case EwM: (nth_error (MM c) m) => [w|] // /sv_eqbP Hw.
subst w.
split; first by rewrite -Epc'.
rewrite /svat -Epc' /=.
by rewrite Em EwM.
Qed.

(* [find_plabel]'s result is a position holding the procedure label *)
Lemma find_plabel_some (S : seq (Transitional.instr * mem_tag))
    (c0 : Component.id) (p0 : Procedure.id) (o : Z) :
  Transitional.find_plabel S c0 p0 = Some o ->
  (0 <= o)%Z /\
  exists tg, nth_error S (Z.to_nat o)
             = Some (TrLabel (inr (c0, p0)), tg).
Proof.
suff Hgen : forall (S0 : seq (Transitional.instr * mem_tag))
    (o0 : Z), (0 <= o0)%Z ->
    (fix aux (cd : seq (Transitional.instr * mem_tag)) (o1 : Z)
       {struct cd} : option Z :=
       match cd with
       | [::] => None
       | (TrLabel (inr (c', p')), _) :: cd' =>
           if Nat.eqb c0 c' && Nat.eqb p0 p' then Some o1
           else aux cd' (1 + o1)%Z
       | _ :: cd' => aux cd' (1 + o1)%Z
       end) S0 o0 = Some o ->
    (o0 <= o)%Z /\
    exists tg, nth_error S0 (Z.to_nat (o - o0))
               = Some (TrLabel (inr (c0, p0)), tg).
{ rewrite /Transitional.find_plabel.
  case: S => [|x S'] //= H.
  have [Ho [tg Htg]] := Hgen (x :: S') 0%Z (Z.le_refl 0) H.
  split; first by lia.
  exists tg. by rewrite Z.sub_0_r in Htg. }
elim=> [|[i tg0] S0 IH] o0 Ho0 //=.
case: i => [|lab|iv r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0|r|l0
           |pl|] /=;
  try (move=> HR;
       have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR;
       split; [by lia| exists tg1];
       rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
       [exact: Htg | by lia]).
case: lab => [l'|[c' p']] /=.
{ move=> HR.
  have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR.
  split; [by lia| exists tg1].
  rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
    [exact: Htg | by lia]. }
case E: (Nat.eqb c0 c' && Nat.eqb p0 p').
- move=> [Eo]. subst o.
  split; first by lia.
  exists tg0.
  rewrite (_ : Z.to_nat (o0 - o0) = 0); last by lia.
  case/andP: E => /PeanoNat.Nat.eqb_eq Ec' /PeanoNat.Nat.eqb_eq Ep'.
  by rewrite /= Ec' Ep'.
- move=> HR.
  have [Hle [tg1 Htg]] := IH (1 + o0)%Z ltac:(lia) HR.
  split; [by lia| exists tg1].
  rewrite (_ : Z.to_nat (o - o0) = (Z.to_nat (o - (1 + o0))).+1);
    [exact: Htg | by lia].
Qed.

(* the cross-call target is the procedure header carrying [sv0] *)
Lemma plabel_target (c' : Component.id) (pid : Procedure.id)
    (pc' : Pointer.t) :
  Transitional.find_plabel_in_code cde c' pid = Some pc' ->
  Pointer.component pc' = c' /\ svat pc' = Some sv0.
Proof.
rewrite /Transitional.find_plabel_in_code.
case Eg: (cde c') => [C_code|] //.
case Efl: (Transitional.find_plabel C_code c' pid) => [o|] // -[Epc'].
have [Ho [tg Htg]] := find_plabel_some Efl.
have Hok : comp_ok (c', 1, 0%Z) C_code (MM c') := HMM Eg.
have Hvc := comp_ok_at Hok Htg.
move: Hvc. rewrite /vc_at Htg.
case EvM: (nth_error (MM c') (Z.to_nat o)) => [v0|] //.
case EV: (vstep _ _ _) => [v0'|] //.
case/andP => _ /sv_eqbP Ev0.
subst v0.
split; first by rewrite -Epc'.
rewrite /svat -Epc' /=.
by rewrite EvM.
Qed.

(* the register wipe at cross calls/returns *)
Lemma tget_invalidate (r : register)
    (regs : Transitional.Register.t) :
  r <> R_COM -> r <> R_RA ->
  Transitional.Register.get r (Transitional.Register.invalidate regs)
  = Transitional.tUndef.
Proof.
by case: r => // H1 H2.
Qed.

Lemma tget_invalidate_com (regs : Transitional.Register.t) :
  Transitional.Register.get R_COM
    (Transitional.Register.invalidate regs)
  = Transitional.Register.get R_COM regs.
Proof. by []. Qed.

(* ================================================================== *)
(* The dynamic invariant                                              *)
(* ================================================================== *)

(* one suspended activation: component, frame block, resume pc, and
   the saved inherited-scratch value *)
Record act := Act {
  a_comp : Component.id;
  a_blk  : Block.id;
  a_ret  : Pointer.t;
  a_scr  : value
}.

(* the class value a suspended activation resumes at *)
Definition asv (A : act) : sv := odflt sv0 (svat (a_ret A)).

(* cross-suspended: inside a call window *)
Definition in_window (A : act) : bool := ph_eqb (sv_ph (asv A)) PPost.

(* the activation's structural stack pointer *)
Definition sp_of (A : act) : value :=
  Ptr (a_comp A, a_blk A, Z.of_nat (size (sv_sig (asv A)))).

(* topmost chain entry of a component / topmost in-window entry *)
Fixpoint topc (c : Component.id) (ch : seq act) : option act :=
  match ch with
  | [::] => None
  | A :: ch' => if Nat.eqb (a_comp A) c then Some A else topc c ch'
  end.

Fixpoint topw (c : Component.id) (ch : seq act) : option act :=
  match ch with
  | [::] => None
  | A :: ch' =>
      if Nat.eqb (a_comp A) c && in_window A then Some A
      else topw c ch'
  end.

(* the parent carry: what the prologue's Mov parks *)
Definition carry0 (ch : seq act) : value :=
  match ch with
  | [::] => Undef
  | A :: _ => if in_window A then Undef else sp_of A
  end.

(* the scratch pin of a component over a chain suffix *)
Definition scrpin (c : Component.id) (ch : seq act) : value :=
  match topw c ch with
  | Some X => sp_of X
  | None => Undef
  end.

(* the return capability of the activation running above [ch] *)
Definition cap (ch : seq act) : Transitional.tvalue :=
  match ch with
  | [::] => Transitional.tUndef
  | A :: _ =>
      if in_window A
      then Transitional.MVal (Ret (count in_window ch).-1)
             (Ptr (a_ret A))
      else Transitional.MVal InternalJump (Ptr (a_ret A))
  end.

(* the chain-head window test (vacuously true when empty) *)
Definition hdwin (ch : seq act) : bool :=
  match ch with B :: _ => in_window B | [::] => true end.

Lemma topc_window_topw (c : Component.id) (ch : seq act) (X : act) :
  topc c ch = Some X -> in_window X -> topw c ch = Some X.
Proof.
elim: ch => [|A0 ch IH] //=.
case E: (Nat.eqb (a_comp A0) c).
- move=> [<-] Hw. by rewrite Hw.
- move=> H Hw. by rewrite (IH H Hw).
Qed.

Lemma topc_none_topw (c : Component.id) (ch : seq act) :
  topc c ch = None -> topw c ch = None.
Proof.
elim: ch => [|A0 ch IH] //=.
by case E: (Nat.eqb (a_comp A0) c).
Qed.

(* a pointer names an allocated block of its component *)
Definition vblock_ok (mem : Transitional.Memory.t) (p : Pointer.t)
  : Prop :=
  exists cm, getm mem (Pointer.component p) = Some cm /\
    Pointer.block p < Transitional.Memory.nextblock cm.

(* user values: an allocated block outside the frames, never the
   hidden block 1 (validity is what lets a fresh frame block join F
   without colliding with any live user value) *)
Definition goodu (mem : Transitional.Memory.t)
    (F : Component.id -> seq Block.id) (v : value) : Prop :=
  forall p, v = Ptr p ->
    [/\ (Pointer.block p \in F (Pointer.component p)) = false,
        Pointer.block p <> 1
      & vblock_ok mem p].

Definition cell_at (mem : Transitional.Memory.t) (c : Component.id)
    (b : Block.id) (n : nat)
  : option (Transitional.tvalue * mem_tag) :=
  match getm mem c with
  | Some cm =>
      match getm (Transitional.Memory.content cm) b with
      | Some blk => nth_error blk n
      | None => None
      end
  | None => None
  end.

(* one frame's slot claims: CU slots are Other-tagged user cells,
   CSp slots carry the parked SPs (slot 0 = the parent carry, the
   wrapper's slot 1 = the inherited scratch), CRa the capability *)
Definition frame_ok (F : Component.id -> seq Block.id)
    (mem : Transitional.Memory.t) (c : Component.id) (b : Block.id)
    (sg : seq class3) (carry cscr : value)
    (rcap : Transitional.tvalue) : Prop :=
  forall j k, nth_error sg j = Some k ->
    exists cv tg, cell_at mem c b j = Some (cv, tg) /\
      match k with
      | CU => tvtag cv = Other /\ goodu mem F (Transitional.val cv)
      | CArg => tvtag cv = Other /\ goodu mem F (Transitional.val cv)
      | CSp => tvtag cv = Other /\
               Transitional.val cv
               = (match j with 0 => carry | _ => cscr end)
      | CRa => cv = rcap
      end.

(* the aux registers' value claims, per taint *)
Definition aux_claim (mem : Transitional.Memory.t)
    (F : Component.id -> seq Block.id)
    (ch : seq act) (curscr : value) (v : sv) (t : taint)
    (c : Component.id) (x : value) : Prop :=
  match t with
  | AU => goodu mem F x
  | AScr => x = Ptr (c, 1, 0%Z)
  | AFlag => x = Ptr (c, 1, 1%Z)
  | ASp =>
      match sv_ph v, sv_sig v with
      | PProlB, _ => x = carry0 ch
      | PBody, [::] => x = carry0 ch
      | PBody, [:: CSp] => x = curscr
      | _, _ => True
      end
  | ADead => True
  end.

(* the scratch cell of component [c] holds value [x] *)
Definition scr_val (mem : Transitional.Memory.t) (c : Component.id)
    (x : value) : Prop :=
  exists cv tg, cell_at mem c 1 0 = Some (cv, tg) /\
    Transitional.val cv = x.

(* the internally-entered (ek = true) body-sig discipline: CRa slots
   sit at depth >= 2, below the baseline CArg at position 1 *)
Definition bodycarg (sg : seq class3) : Prop :=
  forall j, nth_error sg j = Some CRa ->
    2 <= j /\ nth_error sg 1 = Some CArg.

(* the pend-inclusive sig: the in-flight push-macro slot counts as
   part of the frame string *)
Definition pend_sig (v : sv) : seq class3 :=
  match sv_pend v with
  | Some k => rcons (sv_sig v) k
  | None => sv_sig v
  end.

Record dinv (cur : option Block.id) (chain : seq act)
    (F : Component.id -> seq Block.id) (curscr : value)
    (mem : Transitional.Memory.t) (regs : Transitional.Register.t)
    (pc : Pointer.t) (pct : Transitional.pc_tag) : Prop := DInv {

  di_rtag : forall r, r <> R_RA ->
    tvtag (Transitional.Register.get r regs) = Other;
  di_rval : forall r,
    r <> R_RA -> r <> R_SP -> r <> R_AUX1 -> r <> R_AUX2 ->
    goodu mem F (Transitional.val (Transitional.Register.get r regs));
  di_a1 : forall v, svat pc = Some v ->
    aux_claim mem F chain curscr v (sv_a1 v) (Pointer.component pc)
      (Transitional.val (Transitional.Register.get R_AUX1 regs));
  di_a2 : forall v, svat pc = Some v ->
    aux_claim mem F chain curscr v (sv_a2 v) (Pointer.component pc)
      (Transitional.val (Transitional.Register.get R_AUX2 regs));
  di_one : forall v, svat pc = Some v -> sv_one v = true ->
    Transitional.val (Transitional.Register.get R_ONE regs) = Int 1;

  di_prol : forall v, svat pc = Some v ->
    sv_ph v = PProlA \/ sv_ph v = PProlB ->
    cur = None /\ sv_sig v = [::] /\ sv_pend v = None;
  di_spprol : forall v, svat pc = Some v -> sv_ph v = PProlA ->
    Transitional.val (Transitional.Register.get R_SP regs)
    = carry0 chain;
  di_body : forall v, svat pc = Some v ->
    sv_ph v <> PProlA -> sv_ph v <> PProlB ->
    exists b, cur = Some b /\ b \in F (Pointer.component pc);
  di_sp : forall v b, svat pc = Some v -> sv_ph v = PBody ->
    cur = Some b ->
    Transitional.val (Transitional.Register.get R_SP regs)
    = Ptr (Pointer.component pc, b, Z.of_nat (size (sv_sig v)));
  di_sptear : forall v, svat pc = Some v -> sv_ph v = PTear ->
    Transitional.val (Transitional.Register.get R_SP regs)
    = carry0 chain;

  di_frame : forall v b, svat pc = Some v -> cur = Some b ->
    frame_ok F mem (Pointer.component pc) b (sv_sig v)
      (carry0 chain) curscr (cap chain);
  di_pend : forall v b k, svat pc = Some v -> cur = Some b ->
    sv_pend v = Some k ->
    exists cv tg,
      cell_at mem (Pointer.component pc) b (size (sv_sig v))
      = Some (cv, tg) /\
      match k with
      | CU => tvtag cv = Other /\ goodu mem F (Transitional.val cv)
      | CArg => tvtag cv = Other /\ goodu mem F (Transitional.val cv)
      | CSp => tvtag cv = Other /\
               Transitional.val cv
               = (match size (sv_sig v) with
                  | 0 => carry0 chain
                  | _.+1 => curscr
                  end)
      | CRa => cv = cap chain
      end;

  di_ra : forall v, svat pc = Some v ->
    sv_ph v <> PPost ->
    sv_pend v <> Some CRa ->
    (forall j, nth_error (sv_sig v) j <> Some CRa) ->
    Transitional.Register.get R_RA regs = cap chain;

  di_mem : forall c b j cv tg,
    cell_at mem c b j = Some (cv, tg) ->
    (b \in F c) = false ->
    tvtag cv = Other /\ (b <> 1 -> goodu mem F (Transitional.val cv));

  di_scrtag : forall c cm, getm mem c = Some cm ->
    exists cv tg, cell_at mem c 1 0 = Some (cv, tg) /\ tvtag cv = Other;
  di_scr : forall v, svat pc = Some v ->
    match sv_sc v with
    | SCnone => scr_val mem (Pointer.component pc) curscr
    | SCpark => sv_ph v = PBody ->
                scr_val mem (Pointer.component pc)
                  (Transitional.val
                     (Transitional.Register.get R_SP regs))
    | SCrest => scr_val mem (Pointer.component pc) curscr
    | SCused => True
    end;
  di_post : forall v b, svat pc = Some v -> sv_ph v = PPost ->
    cur = Some b ->
    scr_val mem (Pointer.component pc)
      (Ptr (Pointer.component pc, b, Z.of_nat (size (sv_sig v))));
  di_scrfor : forall c A, c <> Pointer.component pc ->
    topc c chain = Some A ->
    in_window A /\ scr_val mem c (sp_of A);
  di_chain : forall i A, nth_error chain i = Some A ->
    [/\ (exists w, svat (a_ret A) = Some w),
        [/\ sv_ph (asv A) = PBody \/ sv_ph (asv A) = PPost,
            sv_pend (asv A) = None,
            sv_a1 (asv A) = ADead, sv_a2 (asv A) = ADead
          & sv_sc (asv A) = SCused]
        /\ (sv_ph (asv A) = PPost -> sv_one (asv A) = false),
        a_blk A \in F (a_comp A),
        frame_ok F mem (a_comp A) (a_blk A) (sv_sig (asv A))
          (carry0 (drop i.+1 chain)) (a_scr A)
          (cap (drop i.+1 chain))
      & [/\ a_comp A = Pointer.component (a_ret A),
            (in_window A = false -> ~~ nocra (sv_sig (asv A))),
            (sv_ek (asv A) = true ->
             match drop i.+1 chain with
             | B :: _ => in_window B = false
             | [::] => False
             end)
          & (hdwin (drop i.+1 chain) = true ->
             a_scr A = scrpin (a_comp A) (drop i.+1 chain))]];

  di_dist : forall i A b, nth_error chain i = Some A ->
    cur = Some b -> a_comp A = Pointer.component pc ->
    a_blk A <> b;
  di_dist2 : forall i1 i2 A1 A2, i1 <> i2 ->
    nth_error chain i1 = Some A1 -> nth_error chain i2 = Some A2 ->
    a_comp A1 = a_comp A2 -> a_blk A1 <> a_blk A2;
  di_fbound : forall c b, b \in F c ->
    exists cm, getm mem c = Some cm /\
      b < Transitional.Memory.nextblock cm;
  di_f01 : forall c, (0 \in F c) = false /\ (1 \in F c) = false;
  di_nb2 : forall c cm, getm mem c = Some cm ->
    2 <= Transitional.Memory.nextblock cm;
  di_dom : forall c S, getm cde c = Some S ->
    exists cm, getm mem c = Some cm;

  di_level : pct = Transitional.Level (count in_window chain);

  di_flag : forall c cm, getm mem c = Some cm ->
    exists cv tg, cell_at mem c 1 1 = Some (cv, tg) /\
      tvtag cv = Other /\ goodu mem F (Transitional.val cv);

  di_ek : forall v, svat pc = Some v -> sv_ek v = true ->
    match chain with
    | A0 :: _ => in_window A0 = false
    | [::] => False
    end;

  di_nwshadow : forall i X, nth_error chain i = Some X ->
    in_window X = false ->
    (a_comp X = Pointer.component pc /\
     (forall k B, k < i -> nth_error chain k = Some B ->
        a_comp B = a_comp X /\ in_window B = false))
    \/
    (exists j W,
       [/\ j < i, nth_error chain j = Some W,
           a_comp W = a_comp X, in_window W = true
         & forall k B, j < k -> k < i -> nth_error chain k = Some B ->
             a_comp B = a_comp X /\ in_window B = false]);

  di_cswin : hdwin chain = true ->
    curscr = scrpin (Pointer.component pc) chain;

  di_scr0 : forall c0 S0, c0 <> Pointer.component pc ->
    getm cde c0 = Some S0 ->
    topw c0 chain = None -> scr_val mem c0 Undef;

  di_ekwin : forall v, svat pc = Some v -> sv_ek v = false ->
    match chain with
    | A0 :: _ => in_window A0 = true
    | [::] => True
    end;

  di_bodycarg : forall v, svat pc = Some v -> sv_ek v = true ->
    bodycarg (pend_sig v);

  di_chain2 : forall i A, nth_error chain i = Some A ->
    [/\ (sv_ph (asv A) = PPost -> sv_arg (asv A) = false),
        (sv_ek (asv A) = false ->
         match drop i.+1 chain with
         | B :: _ => in_window B = true
         | [::] => True
         end),
        (sv_ek (asv A) = true -> bodycarg (sv_sig (asv A)))
      & (in_window A = true -> sv_ek (asv A) = true ->
         nth_error (sv_sig (asv A)) 1 = Some CArg)]
}.

Definition disc_inv (s : TS.state) : Prop :=
  let '(mem, regs, pc, pct) := s in
  exists cur chain F curscr, dinv cur chain F curscr mem regs pc pct.

(* ================================================================== *)
(* Preservation: transport helpers and the step lemma.                *)
(* ================================================================== *)

(* ---- register and pointer facts ---- *)

Lemma t_to_nat_inj (r r' : register) :
  Transitional.Register.to_nat r = Transitional.Register.to_nat r' ->
  r = r'.
Proof. by case: r; case: r'. Qed.

Lemma is_r_eq (r r' : register) : is_r r r' -> r = r'.
Proof. by case: r; case: r'. Qed.

Lemma is_r_neq (r r' : register) : is_r r r' = false -> r <> r'.
Proof.
move=> E Err. subst r'.
by rewrite /is_r PeanoNat.Nat.eqb_refl in E.
Qed.

Lemma is_r_neq' (r r' : register) : is_r r r' = false -> r' <> r.
Proof.
move=> E Err. subst r'.
by rewrite /is_r PeanoNat.Nat.eqb_refl in E.
Qed.

Lemma is_r_false (r r' : register) : r <> r' -> is_r r r' = false.
Proof. by case: r; case: r' => // H; case: (H (erefl _)). Qed.

Lemma tget_set_eq (r : register) (x : value) (vt : value_tag)
    (regs : Transitional.Register.t) :
  Transitional.Register.get r (Transitional.Register.set r x vt regs)
  = Transitional.MVal vt x.
Proof.
by rewrite /Transitional.Register.get /Transitional.Register.set
   setmE eqxx.
Qed.

Lemma tget_set_neq (r r' : register) (x : value) (vt : value_tag)
    (regs : Transitional.Register.t) :
  r' <> r ->
  Transitional.Register.get r' (Transitional.Register.set r x vt regs)
  = Transitional.Register.get r' regs.
Proof.
move=> Hne.
rewrite /Transitional.Register.get /Transitional.Register.set setmE.
case E: (_ == _) => //.
move/eqP/t_to_nat_inj: E => E.
by case: (Hne E).
Qed.

Lemma ptr_eqb_eq (p q : Pointer.t) : ptr_eqb p q -> p = q.
Proof.
case: p q => [[c b] o] [[c' b'] o'].
case/and3P => /PeanoNat.Nat.eqb_eq /= -> /PeanoNat.Nat.eqb_eq /= ->
  /Z.eqb_eq /= ->.
by [].
Qed.

Lemma wtaint_fields (r : register) (t : taint) (v : sv) :
  [/\ sv_ph (wtaint r t v) = sv_ph v,
      sv_sig (wtaint r t v) = sv_sig v,
      sv_pend (wtaint r t v) = sv_pend v,
      sv_sc (wtaint r t v) = sv_sc v
    & sv_one (wtaint r t v) = sv_one v].
Proof.
rewrite /wtaint.
by case: (is_r r R_AUX1); case: (is_r r R_AUX2).
Qed.

Lemma wone_fields (r : register) (o : bool) (v : sv) :
  [/\ sv_ph (wone r o v) = sv_ph v,
      sv_sig (wone r o v) = sv_sig v
    & sv_pend (wone r o v) = sv_pend v]
  /\ [/\ sv_sc (wone r o v) = sv_sc v,
         sv_a1 (wone r o v) = sv_a1 v
       & sv_a2 (wone r o v) = sv_a2 v].
Proof.
rewrite /wone.
by case: (is_r r R_ONE); do !split.
Qed.

Lemma wtaint_ek (r : register) (t : taint) (v : sv) :
  sv_ek (wtaint r t v) = sv_ek v.
Proof.
rewrite /wtaint.
by case: (is_r r R_AUX1); case: (is_r r R_AUX2).
Qed.

Lemma wone_ek (r : register) (o : bool) (v : sv) :
  sv_ek (wone r o v) = sv_ek v.
Proof.
rewrite /wone.
by case: (is_r r R_ONE).
Qed.

(* the R_ARG-bit writer touches no other field *)
Lemma warg_w_fields (r : register) (v : sv) :
  [/\ sv_ph (warg_w r v) = sv_ph v,
      sv_sig (warg_w r v) = sv_sig v,
      sv_pend (warg_w r v) = sv_pend v
    & sv_sc (warg_w r v) = sv_sc v]
  /\ [/\ sv_a1 (warg_w r v) = sv_a1 v,
         sv_a2 (warg_w r v) = sv_a2 v,
         sv_one (warg_w r v) = sv_one v
       & sv_ek (warg_w r v) = sv_ek v].
Proof.
rewrite /warg_w /warg.
by case: (is_r r R_ARG); do !split.
Qed.

(* both writes of a Mov carry the same value; Other tags *)
Lemma get_write2 (r1 r2 r0 : register) (x : value)
    (regs : Transitional.Register.t) :
  Transitional.Register.get r0
    (Transitional.Register.set r1 x Other
       (Transitional.Register.set r2 x Other regs))
  = if is_r r0 r1 || is_r r0 r2
    then Transitional.MVal Other x
    else Transitional.Register.get r0 regs.
Proof.
case E1: (is_r r0 r1) => /=.
- by rewrite -(is_r_eq E1) tget_set_eq.
- rewrite (tget_set_neq _ _ _ (is_r_neq E1)).
  case E2: (is_r r0 r2).
  + by rewrite -(is_r_eq E2) tget_set_eq.
  + by rewrite (tget_set_neq _ _ _ (is_r_neq E2)).
Qed.

(* binops preserve GOODU (pointer rows keep component/block) *)
Lemma eval_binop_goodu (mem : Transitional.Memory.t)
    (F : Component.id -> seq Block.id)
    (op : Values.binop) (x y : value) :
  goodu mem F x -> goodu mem F y -> goodu mem F (eval_binop op x y).
Proof.
move=> Hx Hy.
have GI : forall n : Z, goodu mem F (Int n) by move=> n p.
have GU : goodu mem F Undef by move=> p.
case: op; case: x Hx => [nx|px|] Hx; case: y Hy => [ny|py|] Hy //=;
  try exact: GI; try exact: GU.
- move=> p [<-].
  case: py Hy => [[cy by0] oy] Hy.
  exact: (Hy (cy, by0, oy) (erefl _)).
- move=> p [<-].
  case: px Hx => [[cx bx] ox] Hx.
  exact: (Hx (cx, bx, ox) (erefl _)).
- move=> p [<-].
  case: px Hx => [[cx bx] ox] Hx.
  exact: (Hx (cx, bx, ox) (erefl _)).
- case: px Hx => [[cx bx] ox] Hx; case: py Hy => [[cy by0] oy] Hy.
  move=> p /=.
  by case: (Nat.eqb cx cy && Nat.eqb bx by0).
- move=> p.
  by case: (Pointer.leq px py).
Qed.

Lemma nth_error_nil (A : Type) (j : nat) :
  nth_error (@nil A) j = None.
Proof. by case: j. Qed.

(* an indexed CRa contradicts nocra *)
Lemma nth_error_hasCRa (sg : seq class3) (j : nat) :
  nth_error sg j = Some CRa -> has (fun k => c3_eqb k CRa) sg.
Proof.
elim: sg j => [|x sg IH] [|j] //=.
- by move=> [->]; rewrite c3_eqb_refl.
- move=> H. by rewrite (IH _ H) orbT.
Qed.

(* nth_error into an rcons *)
Lemma nth_error_rcons (A : Type) (s : seq A) (x : A) (j : nat) :
  nth_error (rcons s x) j
  = if j < size s then nth_error s j
    else if j == size s then Some x else None.
Proof.
elim: s j => [|y s IH] j /=.
- case: j => [|j] //=.
  by rewrite nth_error_nil.
- by case: j => [|j] //=.
Qed.

(* the converse of [nth_error_hasCRa] *)
Lemma hasCRa_nth_error (sg : seq class3) :
  has (fun k => c3_eqb k CRa) sg ->
  exists j, nth_error sg j = Some CRa.
Proof.
elim: sg => [|x sg IH] //=.
case/orP => [Hx|Hs].
- exists 0. by rewrite (c3_eqb_eq Hx).
- have [j Hj] := IH Hs. by exists j.+1.
Qed.

(* ---- [bodycarg] transport kit ---- *)

Lemma bodycarg_nil : bodycarg [::].
Proof. by move=> j; rewrite nth_error_nil. Qed.

(* a non-CRa push preserves the discipline *)
Lemma bodycarg_rcons_u (sg : seq class3) (k : class3) :
  c3_eqb k CRa = false -> bodycarg sg -> bodycarg (rcons sg k).
Proof.
move=> Hk HB j.
rewrite nth_error_rcons.
case Hlt: (j < size sg).
- move=> Hj.
  have [Hj2 H1] := HB _ Hj.
  split; first exact: Hj2.
  have Hlt1 : 1 < size sg := nth_error_size H1.
  by rewrite nth_error_rcons Hlt1.
- case: eqP => // _ -[Hkk].
  by rewrite Hkk c3_eqb_refl in Hk.
Qed.

(* the gated CRa push establishes it *)
Lemma bodycarg_rcons_ra (sg : seq class3) :
  nth_error sg 1 = Some CArg -> bodycarg sg -> bodycarg (rcons sg CRa).
Proof.
move=> H1 HB j.
rewrite nth_error_rcons.
have Hlt1 : 1 < size sg := nth_error_size H1.
case Hlt: (j < size sg).
- move=> Hj.
  have [Hj2 _] := HB _ Hj.
  split; first exact: Hj2.
  by rewrite nth_error_rcons Hlt1.
- case: eqP => // -> _.
  split; first exact: Hlt1.
  by rewrite nth_error_rcons Hlt1.
Qed.

(* pops preserve it *)
Lemma bodycarg_pop (sg : seq class3) (k : class3) :
  bodycarg (rcons sg k) -> bodycarg sg.
Proof.
move=> HB j Hj.
have Hlt : j < size sg := nth_error_size Hj.
have Hj' : nth_error (rcons sg k) j = Some CRa.
{ by rewrite nth_error_rcons Hlt. }
have [Hj2 H1] := HB _ Hj'.
split; first exact: Hj2.
have Hlt1 : 1 < size sg := ltnW (leq_ltn_trans Hj2 Hlt).
by move: H1; rewrite nth_error_rcons Hlt1.
Qed.

(* the consumer form: a CRa-holding ek-sig has the baseline CArg *)
Lemma bodycarg_nocra (sg : seq class3) :
  ~~ nocra sg -> bodycarg sg -> nth_error sg 1 = Some CArg.
Proof.
rewrite /nocra negbK => /hasCRa_nth_error [j Hj] HB.
have [_ H1] := HB _ Hj.
exact: H1.
Qed.

(* ---- [pend_sig] transport kit ---- *)

Lemma pend_sig_eq (v w : sv) :
  sv_sig w = sv_sig v -> sv_pend w = sv_pend v ->
  pend_sig w = pend_sig v.
Proof. by rewrite /pend_sig => -> ->. Qed.

Lemma pend_sig_none (v : sv) :
  sv_pend v = None -> pend_sig v = sv_sig v.
Proof. by rewrite /pend_sig => ->. Qed.

Lemma pend_sig_some (v : sv) (k : class3) :
  sv_pend v = Some k -> pend_sig v = rcons (sv_sig v) k.
Proof. by rewrite /pend_sig => ->. Qed.

Lemma sv_le_fields (v w : sv) :
  sv_le v w ->
  [/\ sv_ph w = sv_ph v, sv_sig w = sv_sig v, sv_pend w = sv_pend v
    & sv_ek w = sv_ek v]
  /\ [/\ t_le (sv_a1 v) (sv_a1 w), t_le (sv_a2 v) (sv_a2 w),
         sc_le (sv_sc v) (sv_sc w) & o_le (sv_one v) (sv_one w)].
Proof.
case/and5P => /ph_eqbP Eph Hon /Bool.eqb_prop Hek _
  /and5P [/cseq_eqb_eq Esg /opt_eqb_eq Epd Ht1 Ht2 Hsc].
by do !split.
Qed.

(* an aux claim survives weakening of the taint at unchanged
   ph/sig/pend *)
Lemma aux_claim_le_nopd (mem0 : Transitional.Memory.t)
    (F : Component.id -> seq Block.id) (ch : seq act)
    (cs : value) (v w : sv) (t t' : taint) (c : Component.id)
    (x : value) :
  sv_ph w = sv_ph v -> sv_sig w = sv_sig v ->
  t_le t t' ->
  aux_claim mem0 F ch cs v t c x -> aux_claim mem0 F ch cs w t' c x.
Proof.
move=> Eph Esg Ht.
rewrite /aux_claim Eph Esg.
by case: t Ht; case: t' => //=.
Qed.

(* the 4-premise spelling for the call sites; the pend premise is
   unused ([aux_claim] no longer keys on it) *)
Lemma aux_claim_le (mem0 : Transitional.Memory.t)
    (F : Component.id -> seq Block.id) (ch : seq act)
    (cs : value) (v w : sv) (t t' : taint) (c : Component.id)
    (x : value) :
  sv_ph w = sv_ph v -> sv_sig w = sv_sig v -> sv_pend w = sv_pend v ->
  t_le t t' ->
  aux_claim mem0 F ch cs v t c x -> aux_claim mem0 F ch cs w t' c x.
Proof.
move=> Eph Esg _ Ht.
exact: aux_claim_le_nopd Eph Esg Ht.
Qed.

(* every non-ASp aux row is independent of the sv keys *)
Lemma aux_claim_nsp (mem0 : Transitional.Memory.t)
    (F : Component.id -> seq Block.id) (ch : seq act)
    (cs : value) (v w : sv) (t : taint) (c : Component.id)
    (x : value) :
  t <> ASp ->
  aux_claim mem0 F ch cs v t c x -> aux_claim mem0 F ch cs w t c x.
Proof.
by case: t.
Qed.

(* the scratch claim survives custody weakening at equal phase *)
Lemma scr_claim_le (mem : Transitional.Memory.t) (c : Component.id)
    (cs rsp : value) (v w : sv) :
  sv_ph w = sv_ph v -> sc_le (sv_sc v) (sv_sc w) ->
  match sv_sc v with
  | SCnone => scr_val mem c cs
  | SCpark => sv_ph v = PBody -> scr_val mem c rsp
  | SCrest => scr_val mem c cs
  | SCused => True
  end ->
  match sv_sc w with
  | SCnone => scr_val mem c cs
  | SCpark => sv_ph w = PBody -> scr_val mem c rsp
  | SCrest => scr_val mem c cs
  | SCused => True
  end.
Proof.
move=> Eph Hsc.
rewrite Eph.
by case: (sv_sc v) Hsc; case: (sv_sc w).
Qed.

(* a silent pc move within the component, the map value weakening
   along sv_le: every keyed claim transports *)
Lemma dinv_pcmove (cur : option Block.id) (chain : seq act)
    (F : Component.id -> seq Block.id) (curscr : value)
    (mem : Transitional.Memory.t) (regs : Transitional.Register.t)
    (pc : Pointer.t) (pct : Transitional.pc_tag) (pc' : Pointer.t)
    (v w : sv) :
  dinv cur chain F curscr mem regs pc pct ->
  Pointer.component pc' = Pointer.component pc ->
  svat pc = Some v -> svat pc' = Some w -> sv_le v w ->
  dinv cur chain F curscr mem regs pc' pct.
Proof.
move=> HI Ec Ev Ew Hle.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
constructor.
- exact: di_rtag HI.
- exact: di_rval HI.
- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
  apply: (aux_claim_le Eph Esg Epd Ht1).
  exact: (di_a1 HI Ev).
- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
  apply: (aux_claim_le Eph Esg Epd Ht2).
  exact: (di_a2 HI Ev).
- move=> w0; rewrite Ew => -[<-] => Hon1.
  apply: (di_one HI Ev).
  exact: o_le_true Hon Hon1.
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP.
  exact: (di_prol HI Ev HP).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
  exact: (di_spprol HI Ev HP).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Ec => HP1 HP2.
  exact: (di_body HI Ev HP1 HP2).
- move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
  exact: (di_sp HI Ev HP Hb).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
  exact: (di_sptear HI Ev HP).
- move=> w0 b; rewrite Ew => -[<-]. rewrite Esg Ec => Hb.
  exact: (di_frame HI Ev Hb).
- move=> w0 b k; rewrite Ew => -[<-]. rewrite Esg Epd Ec => Hb Hk.
  exact: (di_pend HI Ev Hb Hk).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP HPd HK.
  exact: (di_ra HI Ev HP HPd HK).
- exact: di_mem HI.
- exact: di_scrtag HI.
- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
  exact: (scr_claim_le Eph Hsc (di_scr HI Ev)).
- move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
  exact: (di_post HI Ev HP Hb).
- move=> c A. rewrite Ec => Hc HA.
  exact: (di_scrfor HI Hc HA).
- exact: di_chain HI.
- move=> i A b HA Hb. rewrite Ec => HcA.
  exact: (di_dist HI HA Hb HcA).
- exact: di_dist2 HI.
- exact: di_fbound HI.
- exact: di_f01 HI.
- exact: di_nb2 HI.
- exact: di_dom HI.
- exact: di_level HI.
- exact: di_flag HI.
- move=> w0; rewrite Ew => -[<-] Hekw.
  apply: (di_ek HI Ev).
  by rewrite -Eek.
- move=> i X HX Hnw.
  case: (di_nwshadow HI HX Hnw)
    => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
  { right. exists j, W. by split. }
  left. split; last exact: HPre.
  by rewrite Ec.
- move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
- move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
  exact: (di_scr0 HI Hc0 Hg0 Htw).
- move=> w0; rewrite Ew => -[<-] Hekw.
  apply: (di_ekwin HI Ev).
  by rewrite -Eek.
- move=> w0; rewrite Ew => -[<-] Hekw.
  rewrite (pend_sig_eq Esg Epd).
  apply: (di_bodycarg HI Ev).
  by rewrite -Eek.
- exact: (di_chain2 HI).
Qed.

(* what a non-SP non-RA register read is worth, per its taint *)
Lemma rtaint_claim (cur : option Block.id) (chain : seq act)
    (F : Component.id -> seq Block.id) (curscr : value)
    (mem : Transitional.Memory.t) (regs : Transitional.Register.t)
    (pc : Pointer.t) (pct : Transitional.pc_tag)
    (v : sv) (r1 : register) :
  dinv cur chain F curscr mem regs pc pct ->
  svat pc = Some v ->
  is_r r1 R_SP = false -> is_r r1 R_RA = false ->
  aux_claim mem F chain curscr v (rtaint v r1) (Pointer.component pc)
    (Transitional.val (Transitional.Register.get r1 regs)).
Proof.
move=> HI Ev Esp Era.
rewrite /rtaint Esp Era.
case E1: (is_r r1 R_AUX1).
- have -> : r1 = R_AUX1 := is_r_eq E1.
  exact: (di_a1 HI Ev).
- case E2: (is_r r1 R_AUX2).
  + have -> : r1 = R_AUX2 := is_r_eq E2.
    exact: (di_a2 HI Ev).
  + case E0: (is_r r1 R_ONE).
    * case Eone: (sv_one v).
      -- rewrite /aux_claim.
         apply: (di_rval HI).
         ++ exact: is_r_neq Era.
         ++ exact: is_r_neq Esp.
         ++ exact: is_r_neq E1.
         ++ exact: is_r_neq E2.
      -- exact: I.
    * case EA: (is_r r1 R_ARG).
      -- case Earg: (sv_arg v).
         ++ rewrite /aux_claim.
            apply: (di_rval HI).
            ** exact: is_r_neq Era.
            ** exact: is_r_neq Esp.
            ** exact: is_r_neq E1.
            ** exact: is_r_neq E2.
         ++ exact: I.
      -- rewrite /aux_claim.
         apply: (di_rval HI).
         ++ exact: is_r_neq Era.
         ++ exact: is_r_neq Esp.
         ++ exact: is_r_neq E1.
         ++ exact: is_r_neq E2.
Qed.

(* the master transport for a silent register-writing step: the sv
   moves by a structure-preserving transfer (ph/sig/pend/sc equal),
   R_RA and R_SP's value survive, and the caller supplies the four
   register obligations *)
Lemma dinv_regw (cur : option Block.id) (chain : seq act)
    (F : Component.id -> seq Block.id) (cs : value)
    (mem : Transitional.Memory.t)
    (regs regs' : Transitional.Register.t)
    (pc : Pointer.t) (pct : Transitional.pc_tag) (v v' w : sv) :
  dinv cur chain F cs mem regs pc pct ->
  svat pc = Some v -> svat (Pointer.inc pc) = Some w -> sv_le v' w ->
  sv_ph v' = sv_ph v -> sv_sig v' = sv_sig v ->
  sv_pend v' = sv_pend v -> sv_sc v' = sv_sc v ->
  sv_ek v' = sv_ek v ->
  (sv_one v' = true ->
     Transitional.val (Transitional.Register.get R_ONE regs')
     = Int 1) ->
  Transitional.Register.get R_RA regs'
  = Transitional.Register.get R_RA regs ->
  Transitional.val (Transitional.Register.get R_SP regs')
  = Transitional.val (Transitional.Register.get R_SP regs) ->
  (forall r0, r0 <> R_RA ->
     tvtag (Transitional.Register.get r0 regs') = Other) ->
  (forall r0, r0 <> R_RA -> r0 <> R_SP -> r0 <> R_AUX1 ->
     r0 <> R_AUX2 ->
     goodu mem F (Transitional.val (Transitional.Register.get r0 regs'))) ->
  aux_claim mem F chain cs w (sv_a1 w) (Pointer.component pc)
    (Transitional.val (Transitional.Register.get R_AUX1 regs')) ->
  aux_claim mem F chain cs w (sv_a2 w) (Pointer.component pc)
    (Transitional.val (Transitional.Register.get R_AUX2 regs')) ->
  dinv cur chain F cs mem regs' (Pointer.inc pc) pct.
Proof.
move=> HI Ev Ew Hle Wph Wsg Wpd Wsc Wek Oone Era Esp Ortag Orval
       Oa1 Oa2.
have [[Eph Esg Epd Eek] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
rewrite Wph in Eph. rewrite Wsg in Esg. rewrite Wpd in Epd.
rewrite Wsc in Hsc. rewrite Wek in Eek.
have Ec : Pointer.component (Pointer.inc pc) = Pointer.component pc.
{ by case: (pc) => [[c0 b0] o0]. }
constructor.
- exact: Ortag.
- exact: Orval.
- move=> w0; rewrite Ew => -[<-]. rewrite Ec. exact: Oa1.
- move=> w0; rewrite Ew => -[<-]. rewrite Ec. exact: Oa2.
- move=> w0; rewrite Ew => -[<-] Hon1.
  apply: Oone.
  exact: o_le_true Hon Hon1.
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP.
  exact: (di_prol HI Ev HP).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
  rewrite Esp. exact: (di_spprol HI Ev HP).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Ec => HP1 HP2.
  exact: (di_body HI Ev HP1 HP2).
- move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
  rewrite Esp. exact: (di_sp HI Ev HP Hb).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph => HP.
  rewrite Esp. exact: (di_sptear HI Ev HP).
- move=> w0 b; rewrite Ew => -[<-]. rewrite Esg Ec => Hb.
  exact: (di_frame HI Ev Hb).
- move=> w0 b k; rewrite Ew => -[<-]. rewrite Esg Epd Ec => Hb Hk.
  exact: (di_pend HI Ev Hb Hk).
- move=> w0; rewrite Ew => -[<-]. rewrite Eph Esg Epd => HP HPd HK.
  rewrite Era. exact: (di_ra HI Ev HP HPd HK).
- exact: (di_mem HI).
- exact: (di_scrtag HI).
- move=> w0; rewrite Ew => -[<-]. rewrite Ec.
  have HD := di_scr HI Ev.
  move: Hsc. rewrite /sc_le.
  case/orP => [/sc_eqb_eq Escw|/sc_eqb_eq Escw]; last first.
  { by rewrite Escw. }
  rewrite -Escw.
  case: (sv_sc v) HD => HD /=.
  + exact: HD.
  + rewrite Eph Esp => HP. exact: HD HP.
  + exact: HD.
  + by [].
- move=> w0 b; rewrite Ew => -[<-]. rewrite Eph Esg Ec => HP Hb.
  exact: (di_post HI Ev HP Hb).
- move=> c0 A. rewrite Ec => Hc0 HA.
  exact: (di_scrfor HI Hc0 HA).
- exact: (di_chain HI).
- move=> i A b0 HA Hb0. rewrite Ec => HcA.
  exact: (di_dist HI HA Hb0 HcA).
- exact: (di_dist2 HI).
- exact: (di_fbound HI).
- exact: (di_f01 HI).
- exact: (di_nb2 HI).
- exact: (di_dom HI).
- exact: (di_level HI).
- exact: (di_flag HI).
- move=> w0; rewrite Ew => -[<-] Hekw.
  apply: (di_ek HI Ev).
  by rewrite -Eek.
- move=> i X HX Hnw.
  case: (di_nwshadow HI HX Hnw)
    => [[HcX HPre]|[j [W [Hj HW HcW HwW HSeg]]]]; last first.
  { right. exists j, W. by split. }
  left. split; last exact: HPre.
  by rewrite Ec.
- move=> Hh. rewrite Ec. exact: (di_cswin HI Hh).
- move=> c0 S0. rewrite Ec => Hc0 Hg0 Htw.
  exact: (di_scr0 HI Hc0 Hg0 Htw).
- move=> w0; rewrite Ew => -[<-] Hekw.
  apply: (di_ekwin HI Ev).
  by rewrite -Eek.
- move=> w0; rewrite Ew => -[<-] Hekw.
  rewrite (pend_sig_eq Esg Epd).
  apply: (di_bodycarg HI Ev).
  by rewrite -Eek.
- exact: (di_chain2 HI).
Qed.

(* ================================================================== *)
(* Memory-step helpers: allocation.                                   *)
(* ================================================================== *)

Lemma nth_error_repeat_inv (A : Type) (x y : A) (n j : nat) :
  nth_error (repeat x n) j = Some y -> y = x.
Proof.
elim: n j => [|n IH] [|j] //=.
- by move=> [<-].
- exact: IH.
Qed.

Lemma alloc_shape (mem mem' : Transitional.Memory.t)
    (c : Component.id) (n : nat) (ptr : Pointer.t) :
  Transitional.Memory.alloc mem c n = Some (mem', ptr) ->
  exists cm,
    [/\ getm mem c = Some cm,
        ptr = (c, Transitional.Memory.nextblock cm, 0%Z)
      & mem' = setm mem c
          {| Transitional.Memory.content :=
               setm (Transitional.Memory.content cm)
                 (Transitional.Memory.nextblock cm)
                 (repeat (Transitional.tUndef, def_mem_tag c false) n);
             Transitional.Memory.nextblock :=
               (1 + Transitional.Memory.nextblock cm)%N |}].
Proof.
rewrite /Transitional.Memory.alloc.
case E: (getm mem c) => [cm|] //=.
move=> [<- <-].
by exists cm.
Qed.

Section AllocFacts.

Variables (mem mem' : Transitional.Memory.t) (c : Component.id)
          (n : nat) (cm : Transitional.Memory.mem).
Hypothesis Hcm : getm mem c = Some cm.
Local Notation nb := (Transitional.Memory.nextblock cm).
Local Notation ncm :=
  {| Transitional.Memory.content :=
       setm (Transitional.Memory.content cm) nb
         (repeat (Transitional.tUndef, def_mem_tag c false) n);
     Transitional.Memory.nextblock := (1 + nb)%N |}.
Hypothesis Emem' : mem' = setm mem c ncm.

Lemma alloc_getm_same : getm mem' c = Some ncm.
Proof. by rewrite Emem' setmE eqxx. Qed.

Lemma alloc_getm_other (c0 : Component.id) :
  c0 <> c -> getm mem' c0 = getm mem c0.
Proof.
move=> Hne. rewrite Emem' setmE.
case E: (c0 == c) => //.
by move/eqP: E => E; case: (Hne E).
Qed.

Lemma alloc_cell_old (c0 : Component.id) (b0 : Block.id) (j : nat) :
  (c0 == c) && (b0 == nb) = false ->
  cell_at mem' c0 b0 j = cell_at mem c0 b0 j.
Proof.
move=> Hne.
rewrite /cell_at.
case Ec0: (c0 == c).
- move/eqP: Ec0 => Ec0. subst c0.
  move: Hne. rewrite eqxx /= => Hb0.
  rewrite alloc_getm_same Hcm /= setmE Hb0.
  by [].
- have Hne0 : c0 <> c by move=> E; rewrite E eqxx in Ec0.
  by rewrite (alloc_getm_other Hne0).
Qed.

Lemma alloc_cell_new (j : nat) :
  cell_at mem' c nb j
  = nth_error (repeat (Transitional.tUndef, def_mem_tag c false) n) j.
Proof.
rewrite /cell_at alloc_getm_same /= setmE eqxx.
by [].
Qed.

Lemma alloc_vblock (p : Pointer.t) :
  vblock_ok mem p -> vblock_ok mem' p.
Proof.
case=> cm0 [Hc0 Hlt].
case Ec0: (Pointer.component p == c).
- move/eqP: Ec0 => Ec0.
  exists ncm. split; first by rewrite Ec0 alloc_getm_same.
  have Ecm : cm0 = cm by move: Hc0; rewrite Ec0 Hcm => -[].
  subst cm0. move: Hlt => /=. by lia.
- exists cm0. split=> //.
  rewrite alloc_getm_other //.
  by move/eqP: Ec0.
Qed.

Lemma alloc_goodu (F : Component.id -> seq Block.id) (x : value) :
  goodu mem F x -> goodu mem' F x.
Proof.
move=> H p E.
have [H1 H2 H3] := H p E.
split=> //.
exact: alloc_vblock H3.
Qed.

Lemma alloc_scr_val (c0 : Component.id) (x : value) :
  (2 <= nb)%N ->
  scr_val mem c0 x -> scr_val mem' c0 x.
Proof.
move=> Hnb [cv [tg0 [Hcell Hv]]].
exists cv, tg0. split=> //.
rewrite (alloc_cell_old 0) //.
case E: (c0 == c) => //=.
case E1: (1 == nb) => //.
move/eqP: E1 => E1. by lia.
Qed.

Lemma alloc_aux_claim (F : Component.id -> seq Block.id)
    (ch : seq act) (cs0 : value) (v : sv) (t : taint)
    (c0 : Component.id) (x : value) :
  aux_claim mem F ch cs0 v t c0 x ->
  aux_claim mem' F ch cs0 v t c0 x.
Proof.
case: t => //=.
exact: alloc_goodu.
Qed.

End AllocFacts.

(* ================================================================== *)
(* Memory-step helpers: stores.                                       *)
(* ================================================================== *)

Lemma store_shape (mem : Transitional.Memory.t) (ptr : Pointer.t)
    (cell : Transitional.tvalue * mem_tag)
    (mem' : Transitional.Memory.t) :
  Transitional.Memory.store mem ptr cell = Some mem' ->
  exists cm chunk chunk',
    [/\ getm mem (Pointer.component ptr) = Some cm,
        getm (Transitional.Memory.content cm) (Pointer.block ptr)
        = Some chunk,
        (0 <=? Pointer.offset ptr)%Z = true,
        list_upd chunk (Z.to_nat (Pointer.offset ptr)) cell
        = Some chunk'
      & mem' = setm mem (Pointer.component ptr)
          {| Transitional.Memory.content :=
               setm (Transitional.Memory.content cm)
                 (Pointer.block ptr) chunk';
             Transitional.Memory.nextblock :=
               Transitional.Memory.nextblock cm |}].
Proof.
rewrite /Transitional.Memory.store /Transitional.Memory.store_b.
case E1: (getm mem _) => [cm|] //=.
case E2: (getm _ _) => [chunk|] //=.
case E3: (0 <=? _)%Z => //=.
case E4: (list_upd _ _ _) => [chunk'|] //= -[<-].
by exists cm, chunk, chunk'.
Qed.

Section StoreFacts.

Variables (mem mem' : Transitional.Memory.t) (ptr : Pointer.t)
          (cell : Transitional.tvalue * mem_tag)
          (cm : Transitional.Memory.mem)
          (chunk chunk' : seq (Transitional.tvalue * mem_tag)).
Hypothesis Hcm : getm mem (Pointer.component ptr) = Some cm.
Hypothesis Hchunk :
  getm (Transitional.Memory.content cm) (Pointer.block ptr)
  = Some chunk.
Hypothesis Hupd :
  list_upd chunk (Z.to_nat (Pointer.offset ptr)) cell = Some chunk'.
Hypothesis Emem' : mem' = setm mem (Pointer.component ptr)
  {| Transitional.Memory.content :=
       setm (Transitional.Memory.content cm) (Pointer.block ptr)
         chunk';
     Transitional.Memory.nextblock :=
       Transitional.Memory.nextblock cm |}.

Lemma store_getm_other (c0 : Component.id) :
  c0 <> Pointer.component ptr -> getm mem' c0 = getm mem c0.
Proof.
move=> Hne. rewrite Emem' setmE.
case E: (c0 == Pointer.component ptr) => //.
by move/eqP: E => E; case: (Hne E).
Qed.

Lemma store_cell_other (c0 : Component.id) (b0 : Block.id) (j : nat) :
  [&& c0 == Pointer.component ptr, b0 == Pointer.block ptr
    & j == Z.to_nat (Pointer.offset ptr)] = false ->
  cell_at mem' c0 b0 j = cell_at mem c0 b0 j.
Proof.
move=> Hne.
rewrite /cell_at.
case Ec0: (c0 == Pointer.component ptr); last first.
{ have Hne0 : c0 <> Pointer.component ptr.
  { by move=> E; rewrite E eqxx in Ec0. }
  by rewrite (store_getm_other Hne0). }
move/eqP: Ec0 Hne => Ec0. subst c0.
rewrite eqxx /= Emem' setmE eqxx Hcm /= setmE.
case Eb0: (b0 == Pointer.block ptr) => /= Hj.
- move/eqP: Eb0 => Eb0. subst b0.
  rewrite Hchunk.
  apply: (list_upd_nth_error_other Hupd).
  by move=> E; rewrite E eqxx in Hj.
- by [].
Qed.

Lemma store_cell_same :
  cell_at mem' (Pointer.component ptr) (Pointer.block ptr)
    (Z.to_nat (Pointer.offset ptr)) = Some cell.
Proof.
rewrite /cell_at Emem' setmE eqxx /= setmE eqxx.
exact: (list_upd_nth_error_same Hupd).
Qed.

Lemma store_vblock (p : Pointer.t) :
  vblock_ok mem p -> vblock_ok mem' p.
Proof.
case=> cm0 [Hc0 Hlt].
case Ec0: (Pointer.component p == Pointer.component ptr).
- move/eqP: Ec0 => Ec0.
  eexists. split.
  + by rewrite Ec0 Emem' setmE eqxx.
  + have Ecm : cm0 = cm.
    { move: Hc0. rewrite Ec0 Hcm. by move=> [<-]. }
    subst cm0. by move: Hlt => /=.
- exists cm0. split=> //.
  rewrite store_getm_other //.
  by move=> E; rewrite E eqxx in Ec0.
Qed.

Lemma store_goodu (F : Component.id -> seq Block.id) (x : value) :
  goodu mem F x -> goodu mem' F x.
Proof.
move=> H p E.
have [H1 H2 H3] := H p E.
split=> //.
exact: store_vblock H3.
Qed.

Lemma store_aux_claim (F : Component.id -> seq Block.id)
    (ch : seq act) (cs0 : value) (v : sv) (t : taint)
    (c0 : Component.id) (x : value) :
  aux_claim mem F ch cs0 v t c0 x ->
  aux_claim mem' F ch cs0 v t c0 x.
Proof.
case: t => //=.
exact: store_goodu.
Qed.

Lemma store_frame_ok_away (F : Component.id -> seq Block.id)
    (c1 : Component.id) (b1 : Block.id) (sg : seq class3)
    (carry cscr : value) (rcap : Transitional.tvalue) :
  (c1 == Pointer.component ptr) && (b1 == Pointer.block ptr) = false ->
  frame_ok F mem c1 b1 sg carry cscr rcap ->
  frame_ok F mem' c1 b1 sg carry cscr rcap.
Proof.
move=> Hne HF j k Hk.
have [cv [tg0 [Hcell Hrow]]] := HF j k Hk.
exists cv, tg0.
have Hne' : [&& c1 == Pointer.component ptr,
               b1 == Pointer.block ptr
             & j == Z.to_nat (Pointer.offset ptr)] = false.
{ move: Hne. by case: (c1 == _); case: (b1 == _). }
rewrite (store_cell_other Hne').
split=> //.
case: k {Hk} Hrow => //= -[T1 T2]; split=> //;
exact: store_goodu T2.
Qed.

Lemma store_scr_val_away (c0 : Component.id) (x : value) :
  (c0 == Pointer.component ptr) && (1 == Pointer.block ptr) = false ->
  scr_val mem c0 x -> scr_val mem' c0 x.
Proof.
move=> Hne [cv [tg0 [Hcell Hv]]].
exists cv, tg0. split=> //.
have Hne3 : [&& c0 == Pointer.component ptr,
               1 == Pointer.block ptr
             & 0 == Z.to_nat (Pointer.offset ptr)] = false.
{ move: Hne. by case: (c0 == _); case: (1 == _). }
by rewrite (store_cell_other Hne3).
Qed.

Lemma store_nb2 (c0 : Component.id)
    (cm0 : Transitional.Memory.mem) :
  (forall c1 cm1, getm mem c1 = Some cm1 ->
     2 <= Transitional.Memory.nextblock cm1) ->
  getm mem' c0 = Some cm0 ->
  2 <= Transitional.Memory.nextblock cm0.
Proof.
move=> Hnb.
rewrite Emem' setmE.
case Ec0: (c0 == Pointer.component ptr).
- move=> [<-] /=. exact: Hnb Hcm.
- exact: Hnb.
Qed.

Lemma store_dom (c0 : Component.id) :
  (exists cm0, getm mem c0 = Some cm0) ->
  exists cm0, getm mem' c0 = Some cm0.
Proof.
case=> cm0 Hcm0.
rewrite Emem' setmE.
case Ec0: (c0 == Pointer.component ptr).
- by eexists.
- by exists cm0.
Qed.

End StoreFacts.

(* the generic binop arm: both operands AU, the result a fresh AU
   value in a non-structural register *)
Lemma dinv_binop_gen (cur : option Block.id) (chain : seq act)
    (F : Component.id -> seq Block.id) (cs : value)
    (mem : Transitional.Memory.t) (regs : Transitional.Register.t)
    (pc : Pointer.t) (pct : Transitional.pc_tag)
    (op0 : Values.binop) (r1 r2 r3 : register) (v v' w : sv) :
  dinv cur chain F cs mem regs pc pct ->
  svat pc = Some v -> svat (Pointer.inc pc) = Some w -> sv_le v' w ->
  vgeneric_binop v r1 r2 r3 = Some v' ->
  dinv cur chain F cs mem
    (Transitional.Register.set r3
       (eval_binop op0
          (Transitional.val (Transitional.Register.get r1 regs))
          (Transitional.val (Transitional.Register.get r2 regs)))
       Other regs)
    (Pointer.inc pc) pct.
Proof.
move=> HI Ev Ew Hle.
rewrite /vgeneric_binop.
case E3s: (is_r r3 R_SP) => //=.
case E3r: (is_r r3 R_RA) => //=.
case Epd0: (sv_pend v) => //.
case Eaa: (t_eqb (rtaint v r1) AU && t_eqb (rtaint v r2) AU)
  => // -[Evv].
subst v'.
case/andP: Eaa => Ea1 Ea2.
have E1s : is_r r1 R_SP = false.
{ case E: (is_r r1 R_SP) => //.
  move: Ea1. by rewrite (is_r_eq E) /rtaint /=. }
have E1r : is_r r1 R_RA = false.
{ case E: (is_r r1 R_RA) => //.
  move: Ea1. by rewrite (is_r_eq E) /rtaint /=. }
have E2s : is_r r2 R_SP = false.
{ case E: (is_r r2 R_SP) => //.
  move: Ea2. by rewrite (is_r_eq E) /rtaint /=. }
have E2r : is_r r2 R_RA = false.
{ case E: (is_r r2 R_RA) => //.
  move: Ea2. by rewrite (is_r_eq E) /rtaint /=. }
have Hg1 : goodu mem F
    (Transitional.val (Transitional.Register.get r1 regs)).
{ have := rtaint_claim HI Ev E1s E1r.
  by rewrite (t_eqb_eq Ea1). }
have Hg2 : goodu mem F
    (Transitional.val (Transitional.Register.get r2 regs)).
{ have := rtaint_claim HI Ev E2s E2r.
  by rewrite (t_eqb_eq Ea2). }
have Hgv := @eval_binop_goodu mem F op0 _ _ Hg1 Hg2.
have [W1ph W1sg W1pd W1sc W1on] := wtaint_fields r3 AU v.
have [[W2ph W2sg W2pd] [W2sc W2a1 W2a2]]
  := wone_fields r3 false (wtaint r3 AU v).
have [[G1 G2 G3 G4] [G5 G6 G7 G8]]
  := warg_w_fields r3 (wone r3 false (wtaint r3 AU v)).
have [[Eph Esg Epd' Eek'] [Ht1 Ht2 Hsc Hon]] := sv_le_fields Hle.
rewrite G5 W2a1 in Ht1. rewrite G6 W2a2 in Ht2.
apply: (dinv_regw HI Ev Ew Hle (etrans G1 (etrans W2ph W1ph))
          (etrans G2 (etrans W2sg W1sg))
          (etrans G3 (etrans W2pd W1pd))
          (etrans G4 (etrans W2sc W1sc))
          (etrans G8 (etrans (wone_ek _ _ _) (wtaint_ek _ _ _)))).
- move=> Hon1.
  move: Hon1. rewrite G7 /wone.
  case E3o: (is_r r3 R_ONE) => //= Hon1.
  rewrite (tget_set_neq _ _ _ (is_r_neq' E3o)).
  apply: (di_one HI Ev).
  move: Hon1. by rewrite W1on.
- by rewrite (tget_set_neq _ _ _ (is_r_neq' E3r)).
- by rewrite (tget_set_neq _ _ _ (is_r_neq' E3s)).
- move=> r0 Hr0.
  case E0: (is_r r0 r3).
  + have -> : r0 = r3 := is_r_eq E0.
    by rewrite tget_set_eq.
  + rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
    exact: (di_rtag HI).
- move=> r0 H1 H2 H3 H4.
  case E0: (is_r r0 r3).
  + have -> : r0 = r3 := is_r_eq E0.
    by rewrite tget_set_eq.
  + rewrite (tget_set_neq _ _ _ (is_r_neq E0)).
    exact: (di_rval HI H1 H2 H3 H4).
- rewrite (etrans G1 (etrans W2ph W1ph)) in Eph.
  rewrite (etrans G2 (etrans W2sg W1sg)) in Esg.
  rewrite (etrans G3 (etrans W2pd W1pd)) in Epd'.
  case E31: (is_r r3 R_AUX1).
  + have Er3 : r3 = R_AUX1 := is_r_eq E31. subst r3.
    rewrite tget_set_eq /=.
    have Ea1' : sv_a1 (wtaint R_AUX1 AU v) = AU by [].
    move: Ht1. rewrite Ea1' => Ht1.
    apply: (aux_claim_le Eph Esg Epd' Ht1).
    exact: Hgv.
  + rewrite (tget_set_neq _ _ _ (is_r_neq' E31)).
    have Ea1' : sv_a1 (wtaint r3 AU v) = sv_a1 v.
    { rewrite /wtaint E31. by case: (is_r r3 R_AUX2). }
    move: Ht1. rewrite Ea1' => Ht1.
    apply: (aux_claim_le Eph Esg Epd' Ht1).
    exact: (di_a1 HI Ev).
- rewrite (etrans G1 (etrans W2ph W1ph)) in Eph.
  rewrite (etrans G2 (etrans W2sg W1sg)) in Esg.
  rewrite (etrans G3 (etrans W2pd W1pd)) in Epd'.
  case E32: (is_r r3 R_AUX2).
  + have Er3 : r3 = R_AUX2 := is_r_eq E32. subst r3.
    rewrite tget_set_eq /=.
    have Ea2' : sv_a2 (wtaint R_AUX2 AU v) = AU by [].
    move: Ht2. rewrite Ea2' => Ht2.
    apply: (aux_claim_le Eph Esg Epd' Ht2).
    exact: Hgv.
  + rewrite (tget_set_neq _ _ _ (is_r_neq' E32)).
    have Ea2' : sv_a2 (wtaint r3 AU v) = sv_a2 v.
    { rewrite /wtaint E32.
      by case: (is_r r3 R_AUX1). }
    move: Ht2. rewrite Ea2' => Ht2.
    apply: (aux_claim_le Eph Esg Epd' Ht2).
    exact: (di_a2 HI Ev).
Qed.

Arguments dinv_binop_gen [cur chain F cs mem regs pc pct] op0
  [r1 r2 r3 v v' w].

End Disc.

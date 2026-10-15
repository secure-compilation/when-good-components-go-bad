(** * T2M disc_inv: the per-pc stack-discipline static.

    A per-component oracle map (seq sv aligned with the code) is
    checked by the LOCAL relation [vstep].  Each [sv] records the
    frame phase, per-slot classes, a pending push/pop, the aux-
    register taints and the scratch custody; label joins and
    fallthroughs compare under the LATTICE [sv_le].  [vstep] is
    parametrized by the scratch pointer scr (flag cell at scr+1);
    components instantiate (C, 1, 0). *)

Require Import Common.Definitions.
Require Import Common.Values.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* registers have no eqType; compare via to_nat *)
Definition is_r (r1 r2 : register) : bool :=
  Nat.eqb (Intermediate.Register.to_nat r1)
          (Intermediate.Register.to_nat r2).

(* prologue split: PProlA = entry (R_SP still parent), PProlB =
   parked (after Mov R_SP R_AUX1).  Phases compare EXACTLY under sv_le. *)
Inductive sphase := PProlA | PProlB | PBody | PPost | PTear.

Definition ph_eqb (p1 p2 : sphase) : bool :=
  match p1, p2 with
  | PProlA, PProlA | PProlB, PProlB | PBody, PBody
  | PPost, PPost | PTear, PTear => true
  | _, _ => false
  end.

(* frame-slot classes: RA capability / parked SP / user value / saved arg *)
Inductive class3 := CRa | CSp | CU | CArg.

Definition c3_eqb (k1 k2 : class3) : bool :=
  match k1, k2 with
  | CRa, CRa | CSp, CSp | CU, CU | CArg, CArg => true
  | _, _ => false
  end.

Lemma c3_eqbP : Equality.axiom c3_eqb.
Proof. by case; case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build class3 c3_eqbP.

(* taint states for the aux registers: ASp = parked stack pointer;
   AScr/AFlag = the literal scratch/flag address; AU = user value
   (no frame block, not block 1); ADead = no claim, every read rejected *)
Inductive taint := ASp | AScr | AFlag | AU | ADead.

Definition t_eqb (t1 t2 : taint) : bool :=
  match t1, t2 with
  | ASp, ASp | AScr, AScr | AFlag, AFlag | AU, AU | ADead, ADead => true
  | _, _ => false
  end.

Lemma t_eqbP : Equality.axiom t_eqb.
Proof. by case; case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build taint t_eqbP.

(* scratch-cell custody: SCnone = untouched since entry, SCpark =
   just parked own SP (call imminent), SCrest = restored inherited
   value (teardown), SCused = no claim (top) *)
Inductive scst := SCnone | SCpark | SCrest | SCused.

Definition sc_eqb (x y : scst) : bool :=
  match x, y with
  | SCnone, SCnone | SCpark, SCpark | SCrest, SCrest | SCused, SCused
      => true
  | _, _ => false
  end.

Lemma sc_eqbP : Equality.axiom sc_eqb.
Proof. by case; case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build scst sc_eqbP.

Record sv := SV {
  sv_ph   : sphase;
  sv_sig  : seq class3;        (* per-slot classes, bottom first *)
  sv_pend : option class3;     (* mid push/pop macro *)
  sv_a1   : taint;
  sv_a2   : taint;
  sv_sc   : scst;
  sv_one  : bool;              (* R_ONE known to hold Int 1 *)
  sv_ek   : bool;
  sv_arg  : bool
}.

(* the checker's comparisons are PLAIN FIXPOINTS (no eq_op) so
   frag/comp_ok reduce briskly under simpl/cbv, no HB unfoldings *)
Fixpoint cseq_eqb (s1 s2 : seq class3) : bool :=
  match s1, s2 with
  | [::], [::] => true
  | k1 :: r1, k2 :: r2 => c3_eqb k1 k2 && cseq_eqb r1 r2
  | _, _ => false
  end.

Definition opt_eqb (o1 o2 : option class3) : bool :=
  match o1, o2 with
  | None, None => true
  | Some k1, Some k2 => c3_eqb k1 k2
  | _, _ => false
  end.

Definition sv_eqb (v w : sv) : bool :=
  [&& ph_eqb (sv_ph v) (sv_ph w),
      Bool.eqb (sv_one v) (sv_one w),
      Bool.eqb (sv_ek v) (sv_ek w),
      Bool.eqb (sv_arg v) (sv_arg w)
    & [&& cseq_eqb (sv_sig v) (sv_sig w),
          opt_eqb (sv_pend v) (sv_pend w),
          t_eqb (sv_a1 v) (sv_a1 w),
          t_eqb (sv_a2 v) (sv_a2 w)
        & sc_eqb (sv_sc v) (sv_sc w)]].

(* the two entry values: [sv0] at the component HEADER (cross entry,
   R_ONE killed), [sv0_one] at the inl procedure label (internal Jal,
   R_ONE = Int 1 inherited) *)
Definition sv0 : sv := SV PProlA [::] None ADead ADead SCnone false false false.
Definition sv0_one : sv :=
  SV PProlA [::] None ADead ADead SCnone true true false.

(* the taint/custody/one lattices: ADead / SCused / false are the
   tops; joins compare with [sv_le] (inflow's claims must IMPLY the map's) *)
Definition t_le (t1 t2 : taint) : bool := t_eqb t1 t2 || t_eqb t2 ADead.

Definition sc_le (x y : scst) : bool := sc_eqb x y || sc_eqb y SCused.

Definition o_le (x y : bool) : bool := Bool.eqb x y || ~~ y.

Definition sv_le (v w : sv) : bool :=
  [&& ph_eqb (sv_ph v) (sv_ph w),
      o_le (sv_one v) (sv_one w),
      Bool.eqb (sv_ek v) (sv_ek w),
      o_le (sv_arg v) (sv_arg w)
    & [&& cseq_eqb (sv_sig v) (sv_sig w),
          opt_eqb (sv_pend v) (sv_pend w),
          t_le (sv_a1 v) (sv_a1 w),
          t_le (sv_a2 v) (sv_a2 w)
        & sc_le (sv_sc v) (sv_sc w)]].

Lemma sc_eqb_eq (x y : scst) : sc_eqb x y -> x = y.
Proof. by case: x; case: y. Qed.

Lemma sc_eqb_refl (x : scst) : sc_eqb x x.
Proof. by case: x. Qed.

Lemma sc_le_refl (x : scst) : sc_le x x.
Proof. by rewrite /sc_le sc_eqb_refl. Qed.

Lemma sc_le_trans (x y z : scst) :
  sc_le x y -> sc_le y z -> sc_le x z.
Proof. by case: x; case: y; case: z. Qed.

Lemma sc_le_top (x : scst) : sc_le x SCused.
Proof. by rewrite /sc_le orbT. Qed.

Lemma o_le_refl (x : bool) : o_le x x.
Proof. by case: x. Qed.

Lemma o_le_trans (x y z : bool) : o_le x y -> o_le y z -> o_le x z.
Proof. by case: x; case: y; case: z. Qed.

Lemma o_le_true (x y : bool) : o_le x y -> y = true -> x = true.
Proof. by case: x; case: y. Qed.

Lemma c3_eqb_eq (k1 k2 : class3) : c3_eqb k1 k2 -> k1 = k2.
Proof. by case: k1; case: k2. Qed.

Lemma c3_eqb_refl (k : class3) : c3_eqb k k.
Proof. by case: k. Qed.

Lemma t_eqb_eq (t1 t2 : taint) : t_eqb t1 t2 -> t1 = t2.
Proof. by case: t1; case: t2. Qed.

Lemma t_eqb_refl (t : taint) : t_eqb t t.
Proof. by case: t. Qed.

Lemma cseq_eqb_eq (s1 s2 : seq class3) : cseq_eqb s1 s2 -> s1 = s2.
Proof.
elim: s1 s2 => [|k1 r1 IH] [|k2 r2] //=.
case/andP => /c3_eqb_eq -> /IH ->.
by [].
Qed.

Lemma cseq_eqb_refl (s : seq class3) : cseq_eqb s s.
Proof. by elim: s => [|k r IH] //=; rewrite c3_eqb_refl IH. Qed.

Lemma opt_eqb_eq (o1 o2 : option class3) : opt_eqb o1 o2 -> o1 = o2.
Proof.
case: o1 o2 => [k1|] [k2|] //= /c3_eqb_eq ->.
by [].
Qed.

Lemma opt_eqb_refl (o : option class3) : opt_eqb o o.
Proof. by case: o => [k|] //=; rewrite c3_eqb_refl. Qed.

Lemma t_le_refl (t : taint) : t_le t t.
Proof. by rewrite /t_le t_eqb_refl. Qed.

Lemma t_le_trans (t1 t2 t3 : taint) :
  t_le t1 t2 -> t_le t2 t3 -> t_le t1 t3.
Proof. by case: t1; case: t2; case: t3. Qed.

Lemma t_le_top (t : taint) : t_le t ADead.
Proof. by rewrite /t_le orbT. Qed.

Lemma ph_eqb_refl0 (p : sphase) : ph_eqb p p.
Proof. by case: p. Qed.

Lemma sv_le_refl (v : sv) : sv_le v v.
Proof.
by rewrite /sv_le ph_eqb_refl0 !o_le_refl Bool.eqb_reflx cseq_eqb_refl
   opt_eqb_refl !t_le_refl sc_le_refl.
Qed.

Lemma ph_eqb_trans (p1 p2 p3 : sphase) :
  ph_eqb p1 p2 -> ph_eqb p2 p3 -> ph_eqb p1 p3.
Proof. by case: p1; case: p2; case: p3. Qed.

Lemma sv_le_trans (u v w : sv) :
  sv_le u v -> sv_le v w -> sv_le u w.
Proof.
case/and5P => H1 H0 HK HA
  /and5P [/cseq_eqb_eq H2 /opt_eqb_eq H3 H4 H5 H6].
case/and5P => G1 G0 GK GA
  /and5P [/cseq_eqb_eq G2 /opt_eqb_eq G3 G4 G5 G6].
apply/and5P; split.
- exact: ph_eqb_trans H1 G1.
- exact: o_le_trans H0 G0.
- move/Bool.eqb_prop: HK => ->. exact: GK.
- exact: o_le_trans HA GA.
- apply/and5P; split.
  + by rewrite H2 G2 cseq_eqb_refl.
  + by rewrite H3 G3 opt_eqb_refl.
  + exact: t_le_trans H4 G4.
  + exact: t_le_trans H5 G5.
  + exact: sc_le_trans H6 G6.
Qed.

Lemma sv_le_taint (ph : sphase) (sg : seq class3) (pd : option class3)
    (a1 a2 b1 b2 : taint) (c1 c2 : scst) (o ek ag : bool) :
  t_le a1 b1 -> t_le a2 b2 -> sc_le c1 c2 ->
  sv_le (SV ph sg pd a1 a2 c1 o ek ag) (SV ph sg pd b1 b2 c2 o ek ag).
Proof.
move=> H1 H2 H3.
by rewrite /sv_le /= ph_eqb_refl0 !o_le_refl Bool.eqb_reflx
   cseq_eqb_refl opt_eqb_refl H1 H2 H3.
Qed.

(* pointer literal comparison (components/blocks are nats) *)
Definition ptr_eqb (p q : Pointer.t) : bool :=
  [&& Nat.eqb (Pointer.component p) (Pointer.component q),
      Nat.eqb (Pointer.block p) (Pointer.block q)
    & Z.eqb (Pointer.offset p) (Pointer.offset q)].

Lemma ptr_eqb_refl (p : Pointer.t) : ptr_eqb p p.
Proof.
case: p => [[c b] o].
by rewrite /ptr_eqb /= !PeanoNat.Nat.eqb_refl Z.eqb_refl.
Qed.

(* the taint carried by a register read; R_ONE reads as synced only
   when the one-bit is live *)
Definition rtaint (v : sv) (r : register) : taint :=
  if is_r r R_SP then ASp
  else if is_r r R_RA then ADead
  else if is_r r R_AUX1 then sv_a1 v
  else if is_r r R_AUX2 then sv_a2 v
  else if is_r r R_ONE then (if sv_one v then AU else ADead)
  else if is_r r R_ARG then (if sv_arg v then AU else ADead)
  else AU.

(* retaint a write target (only the aux registers carry taint) *)
Definition wtaint (r : register) (t : taint) (v : sv) : sv :=
  if is_r r R_AUX1
  then SV (sv_ph v) (sv_sig v) (sv_pend v) t (sv_a2 v) (sv_sc v)
          (sv_one v) (sv_ek v) (sv_arg v)
  else if is_r r R_AUX2
  then SV (sv_ph v) (sv_sig v) (sv_pend v) (sv_a1 v) t (sv_sc v)
          (sv_one v) (sv_ek v) (sv_arg v)
  else v.

(* R_ONE-knowledge updates: a write to R_ONE re-keys the bit *)
Definition wone (r : register) (o : bool) (v : sv) : sv :=
  if is_r r R_ONE
  then SV (sv_ph v) (sv_sig v) (sv_pend v) (sv_a1 v) (sv_a2 v)
          (sv_sc v) o (sv_ek v) (sv_arg v)
  else v.

(* R_ARG-knowledge updates: a synced write into R_ARG sets the bit *)
Definition warg (b : bool) (v : sv) : sv :=
  SV (sv_ph v) (sv_sig v) (sv_pend v) (sv_a1 v) (sv_a2 v)
     (sv_sc v) (sv_one v) (sv_ek v) b.

Definition warg_w (r : register) (v : sv) : sv :=
  if is_r r R_ARG then warg true v else v.

(* the bit a constant load establishes *)
Definition cone (iv : imvalue) : bool :=
  match iv with IInt z => Z.eqb z 1 | IPtr _ => false end.

(* a store consumes custody of an aux source *)
Definition dead_src (r : register) (v : sv) : sv := wtaint r ADead v.

(* at most one live RA slot: R_RA pushes only into CRa-free sigs *)
Definition nocra (sg : seq class3) : bool :=
  ~~ has (fun k => c3_eqb k CRa) sg.

(* at most one saved-ARG slot: dead-bit R_ARG pushes only into
   CArg-free sigs *)
Definition nocarg (sg : seq class3) : bool :=
  ~~ has (fun k => c3_eqb k CArg) sg.

(* the body-baseline check: position 1 carries the prologue's CArg.
   [simpl never] so the coherence proofs can rewrite it on abstract sigs *)
Definition nth1carg (sg : seq class3) : bool :=
  opt_eqb (nth_error sg 1) (Some CArg).
Arguments nth1carg : simpl never.

Lemma nth1cargP (sg : seq class3) :
  nth1carg sg -> nth_error sg 1 = Some CArg.
Proof. rewrite /nth1carg. exact: opt_eqb_eq. Qed.

Lemma nth1cargI (sg : seq class3) :
  nth_error sg 1 = Some CArg -> nth1carg sg = true.
Proof. rewrite /nth1carg => ->. exact: opt_eqb_refl. Qed.

(* the class a pushed register carries: parked-SP slots come only
   from R_AUX1 (never R_SP or a tainted R_AUX2) *)
Definition pushclass (v : sv) (r : register) : option class3 :=
  if is_r r R_RA
  then (if nocra (sv_sig v)
           && (if sv_ek v
               then opt_eqb (nth_error (sv_sig v) 1) (Some CArg)
               else cseq_eqb (sv_sig v) [:: CSp; CSp])
        then Some CRa else None)
  else if is_r r R_SP then None
  else if [&& is_r r R_AUX1, t_eqb (sv_a1 v) ASp
            & cseq_eqb (sv_sig v) [::] || cseq_eqb (sv_sig v) [:: CSp]]
  then Some CSp
  else if is_r r R_ARG
  then (if sv_arg v then Some CU
        else if nocarg (sv_sig v) then Some CArg else None)
  else match rtaint v r with
       | AU => Some CU
       | _ => None
       end.

(* Everything below is parametrized by the component's scratch-cell
   address scr (flag cell at scr+1); components instantiate (C, 1, 0). *)
Section WithScr.

Variable scr : Pointer.t.

(* the taint an immediate constant assigns *)
Definition ctaint (iv : imvalue) : taint :=
  match iv with
  | IInt _ => AU
  | IPtr p =>
      if ptr_eqb p scr then AScr
      else if ptr_eqb p (Pointer.add scr 1) then AFlag
      else AU
  end.

(* the generic (non-push/pop) binop transfer *)
Definition vgeneric_binop (v : sv) (r1 r2 r3 : register) : option sv :=
  if is_r r3 R_SP || is_r r3 R_RA then None
  else match sv_pend v with
       | Some _ => None
       | None =>
           if t_eqb (rtaint v r1) AU && t_eqb (rtaint v r2) AU
           then Some (warg_w r3 (wone r3 false (wtaint r3 AU v)))
           else None
       end.

(* the fallthrough transfer; None = the instruction is rejected in
   this state (the compiler never emits it there) *)
Definition vstep (v : sv) (i : Transitional.instr) : option sv :=
  match i with
  | TrNop => Some v
  | TrLabel _ => Some v
  | TrConst iv r =>
      if is_r r R_RA then None
      else if is_r r R_SP
      then match sv_ph v with
           | PProlB => Some v
           | _ => None
           end
      else Some (warg_w r (wone r (cone iv) (wtaint r (ctaint iv) v)))
  | TrMov r1 r2 =>
      if is_r r2 R_SP || is_r r2 R_RA then None
      else if is_r r1 R_SP
      then
           match sv_ph v with
           | PProlA =>
               if is_r r2 R_AUX1
               then Some (SV PProlB (sv_sig v) (sv_pend v)
                             ASp ADead (sv_sc v) (sv_one v) (sv_ek v)
                             (sv_arg v))
               else None
           | _ => None
           end
      else if t_eqb (rtaint v r1) ADead then None
      else if is_r r1 R_ARG && ~~ sv_arg v then None
      else if is_r r2 R_AUX1 || is_r r2 R_AUX2
           then Some (wtaint r2 (rtaint v r1) v)
           else if t_eqb (rtaint v r1) AU
                then Some (warg_w r2 (wone r2 false v)) else None
  | TrBinOp op r1 r2 r3 =>
      match op, sv_ph v with
      | Add, PBody =>
          if [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
               & sv_one v]
          then
            match sv_pend v, sv_sc v with
            | _, SCpark => None
            | Some k, _ =>
                Some (SV PBody (rcons (sv_sig v) k) None
                         (if t_eqb (sv_a1 v) ASp then ADead
                          else sv_a1 v)
                         (if t_eqb (sv_a2 v) ASp then ADead
                          else sv_a2 v)
                         (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
            | None, _ => None
            end
          else vgeneric_binop v r1 r2 r3
      | Minus, PBody =>
          if [&& is_r r1 R_SP, is_r r2 R_ONE, is_r r3 R_SP
               & sv_one v]
          then
            match sv_pend v, rev (sv_sig v), sv_sc v with
            | _, _, SCpark => None
            | None, k :: rest, _ =>
                Some (SV PBody (rev rest) (Some k)
                         (if t_eqb (sv_a1 v) ASp then ADead
                          else sv_a1 v)
                         (if t_eqb (sv_a2 v) ASp then ADead
                          else sv_a2 v)
                         (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
            | _, _, _ => None
            end
          else vgeneric_binop v r1 r2 r3
      | _, PBody => vgeneric_binop v r1 r2 r3
      | _, _ => None
      end
  | TrStore r1 r2 =>
      match sv_ph v with
      | PBody =>
          match sv_pend v with
          | Some _ => None
          | None =>
              if is_r r1 R_SP
              then match pushclass v r2 with
                   | Some k =>
                       let v' := dead_src r2 v in
                       Some (SV PBody (sv_sig v) (Some k)
                                (sv_a1 v') (sv_a2 v') (sv_sc v)
                                (sv_one v) (sv_ek v) (sv_arg v))
                   | None => None
                   end
              else match rtaint v r1 with
                   | AScr =>
                       if is_r r2 R_SP
                       then Some (SV PBody (sv_sig v) None
                                     (sv_a1 v) (sv_a2 v) SCpark
                                     (sv_one v) (sv_ek v) (sv_arg v))
                       else if t_eqb (rtaint v r2) ASp
                               && cseq_eqb (sv_sig v) [:: CSp]
                       then Some (SV PBody (sv_sig v) None
                                     (sv_a1 v) (sv_a2 v) SCrest
                                     (sv_one v) (sv_ek v) (sv_arg v))
                       else None
                   | AFlag =>
                       if t_eqb (rtaint v r2) AU
                       then Some v else None
                   | AU =>
                       if t_eqb (rtaint v r2) AU
                       then Some v else None
                   | _ => None
                   end
          end
      | _ => None
      end
  | TrLoad r1 r2 =>
      match sv_ph v with
      | PBody =>
          if is_r r1 R_SP
          then match sv_pend v with
               | Some CRa =>
                   if is_r r2 R_RA
                   then Some (SV PBody (sv_sig v) None (sv_a1 v)
                                 (sv_a2 v) (sv_sc v) (sv_one v) (sv_ek v)
                                 (sv_arg v))
                   else None
               | Some CSp =>
                   if is_r r2 R_SP && cseq_eqb (sv_sig v) [::]
                   then Some (SV PTear (sv_sig v) None (sv_a1 v)
                                 (sv_a2 v) (sv_sc v) (sv_one v) (sv_ek v)
                                 (sv_arg v))
                   else if is_r r2 R_AUX1 && ~~ cseq_eqb (sv_sig v) [::]                   then Some (SV PBody (sv_sig v) None ASp (sv_a2 v)
                                 (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
                   else None
               | Some CU =>
                   if is_r r2 R_SP || is_r r2 R_RA then None
                   else Some (warg_w r2 (wone r2 false (wtaint r2 AU
                          (SV PBody (sv_sig v) None (sv_a1 v)
                              (sv_a2 v) (sv_sc v) (sv_one v) (sv_ek v)
                              (sv_arg v)))))
               | Some CArg =>                   if is_r r2 R_ARG
                   then Some (SV PBody (sv_sig v) None (sv_a1 v)
                                 (sv_a2 v) (sv_sc v) (sv_one v) (sv_ek v)
                                 false)
                   else None
               | None => None
               end
          else match sv_pend v with
               | Some _ => None
               | None =>
                   match rtaint v r1 with
                   | AScr =>
                       if [&& is_r r2 R_AUX1, sc_eqb (sv_sc v) SCnone
                          & cseq_eqb (sv_sig v) [:: CSp]]
                       then Some (wtaint r2 ASp v) else None
                   | AFlag =>
                       if is_r r2 R_SP || is_r r2 R_RA then None
                       else Some (warg_w r2 (wone r2 false (wtaint r2 AU v)))
                   | AU =>
                       if is_r r2 R_SP || is_r r2 R_RA then None
                       else Some (warg_w r2 (wone r2 false (wtaint r2 AU v)))
                   | _ => None
                   end
               end
      | PPost =>          match sv_pend v with
          | Some _ => None
          | None =>
              if [&& t_eqb (rtaint v r1) AScr, is_r r2 R_SP
                 & ~~ nocra (sv_sig v)]
              then Some (SV PBody (sv_sig v) None (sv_a1 v) (sv_a2 v)
                            SCused (sv_one v) (sv_ek v) (sv_arg v))
              else None
          end
      | _ => None
      end
  | TrAlloc r1 r2 =>
      match sv_ph v with
      | PProlB =>
          if is_r r1 R_SP && is_r r2 R_SP
          then match sv_sc v with
               | SCpark => None
               | _ => Some (SV PBody [::] None (sv_a1 v) (sv_a2 v)
                              (sv_sc v) (sv_one v) (sv_ek v) (sv_arg v))
               end
          else None
      | PBody =>
          if [|| is_r r1 R_SP, is_r r2 R_SP | is_r r1 R_RA] then None
          else match sv_pend v with
               | Some _ => None
               | None =>
                   if t_eqb (rtaint v r2) AU
                   then Some (warg_w r1 (wone r1 false (wtaint r1 AU v)))
                   else None
               end
      | _ => None
      end
  | TrBnz r l =>
      match sv_ph v, sv_pend v with
      | PBody, None => Some v
      | PTear, None => Some v
      | _, _ => None
      end
  | TrJalNat l =>
      match sv_ph v, sv_pend v with
      | PBody, None =>
          if sv_one v && ~~ nocra (sv_sig v)
          then Some (SV PBody (sv_sig v) None ADead ADead SCused true
                        (sv_ek v) (sv_arg v))
          else None
      | _, _ => None
      end
  | TrJalProc pl =>
      match sv_ph v, sv_pend v, sv_sc v with
      | PBody, None, SCpark =>          if (if sv_ek v then nth1carg (sv_sig v) else true)
          then Some (SV PPost (sv_sig v) None ADead ADead SCused false
                        (sv_ek v) false)
          else None
      | _, _, _ => None
      end
  | TrJump r =>      match sv_ph v, sv_pend v with
      | PTear, None =>
          if [&& sv_one v, cseq_eqb (sv_sig v) [::]
             & sv_ek v || match sv_sc v with
                          | SCrest | SCnone => true
                          | _ => false
                          end]
          then Some v else None
      | _, _ => None
      end
  | TrHalt => Some v
  end.

(* ================================================================== *)
(* The per-component local check against an oracle map.               *)
(* ================================================================== *)

Section Check.

Variable S : seq (Transitional.instr * mem_tag).
Variable M : seq sv.

(* position n holds the plain label l *)
Definition lbl_at (n : nat) (l : label) : bool :=
  match nth_error S n with
  | Some (TrLabel (inl l'), _) => Nat.eqb l' l
  | _ => false
  end.

Definition terminal (i : Transitional.instr) : bool :=
  match i with TrJump _ | TrHalt => true | _ => false end.

(* some position of S carries label l with map value w satisfying p *)
Definition lbl_ok (l : label) (p : sv -> bool) : bool :=
  has (fun m => lbl_at m l &&
                match nth_error M m with
                | Some w => p w
                | None => false
                end)
      (iota 0 (size S)).

(* the local condition at position n *)
Definition vc_at (n : nat) : bool :=
  match nth_error S n, nth_error M n with
  | None, _ => true
  | Some _, None => false
  | Some (i, _), Some v =>
      match vstep v i with
      | None => false
      | Some v' =>
          (if terminal i then true
           else match nth_error M n.+1 with
                | Some w => sv_le v' w
                | None => false
                end)
          && match i with
             | TrBnz _ l => lbl_ok l (fun w => sv_le v w)
             | TrJalNat l => lbl_ok l (fun w => sv_eqb w sv0_one)
             | TrLabel (inr _) => sv_eqb v sv0
             | _ => true
             end
      end
  end.

(* the whole component checks *)
Definition comp_ok : bool :=
  (size M == size S) && all vc_at (iota 0 (size S)).

End Check.

(* ================================================================== *)
(* Fragment-relative checking (for the compiler-coherence induction). *)
(* ================================================================== *)

Section Frag.
Variable c : seq (Transitional.instr * mem_tag).
Variable M : seq sv.
Variable L : label -> option sv.

(* Bnz targets resolve WITHIN the fragment or via a PROMISE;
   TrJalNat targets are external and checked at component-assembly
   time, so the fragment check SKIPS them. *)
Definition frag_at (vout : sv) (n : nat) : bool :=
  match nth_error c n, nth_error M n with
  | None, _ => true
  | Some _, None => false
  | Some (i, _), Some v =>
      match vstep v i with
      | None => false
      | Some v' =>
          (if terminal i then true
           else match nth_error M n.+1 with
                | Some w => sv_le v' w
                | None => sv_le v' vout
                end)
          && match i with
             | TrBnz _ l =>
                 lbl_ok c M l (fun w => sv_le v w)
                 || match L l with
                    | Some w => sv_le v w
                    | None => false
                    end
             | TrLabel (inr _) => sv_eqb v sv0
             | _ => true
             end
      end
  end.

Definition frag (vin vout : sv) : bool :=
  [&& size M == size c,
      (match M with
       | w :: _ => sv_le vin w
       | [::] => sv_le vin vout
       end)
    & all (frag_at vout) (iota 0 (size c))].

End Frag.

Lemma ph_eqbP (p1 p2 : sphase) : ph_eqb p1 p2 -> p1 = p2.
Proof. by case: p1; case: p2. Qed.

Lemma sv_eqbP (v w : sv) : sv_eqb v w -> v = w.
Proof.
case: v => ph1 sg1 pd1 a1 b1 c1 o1 k1 g1;
case: w => ph2 sg2 pd2 a2 b2 c2 o2 k2 g2.
case/and5P => /= /ph_eqbP -> /Bool.eqb_prop -> /Bool.eqb_prop ->
  /Bool.eqb_prop ->.
case/and5P => /cseq_eqb_eq -> /opt_eqb_eq -> /t_eqb_eq ->
  /t_eqb_eq -> /sc_eqb_eq ->.
by [].
Qed.

(* sv_eqb is an equivalence-enough *)
Lemma ph_eqb_refl (p : sphase) : ph_eqb p p.
Proof. by case: p. Qed.

Lemma sv_eqb_refl (v : sv) : sv_eqb v v.
Proof.
by rewrite /sv_eqb ph_eqb_refl !Bool.eqb_reflx cseq_eqb_refl
   opt_eqb_refl !t_eqb_refl sc_eqb_refl.
Qed.

(* nth_error over app, ssr-typed *)
Lemma nth_error_cat1 (A : Type) (l1 l2 : seq A) (n : nat) :
  n < size l1 -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
elim: l1 n => [|x l1 IH] [|n] //= Hn.
exact: IH.
Qed.

Lemma nth_error_cat2 (A : Type) (l1 l2 : seq A) (n : nat) :
  nth_error (l1 ++ l2) (size l1 + n) = nth_error l2 n.
Proof.
by elim: l1 => [|x l1 IH] //=.
Qed.

Lemma nth_error_cat_size (A : Type) (l1 l2 : seq A) :
  nth_error (l1 ++ l2) (size l1) = nth_error l2 0.
Proof.
rewrite (_ : size l1 = size l1 + 0); last by rewrite addn0.
by rewrite nth_error_cat2.
Qed.

Lemma nth_error_size (A : Type) (l : seq A) (n : nat) (x : A) :
  nth_error l n = Some x -> n < size l.
Proof.
elim: n l => [|n IH] [|y l] //= Hn.
exact: IH Hn.
Qed.

Lemma nth_error_lt (A : Type) (l : seq A) (n : nat) :
  n < size l -> exists x, nth_error l n = Some x.
Proof.
elim: n l => [|n IH] [|y l] //= Hn; first by exists y.
exact: IH.
Qed.

(* lbl_ok transport into a concatenation *)
Lemma lbl_at_cat1 (c1 c2 : seq (Transitional.instr * mem_tag))
    (m : nat) (l : label) :
  m < size c1 -> lbl_at (c1 ++ c2) m l = lbl_at c1 m l.
Proof.
move=> Hm. by rewrite /lbl_at (nth_error_cat1 c2 Hm).
Qed.

Lemma lbl_at_cat2 (c1 c2 : seq (Transitional.instr * mem_tag))
    (m : nat) (l : label) :
  lbl_at (c1 ++ c2) (size c1 + m) l = lbl_at c2 m l.
Proof.
by rewrite /lbl_at nth_error_cat2.
Qed.

Lemma lbl_ok_catl (c1 c2 : seq (Transitional.instr * mem_tag))
    (M1 M2 : seq sv) (l : label) (p : sv -> bool) :
  size M1 = size c1 ->
  lbl_ok c1 M1 l p -> lbl_ok (c1 ++ c2) (M1 ++ M2) l p.
Proof.
move=> Hsz /hasP [m Hm /andP [Hl Hw]].
move: Hm. rewrite mem_iota /= add0n => Hm.
apply/hasP. exists m.
- rewrite mem_iota /= add0n size_cat.
  by apply: (leq_trans Hm); exact: leq_addr.
- rewrite (lbl_at_cat1 c2 l Hm) Hl /=.
  case EM: (nth_error M1 m) Hw => [w|] // Hw.
  have Hmw : m < size M1 := nth_error_size EM.
  by rewrite (nth_error_cat1 M2 Hmw) EM.
Qed.

Lemma lbl_ok_catr (c1 c2 : seq (Transitional.instr * mem_tag))
    (M1 M2 : seq sv) (l : label) (p : sv -> bool) :
  size M1 = size c1 ->
  lbl_ok c2 M2 l p -> lbl_ok (c1 ++ c2) (M1 ++ M2) l p.
Proof.
move=> Hsz /hasP [m Hm Hpred].
apply/hasP. exists (size c1 + m).
- rewrite mem_iota /= add0n size_cat ltn_add2l.
  by move: Hm; rewrite mem_iota /= add0n.
- move: Hpred => /andP [Hl Hw].
  rewrite lbl_at_cat2 Hl /=.
  rewrite (_ : size c1 + m = size M1 + m); last by rewrite Hsz.
  rewrite nth_error_cat2.
  exact: Hw.
Qed.

(* the composition lemma *)
Lemma frag_cat (c1 c2 : seq (Transitional.instr * mem_tag))
    (M1 M2 : seq sv) (L : label -> option sv) (v0 v1 v2 : sv) :
  frag c1 M1 L v0 v1 -> frag c2 M2 L v1 v2 ->
  frag (c1 ++ c2) (M1 ++ M2) L v0 v2.
Proof.
case/and3P => /eqP Hs1 Hh1 /allP Ha1.
case/and3P => /eqP Hs2 Hh2 /allP Ha2.
rewrite /frag !size_cat Hs1 Hs2 eqxx /=.
apply/andP; split.
-  case: M1 Hh1 Hs1 Ha1 => [|w M1'] Hh1 Hs1 Ha1 /=.
  +    case: M2 Hh2 {Hs2 Ha2} => [|w2 M2'] Hh2 /=.
    * exact: sv_le_trans Hh1 Hh2.
    * exact: sv_le_trans Hh1 Hh2.
  + exact: Hh1.
-  apply/allP => n.
  rewrite mem_iota /= add0n => Hn.
  case Hlt: (n < size c1).
  +    have Hor := Ha1 n.
    rewrite mem_iota /= add0n in Hor.
    have {Hor} Hor := Hor Hlt.
    move: Hor. rewrite /frag_at.
    rewrite (nth_error_cat1 c2 Hlt).
    rewrite (nth_error_cat1 M2 (l1 := M1)) ?Hs1 //.
    case EI: (nth_error c1 n) => [[i tg0]|] //.
    case EM: (nth_error M1 n) => [v|] //.
    case EV: (vstep v i) => [v'|] //.
    case/andP => Hsucc Hside.
    apply/andP; split; last first.
    *      case: i EI EV Hside {Hsucc}
        => [|pl|iv r0|ra rb|op ra rb rc|ra rb|ra rb|ra rb|rb lb|rj
           |lj|plj|] EI EV Hside //=.
      case/orP: Hside => [Hin|Hpr].
      -- by rewrite (lbl_ok_catl c2 M2 Hs1 Hin).
      -- by rewrite Hpr orbT.
    *      case Ht: (terminal i) => //.
      move: Hsucc. rewrite Ht => Hsucc'.
      case Hn1: (n.+1 < size M1).
      -- have [w Ew] := nth_error_lt Hn1.
         have E := @nth_error_cat1 _ M1 M2 n.+1 Hn1.
         move: Hsucc'. rewrite E Ew. by [].
      --         case EW: (nth_error M1 n.+1) Hsucc' => [w|] Hv1.
         ++ by have := nth_error_size EW; rewrite Hn1.
         ++            have En1 : n.+1 = size M1.
            { have Hle : n < size M1 by rewrite Hs1.
              have : n.+1 <= size M1 by [].
              rewrite leq_eqVlt Hn1 orbF => /eqP //. }
            have E : nth_error (M1 ++ M2) n.+1 = nth_error M2 0.
            { rewrite En1 (_ : size M1 = size M1 + 0);
                last by rewrite addn0.
              by rewrite nth_error_cat2. }
            rewrite E.
            case: M2 Hh2 {Hs2 Ha2 E} => [|w2 M2'] Hh2 /=.
            ** exact: sv_le_trans Hv1 Hh2.
            ** exact: sv_le_trans Hv1 Hh2.
  +    have Hge : size c1 <= n by rewrite leqNgt Hlt.
    have En : n = size c1 + (n - size c1) by rewrite subnKC.
    have Hk : n - size c1 < size c2.
    { by rewrite ltn_subLR // addnC. }
    have Hor := Ha2 (n - size c1).
    rewrite mem_iota /= add0n in Hor.
    have {Hor} Hor := Hor Hk.
    have Ec : nth_error (c1 ++ c2) n = nth_error c2 (n - size c1).
    { by rewrite {1}En nth_error_cat2. }
    have Em : nth_error (M1 ++ M2) n = nth_error M2 (n - size c1).
    { rewrite {1}(_ : n = size M1 + (n - size c1));
        last by rewrite Hs1; exact: En.
      by rewrite nth_error_cat2. }
    move: Hor. rewrite /frag_at Ec Em.
    case EI: (nth_error c2 (n - size c1)) => [[i tg0]|] //.
    case EM: (nth_error M2 (n - size c1)) => [v|] //.
    case EV: (vstep v i) => [v'|] //.
    case/andP => Hsucc Hside.
    apply/andP; split; last first.
    * case: i EI EV Hside {Hsucc}
        => [|pl|iv r0|ra rb|op ra rb rc|ra rb|ra rb|ra rb|rb lb|rj
           |lj|plj|] EI EV Hside //=.
      case/orP: Hside => [Hin|Hpr].
      -- by rewrite (lbl_ok_catr Hs1 Hin).
      -- by rewrite Hpr orbT.
    * case Ht: (terminal i) => //.
      move: Hsucc. rewrite Ht => Hsucc'.
      have E := @nth_error_cat2 sv M1 M2 (n - size c1).+1.
      move: Hsucc'. rewrite -E.
      rewrite (_ : size M1 + (n - size c1).+1 = n.+1);
        last by rewrite Hs1 addnS -En.
      by [].
Qed.

Lemma frag_nil (L : label -> option sv) (v : sv) : frag [::] [::] L v v.
Proof. by rewrite /frag /= sv_le_refl. Qed.

(* weakening the exit value *)
Lemma frag_wout (c : seq (Transitional.instr * mem_tag)) (M : seq sv)
    (L : label -> option sv) (vin vout vout' : sv) :
  sv_le vout vout' ->
  frag c M L vin vout -> frag c M L vin vout'.
Proof.
move=> Hle. case/and3P => Hs Hh Ha.
rewrite /frag Hs /=.
apply/andP; split.
- move: Hh. case: (M) => [|w M'] Hh //.
  exact: sv_le_trans Hh Hle.
- apply/allP => n Hn.
  have := allP Ha n Hn.
  rewrite /frag_at.
  case: (nth_error c n) => [[i tg]|] //.
  case: (nth_error M n) => [v|] //.
  case: (vstep v i) => [v'|] //.
  case/andP => H1 H2.
  apply/andP; split=> //.
  case Ht: (terminal i) H1 => //.
  case: (nth_error M n.+1) => [w|] // Hv'.
  exact: sv_le_trans Hv' Hle.
Qed.

Lemma lbl_ok_impl (c : seq (Transitional.instr * mem_tag))
    (M : seq sv) (l : label) (p q : sv -> bool) :
  (forall w, p w -> q w) -> lbl_ok c M l p -> lbl_ok c M l q.
Proof.
move=> Hpq /hasP [m Hm /andP [Hl Hw]].
apply/hasP. exists m => //.
rewrite Hl /=.
case: (nth_error M m) Hw => [w|] // Hw.
exact: Hpq.
Qed.

(* trade promises for actual in-fragment labels *)
Lemma frag_promise (c : seq (Transitional.instr * mem_tag))
    (M : seq sv) (L L' : label -> option sv) (vin vout : sv) :
  (forall l w, L l = Some w ->
     L' l = Some w \/ lbl_ok c M l (fun x => sv_eqb x w)) ->
  frag c M L vin vout -> frag c M L' vin vout.
Proof.
move=> HLL. case/and3P => Hs Hh Ha.
rewrite /frag Hs Hh /=.
apply/allP => n Hn.
have := allP Ha n Hn.
rewrite /frag_at.
case: (nth_error c n) => [[i tg]|] //.
case: (nth_error M n) => [v|] //.
case: (vstep v i) => [v'|] //.
case/andP => H1 H2.
rewrite H1 {H1} /=.
case: i H2 => //= r l.
case/orP => [-> //|].
case EL: (L l) => [w|] // Hw.
case: (HLL _ _ EL) => [->|Hint].
- by rewrite Hw orbT.
- have Himp : forall x, sv_eqb x w -> sv_le v x.
  { move=> x /sv_eqbP ->. exact: Hw. }
  by rewrite (lbl_ok_impl Himp Hint).
Qed.

(* ---- the push/pop macro fragments ---- *)

Lemma frag_push (L : label -> option sv) (r : register)
    (tg1 tg2 : mem_tag) (sg : seq class3) (a1 a2 b1 b2 : taint)
    (sc : scst) (k : class3) (ag : bool) :
  sc_eqb sc SCpark = false ->
  t_eqb b1 ASp = false -> t_eqb b2 ASp = false ->
  pushclass (SV PBody sg None a1 a2 sc true true ag) r = Some k ->
  dead_src r (SV PBody sg None a1 a2 sc true true ag)
  = SV PBody sg None b1 b2 sc true true ag ->
  frag [:: (TrStore R_SP r, tg1); (TrBinOp Add R_SP R_ONE R_SP, tg2)]
       [:: SV PBody sg None a1 a2 sc true true ag;
           SV PBody sg (Some k) b1 b2 sc true true ag]
       L (SV PBody sg None a1 a2 sc true true ag)
       (SV PBody (rcons sg k) None b1 b2 sc true true ag).
Proof.
move=> Hnp Hb1 Hb2 Hk Hd.
case: sc Hnp Hk Hd => // _ Hk Hd;
rewrite /frag /= /frag_at /= Hk Hd /= Hb1 Hb2;
by rewrite !sv_le_refl.
Qed.

(* the pop macro, one variant per emitted pop target:
   user pops (R_COM/R_ARG/R_AUX1 at class CU), the RA restore,
   the teardown SP restore, and the wrapper scratch restore *)
Lemma frag_pop_u (L : label -> option sv) (r : register)
    (tg1 tg2 : mem_tag) (sg : seq class3) (a1 a2 : taint) (sc : scst)
    (ag : bool) (w : sv) :
  ~~ is_r r R_SP -> ~~ is_r r R_RA -> ~~ is_r r R_ONE ->
  sc_eqb sc SCpark = false ->
  t_eqb a1 ASp = false -> t_eqb a2 ASp = false ->
  warg_w r (wone r false
    (wtaint r AU (SV PBody sg None a1 a2 sc true true ag))) = w ->
  frag [:: (TrBinOp Minus R_SP R_ONE R_SP, tg1); (TrLoad R_SP r, tg2)]
       [:: SV PBody (rcons sg CU) None a1 a2 sc true true ag;
           SV PBody sg (Some CU) a1 a2 sc true true ag]
       L (SV PBody (rcons sg CU) None a1 a2 sc true true ag) w.
Proof.
move=> Hsp Hra Hone Hnp Ha1 Ha2 Hw.
case: sc Hnp Hw => // _ Hw;
rewrite /frag /= /frag_at /= rev_rcons /= revK Ha1 Ha2;
rewrite (negbTE Hsp) (negbTE Hra) /=;
rewrite Hw;
by rewrite !sv_le_refl.
Qed.

Lemma frag_pop_ra (L : label -> option sv)
    (tg1 tg2 : mem_tag) (sg : seq class3) (a1 a2 : taint) (sc : scst)
    (ag : bool) :
  sc_eqb sc SCpark = false ->
  t_eqb a1 ASp = false -> t_eqb a2 ASp = false ->
  frag [:: (TrBinOp Minus R_SP R_ONE R_SP, tg1); (TrLoad R_SP R_RA, tg2)]
       [:: SV PBody (rcons sg CRa) None a1 a2 sc true true ag;
           SV PBody sg (Some CRa) a1 a2 sc true true ag]
       L (SV PBody (rcons sg CRa) None a1 a2 sc true true ag)
       (SV PBody sg None a1 a2 sc true true ag).
Proof.
move=> Hnp Ha1 Ha2.
case: sc Hnp => // _;
rewrite /frag /= /frag_at /= rev_rcons /= revK Ha1 Ha2;
by rewrite !sv_le_refl.
Qed.

(* the canonical map for a fragment: thread vstep from the entry
   (junk after a rejection — callers only use it where vstep runs) *)
Fixpoint mkmap (v : sv) (c : seq (Transitional.instr * mem_tag))
  : seq sv :=
  match c with
  | [::] => [::]
  | (i, _) :: c' =>
      v :: match vstep v i with
           | Some v' => mkmap v' c'
           | None => mkmap v c'
           end
  end.

(* the translated form of a compiled fragment (the component id only
   picks tags, which the checker ignores) *)
Definition trc (C : Component.id) (c : Machine.code)
  : seq (Transitional.instr * mem_tag) :=
  map (instr_to_transitional C) c.

Lemma trc_cat (C : Component.id) (c1 c2 : Machine.code) :
  trc C (c1 ++ c2) = trc C c1 ++ trc C c2.
Proof. exact: map_cat. Qed.

(* a branch singleton, satisfied by a promise *)
Lemma frag_bnz (L : label -> option sv) (r : register) (l : label)
    (tg : mem_tag) (sg : seq class3) (a1 a2 : taint) (sc : scst)
    (o ag : bool) :
  (match L l with
   | Some w => sv_le (SV PBody sg None a1 a2 sc o true ag) w
   | None => false
   end) ->
  frag [:: (TrBnz r l, tg)] [:: SV PBody sg None a1 a2 sc o true ag] L
       (SV PBody sg None a1 a2 sc o true ag)
       (SV PBody sg None a1 a2 sc o true ag).
Proof.
move=> HL.
rewrite /frag /= /frag_at /= !sv_le_refl /=.
by rewrite HL.
Qed.

(* a plain-label singleton *)
Lemma frag_lbl (L : label -> option sv) (l : label) (tg : mem_tag)
    (v : sv) :
  frag [:: (TrLabel (inl l), tg)] [:: v] L v v.
Proof.
by rewrite /frag /= /frag_at /= !sv_le_refl.
Qed.

(* the in-place label witness for promise discharge *)
Lemma lbl_ok_here (c1 c2 : seq (Transitional.instr * mem_tag))
    (M1 M2 : seq sv) (l : label) (tg : mem_tag) (v : sv)
    (p : sv -> bool) :
  size M1 = size c1 -> p v ->
  lbl_ok (c1 ++ (TrLabel (inl l), tg) :: c2) (M1 ++ v :: M2) l p.
Proof.
move=> Hsz Hp.
apply/hasP. exists (size c1).
- rewrite mem_iota /= add0n size_cat /=.
  by rewrite -addSnnS leq_addr.
- rewrite /lbl_at.
  rewrite (_ : size c1 = size c1 + 0); last by rewrite addn0.
  rewrite nth_error_cat2 /=.
  rewrite PeanoNat.Nat.eqb_refl /=.
  rewrite (_ : size c1 + 0 = size M1 + 0); last by rewrite Hsz.
  by rewrite nth_error_cat2 /=.
Qed.

(* a procedure-header singleton *)
Lemma frag_hdr (L : label -> option sv)
    (cp : Component.id * Procedure.id) (tg : mem_tag) :
  frag [:: (TrLabel (inr cp), tg)] [:: sv0] L sv0 sv0.
Proof.
by [].
Qed.

(* ================================================================== *)
(* From a whole-component fragment to the component check.            *)
(* ================================================================== *)

(* the component's last instruction is terminal (compiled procedures
   end with a jump) *)
Definition ends_term (S : seq (Transitional.instr * mem_tag)) : bool :=
  match rev S with
  | (i, _) :: _ => terminal i
  | [::] => true
  end.

Lemma comp_ok_of_frag (S : seq (Transitional.instr * mem_tag))
    (M : seq sv) :
  frag S M (fun _ => None) sv0 sv0 ->
  ends_term S ->
  (forall n l tg, nth_error S n = Some (TrJalNat l, tg) ->
     lbl_ok S M l (fun w => sv_eqb w sv0_one)) ->
  comp_ok S M.
Proof.
case/and3P => Hs Hh Ha Hterm Hjal.
rewrite /comp_ok Hs /=.
apply/allP => n Hn.
have := allP Ha n Hn.
move: Hn. rewrite mem_iota /= add0n => Hn.
rewrite /frag_at /vc_at.
case EI: (nth_error S n) => [[i tg]|] //.
case EM: (nth_error M n) => [v|] //.
case EV: (vstep v i) => [v'|] //.
case/andP => Hsucc Hside.
apply/andP; split.
-  case Ht: (terminal i) => //.
  move: Hsucc. rewrite Ht.
  case EW: (nth_error M n.+1) => [w|] // _.  exfalso.
  have En1 : n.+1 = size M.
  { have Hlt : n < size M.
    { rewrite (eqP Hs). exact: nth_error_size EI. }
    have Hge : size M <= n.+1.
    { case Hc: (size M <= n.+1) => //.
      move/negbT: Hc. rewrite -ltnNge => Hc.
      have [x Ex] := nth_error_lt Hc.
      by rewrite Ex in EW. }
    by apply/eqP; rewrite eqn_leq Hlt Hge. }
  move: Hterm. rewrite /ends_term.
  have En1' : n.+1 = size S by rewrite En1 (eqP Hs).
  have ES : rev S = (i, tg) :: rev (take n S).
  { have Hsz : n < size S by rewrite -En1'.
    have Hd : size (drop n S) = 1.
    { by rewrite size_drop -En1' subSnn. }
    have ED0 : nth_error (drop n S) 0 = Some (i, tg).
    { rewrite -(nth_error_cat_size (take n S) (drop n S))
              cat_take_drop size_take Hsz.
      exact: EI. }
    have ED : drop n S = [:: (i, tg)].
    { by case: (drop n S) Hd ED0 => [|x [|y d]] //= _ [->]. }
    by rewrite -{1}(cat_take_drop n S) ED rev_cat /=. }
  by rewrite ES Ht.
-  case: i EI EV Hside {Hsucc}
    => [|pl|iv r0|ra rb|op ra rb rc|ra rb|ra rb|ra rb|rb lb|rj
       |lj|plj|] EI EV Hside //=.
  +    by move: Hside; rewrite orbF.
  +    exact: Hjal EI.
Qed.

(* terminality composes *)
Lemma ends_term_cat (c1 c2 : seq (Transitional.instr * mem_tag)) :
  ends_term c1 -> ends_term c2 -> ends_term (c1 ++ c2).
Proof.
rewrite /ends_term rev_cat.
by case: (rev c2) => [|x r] //=.
Qed.

Lemma ends_term_flatten
    (pieces : seq (seq (Transitional.instr * mem_tag))) :
  (forall pc, List.In pc pieces -> ends_term pc) ->
  ends_term (flatten pieces).
Proof.
elim: pieces => [|pc pieces IH] Hall //=.
apply: ends_term_cat.
- exact: Hall pc (or_introl (erefl _)).
- exact: IH (fun q Hq => Hall q (or_intror Hq)).
Qed.

(* a nonempty terminal tail decides the cat *)
Lemma ends_term_catr (c1 c2 : seq (Transitional.instr * mem_tag)) :
  c2 <> [::] -> ends_term c2 -> ends_term (c1 ++ c2).
Proof.
rewrite /ends_term rev_cat.
by case: c2 => [|y c2] //= _; rewrite rev_cons;
   case: (rev c2) => [|z r] //=.
Qed.

(* a nonempty terminal-ended tail absorbs a prepended header *)
Lemma ends_term_cons (x : Transitional.instr * mem_tag)
    (c : seq (Transitional.instr * mem_tag)) :
  c <> [::] -> ends_term c -> ends_term (x :: c).
Proof.
rewrite /ends_term rev_cons.
case: c => [|y c] //= _.
rewrite rev_cons.
by case: (rev c) => [|z r] //=.
Qed.

Lemma comp_ok_at (S : seq (Transitional.instr * mem_tag)) (M : seq sv)
    (n : nat) (i : Transitional.instr) (tg : mem_tag) :
  comp_ok S M ->
  nth_error S n = Some (i, tg) ->
  vc_at S M n.
Proof.
case/andP => _ /allP Hall Hn.
apply: Hall.
rewrite mem_iota /= add0n.
have : n < size S.
{ elim: n S Hn => [|n IH] [|x s] //= Hn.
  exact: IH Hn. }
by [].
Qed.

(* the per-position facts in usable form *)
Lemma vc_at_inv (S : seq (Transitional.instr * mem_tag)) (M : seq sv)
    (n : nat) (i : Transitional.instr) (tg : mem_tag) :
  comp_ok S M ->
  nth_error S n = Some (i, tg) ->
  exists v v',
    [/\ nth_error M n = Some v,
        vstep v i = Some v'
      & ~~ terminal i ->
        exists w, nth_error M n.+1 = Some w /\ sv_le v' w].
Proof.
move=> Hok Hn.
have := comp_ok_at Hok Hn.
rewrite /vc_at Hn.
case EM: (nth_error M n) => [v|] //.
case EV: (vstep v i) => [v'|] //.
case/andP => Hsucc _.
exists v, v'. split=> // Hnt.
move: Hsucc. rewrite (negbTE Hnt).
case EW: (nth_error M n.+1) => [w|] //= Hw.
by exists w.
Qed.

End WithScr.

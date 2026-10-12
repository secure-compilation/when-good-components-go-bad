(* LinearizeMerged: the ON-BUILD MP-program generator
     [Transitional.intermediate_to_transitional] + [Merged.transitional_to_merged_gen]
   (with the canonical label scheme of LabelScheme.v) produces RECOMPOSITION-READY programs:
   its output satisfies [lin_output_wf] (Recomposition/Definitions.v), Merged-side
   [well_formed_program], and the label-disjointness / cross-side-call facts of
   [LinearizerFacts] — all under Intermediate-level well-formedness premises.

   This file verifies STATIC well-formedness of the generator's output; it does NOT prove a
   semantic Intermediate↔MP simulation (out of scope).

   Structure:
     1. findopt helpers (existence/None/nth characterizations)
     2. provenance toolkit: cells of the merged output ↔ cells of the transitional map
        ↔ (entry cell | translated Intermediate instruction) of some (component, procedure)
     3. instr_translation / instr_to_transitional shape inversions
     4. the [compiler] constructor + the emission theorems *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Maps.
Require Import Common.Linking.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import Coq.micromega.Lia.
Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ------------------------------------------------------------------ *)
(* 1. findopt helpers ([Merged.findopt] is a RIGHT fold: it reports the
      LAST matching index — suffix-priority, cf. RecInit's findopt_cat). *)
(* ------------------------------------------------------------------ *)

Lemma findopt_In_ex {A : Type} (pred : A -> bool) (l : seq A) x :
  List.In x l -> pred x = true -> exists m, findopt pred l = Some m.
Proof.
  rewrite /findopt.
  elim: l => [|a s IH] //= HIn Hp.
  case E: (foldr _ None s) => [n|].
  - by exists (n + 1).
  - case: HIn => [Ha|HIn].
    + subst a. rewrite Hp. by exists 0.
    + have [m Hm] := IH HIn Hp. by rewrite Hm in E.
Qed.

Lemma findopt_None_notIn {A : Type} (pred : A -> bool) (l : seq A) :
  findopt pred l = None -> forall x, List.In x l -> pred x = false.
Proof.
  move=> HN x HIn.
  case E: (pred x) => //.
  have [m Hm] := findopt_In_ex HIn E.
  by rewrite Hm in HN.
Qed.

Lemma findopt_nth {A : Type} (pred : A -> bool) (l : seq A) m :
  findopt pred l = Some m ->
  exists x, nth_error l m = Some x /\ pred x = true.
Proof.
  rewrite /findopt.
  elim: l m => [|a s IH] m //=.
  case E: (foldr _ None s) => [n|].
  - move=> [Hm]. subst m.
    have [x [Hx Hpx]] := IH n E.
    exists x. split=> //.
    have -> : n + 1 = S n by lia.
    exact: Hx.
  - case Ep: (pred a) => //.
    move=> [Hm]. subst m.
    by exists a.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Provenance toolkit                                                *)
(* ------------------------------------------------------------------ *)

(* List.In through flatten-of-map. *)
Lemma In_flatten_map {A B : Type} (f : A -> seq B) (l : seq A) (x : B) :
  List.In x (flatten (map f l)) <-> exists y, List.In y l /\ List.In x (f y).
Proof.
  elim: l => [|a s IH] /=.
  - split=> [[]|[y [[] _]]] //.
  - split.
    + move/List.in_app_iff => [Hx|Hx].
      * by exists a; split; [left|].
      * have [y [Hy Hfy]] := proj1 IH Hx. by exists y; split; [right|].
    + move=> [y [[Ha|Hy] Hfy]].
      * subst y. apply/List.in_app_iff. by left.
      * apply/List.in_app_iff. right. apply/(proj2 IH). by exists y.
Qed.

(* seq membership -> List.In (converse of BufferLayout's List_In_mem). *)
Lemma mem_List_In {T : eqType} (l : seq T) x :
  x \in l -> List.In x l.
Proof.
  elim: l => [|a s IH] //=.
  rewrite inE => /orP [/eqP ->|Hx]; [by left | by right; exact: IH].
Qed.

(* Assoc-list view of an fmap: [Maps.elementsm] is the underlying [fmval], so membership
   is exactly [getm] (BufferLayout's getm_In / In_fmap_getm on the seq coercion). *)
Lemma In_elementsm {A : Type} (m : NMap A) k v :
  List.In (k, v) (Maps.elementsm m) <-> m k = Some v.
Proof.
  split; [exact: In_fmap_getm | exact: getm_In].
Qed.

(* Merged cells of the generalized flattening <-> transitional cells + translation. *)
Lemma t2m_gen_In (make : proc_label -> nat) (upd : Component.id -> nat -> nat)
      (pb : NMap {fmap Block.id -> nat + seq value}) (cde : Transitional.code) i t :
  List.In (i, t) (transitional_to_merged_gen (mt := mt) make upd pb cde) <->
  exists itr, List.In (itr, t) (flatten (map snd (Maps.elementsm cde)))
         /\ List.In i (instr_translation make (upd (color t)) (memory_lengths pb) itr).
Proof.
  rewrite /transitional_to_merged_gen.
  elim: (flatten (map snd (Maps.elementsm cde))) => [|[itr' t'] s IH] /=.
  - split=> [[]|[itr [[] _]]] //.
  - split.
    + move/List.in_app_iff => [Hx|Hx].
      * move/List.in_map_iff: Hx => [i0 [Hpair HIn0]].
        case: Hpair => Hi Ht; subst i0 t'.
        exists itr'. split; [by left | exact: HIn0].
      * have [itr [HInc HInt]] := proj1 IH Hx.
        exists itr. split; [by right | exact: HInt].
    + move=> [itr [[Hhd|HIn] HInt]].
      * case: Hhd => -> ->.
        apply/List.in_app_iff. left.
        apply/List.in_map_iff. by exists i.
      * apply/List.in_app_iff. right.
        apply/(proj2 IH). by exists itr.
Qed.

(* getm through [compile_component_list].  Generalized over the joint
   interface [PI] the entry tags are computed against (plan-t2me.md §3.8);
   the whole-program forms are the [PI := prog_interface pr] instances. *)
Lemma ccl_getm_def (PI : Program.interface) (pr : Intermediate.program)
      (l : seq (Component.id * NMap Machine.code)) cid :
  getm_def (compile_component_list_gen PI pr l) cid
  = omap (fun=> linearize_component_gen PI pr cid) (getm_def l cid).
Proof.
  elim: l => [|[c0 t0] s IH] //=.
  case E: (cid == c0) => //=.
  by move/eqP: E => ->.
Qed.

Lemma i2t_getm (PI : Program.interface) (pr : Intermediate.program) cid :
  intermediate_to_transitional_gen PI pr cid
  = omap (fun=> linearize_component_gen PI pr cid) (Intermediate.prog_procedures pr cid).
Proof.
  by rewrite /intermediate_to_transitional_gen mkfmapE ccl_getm_def.
Qed.

(* Cells of a linearized component <-> cells of some procedure's linearization. *)
Lemma lin_comp_In (PI : Program.interface) (pr : Intermediate.program) cid cell :
  List.In cell (linearize_component_gen PI pr cid) <->
  exists Cprocs Pid,
    Intermediate.prog_procedures pr cid = Some Cprocs
    /\ Pid \in domm Cprocs
    /\ List.In cell (linearize_proc_gen PI pr cid Pid).
Proof.
  rewrite /linearize_component_gen.
  case E: (Intermediate.prog_procedures pr cid) => [Cprocs|] /=.
  - rewrite In_flatten_map. split.
    + move=> [Pid [HPin Hcell]].
      exists Cprocs, Pid. split=> //. split=> //.
      apply/List_In_mem. exact: HPin.
    + move=> [Cprocs' [Pid [HCp [HPd Hcell]]]].
      case: HCp => Heq; subst Cprocs'.
      exists Pid. split=> //.
      exact: mem_List_In HPd.
  - split=> [HIn | [Cprocs [Pid [HCp _]]]].
    + by case: HIn.
    + by case: HCp.
Qed.

(* The procedure body used by [linearize_proc]. *)
Definition proc_code (pr : Intermediate.program) (cid : Component.id) (Pid : Procedure.id)
  : Machine.code :=
  Option.default [::] (do map <- getm (Intermediate.prog_procedures pr) cid;
                       getm map Pid).

(* Cells of a linearized procedure: the entry-label cell, or a translated body instruction. *)
Lemma lin_proc_In (PI : Program.interface) (pr : Intermediate.program) cid Pid cell :
  List.In cell (linearize_proc_gen PI pr cid Pid) <->
  cell = (TrLabel (inr (cid, Pid)), head_tag_gen PI cid Pid)
  \/ exists mi, List.In mi (proc_code pr cid Pid) /\ cell = instr_to_transitional cid mi.
Proof.
  rewrite /linearize_proc_gen -/(proc_code pr cid Pid) /=.
  split.
  - move=> [Hhd|HIn].
    + by left; rewrite Hhd.
    + right.
      move/List.in_map_iff: HIn => [mi [Hmi HInmi]].
      by exists mi; split; last by rewrite Hmi.
  - move=> [Hhd|[mi [HInmi Hcell]]].
    + by left; rewrite Hhd.
    + right. apply/List.in_map_iff. by exists mi; split; last by [].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Shape inversions                                                  *)
(* ------------------------------------------------------------------ *)

(* Every translated Intermediate instruction carries the plain code tag. *)
Lemma i2t_snd (cid : Component.id) (mi : Machine.instr) :
  (instr_to_transitional cid mi).2 = def_mem_tag cid true.
Proof.
  case: mi => //=.
  move=> c' P'. by case: (Nat.eqb cid c').
Qed.

Lemma color_head_tag (PI : Program.interface) cid Pid :
  color (head_tag_gen PI cid Pid) = cid.
Proof. by []. Qed.

Lemma color_def_mem_tag (cid : Component.id) b :
  color (def_mem_tag cid b) = cid.
Proof. by []. Qed.

(* [MrLabel] sources: a body label (updated) or a procedure-entry label (made). *)
Lemma it_label_inv (make : proc_label -> nat) (upd : nat -> nat)
      (msz : NMap (NMap nat)) (itr : Transitional.instr) m :
  List.In (@MrLabel Int32.mt m) (instr_translation make upd msz itr) ->
  (exists l, itr = TrLabel (inl l) /\ m = upd l)
  \/ (exists pl, itr = TrLabel (inr pl) /\ m = make pl).
Proof.
  case: itr => /=.
  - by move=> [E|[]].
  - move=> lbl.
    case: lbl => [l|pl].
    + move=> [E|[]]. case: E => <-. left. by exists l.
    + move=> [E|[]]. case: E => <-. right. by exists pl.
  - by move=> iv r [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> b r1 r2 r3 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> rptr rsize [E|[E|[E|[E|[E|[]]]]]].
  - by move=> r l [E|[]].
  - by move=> r [E|[]].
  - by move=> l [E|[]].
  - by move=> pl [E|[]].
  - by move=> [E|[]].
Qed.

(* [MrJal] sources: the allocator stub, a body-label jal, or a procedure call. *)
Lemma it_jal_inv (make : proc_label -> nat) (upd : nat -> nat)
      (msz : NMap (NMap nat)) (itr : Transitional.instr) l :
  List.In (@MrJal Int32.mt l) (instr_translation make upd msz itr) ->
  (l = alloc_label /\ exists r1 r2, itr = TrAlloc r1 r2)
  \/ (exists l0, itr = TrJalNat l0 /\ l = upd l0)
  \/ (exists pl, itr = TrJalProc pl /\ l = make pl).
Proof.
  case: itr => /=.
  - by move=> [E|[]].
  - move=> lbl. case: lbl => [l0|pl]; by move=> [E|[]].
  - by move=> iv r [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> b r1 r2 r3 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> r1 r2 [E|[]].
  - move=> rptr rsize [E|[E|[E|[E|[E|[]]]]]]; try discriminate.
    case: E => <-. left. split=> //. by exists rptr, rsize.
  - by move=> r l0 [E|[]].
  - by move=> r [E|[]].
  - move=> l0 [E|[]]. case: E => <-. right; left. by exists l0.
  - move=> pl [E|[]]. case: E => <-. right; right. by exists pl.
  - by move=> [E|[]].
Qed.

(* [MrBnz] sources: exactly a translated [TrBnz] with an updated body label. *)
Lemma it_bnz_inv (make : proc_label -> nat) (upd : nat -> nat)
      (msz : NMap (NMap nat)) (itr : Transitional.instr) r l :
  List.In (@MrBnz Int32.mt r l) (instr_translation make upd msz itr) ->
  exists l0, itr = TrBnz r l0 /\ l = upd l0.
Proof.
  case: itr => /=.
  - by move=> [E|[]].
  - move=> lbl. case: lbl => [l0|pl]; by move=> [E|[]].
  - by move=> iv r0 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> b r1 r2 r3 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> r1 r2 [E|[]].
  - by move=> rptr rsize [E|[E|[E|[E|[E|[]]]]]].
  - move=> r0 l0 [E|[]]. case: E => <- <-. by exists l0.
  - by move=> r0 [E|[]].
  - by move=> l0 [E|[]].
  - by move=> pl [E|[]].
  - by move=> [E|[]].
Qed.

(* Which Machine instruction produced a given transitional shape. *)
Lemma m2t_label_inl (cid : Component.id) (mi : Machine.instr) l :
  (instr_to_transitional cid mi).1 = TrLabel (inl l) -> mi = ILabel l.
Proof.
  case: mi => //=.
  - by move=> l0 [->].
  - move=> c' P'. by case: (Nat.eqb cid c').
Qed.

Lemma m2t_label_inr (cid : Component.id) (mi : Machine.instr) pl :
  (instr_to_transitional cid mi).1 = TrLabel (inr pl) -> False.
Proof.
  case: mi => //=.
  move=> c' P'. by case: (Nat.eqb cid c').
Qed.

Lemma m2t_bnz (cid : Component.id) (mi : Machine.instr) r l :
  (instr_to_transitional cid mi).1 = TrBnz r l -> mi = IBnz r l.
Proof.
  case: mi => //=.
  - by move=> r0 l0 [-> ->].
  - move=> c' P'. by case: (Nat.eqb cid c').
Qed.

Lemma m2t_jalnat (cid : Component.id) (mi : Machine.instr) l :
  (instr_to_transitional cid mi).1 = TrJalNat l -> mi = IJal l.
Proof.
  case: mi => //=.
  - by move=> l0 [->].
  - move=> c' P'. by case: (Nat.eqb cid c').
Qed.

Lemma m2t_jalproc (cid : Component.id) (mi : Machine.instr) pl :
  (instr_to_transitional cid mi).1 = TrJalProc pl -> mi = ICall pl.1 pl.2.
Proof.
  case: mi => //=.
  move=> c' P'. case: (Nat.eqb cid c') => -[<-] //.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Master provenance for the generator output                        *)
(* ------------------------------------------------------------------ *)

Section Generator.

Variable pr : Intermediate.program.
Variable make : proc_label -> nat.
Variable upd : Component.id -> nat -> nat.

(* The CANONICAL JOINT BUFFER MAP (T2M audit, plan-t2me.md §3.7, 2026-08-08).
   [transitional_to_merged_gen]'s buffer argument is used ONLY for
   [memory_lengths] — the (component, block) ↦ flat-base map baked into
   [IConst (IPtr …)] immediates.  Passing the side's OWN buffers here made
   every baked pointer immediate wrong under LINKING whenever component ids
   interleave across the link: the linked machine's [initial_memory] lays
   data out by the JOINT union layout.  Exactly like the canonical label
   scheme ([make]/[upd] replacing the side-local legacy numbering),
   separately-compiled sides must agree on the joint memory map [PB]
   (⊇ the side's own buffers; only block SHAPES matter to
   [memory_lengths]). *)
Variable PB : NMap {fmap Block.id -> nat + seq value}.

(* the canonical JOINT INTERFACE the entry tags are computed against
   (plan-t2me.md §3.8) — same medicine as [PB] and the label scheme *)
Variable PI : Program.interface.

Let msz := memory_lengths PB.

Definition compiler_gen : @Merged.code Int32.mt :=
  transitional_to_merged_gen make upd PB (intermediate_to_transitional_gen PI pr).

(* Every merged cell comes from a declared procedure of the tag's colour: either its
   ENTRY cell (head_tag) or a TRANSLATED body instruction (def_mem_tag). *)
Lemma compiler_gen_cell_inv i t :
  List.In (i, t) compiler_gen ->
  exists Cprocs Pid,
    Intermediate.prog_procedures pr (color t) = Some Cprocs
    /\ Pid \in domm Cprocs
    /\ ( (t = head_tag_gen PI (color t) Pid
          /\ List.In i (instr_translation make (upd (color t)) msz
                          (TrLabel (inr (color t, Pid)))))
       \/ (exists mi Pcode,
             Cprocs Pid = Some Pcode /\ List.In mi Pcode
             /\ t = def_mem_tag (color t) true
             /\ List.In i (instr_translation make (upd (color t)) msz
                             (instr_to_transitional (color t) mi).1)) ).
Proof.
  rewrite /compiler_gen t2m_gen_In => -[itr [Hflat HInt]].
  move: Hflat.
  rewrite In_flatten_map => -[[cid cl] [Helem /= HIncl]].
  move/In_elementsm: Helem.
  rewrite i2t_getm.
  case Eproc: (Intermediate.prog_procedures pr cid) => [Cprocs|] //= [Hcl].
  subst cl.
  move/lin_comp_In: HIncl => [Cprocs' [Pid [HCp' [HPd Hcell]]]].
  rewrite Eproc in HCp'. case: HCp' => ?; subst Cprocs'.
  move/lin_proc_In: Hcell => [Hhd | [mi [HInmi Hcell]]].
  - (* entry cell *)
    case: Hhd => Hitr Ht.
    have Hcol : color t = cid by rewrite Ht.
    exists Cprocs, Pid.
    rewrite Hcol Eproc. split=> //. split=> //.
    left. split; first exact: Ht.
    rewrite Hitr /= in HInt. exact: HInt.
  - (* body cell *)
    have Ht : t = def_mem_tag cid true.
    { by rewrite -(i2t_snd cid mi) -Hcell. }
    have Hcol : color t = cid by rewrite Ht.
    have Hitr : itr = (instr_to_transitional cid mi).1.
    { by rewrite -Hcell. }
    move: HInmi. rewrite /proc_code Eproc /=.
    case Epc: (Cprocs Pid) => [Pcode|] //= HInmi.
    exists Cprocs, Pid.
    rewrite Hcol Eproc. split=> //. split=> //.
    right. exists mi, Pcode. split=> //. split=> //.
    split; first by rewrite Ht.
    rewrite Hcol in HInt. rewrite -Hitr. exact: HInt.
Qed.

(* Construction: any cell of a declared procedure's linearization, translated, is in. *)
Lemma compiler_gen_cell_intro cid Pid itr t i :
  Intermediate.prog_procedures pr cid <> None ->
  Pid \in domm (odflt emptym (Intermediate.prog_procedures pr cid)) ->
  List.In (itr, t) (linearize_proc_gen PI pr cid Pid) ->
  List.In i (instr_translation make (upd (color t)) msz itr) ->
  List.In (i, t) compiler_gen.
Proof.
  move=> Hne HPd Hcell HInt.
  rewrite /compiler_gen t2m_gen_In.
  exists itr. split=> //.
  rewrite In_flatten_map.
  case Eproc: (Intermediate.prog_procedures pr cid) => [Cprocs|]; last by [].
  exists (cid, linearize_component_gen PI pr cid). split=> /=.
  - apply/In_elementsm. by rewrite i2t_getm Eproc.
  - apply/lin_comp_In. exists Cprocs, Pid. split=> //. split=> //.
    by move: HPd; rewrite Eproc.
Qed.

End Generator.

(* ------------------------------------------------------------------ *)
(* 5. More findopt / rcons plumbing                                     *)
(* ------------------------------------------------------------------ *)

Lemma findopt_notIn_None {A : Type} (pred : A -> bool) (l : seq A) :
  (forall x, List.In x l -> pred x = false) -> findopt pred l = None.
Proof.
  rewrite /findopt. elim: l => [|a s IH] //= Hall.
  rewrite IH; last by move=> x Hx; apply: Hall; right.
  by rewrite Hall; last by left.
Qed.

Lemma findopt_rcons {A : Type} (pred : A -> bool) (s : seq A) (x : A) :
  findopt pred (rcons s x) = if pred x then Some (size s) else findopt pred s.
Proof.
  rewrite /findopt. elim: s => [|a s IH] /=.
  - by case: (pred x).
  - rewrite IH. case: (pred x) => //=. by rewrite addn1.
Qed.

Lemma In_rcons {A : Type} (s : seq A) (x y : A) :
  List.In y (rcons s x) <-> List.In y s \/ y = x.
Proof.
  rewrite -cats1. split.
  - by move/List.in_app_iff => [H|[H|[]]]; [left | right].
  - by move=> [H|H]; apply/List.in_app_iff; [left | right; left].
Qed.

Lemma List_In_last {A : Type} (cell : A) (rest : seq A) :
  List.In (last cell rest) (cell :: rest).
Proof.
  elim: rest cell => [|a s IH] cell /=; first by left.
  by right; apply: IH.
Qed.

Lemma nth_error_rcons_size {A : Type} (s : seq A) (x : A) :
  List.nth_error (rcons s x) (size s) = Some x.
Proof. by elim: s => [|a s IH] //=. Qed.

Lemma app_cat {A : Type} (s1 s2 : seq A) : List.app s1 s2 = s1 ++ s2.
Proof. by elim: s1 => [|a s1 IH] //=; rewrite IH. Qed.

Lemma In_has {A : Type} (pe : A -> bool) (l : seq A) x :
  List.In x l -> pe x -> has pe l.
Proof.
  elim: l => [|a s IH] //= [->|HIn] Hp; first by rewrite Hp.
  by rewrite IH // orbT.
Qed.

Lemma In_map_mem {A : Type} {B : eqType} (f : A -> B) (s : seq A) x :
  List.In x s -> f x \in map f s.
Proof.
  elim: s => [|a s IH] //= [->|HIn]; first by rewrite inE eqxx.
  by rewrite inE IH // orbT.
Qed.

Lemma mem_map_In {A : Type} {B : eqType} (f : A -> B) (s : seq A) y :
  y \in map f s -> exists x, List.In x s /\ y = f x.
Proof.
  elim: s => [|a s IH] //=.
  rewrite inE => /orP [/eqP ->|/IH [x [HIn ->]]].
  - by exists a; split; first by left.
  - by exists x; split; first by right.
Qed.

Lemma In_unzip1_mem {K : eqType} {V : Type} (s : seq (K * V)) k v :
  List.In (k, v) s -> k \in unzip1 s.
Proof.
  elim: s => [|[k' v'] s IH] //= [[-> _]|HIn]; first by rewrite inE eqxx.
  by rewrite inE IH // orbT.
Qed.

Lemma sumn_map_eq0 {A : Type} (g : A -> nat) (s : seq A) :
  (forall x, List.In x s -> g x = 0) -> sumn [seq g x | x <- s] = 0.
Proof.
  elim: s => [|a s IH] //= Hz.
  rewrite Hz; last by left.
  rewrite IH //. by move=> x Hx; apply: Hz; right.
Qed.

(* Sum over an assoc list with uniq keys, where only key [c0] may contribute (and
   then at most 1): total is at most 1. *)
Lemma sumn_le1_uniq_keys {K : eqType} {V : Type} (g : V -> nat) (s : seq (K * V)) (c0 : K) :
  uniq (unzip1 s) ->
  (forall k v, List.In (k, v) s -> g v <= if k == c0 then 1 else 0) ->
  sumn [seq g x.2 | x <- s] <= 1.
Proof.
  elim: s => [|[k v] s IH] //= /andP [Hk Hu] Hb.
  case Ek: (k == c0).
  - move/eqP: Ek => Ek. subst k.
    have Hz : sumn [seq g x.2 | x <- s] = 0.
    { apply: sumn_map_eq0 => -[k' v'] HIn /=.
      have Hle := Hb k' v' (or_intror HIn).
      case Ek': (k' == c0) Hle => Hle; last by lia.
      move/eqP: Ek' => ?; subst k'.
      by rewrite (In_unzip1_mem HIn) in Hk. }
    rewrite Hz addn0.
    have := Hb c0 v (or_introl erefl). by rewrite eqxx.
  - have Hle := Hb k v (or_introl erefl). rewrite Ek in Hle.
    have Hg0 : g v = 0 by lia.
    rewrite Hg0 add0n. apply: IH => // k' v' HIn. by apply: Hb; right.
Qed.

(* Positional uniqueness from a count bound. *)
Lemma count_le1_nth_unique {A : Type} (pe : A -> bool) (l : seq A) :
  count pe l <= 1 ->
  forall n m x y,
    List.nth_error l n = Some x -> pe x ->
    List.nth_error l m = Some y -> pe y ->
    n = m.
Proof.
  elim: l => [|a s IH] Hc n m x y; first by case: n.
  case: n => [|n]; case: m => [|m] //=.
  - move=> [Ex] Hpx Hy Hpy. exfalso. subst a.
    have Hhas := In_has (List.nth_error_In _ _ Hy) Hpy.
    rewrite has_count in Hhas.
    move: Hc => /=. rewrite Hpx /=. by lia.
  - move=> Hx Hpx [Ey] Hpy. exfalso. subst a.
    have Hhas := In_has (List.nth_error_In _ _ Hx) Hpx.
    rewrite has_count in Hhas.
    move: Hc => /=. rewrite Hpy /=. by lia.
  - move=> Hx Hpx Hy Hpy.
    have Hc' : count pe s <= 1 by move: Hc => /=; lia.
    by rewrite (IH Hc' _ _ _ _ Hx Hpx Hy Hpy).
Qed.

Lemma elementsm_keys_uniq {A : Type} (m : NMap A) :
  uniq (unzip1 (Maps.elementsm m)).
Proof. exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP m)). Qed.

(* Counting a tag-level predicate through one translated transitional cell. *)
Lemma count_map_tag (pe_t : mem_tag -> bool) (t : mem_tag)
      (li : seq (@Merged.instr Int32.mt)) :
  count (fun cell : Merged.instr * mem_tag => pe_t cell.2) [seq (i0, t) | i0 <- li]
  = if pe_t t then size li else 0.
Proof.
  elim: li => [|i0 li IH] /=; first by case: (pe_t t).
  rewrite IH. by case: (pe_t t).
Qed.

(* Counting through the generalized flattening: bounded by the transitional count,
   provided matching cells translate to at most one instruction. *)
Lemma t2m_count_le (pe_t : mem_tag -> bool) (make : proc_label -> nat)
      (upd : Component.id -> nat -> nat)
      (pb : NMap {fmap Block.id -> nat + seq value}) (cde : Transitional.code) :
  (forall itr t, List.In (itr, t) (flatten (map snd (Maps.elementsm cde))) -> pe_t t ->
     size (instr_translation (mt := mt) make (upd (color t)) (memory_lengths pb) itr) <= 1) ->
  count (fun cell : Merged.instr * mem_tag => pe_t cell.2)
        (transitional_to_merged_gen (mt := mt) make upd pb cde)
  <= count (fun cell : Transitional.instr * mem_tag => pe_t cell.2)
           (flatten (map snd (Maps.elementsm cde))).
Proof.
  rewrite /transitional_to_merged_gen.
  elim: (flatten (map snd (Maps.elementsm cde))) => [|[itr t] s IH] //= Hprem.
  rewrite app_cat count_cat count_map_tag.
  case Ep: (pe_t t).
  - apply: leq_add.
    + exact: (Hprem _ _ (or_introl erefl) Ep).
    + apply: IH => itr' t' HIn' Hp'. exact: (Hprem _ _ (or_intror HIn') Hp').
  - apply: IH => itr' t' HIn' Hp'. exact: (Hprem _ _ (or_intror HIn') Hp').
Qed.

(* The entry-cell predicate: colour c, entry tag exactly e. *)
Definition entry_predt (c : Component.id) (e : Procedure.id * seq Component.id)
           (t : mem_tag) : bool :=
  (color t == c) && (entry t == Some e).

(* ------------------------------------------------------------------ *)
(* 6. The linearized side: canonical labels + trailing Halt             *)
(* ------------------------------------------------------------------ *)

Section LinSide.

(* Strict bounds of the canonical label scheme (instantiated by the wrapper as
   maxima+1 over the program quadruple). *)
Variables L P C : nat.

Definition can_make (pl : proc_label) : nat := mk_entry L P C pl.1 pl.2.
Definition can_upd (cid : Component.id) (l : nat) : nat := mk_body L cid l.

(* the canonical joint buffer map and joint interface
   (see Section Generator's [PB]/[PI]) *)
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Variable pr : Intermediate.program.
Hypothesis Hwf : Intermediate.well_formed_program pr.

Definition compiler_body : @Merged.code Int32.mt :=
  compiler_gen pr can_make can_upd PB PI.

(* Trailing Halt (the recomposition wf requires last-is-Halt), coloured like the
   last body cell so [low_colors] extends. *)
Definition compiler_code : @Merged.code Int32.mt :=
  match compiler_body with
  | [::] => [::]
  | cell :: rest => rcons compiler_body (MrHalt, def_mem_tag (color (last cell rest).2) true)
  end.

Definition compiler : program :=
  {| prog_interface := Intermediate.prog_interface pr;
     code := compiler_code;
     prog_buffers := Intermediate.prog_buffers pr;
     prog_main := Component.main \in domm (Intermediate.prog_interface pr) |}.

(* ---- body-cell facts ---- *)

Lemma compiler_body_tags i t :
  List.In (i, t) compiler_body -> is_code t = true /\ vtag t = Other.
Proof.
  move/compiler_gen_cell_inv => [Cprocs [Pid [_ [_ [[Ht _]|[mi [Pcode [_ [_ [Ht _]]]]]]]]]].
  - by rewrite Ht.
  - by rewrite Ht.
Qed.

Lemma compiler_body_colors i t :
  List.In (i, t) compiler_body -> color t \in domm (Intermediate.prog_interface pr).
Proof.
  move/compiler_gen_cell_inv => [Cprocs [Pid [Hproc _]]].
  rewrite (Intermediate.wfprog_defined_procedures Hwf).
  by apply/dommP; exists Cprocs.
Qed.

(* Every label of the body is canonical: a body label or an entry label. *)
Lemma compiler_body_label_canonical l t :
  List.In (@MrLabel Int32.mt l, t) compiler_body ->
  (exists cid l0, l = mk_body L cid l0) \/ (exists cid p0, l = mk_entry L P C cid p0).
Proof.
  move/compiler_gen_cell_inv => [Cprocs [Pid [_ [_ [[Ht HIn]|[mi [Pcode [_ [_ [Ht HIn]]]]]]]]]].
  - move: HIn => /= [E|[]].
    case: E => E. right. exists (color t), Pid. by rewrite -E.
  - move/it_label_inv: HIn => [[l0 [_ ->]]|[pl [_ ->]]].
    + left. by exists (color t), l0.
    + right. by exists pl.1, pl.2.
Qed.

(* ---- compiler_code cell characterization ---- *)

Lemma compiler_code_In i t :
  List.In (i, t) compiler_code ->
  List.In (i, t) compiler_body
  \/ exists cell rest, compiler_body = cell :: rest
       /\ (i, t) = (@MrHalt Int32.mt, def_mem_tag (color (last cell rest).2) true).
Proof.
  rewrite /compiler_code.
  case E: compiler_body => [|cell rest]; first by move=> [].
  move/In_rcons => [HIn|Heq].
  - left. exact: HIn.
  - right. exists cell, rest. by split.
Qed.

(* ---- the easy lin_output_wf fields ---- *)

Lemma lin_low_tags : forall i t,
  List.In (i, t) compiler_code -> is_code t = true /\ vtag t = Other.
Proof.
  move=> i t /compiler_code_In [HIn|[cell [rest [_ Heq]]]].
  - exact: compiler_body_tags HIn.
  - by case: Heq => _ ->.
Qed.

Lemma lin_low_colors : forall i t,
  List.In (i, t) compiler_code -> color t \in domm (Intermediate.prog_interface pr).
Proof.
  move=> i t /compiler_code_In [HIn|[cell [rest [E Heq]]]].
  - exact: compiler_body_colors HIn.
  - case: Heq => _ ->.
    have HInl : List.In (last cell rest) compiler_body by rewrite E; exact: List_In_last.
    case Ecell: (last cell rest) HInl => [il tl] HInl.
    exact: (compiler_body_colors HInl).
Qed.

Lemma lin_low_no_alloc : findopt (is_label_def alloc_label) compiler_code = None.
Proof.
  apply: findopt_notIn_None => -[i t] HIn.
  rewrite /is_label_def /=.
  case: i HIn => // l0 HIn.
  apply: negbTE. apply/negP => /eqP E. subst l0.
  case/compiler_code_In: HIn => [HIn|[cell [rest [_ Heq]]]]; last by case: Heq.
  case/compiler_body_label_canonical: HIn => [[cid [lb Hl]]|[cid [p0 Hl]]].
  - exact: mk_body_neq_alloc (esym Hl).
  - exact: mk_entry_neq_alloc (esym Hl).
Qed.

(* ---- body-to-code transport + construction ---- *)

Lemma compiler_body_sub i t : List.In (i, t) compiler_body -> List.In (i, t) compiler_code.
Proof.
  move=> HIn. rewrite /compiler_code.
  case E: compiler_body => [|cell rest]; first by rewrite E in HIn.
  apply/In_rcons. left. by rewrite -E.
Qed.

(* Any translated body instruction of a declared procedure is a compiler_body cell. *)
Lemma compiler_body_intro cid Cprocs Pid Pcode mi i :
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Cprocs Pid = Some Pcode ->
  List.In mi Pcode ->
  List.In i (instr_translation can_make (can_upd cid)
               (memory_lengths PB)
               (instr_to_transitional cid mi).1) ->
  List.In (i, def_mem_tag cid true) compiler_body.
Proof.
  move=> Hproc Epc HmiIn HInt.
  apply: (compiler_gen_cell_intro (cid := cid) (Pid := Pid)
            (itr := (instr_to_transitional cid mi).1)).
  - by rewrite Hproc.
  - rewrite Hproc /=. apply/dommP. by exists Pcode.
  - apply/lin_proc_In. right. exists mi. split.
    + by rewrite /proc_code Hproc /= Epc.
    + by rewrite -(i2t_snd cid mi) -surjective_pairing.
  - exact: HInt.
Qed.

(* A body label of a declared procedure is DEFINED in compiler_code (canonical form). *)
Lemma lin_label_defined cid Cprocs Pid Pcode l0 :
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Cprocs Pid = Some Pcode ->
  List.In (ILabel l0) Pcode ->
  exists m, findopt (is_label_def (can_upd cid l0)) compiler_code = Some m.
Proof.
  move=> Hproc Epc HlIn.
  have HInb : List.In (@MrLabel Int32.mt (can_upd cid l0), def_mem_tag cid true) compiler_body.
  { apply: compiler_body_intro Hproc Epc HlIn _. by rewrite /=; left. }
  have HInc := compiler_body_sub HInb.
  apply: (findopt_In_ex HInc).
  by rewrite /is_label_def /= eqxx.
Qed.

(* ---- low_bnz_resolved ---- *)

Lemma lin_low_bnz_resolved : forall n r l t,
  List.nth_error compiler_code n = Some (@MrBnz Int32.mt r l, t) ->
  exists m, findopt (is_label_def l) compiler_code = Some m.
Proof.
  move=> n r l t Hnth.
  have HIn : List.In (MrBnz r l, t) compiler_code := List.nth_error_In _ _ Hnth.
  case/compiler_code_In: HIn => [HIn|[cell [rest [_ Heq]]]]; last by case: Heq.
  case/compiler_gen_cell_inv: HIn
    => [Cprocs [Pid [Hproc [HPd [[_ HInt]|[mi [Pcode [Epc [Hmi [Ht HInt]]]]]]]]]].
  - by move: HInt => /= [E|[]].
  - case/it_bnz_inv: HInt => l0 [Hitr Hl].
    have ? : mi = IBnz r l0 := m2t_bnz Hitr. subst mi.
    have Hwfi := Intermediate.wfprog_well_formed_instructions Hwf Hproc Epc Hmi.
    case: Hwfi => Cprocs' [Pcode' [Hproc' [Epc' HlIn]]].
    subst l.
    exact: lin_label_defined Hproc' Epc' HlIn.
Qed.

Lemma lin_low_last_halt :
  compiler_code = [::]
  \/ exists t, List.nth_error compiler_code (size compiler_code - 1) = Some (@MrHalt Int32.mt, t).
Proof.
  rewrite /compiler_code.
  case E: compiler_body => [|cell rest]; first by left.
  right. exists (def_mem_tag (color (last cell rest).2) true).
  by rewrite size_rcons subn1 /= nth_error_rcons_size.
Qed.

(* ---- entry determinism ---- *)

(* Every entry-carrying cell IS the interface-determined head tag of its (colour, proc). *)
Lemma lin_entry_head i t e :
  List.In (i, t) compiler_code -> entry t = Some e ->
  t = head_tag_gen PI (color t) e.1.
Proof.
  move=> /compiler_code_In [HIn|[cell [rest [_ Heq]]]]; last first.
  { by case: Heq => _ ->. }
  case/compiler_gen_cell_inv: HIn
    => [Cprocs [Pid [Hproc [HPd [[Ht _]|[mi [Pcode [_ [_ [Ht _]]]]]]]]]]; last first.
  { by rewrite Ht. }
  move=> He. move: (He). rewrite Ht /= => -[He'].
  by rewrite Ht -He'.
Qed.

Lemma lin_low_entry_det : forall i1 t1 i2 t2 e1 e2,
  List.In (i1, t1) compiler_code -> List.In (i2, t2) compiler_code ->
  color t1 = color t2 -> entry t1 = Some e1 -> entry t2 = Some e2 -> e1.1 = e2.1 ->
  t1 = t2.
Proof.
  move=> i1 t1 i2 t2 e1 e2 HIn1 HIn2 Hcol He1 He2 Hp.
  rewrite (lin_entry_head HIn1 He1) (lin_entry_head HIn2 He2).
  by rewrite Hcol Hp.
Qed.

(* ---- entry-cell construction ---- *)

Lemma lin_entry_In cid Cprocs Pid :
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Pid \in domm Cprocs ->
  List.In (@MrLabel Int32.mt (can_make (cid, Pid)), head_tag_gen PI cid Pid) compiler_body.
Proof.
  move=> Hproc HPd.
  apply: (compiler_gen_cell_intro (cid := cid) (Pid := Pid)
            (itr := TrLabel (inr (cid, Pid)))).
  - by rewrite Hproc.
  - by rewrite Hproc /=.
  - apply/lin_proc_In. by left.
  - by rewrite /=; left.
Qed.

(* ---- entry-cell counting: at most one cell per (colour, entry tag) ---- *)

Lemma lin_proc_count (pe_t : mem_tag -> bool) c p :
  pe_t (def_mem_tag c true) = false ->
  count (fun cell : Transitional.instr * mem_tag => pe_t cell.2) (linearize_proc_gen PI pr c p)
  = pe_t (head_tag_gen PI c p).
Proof.
  move=> Hdef.
  rewrite /linearize_proc /=.
  set cd := Option.default [::] _.
  suff -> : count (fun cell : Transitional.instr * mem_tag => pe_t cell.2)
                  [seq instr_to_transitional c i0 | i0 <- cd] = 0 by rewrite addn0.
  elim: cd => [|mi cd IH] //=.
  by rewrite i2t_snd Hdef IH.
Qed.

Lemma lin_procs_count c0 c e (procs : seq Procedure.id) :
  uniq procs ->
  sumn [seq count (fun cell : Transitional.instr * mem_tag => entry_predt c0 e cell.2)
              (linearize_proc_gen PI pr c q) | q <- procs]
  <= if c == c0 then 1 else 0.
Proof.
  move=> Hu.
  have Hf : forall q,
      count (fun cell : Transitional.instr * mem_tag => entry_predt c0 e cell.2)
            (linearize_proc_gen PI pr c q)
      = nat_of_bool (entry_predt c0 e (head_tag_gen PI c q)).
  { move=> q. by rewrite lin_proc_count // /entry_predt /= andbF. }
  rewrite (eq_map Hf).
  have Hsc : forall (T : Type) (b : T -> bool) (s : seq T),
      sumn [seq nat_of_bool (b x) | x <- s] = count b s.
  { move=> T b; elim=> [|a s IH] //=. by rewrite IH. }
  rewrite Hsc.
  case Ec: (c == c0).
  - apply: leq_trans (_ : count (pred1 e.1) procs <= 1); last first.
    { by rewrite count_uniq_mem //; case: (e.1 \in procs). }
    apply: sub_count => q /andP [_ /eqP He].
    case: He => He'.
    by rewrite /= -He' /= eqxx.
  - rewrite leqn0. apply/eqP.
    rewrite (eq_count (a2 := pred0)) ?count_pred0 //.
    move=> q /=. rewrite /entry_predt.
    have -> : color (head_tag_gen PI c q) = c by [].
    by rewrite Ec.
Qed.

Lemma lin_comp_count c0 c e :
  count (fun cell : Transitional.instr * mem_tag => entry_predt c0 e cell.2)
        (linearize_component_gen PI pr c)
  <= if c == c0 then 1 else 0.
Proof.
  rewrite /linearize_component count_flatten -map_comp.
  apply: lin_procs_count.
  case: (do map <- Intermediate.prog_procedures pr c; Some (domm map))
    => [procs'|] /=; last by [].
  exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP procs')).
Qed.

Lemma compiler_body_entry_count c0 e :
  count (fun cell : Merged.instr * mem_tag => entry_predt c0 e cell.2) compiler_body <= 1.
Proof.
  have Hsz : forall itr t,
      List.In (itr, t) (flatten (map snd (Maps.elementsm (intermediate_to_transitional_gen PI pr)))) ->
      entry_predt c0 e t ->
      size (instr_translation (mt := mt) can_make (can_upd (color t))
              (memory_lengths PB) itr) <= 1.
  { move=> itr t HIn Hpe.
    move: HIn Hpe. rewrite In_flatten_map => -[[cid cl] [Helem /= HIncl]] Hpe.
    move/In_elementsm: Helem. rewrite i2t_getm.
    case Eproc: (Intermediate.prog_procedures pr cid) => [Cprocs|] //= [Hcl]. subst cl.
    case/lin_comp_In: HIncl => Cprocs' [Pid [_ [_ Hcell]]].
    case/lin_proc_In: Hcell => [Hhd|[mi [_ Hcell]]].
    - by case: Hhd => -> _.
    - exfalso.
      have Ht : t = def_mem_tag cid true.
      { by rewrite -(i2t_snd cid mi) -Hcell. }
      move: Hpe. rewrite Ht /entry_predt /= andbF. by []. }
  apply: (leq_trans (t2m_count_le Hsz)).
  rewrite count_flatten -map_comp.
  apply: (sumn_le1_uniq_keys (c0 := c0)) => [|k v HIn].
  - exact: elementsm_keys_uniq.
  - move/In_elementsm: HIn. rewrite i2t_getm.
    case Eproc: (Intermediate.prog_procedures pr k) => [Cprocs|] //= [Hv]. subst v.
    exact: lin_comp_count.
Qed.

Lemma compiler_code_entry_count c0 e :
  count (fun cell : Merged.instr * mem_tag => entry_predt c0 e cell.2) compiler_code <= 1.
Proof.
  rewrite /compiler_code.
  case E: compiler_body => [|cell rest] //.
  rewrite -cats1 count_cat.
  have Hh : forall ct : Component.id,
      count (fun cell0 : Merged.instr * mem_tag => entry_predt c0 e cell0.2)
            [:: (@MrHalt Int32.mt, def_mem_tag ct true)] = 0.
  { move=> ct. by rewrite /= /entry_predt andbF. }
  rewrite Hh addn0 -E.
  exact: compiler_body_entry_count.
Qed.

Lemma lin_low_unique_entry : unique_entry_points compiler_code.
Proof.
  move=> c e n m i i' t t' Hc Hc' He He' Hn Hm.
  apply: (count_le1_nth_unique (compiler_code_entry_count c e) Hn _ Hm _).
  - by rewrite /entry_predt /= Hc He !eqxx.
  - by rewrite /entry_predt /= Hc' He' !eqxx.
Qed.

(* ---- Merged-side well-formedness of compiler ---- *)

Hypothesis Hprocs_nonempty : forall cid Cprocs,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  exists Pid, Pid \in domm Cprocs.

Hypothesis Hbuffers_wf : forall C0,
  Intermediate.prog_interface pr C0 ->
  has_required_local_buffers compiler C0.

Lemma lin_get_procedures :
  domm (Intermediate.prog_interface pr) = get_procedures compiler.
Proof.
  apply/eq_fset => c. rewrite /get_procedures in_fset.
  apply/idP/idP.
  - move=> Hc.
    have Hcp : c \in domm (Intermediate.prog_procedures pr)
      by rewrite -(Intermediate.wfprog_defined_procedures Hwf).
    case/dommP: Hcp => Cprocs Hproc.
    have [Pid HPd] := Hprocs_nonempty Hproc.
    have HIn := compiler_body_sub (lin_entry_In Hproc HPd).
    exact: (In_map_mem (fun '(_, tag) => color tag) HIn).
  - move/mem_map_In => [[i0 t0] [HIn ->]].
    exact: lin_low_colors HIn.
Qed.

Lemma lin_find_procedure C0 P0 :
  exported_procedure (Intermediate.prog_interface pr) C0 P0 ->
  find_procedure compiler C0 P0.
Proof.
  case=> CI [HCI Hexp].
  have [Cprocs [Pcode [Hproc Epc]]]
    := Intermediate.wfprog_exported_procedures_existence Hwf HCI Hexp.
  have HPd : P0 \in domm Cprocs by apply/dommP; exists Pcode.
  have HIn := compiler_body_sub (lin_entry_In Hproc HPd).
  rewrite /find_procedure.
  apply/List.Exists_exists.
  exists (MrLabel (can_make (C0, P0)), head_tag_gen PI C0 P0).
  split; first exact: HIn.
  by split.
Qed.

(* ---- the two record assemblies ---- *)

Theorem compiler_output_wf : lin_output_wf compiler.
Proof.
  constructor.
  - exact: lin_low_tags.
  - exact: lin_low_colors.
  - exact: lin_low_bnz_resolved.
  - exact: lin_low_no_alloc.
  - exact: lin_low_entry_det.
  - exact: lin_low_last_halt.
Qed.

Theorem compiler_wf : well_formed_program compiler.
Proof.
  constructor.
  - exact: (Intermediate.wfprog_interface_soundness Hwf).
  - exact: lin_get_procedures.
  - exact: lin_find_procedure.
  - exact: lin_low_unique_entry.
  - exact: (Intermediate.wfprog_defined_buffers Hwf).
  - exact: Hbuffers_wf.
  - by [].
Qed.

(* ---- canonical label shapes (with bounds), for cross-program facts ---- *)

Hypothesis HboundL : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis HboundP : forall cid Cprocs Pid,
  Intermediate.prog_procedures pr cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
Hypothesis HboundC : forall cid,
  cid \in domm (Intermediate.prog_interface pr) -> cid < C.

(* Every label cell of compiler_code carries a canonical label of a DECLARED component:
   a (bounded) body label, or a (bounded) entry label with the head tag. *)
Lemma lin_label_cases l t :
  List.In (@MrLabel Int32.mt l, t) compiler_code ->
  (exists cid l0,
      [/\ cid \in domm (Intermediate.prog_interface pr), cid < C, l0 < L
        & l = mk_body L cid l0])
  \/ (exists cid p0,
      [/\ cid \in domm (Intermediate.prog_interface pr), cid < C, p0 < P,
          l = mk_entry L P C cid p0 & t = head_tag_gen PI cid p0]).
Proof.
  move=> /compiler_code_In [HIn|[cell [rest [_ Heq]]]]; last by case: Heq.
  case/compiler_gen_cell_inv: HIn
    => [Cprocs [Pid [Hproc [HPd [[Ht HInt]|[mi [Pcode [Epc [Hmi [Ht HInt]]]]]]]]]].
  - (* entry cell *)
    move: HInt => /= [E|[]].
    case: E => E.
    have Hdom : color t \in domm (Intermediate.prog_interface pr).
    { rewrite (Intermediate.wfprog_defined_procedures Hwf). by apply/dommP; exists Cprocs. }
    right. exists (color t), Pid.
    split.
    + exact: Hdom.
    + exact: HboundC Hdom.
    + exact: HboundP Hproc HPd.
    + by rewrite -E.
    + exact: Ht.
  - (* body cell *)
    move/it_label_inv: HInt => [[l0 [Hitr ->]]|[pl [Hitr _]]]; last first.
    { by case: (m2t_label_inr Hitr). }
    have ? : mi = ILabel l0 := m2t_label_inl Hitr. subst mi.
    have Hdom : color t \in domm (Intermediate.prog_interface pr).
    { rewrite (Intermediate.wfprog_defined_procedures Hwf). by apply/dommP; exists Cprocs. }
    left. exists (color t), l0.
    split.
    + exact: Hdom.
    + exact: HboundC Hdom.
    + exact: HboundL Hproc Epc Hmi.
    + by [].
Qed.

(* Every JAL of compiler_code: the allocator stub, a locally-resolved body label, or a
   CROSS-COMPONENT call to an imported procedure, carrying its canonical entry label. *)
Lemma lin_jal_cases l t :
  List.In (@MrJal Int32.mt l, t) compiler_code ->
  l = alloc_label
  \/ (exists m, findopt (is_label_def l) compiler_code = Some m)
  \/ (exists C0 P0,
        [/\ l = mk_entry L P C C0 P0,
            imported_procedure (Intermediate.prog_interface pr) (color t) C0 P0
          & color t <> C0]).
Proof.
  move=> /compiler_code_In [HIn|[cell [rest [_ Heq]]]]; last by case: Heq.
  case/compiler_gen_cell_inv: HIn
    => [Cprocs [Pid [Hproc [HPd [[Ht HInt]|[mi [Pcode [Epc [Hmi [Ht HInt]]]]]]]]]].
  - by move: HInt => /= [E|[]].
  - move/it_jal_inv: HInt => [[-> _]|[[l0 [Hitr ->]]|[pl [Hitr ->]]]].
    + by left.
    + have ? : mi = IJal l0 := m2t_jalnat Hitr. subst mi.
      have Hwfi := Intermediate.wfprog_well_formed_instructions Hwf Hproc Epc Hmi.
      case: Hwfi => Cprocs' [P' [P'code [Hproc' [Epc' HlIn]]]].
      right; left.
      exact: lin_label_defined Hproc' Epc' HlIn.
    + have ? : mi = ICall pl.1 pl.2 := m2t_jalproc Hitr. subst mi.
      have Hwfi := Intermediate.wfprog_well_formed_instructions Hwf Hproc Epc Hmi.
      case: Hwfi => Hneq Himp.
      right; right. exists pl.1, pl.2.
      split.
      * by [].
      * exact: Himp.
      * exact: Hneq.
Qed.

End LinSide.

(* [head_tag_gen] no longer depends on the compiled program at all (§3.8:
   both sides share the joint interface), so the cross-variant agreement
   this lemma used to provide is reflexivity; kept by name for callers. *)
Lemma head_tag_iface (PI : Program.interface) (pr1 pr2 : Intermediate.program) c p :
  Intermediate.prog_interface pr1 = Intermediate.prog_interface pr2 ->
  head_tag_gen PI c p = head_tag_gen PI c p.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(* 7. Cross-program facts: label disjointness + foreign-call resolution *)
(* ------------------------------------------------------------------ *)

Section TwoProgs.

Variables L P C : nat.
(* both sides compiled against the SAME canonical joint buffer map and
   joint interface *)
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.
Variables pr1 pr2 : Intermediate.program.
Hypothesis Hwf1 : Intermediate.well_formed_program pr1.
Hypothesis Hwf2 : Intermediate.well_formed_program pr2.
Hypothesis HboundL1 : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pr1 cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis HboundP1 : forall cid Cprocs Pid,
  Intermediate.prog_procedures pr1 cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
Hypothesis HboundC1 : forall cid,
  cid \in domm (Intermediate.prog_interface pr1) -> cid < C.
Hypothesis HboundL2 : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pr2 cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis HboundP2 : forall cid Cprocs Pid,
  Intermediate.prog_procedures pr2 cid = Some Cprocs -> Pid \in domm Cprocs -> Pid < P.
Hypothesis HboundC2 : forall cid,
  cid \in domm (Intermediate.prog_interface pr2) -> cid < C.
Hypothesis Hdis : fdisjoint (domm (Intermediate.prog_interface pr1))
                            (domm (Intermediate.prog_interface pr2)).

(* Labels defined by [pr1]'s linearization are NOT defined by [pr2]'s. *)
Lemma lin_labels_disjoint l :
  findopt (is_label_def l) (compiler_code L P C PB PI pr1) <> None ->
  findopt (is_label_def l) (compiler_code L P C PB PI pr2) = None.
Proof.
  move=> H1.
  case E1: (findopt (is_label_def l) (compiler_code L P C PB PI pr1)) H1 => [m1|]; last by [].
  move=> _.
  have [[i1 t1] [Hnth1 Hp1]] := findopt_nth E1.
  have HIn1 : List.In (i1, t1) (compiler_code L P C PB PI pr1) := List.nth_error_In _ _ Hnth1.
  case: i1 Hnth1 HIn1 Hp1 => // l1 _ HIn1 Hp1.
  move: Hp1. rewrite /is_label_def /= => /eqP El. subst l1.
  apply: findopt_notIn_None => -[i2 t2] HIn2.
  rewrite /is_label_def /=.
  case: i2 HIn2 => // l2 HIn2.
  apply: negbTE. apply/negP => /eqP El2. subst l2.
  case: (lin_label_cases Hwf1 HboundL1 HboundP1 HboundC1 HIn1)
    => [[cid1 [l01 [Hd1 HC1 HL1 Hl1]]]|[cid1 [p01 [Hd1 HC1 HP1 Hl1 _]]]];
  case: (lin_label_cases Hwf2 HboundL2 HboundP2 HboundC2 HIn2)
    => [[cid2 [l02 [Hd2 HC2 HL2 Hl2]]]|[cid2 [p02 [Hd2 HC2 HP2 Hl2 _]]]].
  - have [Ec _] := mk_body_inj HL1 HL2 (etrans (esym Hl1) Hl2).
    move: (fdisjointP Hdis _ Hd1). by rewrite Ec Hd2.
  - exact: (mk_body_entry_disjoint HC1 HL1 (etrans (esym Hl1) Hl2)).
  - exact: (mk_body_entry_disjoint HC2 HL2 (etrans (esym Hl2) Hl1)).
  - have [Ec _] := mk_entry_inj HP1 HP2 (etrans (esym Hl1) Hl2).
    move: (fdisjointP Hdis _ Hd1). by rewrite Ec Hd2.
Qed.

(* A FOREIGN (unresolved, non-alloc) JAL of [pr1]'s code resolves in [pr2]'s code
   at its canonical entry cell — an entry-tagged label cell of [pr2]'s colour. *)
Lemma lin_jal_foreign n l t :
  closed_interface (unionm (Intermediate.prog_interface pr1)
                           (Intermediate.prog_interface pr2)) ->
  List.nth_error (compiler_code L P C PB PI pr1) n = Some (@MrJal Int32.mt l, t) ->
  l <> alloc_label ->
  findopt (is_label_def l) (compiler_code L P C PB PI pr1) = None ->
  exists m C0 P0,
    [/\ findopt (is_label_def l) (compiler_code L P C PB PI pr2) = Some m,
        List.nth_error (compiler_code L P C PB PI pr2) m
          = Some (@MrLabel Int32.mt l, head_tag_gen PI C0 P0),
        l = mk_entry L P C C0 P0,
        C0 \in domm (Intermediate.prog_interface pr2)
      & C0 < C /\ P0 < P].
Proof.
  move=> Hclosed Hnth Halloc Hnone.
  have HIn1 : List.In (MrJal l, t) (compiler_code L P C PB PI pr1) := List.nth_error_In _ _ Hnth.
  case: (lin_jal_cases Hwf1 HIn1) => [Ea|[Hloc|[C0 [P0 [Hl Himp Hneq]]]]].
  - by case: (Halloc Ea).
  - case: Hloc => m Hm. by rewrite Hnone in Hm.
  - (* the callee is not pr1's: it would be locally resolved *)
    have HnotIn1 : C0 \notin domm (Intermediate.prog_interface pr1).
    { apply/negP => HIn0.
      have Hsound := Intermediate.wfprog_interface_soundness Hwf1.
      case/dommP: HIn0 => CI0 HCI0.
      have Hexp : Component.is_exporting CI0 P0 := Hsound _ _ _ Himp _ HCI0.
      have [Cprocs [Pcode [Hproc Epc]]]
        := Intermediate.wfprog_exported_procedures_existence Hwf1 HCI0 Hexp.
      have HPd : P0 \in domm Cprocs by apply/dommP; exists Pcode.
      have HInc : List.In (@MrLabel Int32.mt (can_make L P C (C0, P0)),
                           head_tag_gen PI C0 P0) (compiler_code L P C PB PI pr1)
        := compiler_body_sub (lin_entry_In L P C PB PI Hproc HPd).
      have [m Hm] : exists m, findopt (is_label_def l) (compiler_code L P C PB PI pr1) = Some m.
      { apply: (findopt_In_ex HInc). by rewrite /is_label_def /= Hl eqxx. }
      by rewrite Hnone in Hm. }
    (* closedness: the callee is exported by the union, hence by pr2 *)
    have Himp_u : imported_procedure (unionm (Intermediate.prog_interface pr1)
                                             (Intermediate.prog_interface pr2))
                                     (color t) C0 P0.
    { case: Himp => CI [HCI Him]. exists CI. split=> //.
      by rewrite /Program.has_component unionmE HCI. }
    case: (Hclosed _ _ _ Himp_u) => CIu [HCIu Hexpu].
    have HCI2 : Intermediate.prog_interface pr2 C0 = Some CIu.
    { move: HCIu. rewrite /Program.has_component unionmE.
      case E0: (Intermediate.prog_interface pr1 C0) => [CI0|] //.
      have HIn0 : C0 \in domm (Intermediate.prog_interface pr1)
        by apply/dommP; exists CI0.
      by rewrite HIn0 in HnotIn1. }
    have Hdom2 : C0 \in domm (Intermediate.prog_interface pr2)
      by apply/dommP; exists CIu.
    have [Cprocs2 [Pcode2 [Hproc2 Epc2]]]
      := Intermediate.wfprog_exported_procedures_existence Hwf2 HCI2 Hexpu.
    have HPd2 : P0 \in domm Cprocs2 by apply/dommP; exists Pcode2.
    have HInc2 : List.In (@MrLabel Int32.mt (can_make L P C (C0, P0)),
                          head_tag_gen PI C0 P0) (compiler_code L P C PB PI pr2)
      := compiler_body_sub (lin_entry_In L P C PB PI Hproc2 HPd2).
    have HP0 : P0 < P := HboundP2 Hproc2 HPd2.
    have HC0 : C0 < C := HboundC2 Hdom2.
    have [m Hm] : exists m, findopt (is_label_def l) (compiler_code L P C PB PI pr2) = Some m.
    { apply: (findopt_In_ex HInc2). by rewrite /is_label_def /= Hl eqxx. }
    have [[i2 t2] [Hnth2 Hp2]] := findopt_nth Hm.
    have HIn2 : List.In (i2, t2) (compiler_code L P C PB PI pr2) := List.nth_error_In _ _ Hnth2.
    case: i2 Hnth2 HIn2 Hp2 => // l2 Hnth2 HIn2 Hp2.
    move: Hp2. rewrite /is_label_def /= => /eqP El2. subst l2.
    case: (lin_label_cases Hwf2 HboundL2 HboundP2 HboundC2 HIn2)
      => [[cid2 [l02 [_ HC2 HL2 Hl2]]]|[cid2 [p02 [_ _ HP2 Hl2 Ht2]]]].
    + by case: (mk_body_entry_disjoint HC2 HL2 (etrans (esym Hl2) Hl)).
    + have [Ec Ep] := mk_entry_inj HP2 HP0 (etrans (esym Hl2) Hl).
      subst cid2 p02.
      exists m, C0, P0.
      split.
      * exact: Hm.
      * by rewrite Hnth2 Ht2.
      * exact: Hl.
      * exact: Hdom2.
      * by split.
Qed.

End TwoProgs.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype ssrint.
From mathcomp Require Import zify.
From HB Require Import structures.
From CoqUtils Require Import hseq.
Require Import Coq.micromega.Lia.

Require Import MicroPolicies.Utils MicroPolicies.Types MicroPolicies.Symbolic MicroPolicies.Exec.
Require Import MicroPolicies.WordExtra.
Require Import Common.Definitions CompCert.Events.


(** Tags **)

(* TL TODO: this mechanism of value tag and location tag moy be generalized *)

Inductive value_tag : Type := Ret : nat -> value_tag | Other : value_tag | InternalJump : value_tag | Invalidated : value_tag.

Module Import ValueTagEq.
Definition nat_of_value_tag t :=
  match t with
  | Other => 0
  | InternalJump => 1
  | Invalidated => 2
  | Ret n => S (S (S n))
  end.

Definition value_tag_of_nat t :=
  match t with
  | 0 => Other
  | 1 => InternalJump
  | 2 => Invalidated
  | S (S (S n)) => Ret n
  end.


Lemma nat_of_value_tagK : cancel nat_of_value_tag value_tag_of_nat.
Proof. by case. Qed.

HB.instance Definition _ := Equality.copy value_tag (can_type nat_of_value_tagK).
End ValueTagEq.

Inductive pc_tag : Type := Level : nat  -> Component.id -> pc_tag.

Module Import PCTagEq.
Definition nat_of_pc_tag t :=
  match t with
  | Level n c => (n, c)
  end.

Definition pc_tag_of_nat '(n, c) := Level n c.

Lemma nat_of_pc_tagK : cancel nat_of_pc_tag pc_tag_of_nat.
Proof. by case. Qed.

HB.instance Definition _ := Equality.copy pc_tag (can_type nat_of_pc_tagK).
End PCTagEq.

Record mem_tag : Type := MTag {
  vtag   : value_tag;
  color  : Component.id;
  entry  : option (Procedure.id * list Component.id);
  is_code : bool;
}.


Definition def_mem_tag (c : Component.id) code : mem_tag :=
  {| vtag := Other ;
     color := c ;
     entry := None ;
     is_code := code;
  |}.



Module Export MemTagEq.
Definition tuple_of_mem_tag t := (vtag t, color t, entry t, is_code t).
Definition mem_tag_of_tuple tp :=
  match tp with
  | (vt, c, e, b) => MTag vt c e b
  end.

Lemma tuple_of_mem_tagK : cancel tuple_of_mem_tag mem_tag_of_tuple.
Proof. by case. Qed.

HB.instance Definition _ := Equality.copy mem_tag (can_type tuple_of_mem_tagK).
End MemTagEq.

Import Symbolic.

Definition lrc_tags := {|
  pc_tag_type    := pc_tag;
  reg_tag_type   := value_tag;
  mem_tag_type   := mem_tag;
  entry_tag_type := unit;
|}.


(** Tag propagation rules **)

Import DoNotation.


Definition belong (c : Component.id) (m : option (tag_type lrc_tags M)) : bool :=
  match m with
  | Some {| color := c'  |} => c == c'
  | None => true (* accepting ni = None, assuming it implies monitor service or stopping the machine *)
  end.

Definition check_belong (c : Component.id) (m : option (tag_type lrc_tags M)) : option unit :=
  match belong c m with
    | true => Some tt
    | false => None
  end.


Definition check_ret (n : nat) (r : tag_type lrc_tags R) : option unit :=
  match r with
    | Ret n' => if n == S n' then Some tt else None
    | _ => None
  end.

Definition check_entry (c : Component.id) (m : option (tag_type lrc_tags M)) : option unit :=
  match m with
    | Some {| entry := Some (_, l) |} => if mem_seq l c then Some tt else None
    | Some {| entry := None |} => None
    | None => Some tt (* accepting ni = None, assuming it implies monitor service or stopping the machine *)
  end.

Definition get_tni_color (m : option (tag_type lrc_tags M)) : option Component.id :=
  match m with
  | Some {| color := c' |} => Some c'
  | _ => None
  end.

Definition get_proc_name (m : option (tag_type lrc_tags M)) : option Procedure.id :=
  match m with
  | Some {| entry := Some (p, _) |} => Some p
  | _ => None
  end.

Definition switch_val (m : tag_type lrc_tags M)
           (v : tag_type lrc_tags R) : (tag_type lrc_tags M * tag_type lrc_tags R) :=
  match m with
    | {| vtag := v' ; color := c ; entry := e ; is_code := b |} => ({| vtag := v ; color := c ; entry := e ; is_code := b|}, v')
  end.


(* TL TODO: without this, I get a type error *)
Definition build_tpc (n : nat) c : tag_type lrc_tags P := Level n c.

Definition is_not_invalid (t:value_tag) : option unit :=
  match t with | Invalidated => None  | _ => Some tt end.

(* is not invalid, a jump, or a capability *)
Definition is_other (t:value_tag) : option unit :=
  match t with | Other => Some tt | _ => None end.

Definition is_jump (t:value_tag) : option unit :=
  match t with | InternalJump => Some tt | _ => None end.

(* tags of values that are (potentially) addresses *)
Definition is_address (t:value_tag) : bool :=
  match t with | Ret _ | InternalJump | Invalidated => true | Other => false end.

Definition moved_tag (t : value_tag) : value_tag :=
  match t with
  | Ret _ | Invalidated => Invalidated
  | InternalJump => InternalJump
  | Other => Other
  end.

Lemma moved_tag_not_ret t n : moved_tag t <> Ret n.
Proof. by case: t. Qed.

Fixpoint make_hseq n tag : (hseq (tag_type lrc_tags) (nseq n R))  :=
  match n with
  | O => HSeqNil
  | S m => HSeqCons tag (make_hseq m tag)
  end.

Definition reg_invalidate_hseq : (hseq (tag_type lrc_tags) (nseq 10 R)) :=
  make_hseq 10 Invalidated.

(* TL TODO: comments? cf org file *)
Definition instr_rules (evi : ev_inputs) (op : opcode)
           (tpc : tag_type lrc_tags P)
           (ti : tag_type lrc_tags M)
           (ts : hseq (tag_type lrc_tags) (inputs op))
           (tni : option (tag_type lrc_tags M)) : option (ovec lrc_tags op * option event) :=
  let current := match ti with {| color := c |} => c end in
  let (level, current') := match tpc with Level n c'=> (n, c') end in
  do! _ <- (if (current == current') then Some tt else None);
  match op, ts return option (ovec _ op * option event) with
  | NOP,     [hseq]            => do! _ <- check_belong current tni;
                                     Some (OVec NOP       tpc [hseq], None)

  | CONST,   [hseq td]         => do! _ <- check_belong current tni;
                                     Some (OVec CONST     tpc [hseq Other], None)

  | MOV,     [hseq ts; td]     => (*do! _ <- is_not_invalid ts;*)
                                  do! _ <- check_belong current tni;
                                  let ts' := moved_tag ts in
                                     Some (OVec MOV       tpc [hseq ts'; ts], None)

  | BINOP b, [hseq tx; ty; td] => do! _ <- is_other tx;
                                  do! _ <- is_other ty;
                                  do! _ <- check_belong current tni;
                                     Some (OVec (BINOP b) tpc [hseq tx; ty; Other], None)

  | LOAD,    [hseq tp; ts; td] => do! _ <- is_other tp;
                                  do! _ <- check_belong current tni;
                                     if orb (belong current (Some ts)) (is_code ts) then
                                       let ts' := moved_tag (vtag ts) in
                                       let (ts', td') := switch_val ts ts' in
                                       Some (OVec LOAD tpc [hseq tp; ts'; td'], None)
                                     else
                                       None

  | STORE,   [hseq tp; ts; td] => do! _ <- is_other tp;
                                  do! _ <- check_belong current tni;
                                  do! _ <- check_belong current (Some td);
                                  (* TODO: delete this line to allow editing your own static code *)
                                  if (is_code td) then None else
                                  let ts' := moved_tag ts in
                                     let (td', _) := switch_val td ts in
                                     Some (OVec STORE tpc [hseq tp; ts'; td'], None)

  | BNZ,     [hseq tx]         => do! _ <- is_other tx;
                                  do! _ <- check_belong current tni;
                                     Some (OVec BNZ       tpc [hseq tx], None)

  | JUMP,    (tra :: tp :: trcom :: next)%hseq => if belong current tni then
                                   do! _ <- is_jump tp;
                                   Some (OVec JUMP tpc (tra :: tp :: trcom :: next)%hseq, None)
                                      else
                                   (* TL TODO: should forbid return if level = 0 ?         *)
                                   (*          I think it is already enforced by invariant *)
                                   (*          (unique Ret n)                              *)
                                   do! _ <- is_other trcom;
                                   do! c' <- get_tni_color tni;
                                   let ev := Some (ERet current (rcom_value evi) c') in
                                   do! _ <- check_ret level tp;
                                   Some (OVec JUMP (build_tpc (level.-1) c')
                                           (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq, ev)

  | JAL,     (tnext :: tra :: trcom :: next)%hseq => 
                                   do! _ <- check_belong current (Some tnext);
                                   if belong current tni then
                                   Some (OVec JAL tpc (tnext :: InternalJump :: trcom :: next)%hseq, None)
                                      else
                                   do! _ <- is_other trcom;
                                   do! c' <- get_tni_color tni;
                                   let ev := do! p  <- get_proc_name tni;
                                             Some (ECall current p (rcom_value evi) c') in
                                   do! _ <- check_entry current tni;
                                   Some (OVec JAL (build_tpc (level.+1) c')
                                           (tnext :: (Ret level) :: Other :: reg_invalidate_hseq)%hseq, ev)

  | _,     _                   => None
  end.



Definition transfer (iv : ivec lrc_tags) (evi : ev_inputs) : option (vovec lrc_tags (op iv) * option event) :=
  match iv with (* TL TODO: ask someone obout this dependent boilerplate *)
  | IVec vop tpc ti ts tni =>
    match vop, ts, ti, tni return option (vovec _ vop * option event) with
    | (OP op), ts, ti, tni => instr_rules evi op tpc ti ts tni
    (* Monitor stuff *)
    | SERVICE, [hseq], ti, None => Some (tt, None)
    |       _,      _,  _,    _ => None
    end
  end.



(** Instance **)

Global Instance sym_lrc : params := {
  ttypes := lrc_tags;
  transfer := transfer;
  internal_state := unit
}.



(** Syscalls **)

From CoqUtils Require Import word.

Section WithClasses.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {sregs : syscall_regs mt}
        {NC: nat}. (* smallest natural number n such that number of components < 2^n *)

(* TL TODO: these notations inside a module? *)

Notation state := (@Symbolic.state mt lrc_tags unit).
Notation State := (@Symbolic.State mt lrc_tags unit).

Definition ratom := (atom (mword mt) value_tag).
Definition matom := (atom (mword mt) mem_tag).


(* allows to split memory between components *)
Definition component_memory_prefix (c: int): word (word_size mt) :=
  shlw (as_word c) (as_word (word_size mt - NC)).

(* [1+n < 2^NC] is essential: component_memory_prefix puts [1+n] in the top NC bits, so for
   [1+n = 2^NC] it wraps to [prefix 0] and the inequality is FALSE.  Sound for valid component
   ids (< 2^NC - 1), which is exactly what [colors_bounded] gives. *)
(* [NC <= word_size] is essential: the prefix shift is [word_size - NC] (an INT subtraction in
   [component_memory_prefix], so negative — a huge shift that zeroes everything — when NC > ws). *)
Lemma component_memory_prefix_succ_not_zero:
  forall n,
    NC <= word_size mt ->
    1 + n < expn 2 NC ->
    component_memory_prefix (ssrint.Posz (1 + n)) <> component_memory_prefix (ssrint.Posz 0).
Proof.
move=> n HNC Hn Habs.
have He : expn 2 NC <= expn 2 (word_size mt) by rewrite leq_exp2l.
have Hbase : 1 + n < expn 2 (word_size mt) by apply: leq_trans He.
have Hsub : word_size mt - NC < expn 2 (word_size mt)
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
have Hprod : (1 + n) * expn 2 (word_size mt - NC) < expn 2 (word_size mt).
{ rewrite -{2}(subnK HNC) expnD [X in _ < X]mulnC ltn_mul2r expn_gt0 /=.
  exact: Hn. }
have Hvsh : (val (as_word (Posz (word_size mt - NC)) : word (word_size mt)) : nat) = word_size mt - NC
  by rewrite valw_as_word modn_small.
have Hv1 : (val (component_memory_prefix (ssrint.Posz (1 + n)) : word (word_size mt)) : nat)
           = (1 + n) * expn 2 (word_size mt - NC).
{ rewrite /component_memory_prefix valw_shlw Hvsh valw_as_word
          (modn_small Hbase) (modn_small Hprod) //. }
have Hv0 : (val (component_memory_prefix (ssrint.Posz 0) : word (word_size mt)) : nat) = 0
  by rewrite /component_memory_prefix valw_shlw valw_as_word mod0n mul0n mod0n.
have Hpos : 0 < (1 + n) * expn 2 (word_size mt - NC) by rewrite muln_gt0 expn_gt0 andbT.
have Hve : (val (component_memory_prefix (ssrint.Posz (1 + n)) : word (word_size mt)) : nat)
         = val (component_memory_prefix (ssrint.Posz 0) : word (word_size mt)) by rewrite Habs.
by move: Hpos; rewrite -Hv1 Hve Hv0 ltnn.
Qed.

Lemma component_memory_prefix_zero:
  component_memory_prefix (ssrint.Posz 0) = 0%w.
Proof. rewrite /component_memory_prefix. apply: shlw_zero'. Qed.

(* [component_memory_prefix] puts [c] in the top [NC] bits, so it is injective only on the
   [< 2^NC] range (the valid component ids); unbounded it wraps.  [NC <= word_size] is needed
   so the prefix shift [word_size - NC] is non-degenerate (cf. [_succ_not_zero]). *)
Lemma component_memory_prefix_inj: forall c c',
    NC <= word_size mt ->
    c < expn 2 NC -> c' < expn 2 NC ->
    component_memory_prefix (ssrint.Posz c) = component_memory_prefix (ssrint.Posz c') ->
    c = c'.
Proof.
move=> c c' HNC Hc Hc' Habs.
have Hval : forall m, m < expn 2 NC ->
  (val (component_memory_prefix (ssrint.Posz m) : word (word_size mt)) : nat)
    = m * expn 2 (word_size mt - NC).
{ move=> m Hm.
  have Hsub : word_size mt - NC < expn 2 (word_size mt)
    by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
  have Hmw : m < expn 2 (word_size mt) by apply: (leq_trans Hm); rewrite leq_exp2l.
  have Hprod : m * expn 2 (word_size mt - NC) < expn 2 (word_size mt).
  { rewrite -{2}(subnK HNC) expnD [X in _ < X]mulnC ltn_mul2r expn_gt0 /=. exact: Hm. }
  have Hvsh : (val (as_word (Posz (word_size mt - NC)) : word (word_size mt)) : nat)
            = word_size mt - NC by rewrite valw_as_word modn_small.
  by rewrite /component_memory_prefix valw_shlw Hvsh valw_as_word
             (modn_small Hmw) (modn_small Hprod). }
have Hcc : c * expn 2 (word_size mt - NC) = c' * expn 2 (word_size mt - NC).
{ by rewrite -(Hval c Hc) -(Hval c' Hc') Habs. }
apply/eqP; move: Hcc => /eqP; rewrite eqn_pmul2r // expn_gt0 //.
Qed.

Definition mask: word (word_size mt) :=
  shlw (as_word (2 ^ (word_size mt) - 1))
    (as_word ((word_size mt) - NC)).

(* [n+1 <= 2^(word_size-NC)] (the range fits in one offset field) is essential: with both
   endpoints [x] and [x+(n+1)] in prefix [C] but [n+1] spanning a full offset cycle, the
   intermediate points cross OTHER prefixes and wrap back — the conclusion is then false.
   The allocator now enforces exactly this bound (see [alloc_fun]). *)
Lemma mask_range: forall x n C,
    leq (n + 1) (expn 2 (word_size mt - NC)) ->
    andw x mask = component_memory_prefix C ->
    andw (x + (as_word (ssrint.Posz (n + 1))))%w mask =
      component_memory_prefix C ->
    forall k, k \in iota 0 n ->
         andw (x + (as_word (ssrint.Posz (k + 1))))%w mask =
           component_memory_prefix C.
Proof.
move=> x n C Hsz H1 H2 k Hk.
have HE : 0 < expn 2 (word_size mt - NC) by rewrite expn_gt0.
have HM : 0 < expn 2 (word_size mt) by rewrite expn_gt0.
have HEM : expn 2 (word_size mt - NC) <= expn 2 (word_size mt) by rewrite leq_exp2l // leq_subr.
(* LRC's [_ ^ _] is [Nat.pow] (stdlib), but the word lemmas use ssrnat's [expn]. *)
have NatpowE : forall a b, Nat.pow a b = expn a b.
{ move=> a; elim => [|b IH]; first by rewrite expn0.
  by rewrite expnS /= IH. }
have Hmone : (as_word (2 ^ word_size mt - 1) : word (word_size mt)) = monew.
{ rewrite NatpowE; apply: mone_as_word. }
have Hvsh : (val (as_word (Posz (word_size mt - NC)) : word (word_size mt)) : nat)
          = word_size mt - NC.
{ rewrite valw_as_word modn_small //.
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl. }
have Hmask : forall y : word (word_size mt),
   (val (andw y mask) : nat)
     = (val y %/ expn 2 (word_size mt - NC)) * expn 2 (word_size mt - NC).
{ move=> y. by rewrite /mask Hmone val_andw_shlw_mone Hvsh. }
apply: word_nat_inj; rewrite Hmask.
have Haddw : forall j, (val (x + as_word (Posz j))%w : nat)
                     = (val x + j %% expn 2 (word_size mt)) %% expn 2 (word_size mt)
  by move=> j; rewrite valw_addw valw_as_word.
have E1 : (val x %/ expn 2 (word_size mt - NC)) * expn 2 (word_size mt - NC)
        = (val (component_memory_prefix C) : nat) by rewrite -Hmask H1.
have E2 : ((val (x + as_word (ssrint.Posz (n + 1)))%w) %/ expn 2 (word_size mt - NC))
            * expn 2 (word_size mt - NC)
        = (val (component_memory_prefix C) : nat) by rewrite -Hmask H2.
have Hkn : k < n by move: Hk; rewrite mem_iota add0n; case/andP.
have Hax : (val x : nat) < expn 2 (word_size mt) by apply: ltn_ord.
rewrite -E1; congr (_ * _).
case: (leqP (expn 2 (word_size mt)) (expn 2 (word_size mt - NC))) => [HME | EltM].
- (* degenerate E = M: every value sits in page 0 *)
  have HEMeq : expn 2 (word_size mt - NC) = expn 2 (word_size mt)
    by apply/eqP; rewrite eqn_leq HEM HME.
  rewrite HEMeq (divn_small Hax) divn_small // Haddw; exact: ltn_pmod.
- (* E < M: the block fits in one page and the endpoints share it, so no carry crosses *)
  have HltNC : word_size mt - NC < word_size mt by move: EltM; rewrite ltn_exp2l.
  have H2E : 2 * expn 2 (word_size mt - NC) <= expn 2 (word_size mt)
    by rewrite -expnS leq_exp2l.
  have HnM : n + 1 < expn 2 (word_size mt) by apply: (leq_ltn_trans Hsz).
  have Hk1 : k + 1 <= n + 1 by rewrite leq_add2r ltnW.
  have Hovf : val x + (n + 1) < expn 2 (word_size mt).
  { rewrite ltnNge; apply/negP => Hge.
    have Htop : (val (x + as_word (ssrint.Posz (n + 1)))%w : nat)
              = val x + (n + 1) - expn 2 (word_size mt).
    { rewrite Haddw (modn_small HnM) -{1}(subnK Hge) modnDr modn_small //; lia. }
    have Hq0 : (val (x + as_word (ssrint.Posz (n + 1)))%w) %/ expn 2 (word_size mt - NC) = 0
      by rewrite Htop divn_small //; lia.
    have Ha0 : val x %/ expn 2 (word_size mt - NC) = 0.
    { move: E1; rewrite -E2 Hq0 mul0n => /eqP.
      by rewrite muln_eq0 (negbTE (lt0n_neq0 HE)) orbF => /eqP. }
    have Halt : val x < expn 2 (word_size mt - NC).
    { have H := divn_eq (val x) (expn 2 (word_size mt - NC)).
      rewrite Ha0 mul0n add0n in H.
      by rewrite H; apply: ltn_pmod. }
    lia. }
  have Hnw : forall j, j <= n + 1 -> (val (x + as_word (Posz j))%w : nat) = val x + j.
  { move=> j Hj.
    have Hjm : j < expn 2 (word_size mt) by lia.
    have Hxj : val x + j < expn 2 (word_size mt) by lia.
    by rewrite Haddw (modn_small Hjm) (modn_small Hxj). }
  have HQ : (val x + (n + 1)) %/ expn 2 (word_size mt - NC)
          = val x %/ expn 2 (word_size mt - NC).
  { move: E2; rewrite (Hnw _ (leqnn _)) -E1 => /eqP.
    by rewrite eqn_pmul2r // => /eqP. }
  rewrite (Hnw _ Hk1).
  exact: (divn_between (erefl (val x %/ expn 2 (word_size mt - NC))) HQ Hk1).
Qed.

(* And-ing with [mask] keeps only the top [NC] bits, so a value below the offset window
   [2^(word_size - NC)] is masked to zero.  (Reusable for the [alloc_label] mask facts.) *)
Lemma andw_mask_low (w : word (word_size mt)) :
  (val w : nat) < expn 2 (word_size mt - NC) -> andw w mask = 0%w.
Proof.
move=> Hlt.
have NatpowE : forall a b, Nat.pow a b = expn a b.
{ move=> a; elim => [|b IH]; first by rewrite expn0.
  by rewrite expnS /= IH. }
have Hmone : (as_word (2 ^ word_size mt - 1) : word (word_size mt)) = monew.
{ rewrite NatpowE; apply: mone_as_word. }
have Hvsh : (val (as_word (Posz (word_size mt - NC)) : word (word_size mt)) : nat)
          = word_size mt - NC.
{ rewrite valw_as_word modn_small //.
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl. }
apply: word_nat_inj.
rewrite /mask Hmone val_andw_shlw_mone Hvsh (divn_small Hlt) mul0n.
by rewrite valw_zero'.
Qed.

(* alloc is a syscall taking one argument, the size to allocate *)
(* a syscall don't change the pc level *)
Definition alloc_fun (st : state) : option state :=
  let current_c := (match (taga (pc st)) with Level _ c => c end) in
  do! ra_val <- regs st ra;
  do! _ <- is_jump (taga ra_val);
  let next_pc := (vala ra_val)@(taga (pc st)) in
  do! ret_addr <- mem st (vala ra_val);
  do! _ <- (if is_code (taga ret_addr) && (color (taga ret_addr) == current_c)
            then Some tt else None);
  let prefix := (component_memory_prefix (1 + current_c)) in
  (* let mask := (component_memory_prefix ((2 ^ 32)-1)) in *)
  let prefix_filter := (fun mw => ((word.andw mw mask) == prefix) ) in (* keep only words starting with exactly prefix *)
  (* TL TODO: Rely on the fact that it set implem is a sorted list, kinda fishy *)
  let max_addr := last (filter prefix_filter (domm (mem st))) (prefix) in
  (* create the new bloc *)
  let atom : matom := (word.as_word 0)@(def_mem_tag current_c false) in
  do! size <- regs st syscall_arg1;
  do! _ <- is_other (taga size);
  do! length <- match word.int_of_word (vala size) with
                | Posz x => Some x
                | Negz _ => None
                end;
  (* The block must fit in the component's offset field (the low [word_size - NC] bits):
     [length + 1 <= 2^(word_size - NC)].  Without this an oversized request could wrap the
     offset past the prefix boundary and back, silently corrupting another compartment — and
     [mask_range] (used to prove the block stays in the component's prefix region) would be
     unsound.  Checking it here makes [alloc_fun = Some] *imply* the bound. *)
  do! _ <- (if leq (length + 1) (expn 2 (word_size mt - NC)) then Some tt else None);
  if negb (prefix_filter (word.addw max_addr (word.as_word (length + 1)))) then
    (* check we're not going past the compartment's memory space *)
    None
  else
  let bloc :=
      mkseq (fun n => ((word.addw max_addr (word.as_word (n + 1))), atom))
            length in
  let mem' := unionm (mem st) (mkfmap bloc) in
  (* return *)
  do! addr <- (do! x <- head bloc;
                 Some (fst x));
  do! regs' <- updm (regs st) syscall_ret addr@Other;
  Some (State mem' regs' next_pc tt).

End WithClasses.

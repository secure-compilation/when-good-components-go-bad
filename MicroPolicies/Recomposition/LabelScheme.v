(* Canonical, collision-free nat labels for SEPARATELY-compiled Merged programs.

   [transitional_to_merged]'s legacy scheme computes its label bounds from the code map being
   compiled, so two separately-compiled programs disagree on entry-label values (breaking
   cross-program call resolution) and have boundary collisions.  This kernel provides a
   canonical scheme over SHARED strict bounds [L] (body labels), [P] (procedure ids),
   [C] (component ids) — supplied identically to all four recomposition programs:

     mk_body  c l = 2*(l + L*c) + 1        (ILabel/IBnz/IJal operands of component c)
     mk_entry c p = 2*(L*C + c*P + p) + 1  (procedure-entry labels)

   All values are ODD, hence never [alloc_label = 2^14]; body and entry ranges are disjoint
   (body < 2*L*C+1 <= entry); each family is injective with the defining component recoverable,
   which gives label disjointness across programs with disjoint interfaces. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Merged.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LabelScheme.

Variables L P C : nat.

Definition mk_body (c l : nat) : nat := 2 * (l + L * c) + 1.
Definition mk_entry (c p : nat) : nat := 2 * (L * C + c * P + p) + 1.

Lemma mk_body_odd c l : odd (mk_body c l).
Proof. rewrite /mk_body. by lia. Qed.

Lemma mk_entry_odd c p : odd (mk_entry c p).
Proof. rewrite /mk_entry. by lia. Qed.

Lemma alloc_label_not_odd : odd alloc_label = false.
Proof. rewrite /alloc_label. by rewrite oddX. Qed.

Lemma mk_body_neq_alloc c l : mk_body c l <> alloc_label.
Proof.
move=> E. have H1 := mk_body_odd c l. have H2 := alloc_label_not_odd.
by rewrite E H2 in H1.
Qed.

Lemma mk_entry_neq_alloc c p : mk_entry c p <> alloc_label.
Proof.
move=> E. have H1 := mk_entry_odd c p. have H2 := alloc_label_not_odd.
by rewrite E H2 in H1.
Qed.

(* Injectivity: the body value determines (c, l) — Euclidean division by L. *)
Lemma mk_body_inj c1 l1 c2 l2 :
  l1 < L -> l2 < L -> mk_body c1 l1 = mk_body c2 l2 -> c1 = c2 /\ l1 = l2.
Proof.
rewrite /mk_body => Hl1 Hl2 E.
have E' : c1 * L + l1 = c2 * L + l2 by lia.
have HL : 0 < L by lia.
have Hc : c1 = c2.
{ have := congr1 (fun x => x %/ L) E'.
  by rewrite !divnMDl // !divn_small // !addn0. }
split; [exact Hc | by lia]. 
Qed.

(* Injectivity: the entry value determines (c, p) — Euclidean division by P. *)
Lemma mk_entry_inj c1 p1 c2 p2 :
  p1 < P -> p2 < P -> mk_entry c1 p1 = mk_entry c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
rewrite /mk_entry => Hp1 Hp2 E.
have E' : c1 * P + p1 = c2 * P + p2 by lia.
have HP : 0 < P by lia.
have Hc : c1 = c2.
{ have := congr1 (fun x => x %/ P) E'.
  by rewrite !divnMDl // !divn_small // !addn0. }
split; [exact Hc | by lia].
Qed.

(* Range disjointness: a bounded body label is never an entry label. *)
Lemma mk_body_entry_disjoint c l c' p :
  c < C -> l < L -> mk_body c l <> mk_entry c' p.
Proof.
rewrite /mk_body /mk_entry => Hc Hl E.
have H1 : l + L * c < L * c.+1 by rewrite mulnS; lia.
have H2 : L * c.+1 <= L * C by apply: leq_mul.
have H3 : L * C <= L * C + c' * P + p by rewrite -addnA; apply: leq_addr.
by lia.
Qed.

End LabelScheme.

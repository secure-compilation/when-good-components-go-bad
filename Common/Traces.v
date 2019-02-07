Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.

From mathcomp
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Suffix.

Variable T : eqType.

Implicit Types (x : T) (s : seq T).

(* Decidable notion of a suffix (s1 is a suffix of s2) *)
Fixpoint suffix_rec s1 s2 : bool :=
  (s1 == s2) ||
  if s2 is x :: s2' then suffix_rec s1 s2' else false.

Definition suffix := locked suffix_rec.

Lemma suffix_refl : reflexive suffix.
Proof. by case=> [|??]; rewrite /suffix -lock //= eqxx. Qed.

Lemma suffix_cons s1 x s2 :
  suffix s1 (x :: s2) = (s1 == x :: s2) || suffix s1 s2.
Proof. by rewrite /suffix; unlock. Qed.

Lemma suffix_nil s1 : suffix s1 [::] = (s1 == [::]).
Proof. by rewrite /suffix -lock /= orbF. Qed.

(** Produces suffixes of a sequence (except the empty one)
    Would be used to produce the suffixes of a trace for the back-translation
    (since we don't look at the events, we can use a sequence of type T)
 *)

Definition suffixes_of_seq s : seq (seq T) :=
  let fix aux s (acc:seq (seq T)) :=
      match s with
      | [::]  => acc
      | h::t => aux t ((h::t)::acc)
      end in
  rev (aux s [::]).

(* Non tail-recursive but still fairly efficient (doesn't use append) *)
(* Fixpoint suffixes_of_seq' s : seq (seq T) := *)
(*   match s with *)
(*   | [::]  => [::] *)
(*   | h::t => (h::t) :: suffixes_of_seq' t *)
(*   end. *)

Definition suffix_flip a b := suffix b a.

Definition all_sfxs s (suffxs : seq (seq T)) : Prop :=
  all (suffix_flip s) suffxs.

Definition shape_sfxs s (suffxs : seq (seq T)) :=
  shape suffxs =(* == ? *) rev (iota 1 (size s)).

Definition wf_suffixes s :=
  { suffxs : seq (seq T) | all_sfxs s suffxs &
                         shape_sfxs s suffxs}.

Lemma suffix_prepended s1 x s2 :
  suffix s1 s2 -> suffix s1 (x::s2).
Proof. by rewrite suffix_cons orbC => ->. Qed.

Corollary suffix_prepended_bool s1 x s2 :
  suffix s1 s2 ==> suffix s1 (x::s2).
Proof. by apply /implyP ; apply suffix_prepended. Qed.

Lemma suffix_subpred x seq :
  subpred (suffix_flip seq) (suffix_flip (x::seq)).
Proof. rewrite /subpred/suffix_flip. move => suffix. by apply suffix_prepended. Qed.

(* Lemma all_sfxs_cons {T: eqType} (t:trace) (x:event) (suffxs: seq trace) : *)
(*   all_sfxs t suffxs -> all_sfxs (x::t) suffxs. *)
(* Proof. *)

(* RB: STATIC_READ: Missing definition, used later and for now aliased to a
   previous one. To fix. *)
Definition suffixes_of_seq' := suffixes_of_seq.

Lemma suffixes_of_seq_correct seq :
  all (suffix_flip seq) (suffixes_of_seq' seq) /\
  shape (suffixes_of_seq' seq) = rev (iota 1 (size seq)).
Proof.
  split.
  (* all are suffixes *)
  -
    rewrite /suffix_flip.
    (* rewrite all_cat all_seq1 suffix_refl => /=. *)
    (* move => /all_filterP IHt'. *)
    apply /all_filterP.         (* or allP ? *)

    elim: seq => [//| h t].
  (* RB: STATIC_READ: To fix. *)
  (*   have: (suffixes_of_seq' (h::t)) = [h::t] ++ (suffixes_of_seq' t) *)
  (*     by rewrite /suffixes_of_seq' => //=. *)
  (*   move => -> . *)
  (*   rewrite filter_cat => /= ; rewrite suffix_refl => /=. move => IHt. *)
  (*   (* Getting rid of the leading trace *) *)
  (*   apply /eqseqP => /=. apply /andP ; split ; [done| apply /eqseqP]. *)

  (*   apply /all_filterP. move : IHt => /all_filterP. *)

  (*   (* OK now since we can generalize about this one here, maybe we don't have *)
  (*      to deal with all this boilerplate above. *) *)
  (*   generalize (suffixes_of_seq' t). *)
  (*   have: subpred (suffix_flip t) (suffix_flip (h::t)) by apply suffix_subpred. *)
  (*   rewrite/suffix_flip. *)
  (*   by apply sub_all. *)
  (* - (* right order and right sizes *) *)
  (*   (* induction s => //=.          (* wth?? the simplification with iota is plainly wrong *) *) *)
  (*   induction seq => //. set size_seq := size seq. *)
  (*   (* rewrite -[size (a::s)](size s).+1. *) *)
  (*   admit. *)
Admitted.

(* Relocate in Lib/Extra ? *)
Lemma size_shape {A:Type} (s : seq (seq A)) :
  size s = size (shape s).
Proof.
    by rewrite /shape size_map.
Qed.

End Suffix.

Section Traces.

Inductive stack_state := StackState {
  (* The current running component.  *)
  cur_comp : Component.id;

  (* Other running components further down the stack. *)
  callers  : list Component.id
}.

Definition stack_state0 := StackState Component.main [::].

Implicit Types (t : trace) (C : Component.id) (s : stack_state) (intf : Program.interface).

Fixpoint well_bracketed_trace s t : bool :=
  match t with
  | [::] => true
  | e :: t' =>
    (cur_comp s == cur_comp_of_event e) &&
    match e with
    | ECall C _ _ C' =>
      well_bracketed_trace (StackState C' (C :: callers s)) t'
    | ERet C _ C' =>
      match callers s with
      | [] => false
      | head :: tail =>
        (head == C') && well_bracketed_trace (StackState C' tail) t'
      end
    | ELoad C _ _ _ => well_bracketed_trace s t' (* since we're not giving turn, this doesn't change the stack state and we go on *)
    end
  end.

Definition run_event s e :=
  match e with
  | ECall C _ _ C' => StackState C' (C :: callers s)
  | ERet  C _   C' => StackState C' (tail (callers s))
  | ELoad C _ _ _  => s
  end.

Definition run_trace s t := foldl run_event s t.

Lemma run_trace1 s t e : run_trace s (rcons t e) = run_event (run_trace s t) e.
Proof. by rewrite -cats1 /run_trace foldl_cat. Qed.

Lemma well_bracketed_trace_cat s t1 t2 :
  well_bracketed_trace s (t1 ++ t2) =
  well_bracketed_trace s t1 &&
  well_bracketed_trace (run_trace s t1) t2.
Proof.
elim: t1 s=> [//|[C ? ? C'|C ? C'| C _ _ _] t1 IH] [Ccur callers] /=.
  by rewrite IH andbA.
case: eqP callers => [_ {Ccur}|_] //= [|top callers] //=.
by rewrite IH andbA.
  by case: eqP => [] //=.
Qed.

Definition seq_of_stack_state s := cur_comp s :: callers s.

Coercion seq_of_stack_state : stack_state >-> seq.

Lemma seq_of_stack_state_inj : injective seq_of_stack_state.
Proof. by case=> [??] [??] [-> ->]. Qed.

Lemma well_bracketed_trace_suffix t C C' Cs :
  well_bracketed_trace stack_state0 t ->
  suffix [:: C, C' & Cs] (run_trace stack_state0 t) ->
  exists t1 P arg t2, t = t1 ++ ECall C' P arg C :: t2.
Proof.
set s0 := stack_state0.
elim/last_ind: t=> [|t e IH] //=.
  by rewrite suffix_cons suffix_nil /= orbF => _ /eqP.
have -> : well_bracketed_trace s0 (rcons t e) =
          well_bracketed_trace s0 t &&
          well_bracketed_trace (run_trace s0 t) [:: e].
  by rewrite -cats1 well_bracketed_trace_cat andbC.
rewrite run_trace1; case: e => [C1 P arg C2|C1 ? C2|C1 ? ? ?] /=.
  - (* ECall *)
  rewrite andbT; case/andP=> wb_t /eqP <- {C1} /=.
  rewrite -[_ :: callers _]/(run_trace s0 t : seq _) suffix_cons /=.
  case/orP=> [/eqP|Hsuff].
    case: (run_trace _ _)=> [? ?] [<- <- <-] /=.
    by eexists t, _, _, [::]; rewrite cats1.
  case/(_ wb_t Hsuff): IH=> [t1 [P' [arg' [t2 ->]]]].
  by eexists t1, P', arg', (rcons t2 _); rewrite rcons_cat; split; eauto.
  - (* ERet *)
case/and3P=> wb_t /eqP e1 e2.
have -> : StackState C2 (tl (callers (run_trace s0 t))) =
          callers (run_trace s0 t) :> seq _.
  by case: (callers _) e2=> [|e cs] //= /andP [/eqP ->].
move=> Hsuff; have {Hsuff} Hsuff: suffix [:: C, C' & Cs] (run_trace s0 t).
  by rewrite suffix_cons Hsuff orbT.
case/(_ wb_t Hsuff): IH=> [t1 [P [arg [t2 ->]]]].
by eexists t1, P, arg, (rcons _ _); rewrite rcons_cat.
  - (* ELoad *)
    case /and3P => wb_t /eqP e1 _.
    move => Hsuff; case/(_ wb_t Hsuff): IH=> [t1 [P [arg [t2 ->]]]].
      by eexists t1, P, arg, (rcons _ _); rewrite rcons_cat.
Qed.

Lemma well_bracketed_trace_inv t C res C' :
  well_bracketed_trace stack_state0 (t ++ [:: ERet C res C']) ->
  exists t1 P arg t2, t = t1 ++ ECall C' P arg C :: t2.
Proof.
rewrite -[t]cat0s.
elim: t {1 3}nil=> [|e t IH] pre //=; last first.
  rewrite -cat1s [pre ++ _]catA; exact: IH.
rewrite cats0 well_bracketed_trace_cat /=.
case/and3P=> wb_t /eqP e_C e_C'.
have : suffix [:: C, C' & tail (callers (run_trace stack_state0 pre))]
              (run_trace stack_state0 pre).
  case: run_trace e_C e_C'=> [? [|??]] //=; rewrite andbT.
  by move=> -> /eqP ->; rewrite suffix_refl.
exact: well_bracketed_trace_suffix=> //.
Qed.

Definition well_formed_event intf (e: event) : bool :=
  match e with
  | ECall C P _ C' => (C != C') && imported_procedure_b intf C C' P
  | ERet  C _   C' => (C != C')
  | ELoad C _ v C' => (C != C') && (is_transferable_value v)
  end.

Definition well_formed_trace intf (t: trace) : bool :=
  well_bracketed_trace stack_state0 t &&
  all (well_formed_event intf) t.

Definition declared_event_comps intf e :=
  match e with
  | ELoad C _ _ C' => Program.has_component_id intf C && Program.has_component_id intf C' (* when would we want to check the offset compared to the interface ? *)
  | _ => [&& cur_comp_of_event e \in domm intf &
                                    next_comp_of_event e \in domm intf]
  end.

Lemma well_formed_trace_int intf t :
  well_formed_trace intf t ->
  closed_interface intf ->
  all (declared_event_comps intf) t.
Proof.
case/andP=> wb wf clos; rewrite /declared_event_comps.
apply/allP; case=> [C P v C'|C v C' | C off v C'] /=; unfold Program.has_component_id; rewrite !mem_domm.
- move/(allP wf)=> /andP [_ imp].
  move: (imp); rewrite /imported_procedure_b; case: getm => //= _ _.
  by case/imported_procedure_iff/clos: imp=> ? [->].
- move=> in_p; case/path.splitP: in_p wb wf => {t} t1 t2.
  rewrite -cats1 /= well_bracketed_trace_cat.
  case/andP=> /well_bracketed_trace_inv [t11 [P [v' [t12 ->]]]] _ wf.
  have : well_formed_event intf (ECall C' P v' C).
    by move/allP: wf; apply; rewrite !mem_cat inE eqxx /= orbT.
  case/andP=> _ imp.
  case/imported_procedure_iff/clos: (imp)=> ? [-> _] /=.
  by move: imp; rewrite /imported_procedure_b; case: getm.
  admit.
Admitted.
(* Qed. *)

End Traces.

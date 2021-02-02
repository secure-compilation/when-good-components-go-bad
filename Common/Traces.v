Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import Common.Definitions.
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

End Suffix.

Section Traces.
  
Inductive stack_state := StackState {
  (* The current running component.  *)
  cur_comp : Component.id;

  (* Other running components further down the stack. *)
  callers  : list Component.id
}.

Definition stack_state0 := StackState Component.main [::].

Implicit Types (t : trace event) (C : Component.id) (s : stack_state) (intf : Program.interface).

Fixpoint well_bracketed_trace s t : bool :=
  match t with
  | [::] => true
  | e :: t' =>
    (cur_comp s == cur_comp_of_event e) &&
    match e with
    | ECall C _ _ _ C' =>
      well_bracketed_trace (StackState C' (C :: callers s)) t'
    | ERet C _ _ C' =>
      match callers s with
      | [] => false
      | head :: tail =>
        (head == C') && well_bracketed_trace (StackState C' tail) t'
      end
  (*| _ => well_bracketed_trace s t'*)
    end
  end.

(* [DynShare] TODO *)
Fixpoint well_bracketed_trace_rev (s : stack_state) (t : seq event) : bool :=
  let fix aux (acc t : seq event) : bool :=
      match t with
      (* Process trace events in reverse order.  *)
      | e :: t' =>
        match e with
        | ECall Csrc _ _ _ Cdst =>
          match acc with
          (* Unfinished call at the end of the trace. *)
          | [::]
          | ECall _ _ _ _ _ :: _ => (* Only calls found deeper down. *)
            aux (e :: acc) t'
          (* If a call encounters a return at the top of the pending stack,
             they must match; then they cancel out and we recurse. *)
          | ERet Csrc' _ _ Cdst' :: acc' =>
            (Csrc == Cdst') && (Csrc' == Cdst) && aux acc t'
          end
        | ERet Csrc _ _ Cdst =>
          (* A return needs a matching call in the past: accumulate. *)
          aux (e :: acc) t'
        end
      (* When the trace is done, [acc] is split into a sequence of returns at
         the top, followed by a sequence of calls. Two things must happen:
          1. The stack [s] must be able to match and pop all pending returns.
          2. The remaining calls in [s] and the calls at the bottom of [acc]
             must form a well-formed stack state. *)
      | [::] =>
        false (* FIXME *)
      end
  in
  aux [] (rev t).

Definition run_event s e :=
  match e with
  | ECall C _ _ _ C' => StackState C' (C :: callers s)
  | ERet  C _ _   C' => StackState C' (tail (callers s))
  (*| _ => s*)
  end.

Definition run_trace s t := foldl run_event s t.

Lemma run_trace1 s t e : run_trace s (rcons t e) = run_event (run_trace s t) e.
Proof. by rewrite -cats1 /run_trace foldl_cat. Qed.

Lemma well_bracketed_trace_cat s t1 t2 :
  well_bracketed_trace s (t1 ++ t2) =
  well_bracketed_trace s t1 &&
  well_bracketed_trace (run_trace s t1) t2.
Proof.  
elim: t1 s=> [//|[C ? ? ? C'|C ? ? C'(*|? ? ?|? ? ?*)] t1 IH] [Ccur callers] /=.
  by rewrite IH andbA.
case: eqP callers => [_ {Ccur}|_] //= [|top callers] //=.
  by rewrite IH andbA.
Qed.

Definition seq_of_stack_state s := cur_comp s :: callers s.

Coercion seq_of_stack_state : stack_state >-> seq.

Lemma seq_of_stack_state_inj : injective seq_of_stack_state.
Proof. by case=> [??] [??] [-> ->]. Qed.

Lemma well_bracketed_trace_suffix t C C' Cs :
  well_bracketed_trace stack_state0 t ->
  suffix [:: C, C' & Cs] (run_trace stack_state0 t) ->
  exists t1 P arg mem t2, t = t1 ++ ECall C' P arg mem C :: t2.
Proof.
set s0 := stack_state0.
elim/last_ind: t=> [|t e IH] //=.
  by rewrite suffix_cons suffix_nil /= orbF => _ /eqP.
have -> : well_bracketed_trace s0 (rcons t e) =
          well_bracketed_trace s0 t &&
          well_bracketed_trace (run_trace s0 t) [:: e].
  by rewrite -cats1 well_bracketed_trace_cat andbC.
rewrite run_trace1; case: e => [C1 P arg mem C2|C1 ? ? C2(*|? ? ?|? ? ?*)] /=.
  rewrite andbT; case/andP=> wb_t /eqP <- {C1} /=.
  rewrite -[_ :: callers _]/(run_trace s0 t : seq _) suffix_cons /=.
  case/orP=> [/eqP|Hsuff].
    case: (run_trace _ _)=> [? ?] [<- <- <-] /=.
    by eexists t, _, _, _, [::]; rewrite cats1.
  case/(_ wb_t Hsuff): IH=> [t1 [P' [arg' [mem' [t2 ->]]]]].
  by eexists t1, P', arg', mem', (rcons t2 _); rewrite rcons_cat; split; eauto.
case/and3P=> wb_t /eqP e1 e2.
have -> : StackState C2 (tl (callers (run_trace s0 t))) =
          callers (run_trace s0 t) :> seq _.
  by case: (callers _) e2=> [|e cs] //= /andP [/eqP ->].
move=> Hsuff; have {Hsuff} Hsuff: suffix [:: C, C' & Cs] (run_trace s0 t).
  by rewrite suffix_cons Hsuff orbT.
case/(_ wb_t Hsuff): IH=> [t1 [P [arg [mem [t2 ->]]]]].
  by eexists t1, P, arg, mem, (rcons _ _); rewrite rcons_cat.
Qed.

Lemma well_bracketed_trace_inv t C res mem C' :
  well_bracketed_trace stack_state0 (t ++ [:: ERet C res mem C']) ->
  exists t1 P arg mem' t2, t = t1 ++ ECall C' P arg mem' C :: t2.
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

(* TODO: Here, this is an important definition.
   Need as an extra argument the status of the (shared?) memory at the program state in which
   the event was emitted.
   Only then can we use reachability to compute the views of each component.
   Based on the view of a component memory, we can judge whether an ERead/EWrite that it
   performs is a possible read/write.  *)
Definition well_formed_event intf (e: event) : bool :=
  match e with
  | ECall C P _ _ C' => (C != C') && imported_procedure_b intf C C' P
  | ERet  C _ _   C' => (C != C')
  (*| ERead _ _ _ => false
  | EWrite _ _ _ => false*)
  end.

Definition well_formed_trace intf (t: trace event) : bool :=
  well_bracketed_trace stack_state0 t &&
  all (well_formed_event intf) t.

Definition declared_event_comps intf e :=
  [&& cur_comp_of_event e \in domm intf &
      next_comp_of_event e \in domm intf].

Lemma well_formed_trace_int intf t :
  well_formed_trace intf t ->
  closed_interface intf ->
  all (declared_event_comps intf) t.
Proof.
  (* [DynShare] TODO: The proof below works only if event is an equality type.
     The reason for that is that "allP" relies on this fact.
   *)
Admitted.
(*case/andP=> wb wf clos; rewrite /declared_event_comps.
apply/allP; case=> [C P v C'|C v C'] /=; rewrite !mem_domm.
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
Qed.*)

End Traces.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.Blame.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.
Require Import Lib.Monads.
Require Import Lib.Extra.
Require Import Source.CS.
Import Source.CS.CS.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Module CS.

  (* Why isn't this provable automatically since it's obviously
     contradictory for any inductive type *)
Lemma continuation_absurd : forall k e1 e2,
    Kseq (E_seq e1 e2) k <> k.
Proof.
  elim => // e k IHk e1 e2 Hkseq.
  inversion Hkseq as [[He Hind]]. by apply IHk in Hind.
Qed.
  
Instance state_turn : HasTurn state := {
  turn_of s iface := s_component s \in domm iface
}.

Corollary kstep_deterministic:
  forall G st t st1 st2,
    kstep G st t st1 -> kstep G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hkstep1 Hkstep2.
  apply eval_kstep_correct in Hkstep1.
  apply eval_kstep_correct in Hkstep2.
  rewrite Hkstep1 in Hkstep2.
  inversion Hkstep2.
  reflexivity.
Qed.

Section Semantics.

  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let sem := sem p.

  Lemma trace_wb t cs cs' :
    Star sem cs t cs' ->
    well_bracketed_trace (stack_state_of cs) t.
  Proof.
    elim: cs t cs' / => //= s1 t1 s2 t2 s3 t Hstep Hstar IH -> {t}.
    case: s1 t1 s2 / Hstep Hstar IH=> //=.
    - (* Component buffer load *)
      by move => C stk mem k C' b' o' v arg; rewrite eqxx.
    - (* Internal Return *)
      by move=> C stk mem k _ P v P_expr old <-; rewrite eqxx.
    - (* External Return *)
      move=> C stk mem k C' P v P_expr old.
      by rewrite eq_sym eqxx=> /eqP/negbTE -> /=.
    - (* Internal Call *)
      by move=> C stk mem k v _ _ old <-; rewrite eqxx.
    - (* External Call *)
      by move=> C stk mem k v _ C' old /eqP/negbTE ->; rewrite !eqxx.
  Qed.

  Lemma events_wf st t st' :
    Star sem st t st' ->
    all (well_formed_event (prog_interface p)) t.
  Proof.
    (* have valid_program explicit in signature so that we don't have to use
       closed_program *)
    clear complete_program.
    elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
    rewrite all_cat; case: st1 t1 st2 / Hstep {Hstar} => //=.
    - move=> ?? mem ? C' ? o' ?? /eqP -> -> => mem_load transf. rewrite transf IH /= !andbT.
      move: mem_load ; rewrite /Memory.load/in_bounds/=.
      inversion valid_program as
          [ _ _ _ _ wf_defined_buffers [wf_valid_buffers wf_has_req_buffers] _].
      move: wf_defined_buffers ; rewrite -eq_fset.
      rewrite /valid_buffers in wf_valid_buffers.
      destruct (mem C') eqn:memC => //.
      (* rewrite /ComponentMemory.load. *) (* opaque here *)
      move => wf_defined_buffers Comp_load.

      (* we have pretty much everything, we just need to plug things from here : *)
      (* show that the size of the content of the component's memory is the same as the public_buffer_size in the program interface,
          or the size of the buffers in the program buffers *)
      (* explicit the link between the buffers and the memory content, ...*)
      (* eapply load_in_bounds *)
      (* rewrite -mem_domm in wf_defined_buffers. *)

      (* rewrite /prepare_global_env in G. *)
      (* Maybe use initial_state to get prepare_buffers, which could allow us to link the buffers and the memory *)
      admit.
    - by move=> ????????? /eqP -> /imported_procedure_iff ->.
    - by move=> ????????  /eqP ->.
  Admitted.

  Lemma trace_wf mainP t cs cs' :
    Star sem cs t cs' ->
    initial_state p cs ->
    prog_main p = Some mainP ->
    well_formed_trace (prog_interface p) t.
  Proof.
    move=> Hstar Hinitial Hmain; rewrite /well_formed_trace.
    rewrite (events_wf Hstar) andbT.
    suffices <- : stack_state_of cs = stack_state0 by apply: trace_wb; eauto.
    by move: Hinitial; rewrite /initial_state /initial_machine_state Hmain => ->.
  Qed.

  (* Several alternative formulations are possible. One may include the ERet event
     in the star, express the inclusion of ECall in the trace via In, etc. *)
  Lemma eret_from_initial_star_goes_after_ecall_cs s0 t s1 s2 C' v C :
    CS.initial_state p s0 ->
    Star sem s0 t s1 ->
    Step sem s1 [:: ERet C' v C] s2 ->
    exists t1 s s' t2 P v',
      Star sem s0 t1 s /\
      Step sem s [ECall C P v' C'] s' /\
      Star sem s' t2 s1 /\
      t = t1 ** [ECall C P v' C'] ** t2.
  Proof.
    move=> Hinitial Hstar Hstep.
    have {Hstep} /trace_wb : Star sem s0 (t ++ [:: ERet C' v C]) s2.
      apply: star_trans; eauto; exact: star_one.
    have -> : stack_state_of s0 = stack_state0.
      by rewrite Hinitial /= /CS.initial_machine_state /=; case: prog_main.
    case/well_bracketed_trace_inv=> t1 [P [arg [t2 e]]].
    move: Hstar; rewrite {}e -[seq.cat]/Eapp.
    case/(star_middle1_inv (@singleton_traces p))=> s1' [s2' [Hstar1 [Hstep2 Hstar3]]].
    by exists t1, s1', s2', t2, P, arg; repeat split=> //.
  Qed.

  Local Open Scope fset_scope.
  
  Lemma all_expressions_evaluate (* cs_i t_i *) C s mem k e arg :

    (* Is this the right way to state that e is well typed ? (you can get from
       the initial state of the program to the expr e, and p is well typed so is
       e) *)
    (* initial_state p cs_i -> *)
    (* Star sem cs_i t_i [State C, s, mem, k, e, arg] -> *)

    (* Or maybe is there a more usable way to say that e is well_typed ? *)
    well_formed_expr p C e ->

    exists mem' t v,
      Star sem
           [State C, s, mem,  k, e,       arg] t
           [State C, s, mem', k, E_val v, arg].
  Proof.
    (* intro Hinitial. *)
    move: (* t_i *) C s mem k arg.
    induction e as [ v | b | |
                     bin e1 IHe1 e2 IHe2 |
                     e1 IHe1 e2 IHe2 |
                     e__if IHe__if e__then IHe__then e__else IHe__else |
                     e__alloc IHe__alloc |
                     e__deref IHe__deref |
                     e__assign IHe__assign e__val IHe__val |
                     Cid Pid P__expr IHP__expr |
                     Cid | ]=> C s mem k arg Hwf_e.
      - (* E_val *)
        exists mem, E0, v ; by apply star_refl.
      - (* E_arg *)
        exists mem, E0 ; eexists ; eapply star_one.
        (* eapply KS_Arg *)
        destruct arg ; simpl ; rewrite -eval_kstep_correct ; simpl ;
          first done ; exfalso ;
        (* simpl in Hstep. rewrite <- eval_kstep_correct in Hstep. *)
        (* inversion valid_program as [? ? ? wf_proc ? ? ?]. *)
        (* inversion complete_program. simpl in Hstar. *)
        (* (* simpl in Hstar. *) *)
        (* (* generalize dependent e3 ; generalize dependent e2. *) *)
        (* (* unfold prepare_global_env in G. simpl. unfold G. intro z. *) *)
        (* (* simpl. *) *)
        (* admit. *)
        (** Should be stuck (cannot have Ptr or Undef as arg in a wf_prog and more precisely in a wf_expr), how to show it ? *)
            admit.
      - (* E_local *)
        exists mem, E0 ;
          by destruct b ; eexists ; eapply star_one ; constructor.
      - (* E_binop *)
        destruct Hwf_e as [Hvalid_calls Hval_int ]. simpl in Hvalid_calls, Hval_int.
        move:Hval_int => /andP[Hval_int_e1 Hval_int_e2].
        have Hvalid_equiv: valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e1 :|: called_procedures e2) ->
              valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e1) /\
              valid_calls (prog_procedures p) (prog_interface p) C
                          (called_procedures e2) by admit.
        apply Hvalid_equiv in Hvalid_calls.
        move: Hvalid_calls {Hvalid_equiv} => [Hvalid_calls_e1 Hvalid_calls_e2].
        have Hwf_e1: well_formed_expr p C e1 by split.
        have Hwf_e2: well_formed_expr p C e2 by split.
        specialize (IHe1 C s mem (Kbinop1 bin e2 k) arg Hwf_e1).
        (* inversion Hstar_initial ; subst. inversion Hinitial. unfold initial_machine_state in H0. *)
        destruct IHe1 as [mem1 [?t [v1 star_e1]]].
        specialize (IHe2 C s mem1  (Kbinop2 bin v1 k) arg Hwf_e2).
        destruct IHe2 as [?mem [t2 [v2 star_e2]]].
        do 3 eexists.
        eapply star_step with (t1:=E0) ; last by rewrite E0_left.
        apply KS_Binop1. (* specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *)
        (* destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *)
        eapply star_trans ; first by apply star_e1.
        eapply star_step with (t1:=E0) ; last by rewrite E0_left.
        apply KS_Binop2. (* specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *)
        (* destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *)
        eapply star_trans with (t1:=t2) (t2:=E0) ;
          last rewrite E0_right ;
          first by apply star_e2.
        apply star_one. by apply KS_BinopEval. done. done.
      - (* E_seq *)

        admit.
      - (* E_if *)
        admit.
      - (* E_alloc *)
        admit.
      - (* E_deref *)
        admit.
      - (* E_assign *)
        admit.
      - (* E_call *)
        admit.
      - (* E_component_buf *)
  Admitted.

(* Pondering : E_seq (e1) (E_seq e2 e3) should be the same as E_seq (E_seq e1 e2) e3 *)
(* or more more naturally : e1; (e2; e3) = (e1; e2); e3 *)
(* sequence should be associative ?*)
(* or maybe we just stick to one of the representation since this could
   complicate things in the semantics / during the compilaiton *)

  
  (*
| KS_Seq1 :  forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_seq e1 e2, arg] E0
            [State C, s, mem, Kseq e2 k, e1, arg]
| KS_Seq2 : forall C s mem k v e2 arg,
    kstep G [State C, s, mem, Kseq e2 k, E_val v, arg] E0
            [State C, s, mem, k, e2, arg]
   *)

(** we should have something like :
(Left side)
 Plus sem [State C, s, mem0, k, E_seq (E_seq e1 e2) e3, arg] evs
          [State C, s, mem__final, k, e3, arg]
          ≜
 (KS_Seq1)
 Step sem [State C, s, mem0, k, E_seq (E_seq e1 e2) e3, arg] E0
          [State C, s, mem0, Kseq e3 k, E_seq e1 e2, arg]
 **
 (KS_Seq1)
 Step sem [State C, s, mem0, Kseq e3 k, E_seq e1 e2, arg] E0
          [State C, s, mem0, Kseq e2 (Kseq e3 k), e1, arg]
 **
 (This is the part where case analysis/induction on e1 happens )
 Star sem [State C, s, mem0, Kseq e2 (Kseq e3 k), e1, arg] t1
          [State C, s, mem1, Kseq e2 (Kseq e3 k), E_val v, arg]
 (mem1 may be different from mem0, and t1 may be non empty)
 **
 (KS_Seq2)
 Step sem [State C, s, mem1, Kseq e2 (Kseq e3 k), E_val v, arg] E0
          [State C, s, mem1, Kseq e3 k, e2, arg]
 (case analysis/induction on e2)
 Star sem [State C, s, mem1, Kseq e3 k, e2, arg] t2
          [State C, s, mem__final, Kseq e3 k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem__final, Kseq e3 k, E_val v, arg] E0
          [State C, s, mem__final, k, e3, arg]

And (Right side)
 Plus sem [State C, s, mem0, k, E_seq e1 (E_seq e2 e3), arg] evs
          [State C, s, mem__final, k, e3, arg]
          ≜
 (KS_Seq1)
 Step sem [State C, s, mem0, k, E_seq e1 (E_seq e2 e3), arg] E0
          [State C, s, mem0, Kseq (E_seq e2 e3) k, e1, arg]
 **
 (case analysis/induction on e1)
 Star sem [State C, s, mem0, Kseq (E_seq e2 e3) k, e1, arg] t1
          [State C, s, mem1, Kseq (E_seq e2 e3) k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem1, Kseq (E_seq e2 e3) k, E_val v, arg] E0
          [State C, s, mem1, k, E_seq e2 e3, arg]
 **
 (KS_Seq1)
 Step sem [State C, s, mem1, k, E_seq e2 e3, arg] E0
          [State C, s, mem1, Kseq e3 k, e2, arg]
 **
 (case analysis/induction on e2)
 Star sem [State C, s, mem1, Kseq e3 k, e2, arg] t2
          [State C, s, mem2, Kseq e3 k, E_val v, arg]
 **
 (KS_Seq2)
 Step sem [State C, s, mem2, Kseq e3 k, E_val v, arg] E0
          [State C, s, mem2, k, e3, arg]

We can even draw the finish line right before the case/ind on e2 since it's exactly the same from here *)
  (* Conjecture seq_associative : associative E_seq. *)
  (* Ltac inversion_star_and_subst := *)
  (*   match goal with *)
  (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
  (*     inversion_clear H as [H H' H'' [H''' Hcontra H'''1]|] ; subst *)
  (*   | _  => idtac *)
  (*   end. *)

  Lemma seq_assoc_in_CS_aux_left_seq C s mem mem' k e1 e2 e3 arg evs:
      Plus sem
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           (* [State C, s, mem', Kseq e3 k, e2, arg] *)
           (* Or *)
           [State C, s, mem', k, e3, arg]
      -> Plus sem
           [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
           [State C, s, mem', Kseq e3 k, e2, arg].
  Proof.
    intro H.
    apply plus_trans with (t1:=E0)
                          (t2:=evs)
                          (s2:= [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg]);
      last by rewrite E0_left.
    apply plus_one, KS_Seq1.
    have:  exists mem' t v,
        Star sem
             [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg] t
             [State C, s, mem', Kseq (E_seq e2 e3) k, E_val v, arg]
    (* \/ *)
        (* Plus sem *)
        (*      [State C, s, mem, Kseq (E_seq e2 e3) k, e1, arg] t *)
        (*      [State C, s, mem', Kseq (E_seq e2 e3) k, E_val v, arg] *).
    {
      apply all_expressions_evaluate. admit.
      (* inversion_clear H as [? ? ? ? ? ? Hstep Hstar (* ... *)] ; subst ; *)
      (*   inversion Hstep ; subst. *)
      (* inversion Hstar as [state Hstate Htrace [Hmem Hcontra Hexp]| state1 trace1 state2 trace2 state3 trace3 Hstep' Hstar' Htrace] ; subst ; *)
      (*   (* inversion_star_and_subst *) *)
      (*   (* [>by apply continuation_absurd in Hcontra| ..] *) *)
      (*   (** Not strong enough since we know that all the first goals generated by *)
      (*    inversion Hstar must be solved by this, but the 'subst' in between cannot *)
      (*    allow us to use 'first' *) *)
      (*   (* try by apply continuation_absurd in Hcontra. *) *)
      (*   match goal with *)
      (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
      (*       by apply continuation_absurd in H ; idtac "boup" *)
      (*   | _  => idtac *)
      (*   end. *)
      (* (* move: Hstar Hstep Hstep' Hstar'. *) *)
      (* generalize (Kseq (E_seq e2 e3) k). *)
      (* clear Hstar Hstep Hstar' Hstep'. generalize dependent mem. *)
      (* (* generalize dependent e3 ; generalize dependent e2. generalize dependent k. *) *)
      (* induction e1 => mem c (* => k e2 e3 *) (* H Hstar Hstep *) *)
      (* (* ; exists mem, E0 *) (* . eexists *) *)
      (* (*       inversion Hstar as [H0 H' H'' [H''' Hcontra H'''1]|] ; subst ; *)
      (*   (* inversion_star_and_subst *) *)
      (*   (* [>by apply continuation_absurd in Hcontra| ..] *) *)
      (*   (** Not strong enough since we know that all the first goals generated by *)
      (*    inversion Hstar must be solved by this, but the 'subst' in between cannot *)
      (*    allow us to use 'first' *) *)
      (*   (* try by apply continuation_absurd in Hcontra. *) *)
      (*   match goal with *)
      (*   | H: Kseq (E_seq _ _ ) ?k = ?k |- _ => *)
      (*       by apply continuation_absurd in H *)
      (*   | _  => idtac *)
      (*   end. *) *)
      (* . *)
      (* - (* E_val *) *)
      (*   exists mem, E0, v ; by apply star_refl. *)
      (* - (* E_arg *) *)
      (*   exists mem, E0 ; eexists ; eapply star_one. *)
      (*   (* eapply KS_Arg *) *)
      (*   destruct arg ; simpl ; rewrite -eval_kstep_correct ; simpl ; *)
      (*     first done ; exfalso ; *)
      (*   (* simpl in Hstep. rewrite <- eval_kstep_correct in Hstep. *) *)
      (*   (* inversion valid_program as [? ? ? wf_proc ? ? ?]. *) *)
      (*   (* inversion complete_program. simpl in Hstar. *) *)
      (*   (* (* simpl in Hstar. *) *) *)
      (*   (* (* generalize dependent e3 ; generalize dependent e2. *) *) *)
      (*   (* (* unfold prepare_global_env in G. simpl. unfold G. intro z. *) *) *)
      (*   (* (* simpl. *) *) *)
      (*   (* admit. *) *)
      (*   (** Should be stuck (cannot have Ptr or Undef as arg in a wf_prog and more precisely in a wf_expr), how to show it ? *) *)
      (*       admit. *)
      (* - (* E_local *) *)
      (*   exists mem, E0 ; *)
      (*     by destruct b ; eexists ; eapply star_one ; constructor. *)
      (* - (* E_binop *) *)
      (*   specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *)
      (*   destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *)
      (*   specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *)
      (*   destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *)
      (*   do 3 eexists. *)
      (*   eapply star_step with (t1:=E0) ; last by rewrite E0_left. *)
      (*   apply KS_Binop1. (* specialize IHe1_1 with (c:= Kbinop1 b e1_2 c) (mem:= mem). *) *)
      (*   (* destruct IHe1_1 as [mem1 [?t [v1 star_e1_1]]]. *) *)
      (*   eapply star_trans ; first by apply star_e1_1. *)
      (*   eapply star_step with (t1:=E0) ; last by rewrite E0_left. *)
      (*   apply KS_Binop2. (* specialize IHe1_2 with (c:= Kbinop2 b v1 c) (mem:= mem1). *) *)
      (*   (* destruct IHe1_2 as [?mem [t2 [v2 star_e1_2]]]. *) *)
      (*   eapply star_trans with (t1:=t2) (t2:=E0) ; *)
      (*     last rewrite E0_right ; *)
      (*     first by apply star_e1_2. *)
      (*   apply star_one. by apply KS_BinopEval. done. done. *)

    }
        (* intro. destruct x. destruct H ; destruct H. *)
    intros [mem1 [t1 [v1 Hstar]]].
    inversion H as [? ? ? ? ? ? Hstep Hstar' (* ... *)] ; subst.
    inversion Hstep ; subst.
    (* inversion Hstar' as [|] ; subst. *)
    (*   eapply star_plus_trans with (t1:=t1) *)
    (*                               (t2:=E0) ; *)
    (*     last (rewrite E0_right) ; *)
    (*     first (by apply Hstar) ; clear Hstar. *)
    (*   apply plus_trans with (t1:=E0) *)
    (*                         (t2:=E0) *)
    (*                         (s2:= [State C, s, mem', k, E_seq e2 e3, arg]); *)
    (*     last by rewrite E0_left. *)
    (*   apply plus_one, KS_Seq2. *)
    (*   apply plus_one, KS_Seq1. *)
  Admitted.

  Lemma seq_assoc_in_CS_aux_right_seq C s mem mem' k e1 e2 e3 arg evs:
      Plus sem
           [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
           (* [State C, s, mem', Kseq e3 k, e2, arg] *)
           (* Or *)
           [State C, s, mem', k, e3, arg]
      -> Plus sem
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           [State C, s, mem', Kseq e3 k, e2, arg].
  Proof.
  Admitted.

  (* Not well stated at all, not true in general *)
  Lemma seq_assoc_in_CS_aux_common:
    forall C s mem mem' k e1 e2 e3 arg evs,
      Plus sem
           (* direction doesn't really matter at this point I guess *)
           [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
           [State C, s, mem', k, e3, arg] ->
      Plus sem
           [State C, s, mem, Kseq e3 k, e2, arg] evs
           [State C, s, mem', k, e3, arg].
  Proof.
    intros.
    have: exists v,
        Star sem
             [State C, s, mem, Kseq e3 k, e2, arg] evs
             [State C, s, mem', Kseq e3 k, E_val v, arg].
    induction e2 ; admit.
    intros [v Hstar].
    apply plus_right with (s2:=[State C, s, mem', Kseq e3 k, E_val v, arg])
                           (t1:=evs)
                           (t2:=E0) ;
      last (by rewrite E0_right) ;
      first (by apply Hstar) ; clear Hstar.
    apply KS_Seq2.
    Admitted.

  Lemma seq_assoc_in_CS:
    forall C s mem mem' k e1 e2 e3 arg evs,
      (* If we can go from e1 to e3 ("legal" expressions) *)
      (* Star *) Plus sem [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs
                      [State C, s, mem', k, e3, arg] <->
      (* then the sequencing doesn't matter, we have ((e1;e2); e3) <-> (e1;(e2;e3)) *)
      (* Star *) Plus sem [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs
                      [State C, s, mem', k, e3, arg].

  (* step kstep (prepare_global_env p) [State C, s, mem, k, E_seq (E_seq e1 e2) e3, arg] evs *)
  (*      [State C, s, mem', k, e3, arg] <-> *)
  (* step kstep (prepare_global_env p) [State C, s, mem, k, E_seq e1 (E_seq e2 e3), arg] evs *)
  (*      [State C, s, mem', k, e3, arg]. *)

  (*   (* NB : no need to have different `s` or `arg` since we sequence expressions in the same stack frame (if we make a function call, we should return from it before ending the sequence) *) *)
  Proof.
    split ; intro Dir1.
    (* - (* -> *) *)
    (*   eapply plus_trans. *)
    (*   eapply plus_trans in Dir1. *)
    (*   eapply plus_trans ; [|eapply seq_assoc_in_CS_aux_common |]. *)
    (*    apply seq_trans_in_CS_aux_left_seq. *)
    (*   eapply (plus_trans seq_trans_in_CS_aux_left_seq seq_trans_in_CS_aux_common). *)
    (* - (* <- *) *)
    (*   inversion Dir1 as [? ? ? ? ? ? Hstep Hstar (* ... *)] ; subst. *)
    (*   inversion Hstep ; subst. *)
    (*   eapply plus_trans. repeat econstructor. 2: by rewrite !E0_left. *)
    (*   eapply plus_trans. repeat econstructor. 2: by rewrite !E0_left. *)
    (*   induction e1. *)
    (*   + eapply plus_trans. *)
    (*   (* have: Kseq e2 (Kseq e3 k) = Kseq (E_seq e2 e3) k. *) *)
    (*   (* induction e1 => //. *) *)
    (*   (* eapply plus_left'. *) *)
    (*   apply star_inv in Hstar ; destruct Hstar as [[HcontraState ?] | Hstar] ; subst. *)
    (*   + inversion HcontraState ; subst. *)
    (*   (* inversion Hstar ; subst. *) *)
    (*   + (* Dead-end, cannot have star_refl *) *)
    (*     admit. *)
    (*   + *)
    (*   (* econstructor. constructor. econstructor. constructor. econstructor. *) *)
    (*   repeat econstructor ; last rewrite !E0_left E0_right. *)
    (*   (* inversion Hstep ; subst. *) *)
    (*   induction e1 => //=. *)
    (*   +  apply KS_Seq2. *)

    (*   ; simpl in Dir1, Hstep, Hstar. *)
    (* econstructor. *)
  Admitted.

  
End Semantics.

End CS.

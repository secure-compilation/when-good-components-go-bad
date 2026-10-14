Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import Common.Traces.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import MicroPolicies.Recomposition.TraceInit.
Require Import Coq.micromega.Lia.
Require Import Backtranslation_ME_MP_Seg.

Import DoNotation.
Import Types.
Import Symbolic.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

Definition zarg' (e : event) : BinNums.Z :=
  match e with ECall _ _ z _ => z | ERet _ z _ => z end.

Definition entry_canon (PI : Program.interface)
    (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) : Prop :=
  forall w d p lc, m w = Some d -> entry (taga d) = Some (p, lc) ->
    entry (Transitional.head_tag_gen PI (color (taga d)) p) = Some (p, lc).

Lemma entry_canon_extends PI m0 m1 :
  mem_shape_extends m0 m1 -> entry_canon PI m0 -> entry_canon PI m1.
Proof.
move=> Hext Hc w d p lc Hd He.
case: (Hext _ _ Hd) => [[d0 [Hd0 Esh]]|[Hnone _]]; last by rewrite He in Hnone.
move: Esh. rewrite /tag_shape => -[E1 E2 E3].
rewrite E1. apply: (Hc _ _ _ _ Hd0). by rewrite -E2.
Qed.

Lemma initial_entry_canon (cde : @Merged.code mt) pb pi PI :
  (forall i t e, List.In (i, t) cde -> entry t = Some e ->
     t = Transitional.head_tag_gen PI (color t) e.1) ->
  entry_canon PI (mem (Merged.initial_state cde pb pi)).
Proof.
move=> Hh w d p lc Hw He.
case: (initial_cell_inv Hw) => [[i [t [Hin Ht]]]|[c0 Ht]].
- rewrite Ht in He *. have E := Hh _ _ _ Hin He. rewrite /= in E.
  by rewrite -E He.
- by rewrite Ht in He.
Qed.

Lemma nsuap_evi : forall (st s' : state) (op : opcode) tpc ti
    (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' e,
  @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
    (IVec (OP op) tpc ti ts) updts pc' = Some (s', Some e) ->
  exists evinp ov0,
    evi st = Some evinp /\
    LRC.transfer (IVec (OP op) tpc ti ts
      (match mem st pc' with Some ni => Some (taga ni) | None => None end))
      evinp
      = Some (ov0, Some e).
Proof.
move=> st s' op tpc ti ts updts pc' e.
rewrite /next_state_updates_and_pc /next_state.
case Hevi: (evi st) => [evinp|] //=.
case Hm: (mem st pc') => [ni|] /=.
- case Htr: (LRC.instr_rules_mp evinp op tpc ti ts (Some (taga ni))) => [ov_ev|] //=.
  case: ov_ev Htr => ov0 ev Htr /=.
  case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
  move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
  exists evinp, ov0. split; [by [] | exact: Htr].
- case Htr: (LRC.instr_rules_mp evinp op tpc ti ts None) => [ov_ev|] //=.
  case: ov_ev Htr => ov0 ev Htr /=.
  case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
  move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
  exists evinp, ov0. split; [by [] | exact: Htr].
Qed.

Lemma transfer_event_arg :
  forall (op : opcode) (tpc : tag_type lrc_tags Symbolic.P)
         (ti : tag_type lrc_tags Symbolic.M)
         (ts : hseq (tag_type lrc_tags) (inputs op))
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
    LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
    zarg' e = rcom_value evinp.
Proof.
  move=> op tpc ti ts tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'.
  move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H.
  - rewrite (hseq0 ts) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq0 (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [Hcc {}H].
    move: H. case Hbel: (belong _ _) => H.
    + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    + case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => c' [Hc' {}H].
      case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He].
      by rewrite -He.
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [Hcc {}H].
    case: (obind_inv H) => u1 [_ {}H].
    move: H. case Hbel: (belong _ _) => H.
    + by move: H => [=].
    + case: (obind_inv H) => u2 [_ {}H].
      case: (obind_inv H) => c' [Hc' {}H].
      case: (obind_inv H) => u3 [Hce {}H].
      move: H => [= _ He].
      move: He. case: (get_proc_name _) => [p|] //= [<-]. by [].
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
Qed.

Lemma evi_word (st : state) evinp :
  evi st = Some evinp -> exists w : mword mt, rcom_value evinp = convert (int_of_word w).
Proof. rewrite /evi. case: (regs st rcom) => [a|] //= [<-]. by exists (vala a). Qed.

Lemma step_event_arg_aux :
  forall (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
         (r : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags Symbolic.R)})
         (pcv : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ex : unit)
         (s' : state) (op : opcode)
         (ti : tag_type lrc_tags Symbolic.M)
         (ts : hseq (tag_type lrc_tags) (inputs op)) updts pcn e,
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit
      {| Symbolic.mem := m; Symbolic.regs := r;
         Symbolic.pc := pcv@tpc; Symbolic.internal := ex |}
      (IVec (OP op) tpc ti ts) updts pcn = Some (s', Some e) ->
    exists w : mword mt, zarg' e = convert (int_of_word w).
Proof.
  move=> m r pcv tpc ex s' op ti ts updts pcn e NEXT.
  have [evinp [ov0 [Hevi Htr]]] := nsuap_evi NEXT.
  rewrite (transfer_event_arg Htr). exact: evi_word Hevi.
Qed.

Section Arg.

Variable NC : nat.

Lemma step_event_arg : forall (s s' : state) e,
  step_mp s s' (Some e) (NC := NC) ->
  exists w : mword mt, zarg' e = convert (int_of_word w).
Proof.
  move=> s s' e Hstep. inversion Hstep.
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - unfold mvec in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - unfold mvec, pc' in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - unfold mvec, pc' in NEXT.
    rewrite ST in NEXT *. exact: (step_event_arg_aux NEXT).
  - have Hev := run_syscall_event_none CALL. discriminate Hev.
Qed.

End Arg.

Lemma convert_word_range (w : mword mt) :
  Z.le (Z.opp (Z.pow 2 31)) (convert (int_of_word w))
  /\ Z.lt (convert (int_of_word w)) (Z.pow 2 31).
Proof.
have Hw : fintype.nat_of_ord (ord_of_word w) < 2 ^ 32.
{ apply: (leq_trans (fintype.ltn_ord (ord_of_word w))). rewrite word_size_mt. exact: leqnn. }
have H32 := Zof_nat_expn2 32. have H31 := Zof_nat_expn2 31.
rewrite /int_of_word.
move: Hw. set n := fintype.nat_of_ord (ord_of_word w). move=> Hw.
rewrite word_size_mt /=.
case: ifP => Hlt.
- rewrite /=.
  have Hlt' : Z.lt (Z.of_nat n) (Z.pow 2 31).
  { rewrite -H31. apply/Nat2Z.inj_lt. apply/ltP. exact: Hlt. }
  clear -Hlt'. lia.
- rewrite convert_subz' H32.
  have Hge : Z.le (Z.pow 2 31) (Z.of_nat n).
  { rewrite -H31. apply/Nat2Z.inj_le. apply/leP. rewrite leqNgt Hlt. exact: erefl. }
  have Hlt2 : Z.lt (Z.of_nat n) (Z.pow 2 32).
  { rewrite -H32. apply/Nat2Z.inj_lt. apply/ltP. exact: Hw. }
  clear -Hge Hlt2. lia.
Qed.

Section StarObs.

Variable NC : nat.

Lemma star_obs (W : program) (PI : Program.interface) (s : state) tw (s' : state) :
  Star (mp_sem NC W) s tw s' -> entry_canon PI (mem s) ->
  forall e, List.In e tw ->
  [/\ next_comp_of_event e <> cur_comp_of_event e,
      Z.le (Z.opp (Z.pow 2 31)) (zarg' e) /\ Z.lt (zarg' e) (Z.pow 2 31)
    & forall c p v c', e = ECall c p v c' ->
        exists lc, entry (Transitional.head_tag_gen PI c' p) = Some (p, lc) /\ c \in lc].
Proof.
move=> Hstar. elim: Hstar => [s0 _ e []|s1 t1 s2 t2 s3 tw0 Hstep Hstar IH Etw] Hc e Hin.
rewrite Etw in Hin. clear Etw. move: Hstep. rewrite /= /prog_step_mp.
case: t1 Hin => [|e1 [|??]] Hin // Hstep.
- apply: IH Hin. exact: entry_canon_extends (step_cell_shape Hstep) Hc.
- case: Hin => [Ee|Hin]; last first.
  { apply: IH Hin. exact: entry_canon_extends (step_cell_shape Hstep) Hc. }
  subst e1.
  have [Hcur Hneq Hcall] := step_event_facts Hstep.
  have [w Hw] := step_event_arg Hstep.
  split.
  + exact: Hneq.
  + rewrite Hw. exact: convert_word_range.
  + move=> c p v c' Ee.
    have [w' [iv [tn [Hm Hcol [lc [Hent Hlc]]]]]] := Hcall _ _ _ _ Ee.
    exists lc. split; last exact: Hlc.
    rewrite -Hcol. exact: (Hc _ _ _ _ Hm Hent).
Qed.

End StarObs.

Lemma head_entry_facts (PI : Program.interface) c' p lc c :
  entry (Transitional.head_tag_gen PI c' p) = Some (p, lc) -> c \in lc ->
  exists i i', [/\ PI c' = Some i, PI c = Some i', p \in Component.export i
                 & (c', p) \in Component.import i'].
Proof.
rewrite /Transitional.head_tag_gen /= => -[<-]. rewrite mem_filter => /andP [Hal _].
move: Hal. case E1: (PI c') => [i|] //=. case E2: (PI c) => [i'|] //= /andP [H1 H2].
by exists i, i'.
Qed.

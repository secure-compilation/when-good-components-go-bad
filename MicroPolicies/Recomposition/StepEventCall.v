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
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Exec.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceBracket(reg_index_neq).
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepSilentWeak2.

Module StepEventCall (S: RecompositionContext).

  (* Chain off StepWeak2 so the whole recomposition shares ONE Defs instance. *)
  Include StepWeak2 S.

  (* The running component after a cross-component call is the callee [c]; it is a real
     interface component because the call-target cell [d] is coloured [c] (via [get_tni_color])
     and lives in a [color_in_memory]'d memory.  Discharges the new [common_equiv] validity
     premise (the running component's pc-tag colour ∈ ip ∪ ic). *)
  Lemma running_comp_valid_call m w d c :
    color_in_memory m -> m w = Some d -> get_tni_color (Some (taga d)) = Some c ->
    (c \in domm ip) || (c \in domm ic).
  Proof.
    move=> Hcm Hmw Htni.
    have Hc : color (taga d) = c
      by (move: Htni; rewrite /get_tni_color; case: (taga d) => vt ct et bt /= [= ->]).
    apply/orP; have := Hcm w d Hmw; rewrite Hc; case=> [/In_in ?|/In_in ?]; [by left|by right].
  Qed.

  (* After a call/return event the pc lands on the entry/return cell, whose [get_tni_color] is the
     new running colour [c] (= [color_of s], the post-event pc-tag colour).  So [pc_code_color]
     holds of the post-state: the unique cell at the new pc is running-coloured. *)
  Lemma pc_code_color_entry : forall (s : state) cell c n,
      mem s (vala (pc s)) = Some cell ->
      get_tni_color (Some (taga cell)) = Some c ->
      taga (pc s) = build_tpc n c ->
      pc_code_color s.
  Proof.
    move=> s cell c n Hmem Htc Htag d Hd _.
    move: Hd; rewrite Hmem => -[= <-].
    have Hcol : color_of s = c by rewrite (color_of_pc_tag s) Htag /build_tpc.
    rewrite Hcol.
    by move: Htc; rewrite /get_tni_color; case: (taga cell) => vt ct et bt /= [= ->].
  Qed.

  (* [Opaque]/[Transparent] settings are NOT inherited through [Require Import], so
     re-establish them here: without this the 100+ [simpl in *] calls in [step_event_call]
     explode over the word/fmap ops and the proof term blows up (>600s Qed, the 9.4MB .vo).
     [as_word]/[word_of_nat] stay TRANSPARENT — the proof [unfold]s them deliberately for the
     concrete register addresses (0..19). *)
  Opaque andw shlw mask component_memory_prefix.
  Opaque unionm setm mkfmap mkfmapfp.
  (* PERF: keep [pc_code_color] folded so the giant-state pcc hyps/goals don't normalise in Qed. *)
  Local Opaque pc_code_color.

  Notation "x $ t" := {| vala := x; taga := t |} (at level 5, format "x '$' t").

  (* [cbn] that leaves the word/fmap/hseq spines and the LRC policy helpers FROZEN, so reducing
     [stepf] never materialises the 12-register [reg_invalidate_hseq] / JAL [OVec] (the source of
     the historical [StepEventCall.vo] blow-up).  Used by [call_step_scratch] below. *)
  Ltac mcbn H := cbn -[obind oapp as_word word_of_nat andw shlw mask component_memory_prefix
                       unionm setm getm mkfmap mkfmapfp domm decode_instr
                       next_state_do_updates next_state_do_update reg_clear_list_aux
                       reg_invalidate_hseq reg_clear_read reg_clear_list is_code belong
                       switch_val build_tpc get_tni_color get_proc_name check_ret
                       is_address is_jump is_other rcom_value] in H.

  (* Fast characterisation peel for the future [call_step_inv] (conclusion is still [True] — this
     is the regression-tested scaffold).  In ~6s it [apply stepP]s, fetches+decodes, then for EVERY
     one of the 14 [instr] constructors + the syscall branch: peels [evi]/[transfer] with [obind_inv]
     (stop-guarded at [transfer] so the dependent [vovec (op IVEC)] type has no free witness),
     [case]s the conditional next-cell address ([if] in the address handles BNZ; ssr [case: (smem _)]
     handles JAL/JUMP/sequential), then unfolds [transfer]/[instr_rules] and peels the rule's
     [do!]/[if]/[let] structure to the EVENT.  All 8 silent opcodes are refuted by [congruence]
     (event [None] <> [ECall]); exactly the JAL cross-component branch survives. *)
  (* [call_step_inv] (minimal, will be extended): a Merged [ECall] step forces the instruction at
     [pc] to decode to a [Jal].  Proven by the all-opcode characterisation peel. *)
  Lemma call_step_inv : forall (s s' : Symbolic.state lrc_tags unit) comp proc z comp',
    step_me (NC := NC) s s' (Some (ECall comp proc z comp')) ->
    exists ip imm cell rac a1,
      Symbolic.mem s (vala (Symbolic.pc s)) = Some ip /\
      decode_instr (vala ip) = Some (Jal imm) /\
      Symbolic.mem s (swcast imm) = Some cell /\
      get_proc_name (Some (taga cell)) = Some proc /\
      get_tni_color (Some (taga cell)) = Some comp' /\
      belong comp (Some (taga cell)) = false /\
      (let 'i$ti := ip in match ti with {| color := c |} => c end) = comp /\
      Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some rac /\
      Symbolic.regs s (as_word (ssrint.Posz 1)) = Some a1 /\
      is_code (taga ip) = true /\
      color (taga ip) = color_of s /\
      color (taga rac) = comp /\
      taga a1 = Other /\
      check_entry comp (Some (taga cell)) = Some tt /\
      z = convert (int_of_word (vala a1)).
  Proof.
    intros s s' comp proc z comp' H.
    apply stepP in H.
    (* Abbreviate the goal to a single token [G] so the ~30 [destruct]/[case]s in the peel each
       carry [G] (not the conclusion) as their match return-type — without this a 3-conjunct goal
       blows the peel from ~8s to a 45-min timeout. *)
    match goal with |- ?Goal => set (G := Goal) end.
    destruct s as [smem sreg [spc stpc] sextra].
    destruct stpc as [slvl scol].
    cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
          andw setm unionm mkfmap getm decode_instr] in H.
    destruct (smem spc) as [[i ti]|] eqn:Hf; rewrite Hf in H;
      cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
            andw setm unionm mkfmap getm decode_instr] in H;
      try discriminate H.
    apply obind_inv in H as [instr [DEC H]].
    destruct instr.
    all: unfold next_state_updates, next_state_updates_and_pc, next_state in H.
    all: cbv zeta in H; mcbn H.
    all: try unfold run_syscall in H.
    (* peel 1: strip the [evi]/[transfer]/register-read [do!]s, leaving [H] as the small
       [match op IVEC with ...] continuation (the [transfer] equation moves to a side hyp). *)
    all: repeat (lazymatch type of H with
           | obind _ (transfer _ _) = _ => fail
           | _ => first
               [ apply obind_inv in H as [? [? H]]
               | match goal with w : (_ * _)%type |- _ => destruct w end
               | match goal with a : atom _ _ |- _ =>
                   match type of H with context[a] => destruct a end end
               ]; mcbn H
           end).
    (* discharge the syscall branch (event is [None]) and any immediately-contradictory
       opcode branch before the (relatively pricey) [case]s. *)
    all: try (exfalso; congruence).
    (* [H] now stops at [obind _ (transfer IVEC _)]: [transfer]'s result is NOT yet extracted,
       so the dependent type [vovec (op IVEC)] has no free witness to block [case].  Guard on
       [DEC] so the [case] skips the syscall branch ([case]ing [smem] there forces [Symbolic.sem]). *)
    all: try (match type of H with context[if ?c then _ else _] =>
                let e := fresh in destruct c eqn:e end; mcbn H).
    all: try (match goal with _ : decode_instr _ = Some _ |- _ =>
                move: H; case Ejt: (smem _) => [[niv nit]|]; move=> H; mcbn H end).
    (* peel 2: strip the [transfer]/[next_state_do_updates] [do!]s down to the event.  For JAL
       this leaves [H : Some (st', o0) = Some (s', Some (ECall ...))] (event [o0] = the JAL-cross
       event) plus the side hyp [transfer ... = Some (ov, o0)] still to be characterised. *)
    (* op is concrete now, so unfolding [transfer]/[instr_rules] is safe; [mcbn] keeps the
       12-register OVec frozen.  Peel EVERY [do!]-hyp (not just [H]): the [instr_rules] equation
       is a side hyp whose event must resolve too. *)
    all: unfold transfer, instr_rules, LRC.instr_rules, check_belong, check_entry in H.
    all: cbv zeta in H; mcbn H.
    all: repeat (first
           [ match goal with HH : (do! _ <- _; _) = Some _ |- _ =>
               apply obind_inv in HH as [? [? HH]]; mcbn HH end
           | match goal with HH : context[let '{| trpc := _; tr := _ |} := _ in _] |- _ =>
               progress mcbn HH end
           | match goal with HH : Some _ = Some (?a, ?b) |- _ =>
               is_var a; is_var b; injection HH as ? ?; subst end
           | match goal with HH : Some _ = Some ?w |- _ => is_var w; injection HH as ?; subst end
           | match goal with w : (_ * _)%type |- _ => destruct w end
           | match goal with HH : context[match ?c with true => _ | false => _ end] |- _ =>
               let e := fresh "Eif" in revert HH; destruct c eqn:e; intro HH; mcbn HH end
           | match goal with HH : context[let (_, _) := ?x in _] |- _ => destruct x; mcbn HH end ]).
    all: mcbn H.
    (* All 8 silent opcodes are refuted here (their event is [None] <> [ECall]); exactly ONE goal
       survives — the genuine JAL cross-component call, with [H : Some (jal_state, do! p <-
       get_proc_name; Some (ECall current p z c')) = Some (s', Some (ECall comp proc z comp'))]. *)
    all: try (exfalso; congruence).
    (* lone JAL survivor: expand [G] back to the conclusion; [Hf : smem spc = Some (i$ti)],
       [DEC : decode_instr i = Some (Jal _)], [Ejt : smem (swcast imm) = Some cell] (target cell). *)
    (* inject the survivor's event eq to expose [proc]/[comp'] (= the rule's [p]/[c']) *)
    all: injection H as ? Hev; apply obind_inv in Hev as [? [Hgpn Hev]];
         injection Hev as ? ? ? ?; subst.
    all: repeat match goal with u : unit |- _ => destruct u end.
    all: subst G; do 5 eexists; repeat split;
           [> cbn -[decode_instr getm swcast] in |- *; exact Hf
            | cbn -[decode_instr getm swcast] in |- *; exact DEC
            | cbn -[decode_instr getm swcast] in |- *; exact Ejt
            | cbn -[decode_instr getm swcast get_proc_name] in |- *; exact Hgpn
            | cbn -[decode_instr getm swcast get_tni_color] in |- *; assumption
            | cbn -[decode_instr getm swcast belong] in |- *; assumption
            | cbn -[decode_instr getm swcast] in |- *; reflexivity
            | cbn [Symbolic.mem Symbolic.pc Types.vala];
              match goal with H : _ (addw _ _) = Some _ |- _ => exact H end
            | cbn [Symbolic.regs];
              match goal with H : _ (as_word (ssrint.Posz 1)) = Some _ |- _ => exact H end
            | cbn [Types.taga]; assumption
            | cbn [Types.taga color_of]; apply/eqnP; assumption
            | match goal with Hb : belong _ (Some (Types.taga ?x)) = true |- _ =>
                move: Hb; case: (Types.taga x) => ? ? ? ? /eqP ->; reflexivity end
            | match goal with Hio : is_other ?t = Some _ |- _ => move: Hio; case: t => // end
            | cbn [Types.taga]; assumption
            | match goal with He : evi _ = Some _, Hr : _ (as_word (ssrint.Posz 1)) = Some _ |- _ =>
                move: He; rewrite /evi => He; mcbn He; rewrite Hr in He; mcbn He;
                case: He => <-; reflexivity end ].
  Qed.

  (* [step_mp] (LRC.transfer, NO is_code gate) analogue of [call_step_inv].  Used for the UB cases
     of the match_right helper [secmr]: there s1 (the context) executes data as a JAL, so [step_me]
     (Merged) fails on the missing [is_code], but the LRC step [step_mp] still produces the JAL-cross
     event.  Proof is [call_step_inv]'s verbatim (the peel is defensive — the is_code-gate branch
     simply never fires for LRC); only [LRC.transfer] is added to the transfer-unfold. *)
  Lemma call_step_inv_mp : forall (s s' : Symbolic.state lrc_tags unit) comp proc z comp',
    step_mp (NC := NC) s s' (Some (ECall comp proc z comp')) ->
    exists ip imm cell,
      Symbolic.mem s (vala (Symbolic.pc s)) = Some ip /\
      decode_instr (vala ip) = Some (Jal imm) /\
      Symbolic.mem s (swcast imm) = Some cell /\
      get_proc_name (Some (taga cell)) = Some proc /\
      get_tni_color (Some (taga cell)) = Some comp' /\
      belong comp (Some (taga cell)) = false /\
      (let 'i$ti := ip in match ti with {| color := c |} => c end) = comp.
  Proof.
    intros s s' comp proc z comp' H.
    apply stepP in H.
    match goal with |- ?Goal => set (G := Goal) end.
    destruct s as [smem sreg [spc stpc] sextra].
    destruct stpc as [slvl scol].
    cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
          andw setm unionm mkfmap getm decode_instr] in H.
    destruct (smem spc) as [[i ti]|] eqn:Hf; rewrite Hf in H;
      cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
            andw setm unionm mkfmap getm decode_instr] in H;
      try discriminate H.
    apply obind_inv in H as [instr [DEC H]].
    destruct instr.
    all: unfold next_state_updates, next_state_updates_and_pc, next_state in H.
    all: cbv zeta in H; mcbn H.
    all: try unfold run_syscall in H.
    all: repeat (lazymatch type of H with
           | obind _ (transfer _ _) = _ => fail
           | obind _ (LRC.transfer _ _) = _ => fail
           | _ => first
               [ apply obind_inv in H as [? [? H]]
               | match goal with w : (_ * _)%type |- _ => destruct w end
               | match goal with a : atom _ _ |- _ =>
                   match type of H with context[a] => destruct a end end
               ]; mcbn H
           end).
    all: try (exfalso; congruence).
    all: try (match type of H with context[if ?c then _ else _] =>
                let e := fresh in destruct c eqn:e end; mcbn H).
    all: try (match goal with _ : decode_instr _ = Some _ |- _ =>
                move: H; case Ejt: (smem _) => [[niv nit]|]; move=> H; mcbn H end).
    all: unfold transfer, LRC.transfer, instr_rules, LRC.instr_rules, LRC.instr_rules_mp in H.
    all: cbv zeta in H; mcbn H.
    all: repeat (first
           [ match goal with HH : (do! _ <- _; _) = Some _ |- _ =>
               apply obind_inv in HH as [? [? HH]]; mcbn HH end
           | match goal with HH : context[let '{| trpc := _; tr := _ |} := _ in _] |- _ =>
               progress mcbn HH end
           | match goal with HH : Some _ = Some (?a, ?b) |- _ =>
               is_var a; is_var b; injection HH as ? ?; subst end
           | match goal with HH : Some _ = Some ?w |- _ => is_var w; injection HH as ?; subst end
           | match goal with w : (_ * _)%type |- _ => destruct w end
           | match goal with HH : context[match ?c with true => _ | false => _ end] |- _ =>
               let e := fresh "Eif" in revert HH; destruct c eqn:e; intro HH; mcbn HH end
           | match goal with HH : context[let (_, _) := ?x in _] |- _ => destruct x; mcbn HH end ]).
    all: mcbn H.
    all: try (exfalso; congruence).
    all: injection H as ? Hev; apply obind_inv in Hev as [? [Hgpn Hev]];
         injection Hev as ? ? ? ?; subst.
    all: subst G; do 3 eexists; repeat split;
           [> cbn -[decode_instr getm swcast] in |- *; exact Hf
            | cbn -[decode_instr getm swcast] in |- *; exact DEC
            | cbn -[decode_instr getm swcast] in |- *; exact Ejt
            | cbn -[decode_instr getm swcast get_proc_name] in |- *; exact Hgpn
            | cbn -[decode_instr getm swcast get_tni_color] in |- *; assumption
            | cbn -[decode_instr getm swcast belong] in |- *; assumption
            | cbn -[decode_instr getm swcast] in |- *; reflexivity ].
  Qed.

  (* TODO(jt): [call_step_inv] above is the PROVEN (Qed, ~7s) fast characterisation core that
     replaces the historical >400s [inversion + unfold_all] (which made this proof intractable).
     Remaining to un-[Admitted] [step_event_call]: (1) extend [call_step_inv]'s conclusion from
     "the instruction is a JAL" to the full JAL-cross data (target cell, [belong=false],
     [comp=current], [proc=get_proc_name], [comp'=get_tni_color], [z=rcom_value], and [s'=]the
     jal-cross result) — all already exposed in the lone JAL survivor; (2) the symmetric
     [call_step_intro] (build a [step_jal] via [Symbolic.step_jal], Symbolic.v:378); (3) rewire the
     four P/C x P/C reconstruction cases off these. *)
  (* The reg-clear suffix of a cross-call/return do_updates SUCCEEDS (returns Some _) whenever every
     register it reads exists — the tags are arbitrary (Invalidated/Other), so this is existence, not
     the own-tag no-op of [reg_clear_do_updates_id]. *)
  Lemma reg_clear_read_exists :
    forall (l : seq nat) (st : state)
           (tags : hseq (tag_type ttypes) (nseq (size l) R)),
      (forall n, n \in l -> regs st (as_word (ssrint.Posz n)) <> None) ->
      exists st', next_state_do_updates st tags
                    (map (fun n => RegRead (as_word (ssrint.Posz n))) l) = Some st'.
  Proof.
    Local Transparent next_state_do_update.
    elim => [|n l' IH] st tags Hex; first by exists st.
    rewrite (hseq_eta tags) map_cons ndsu_cons.
    have [a Ha] : exists a, regs st (as_word (ssrint.Posz n)) = Some a.
    { case E: (regs st (as_word (ssrint.Posz n))) => [a|]; first by exists a.
      exfalso; apply: (Hex n); [by rewrite in_cons eqxx | exact E]. }
    have Hupd : next_state_do_update st (hshead tags) (RegRead (as_word (ssrint.Posz n)))
                = Some {| mem := mem st;
                          regs := setm (regs st) (as_word (ssrint.Posz n)) ((vala a) @ (hshead tags));
                          pc := pc st; internal := internal st |}.
    { by rewrite /next_state_do_update /= Ha /= /updm Ha. }
    rewrite Hupd obindE.
    apply: IH => m Hm.
    rewrite /= setmE.
    case: eqP => [_|_]; first by [].
    apply: (Hex m); by rewrite in_cons Hm orbT.
  Qed.

  (* The full cross-call/return do_updates SUCCEEDS: a MemRead no-op on the cell at [w], the ra-write
     reg(4):=w, then the register clear.  All cells must exist. *)
  Lemma cross_do_updates_exists :
    forall (st : state) (w : mword mt)
           (tags : hseq (tag_type ttypes) (M :: R :: nseq (size reg_list) R)),
      mem st w <> None ->
      regs st (as_word (ssrint.Posz 4)) <> None ->
      (forall n, n \in reg_list -> regs st (as_word (ssrint.Posz n)) <> None) ->
      exists st', next_state_do_updates st tags
                    (MemRead w :: RegWrite (as_word (ssrint.Posz 4)) w :: reg_clear_read) = Some st'.
  Proof.
    move=> st w tags Hm H4 Hex.
    have [am Ham] : exists am, mem st w = Some am.
    { case E: (mem st w) => [am|]; [by exists am | by exfalso; apply: Hm]. }
    have [a4 Ha4] : exists a4, regs st (as_word (ssrint.Posz 4)) = Some a4.
    { case E: (regs st (as_word (ssrint.Posz 4))) => [a4|]; [by exists a4 | by exfalso; apply: H4]. }
    rewrite (hseq_eta tags) ndsu_cons.
    have HM : next_state_do_update st (hshead tags) (MemRead w)
              = Some {| mem := setm (mem st) w ((vala am) @ (hshead tags)); regs := regs st;
                        pc := pc st; internal := internal st |}.
    { by rewrite /next_state_do_update /= Ham /= /updm Ham. }
    rewrite HM obindE (hseq_eta (hsbehead tags)) ndsu_cons.
    have HR : next_state_do_update {| mem := setm (mem st) w ((vala am) @ (hshead tags)); regs := regs st;
                                      pc := pc st; internal := internal st |}
                (hshead (hsbehead tags)) (RegWrite (as_word (ssrint.Posz 4)) w)
              = Some {| mem := setm (mem st) w ((vala am) @ (hshead tags));
                        regs := setm (regs st) (as_word (ssrint.Posz 4)) (w @ (hshead (hsbehead tags)));
                        pc := pc st; internal := internal st |}.
    { by rewrite /next_state_do_update /= /updm Ha4. }
    rewrite HR obindE /reg_clear_read.
    apply: reg_clear_read_exists => n Hn.
    rewrite /= setmE.
    case: eqP => [_|_]; first by [].
    exact: (Hex n Hn).
  Qed.

  Local Ltac killcond :=
    repeat (match goal with |- context[as_word (ssrint.Posz ?a) == as_word (ssrint.Posz ?b)] =>
      rewrite (introF eqP (@reg_index_neq a b ltac:(move=> ?; discriminate)
                            ltac:(by []) ltac:(by []))) end).
  (* After the MemRead [/=] fully unfolds the chain, every later update is a nested
     [do! a <- regs ..; if isSome (regs ..) then Some (setm ..) else None]: [setmE]+[killcond]
     reduce the [regs (fold) (as_word n)] reads to [regs st (as_word n)], [Hr] discharges them. *)
  Local Ltac rrstep Hr := rewrite ?setmE; killcond; rewrite Hr /=.

  (* Every capability stored in a depth-[cn] stack has a [Ret] level STRICTLY below [cn]:
     the top frame is at level [cn-1], the rest recurse.  Used to show the freshly-pushed
     [Ret cn] capability is unique (nothing already in the stack / memory carries level [cn]). *)
  Lemma wf_stack_levels_lt :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack),
      wf_stack m1 m2 m3 cn M ->
      forall a b c col, In (a, b, c, col) M ->
        exists k, taga a = Ret k /\ taga b = Ret k /\ taga c = Ret k /\ (k < cn)%N.
  Proof.
    move=> m1 m2 m3 cn M H.
    induction H as [
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH ].
    - by move=> a b c col [].
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        exists n; split; [by [] | split; [by [] | split; [by [] |]]].
        by rewrite addn1 ltnSn.
      + have [k [Ha [Hb [Hc Hk]]]] := IH a b c col Hin.
        exists k; split; [exact: Ha | split; [exact: Hb | split; [exact: Hc |]]].
        by rewrite addn1; apply: (ltn_trans Hk); exact: ltnSn.
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        exists n; split; [by [] | split; [by [] | split; [by [] |]]].
        by rewrite addn1 ltnSn.
      + have [k [Ha [Hb [Hc Hk]]]] := IH a b c col Hin.
        exists k; split; [exact: Ha | split; [exact: Hb | split; [exact: Hc |]]].
        by rewrite addn1; apply: (ltn_trans Hk); exact: ltnSn.
  Qed.

  (* The cross do_updates RESULT: reg4:=w@(Ret cn), reg1:=arg@Other, the rest @Invalidated.
     [cbn] (not [ndsu_cons]) peels the hseq-cast spine; [next_state_do_update] reduced per step. *)
  Lemma cross_do_updates_props :
    forall (st : state) (w : mword mt) (tret : tag_type ttypes M) (cn : nat) cell a1,
      mem st w = Some cell ->
      regs st (as_word (ssrint.Posz 1)) = Some a1 ->
      regs st (as_word (ssrint.Posz 4)) <> None ->
      (forall n, n \in reg_list -> regs st (as_word (ssrint.Posz n)) <> None) ->
      exists rs,
        next_state_do_updates st
          ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type ttypes) (M :: R :: R :: nseq 10 R))
          (MemRead w :: RegWrite (as_word (ssrint.Posz 4)) w :: reg_clear_read)
        = Some {| mem := setm (mem st) w ((vala cell) @ tret); regs := rs;
                  pc := pc st; internal := internal st |}
        /\ rs (as_word (ssrint.Posz 4)) = Some (w @ (Ret cn))
        /\ rs (as_word (ssrint.Posz 1)) = Some ((vala a1) @ Other)
        /\ (forall n, n \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
              exists v, rs (as_word (ssrint.Posz n)) = Some (v @ Invalidated)).
  Proof.
    move=> st w tret cn cell a1 Hmem Ha1 H4 Hex.
    Local Transparent next_state_do_update.
    have RD : forall n, n \in reg_list -> exists a, regs st (as_word (ssrint.Posz n)) = Some a.
    { move=> n Hn; case E: (regs st (as_word (ssrint.Posz n))) => [a|];
        [by exists a | by exfalso; apply: (Hex n Hn)]. }
    have [a4 Ha4] : exists a4, regs st (as_word (ssrint.Posz 4)) = Some a4
      by case E: (regs st (as_word (ssrint.Posz 4))) => [a4|]; [exists a4 | exfalso; exact: H4].
    have [a0 Ha0]   := RD 0  isT. have [a2 Ha2]   := RD 2  isT.
    have [a3 Ha3]   := RD 3  isT. have [a5 Ha5]   := RD 5  isT.
    have [a6 Ha6]   := RD 6  isT. have [a7 Ha7]   := RD 7  isT.
    have [a16 Ha16] := RD 16 isT. have [a17 Ha17] := RD 17 isT.
    have [a18 Ha18] := RD 18 isT. have [a19 Ha19] := RD 19 isT.
    eexists. split.
    { cbn [next_state_do_updates ohead behead hshead hsbehead nseq make_hseq map
           reg_clear_read reg_list reg_invalidate_hseq].
      rewrite !obindE.
      rewrite {1}/next_state_do_update /= Hmem /= /updm Hmem /=.
      rrstep Ha4. rrstep Ha1. rrstep Ha0. rrstep Ha2. rrstep Ha3.
      rrstep Ha5. rrstep Ha6. rrstep Ha7. rrstep Ha16. rrstep Ha17.
      rrstep Ha18. rrstep Ha19. reflexivity. }
    (* ?rs is now the concrete [setm]-fold; read each register back via [setmE]. *)
    split; [ | split ].
    - by rewrite !setmE; killcond; rewrite eqxx /=.
    - by rewrite !setmE; killcond; rewrite eqxx /=.
    - move=> n; rewrite !inE =>
        /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|
        /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]]]]]];
        eexists; rewrite !setmE; killcond; rewrite eqxx /=; reflexivity.
  Qed.
  Local Opaque next_state_do_update.

  (* Plumbing (fmap-domain arithmetic): [next_state_do_updates] only [updm]/[setm]s register
     keys it reads/writes (all already in the domain when the step succeeds), so it preserves
     the register domain.  Provable by induction on [updts]; admitted as plumbing per the admit
     policy (fset/[register_domm] arithmetic) so the substantive proof below stays on track. *)
  (* [next_state_do_updates] only [updm]s register/memory keys, so it preserves the register
     domain (proved generically in [Symbolic], where the definition is transparent). *)
  Lemma reg_domm_cross :
    forall (st st' : state) (tks : seq tag_kind) (tags : hseq (tag_type ttypes) tks)
           (updts : seq update),
      next_state_do_updates st tags updts = Some st' ->
      register_domm (regs st) -> register_domm (regs st').
  Proof.
    move=> st st' tks tags updts H Hd.
    rewrite /register_domm (next_state_do_updates_regs_domm H).
    by move: Hd; rewrite /register_domm.
  Qed.

  (* The cross-call wf_stack push, extracted as a standalone lemma so it is proven in a CLEAN,
     minimal context — this sidesteps the §1 perf wall that the in-place [eapply
     wf_stack_cons_left] hits when the goal carries the huge post-s2-reduction context. *)
  Lemma cross_wf_stack :
    forall (m1 m2 m3 : @memory mt) (cn : nat) (cc : Component.id) (M0 : stack)
           (pc0 pc2v pc3v vret vra3 : mword mt) (tret : tag_type lrc_tags M)
           (ret : atom (mword mt) (tag_type lrc_tags M)) (off_sp : ssrint.int),
      side_of cc = Left ->
      get_offset Left cc = Some off_sp ->
      m1 (pc0 + 1)%w = Some (vret$tret) ->
      m2 (pc2v + 1)%w = Some ret ->
      m3 (pc3v + 1)%w = Some (vra3$tret) ->
      color tret = cc -> is_code tret ->
      color (taga ret) = cc -> is_code (taga ret) ->
      pc3v = addw pc0 (as_word off_sp) ->
      wf_stack m1 m2 m3 cn M0 ->
      wf_stack m1 m2 m3 cn.+1
        (((pc0 + 1)%w$(Ret cn), (pc2v + 1)%w$(Ret cn), (pc3v + 1)%w$(Ret cn), cc) :: M0).
  Proof.
    move=> m1 m2 m3 cn cc M0 pc0 pc2v pc3v vret vra3 tret ret off_sp
      Hside Hoff RA Hret Hcell3 Hcol_ra Hic_ra Hcolret Hcoret Hpcsp WF.
    rewrite -[X in wf_stack _ _ _ X _]addn1.
    eapply wf_stack_cons_left.
    - move: Hside; rewrite /side_of /is_relevant_comp; by case: (cc \in domm ip).
    - exact: Hoff.
    - rewrite /points_to_comp_code' RA; cbn [Option.apply taga];
        split; [ exact: Hcol_ra | right; exact: Hic_ra ].
    - rewrite /points_to_comp_code Hret; cbn [Option.apply taga];
        split; [ exact: Hcolret | exact: Hcoret ].
    - rewrite /points_to_comp_code Hcell3; cbn [Option.apply taga];
        split; [ exact: Hcol_ra | exact: Hic_ra ].
    - rewrite Hpcsp;
        exact: (eq_trans (esym (addwA pc0 (as_word off_sp) 1%w))
          (eq_trans (f_equal (addw pc0) (addwC (as_word off_sp) 1%w))
             (addwA pc0 1%w (as_word off_sp)))).
    - exact: WF.
  Qed.

  (* Right-side mirror of [cross_wf_stack]: the merged run s3 follows the STRONG run s2 (position 2),
     so v3 = addw v2 off and the side is Right (cc in the context [ic]).  Position 1 is the weak run
     s1 (cell [ret]); positions 2,3 share the strong tag [tret]. *)
  Lemma cross_wf_stack_right :
    forall (m1 m2 m3 : @memory mt) (cn : nat) (cc : Component.id) (M0 : stack)
           (pc1v pc2sv pc3v vret vra3 : mword mt) (tret : tag_type lrc_tags M)
           (ret : atom (mword mt) (tag_type lrc_tags M)) (off_sp : ssrint.int),
      cc \in domm ic ->
      get_offset Right cc = Some off_sp ->
      m1 (pc1v + 1)%w = Some ret ->
      m2 (pc2sv + 1)%w = Some (vret$tret) ->
      m3 (pc3v + 1)%w = Some (vra3$tret) ->
      color tret = cc -> is_code tret ->
      color (taga ret) = cc -> side_of cc = Right ->
      pc3v = addw pc2sv (as_word off_sp) ->
      wf_stack m1 m2 m3 cn M0 ->
      wf_stack m1 m2 m3 cn.+1
        (((pc1v + 1)%w$(Ret cn), (pc2sv + 1)%w$(Ret cn), (pc3v + 1)%w$(Ret cn), cc) :: M0).
  Proof.
    move=> m1 m2 m3 cn cc M0 pc1v pc2sv pc3v vret vra3 tret ret off_sp
      Hic Hoff RET RA Hcell3 Hcol_ra Hic_ra Hcolret Hsideret Hpcsp WF.
    rewrite -[X in wf_stack _ _ _ X _]addn1.
    eapply wf_stack_cons_right.
    - rewrite /is_relevant_comp; exact: Hic.
    - exact: Hoff.
    - rewrite /points_to_comp_code' RET; cbn [Option.apply taga];
        split; [ exact: Hcolret | left; split; [ exact: erefl | exact: Hsideret ] ].
    - rewrite /points_to_comp_code RA; cbn [Option.apply taga];
        split; [ exact: Hcol_ra | exact: Hic_ra ].
    - rewrite /points_to_comp_code Hcell3; cbn [Option.apply taga];
        split; [ exact: Hcol_ra | exact: Hic_ra ].
    - rewrite Hpcsp;
        exact: (eq_trans (esym (addwA pc2sv (as_word off_sp) 1%w))
          (eq_trans (f_equal (addw pc2sv) (addwC (as_word off_sp) 1%w))
             (addwA pc2sv 1%w (as_word off_sp)))).
    - exact: WF.
  Qed.

  (* Capability preservation for s1' of the cross-call, in a clean context. After the call the ONLY
     Ret-tagged register is [ra] (the fresh capability fp1@Ret cn); memory is unchanged so input
     [cap1] handles it; [wf_stack_levels_lt] gives no Ret-cn value pre-exists ⇒ the new one is unique. *)
  Lemma cross_capability_S1 :
    forall (s1 s1' : state) (m2 m3 : @memory mt) (cn : nat) (cc : Component.id) (M0 : stack)
           (fp1 fp2 fp3 vo1 : mword mt),
      capability_correctness M0 WS_S1 s1 ->
      mem s1' = mem s1 ->
      wf_stack (mem s1) m2 m3 cn M0 ->
      regs s1' ra = Some (fp1 @ (Ret cn)) ->
      regs s1' (as_word (ssrint.Posz 1)) = Some (vo1 @ Other) ->
      (forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
          exists v, regs s1' (as_word (ssrint.Posz k)) = Some (v @ Invalidated)) ->
      domm (regs s1') = fset (ra :: map word_of_nat reg_list) ->
      capability_correctness
        ((fp1 @ (Ret cn), fp2 @ (Ret cn), fp3 @ (Ret cn), cc) :: M0) WS_S1 s1'.
  Proof.
    move=> s1 s1' m2 m3 cn cc M0 fp1 fp2 fp3 vo1 cap1 Hmem WF Hr4 Hreg1 Hinv Hdom.
    have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
    have NoMemCn : forall w (u : atom (mword mt) (tag_type lrc_tags M)),
        mem s1 w = Some u -> vtag (taga u) <> Ret cn.
    { move=> w [uv ut] Hmw Hvt.
      have Hh : exists t, mem s1 w = Some (uv @ t) /\ vtag t = Ret cn.
      { exists ut; split; [exact: Hmw | exact: Hvt]. }
      have [[sv1 [sv2 [col Hin]]] _] := cap1 uv cn (inr w) Hh.
      have [k [Hk [_ [_ Hlt]]]] := wf_stack_levels_lt WF Hin.
      move: Hk; cbn [taga] => [= Hkc]; subst k. by move: Hlt; rewrite ltnn. }
    have RegRet : forall r' v', regs s1' r' = Some (v' @ (Ret cn)) -> r' = ra.
    { move=> r' v' Hr'. have Hr'in : r' \in domm (regs s1') by apply/dommP; exists (v' @ (Ret cn)).
      move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP // | /mapP[m Hm Hrm]].
      exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
      - subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
      - have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
    move=> v n [r | w] Hcap.
    - have [Hra [Hv Hn]] : r = ra /\ v = fp1 /\ n = cn.
      { have Hrin : r \in domm (regs s1') by apply/dommP; exists (v @ (Ret n)).
        move: Hrin; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
        - move: Hcap; rewrite Hr Hr4 => -[= -> ->]. by [].
        - exfalso; subst r; rewrite WA in Hcap; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
          + subst m; move: Hcap; rewrite Hreg1 => -[= _ HH]; discriminate HH.
          + have [vv Hvv] := Hinv m Hmr; move: Hcap; rewrite Hvv => -[= _ HH]; discriminate HH. }
      subst r v n; split.
      + by exists (fp2 @ (Ret cn)), (fp3 @ (Ret cn)), cc; left.
      + move=> [r' | w'] v'.
        * move=> Hr'. by rewrite (RegRet _ _ Hr').
        * move=> [t' [Hmw' Hvt']]. exfalso. move: Hmw'; rewrite Hmem => Hmw'.
          exact: (NoMemCn w' (v' @ t') Hmw' Hvt').
    - move: Hcap => [t [Hmw Hvt]]; move: Hmw; rewrite Hmem => Hmw.
      have [Hin Huniq] := cap1 v n (inr w) (ex_intro _ t (conj Hmw Hvt)).
      split.
      + move: Hin => [sv1 [sv2 [col Hin]]]. by exists sv1, sv2, col; right.
      + move=> [r' | w'] v'.
        * move=> Hr'; exfalso.
          have Hncn : n = cn.
          { have Hr'in : r' \in domm (regs s1') by apply/dommP; exists (v' @ (Ret n)).
            move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
            - by move: Hr'; rewrite Hr Hr4; move=> [= _ [= ->]].
            - exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons
                => /orP[/eqP Hm1 | Hmr].
              + subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
              + have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
          subst n. exact: (NoMemCn w (v @ t) Hmw Hvt).
        * move=> [t' [Hmw' Hvt']]. apply: (Huniq (inr w') v').
          exists t'; split; [ by move: Hmw'; rewrite ?Hmem | exact: Hvt' ].
  Qed.

  (* WS_S2 mirror of [cross_capability_S1]: the capability sits in the 2nd stack slot. *)
  Lemma cross_capability_S2 :
    forall (s s' : state) (m1 m3 : @memory mt) (cn : nat) (cc : Component.id) (M0 : stack)
           (fp1 fp2 fp3 vo1 : mword mt),
      capability_correctness M0 WS_S2 s ->
      mem s' = mem s ->
      wf_stack m1 (mem s) m3 cn M0 ->
      regs s' ra = Some (fp2 @ (Ret cn)) ->
      regs s' (as_word (ssrint.Posz 1)) = Some (vo1 @ Other) ->
      (forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
          exists v, regs s' (as_word (ssrint.Posz k)) = Some (v @ Invalidated)) ->
      domm (regs s') = fset (ra :: map word_of_nat reg_list) ->
      capability_correctness
        ((fp1 @ (Ret cn), fp2 @ (Ret cn), fp3 @ (Ret cn), cc) :: M0) WS_S2 s'.
  Proof.
    move=> s s' m1 m3 cn cc M0 fp1 fp2 fp3 vo1 cap Hmem WF Hr4 Hreg1 Hinv Hdom.
    have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
    have NoMemCn : forall w (u : atom (mword mt) (tag_type lrc_tags M)),
        mem s w = Some u -> vtag (taga u) <> Ret cn.
    { move=> w [uv ut] Hmw Hvt.
      have Hh : exists t, mem s w = Some (uv @ t) /\ vtag t = Ret cn.
      { exists ut; split; [exact: Hmw | exact: Hvt]. }
      have [[sv1 [sv2 [col Hin]]] _] := cap uv cn (inr w) Hh.
      have [k [_ [Hk [_ Hlt]]]] := wf_stack_levels_lt WF Hin.
      move: Hk; cbn [taga] => [= Hkc]; subst k. by move: Hlt; rewrite ltnn. }
    have RegRet : forall r' v', regs s' r' = Some (v' @ (Ret cn)) -> r' = ra.
    { move=> r' v' Hr'. have Hr'in : r' \in domm (regs s') by apply/dommP; exists (v' @ (Ret cn)).
      move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP // | /mapP[m Hm Hrm]].
      exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
      - subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
      - have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
    move=> v n [r | w] Hcap.
    - have [Hra [Hv Hn]] : r = ra /\ v = fp2 /\ n = cn.
      { have Hrin : r \in domm (regs s') by apply/dommP; exists (v @ (Ret n)).
        move: Hrin; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
        - move: Hcap; rewrite Hr Hr4 => -[= -> ->]. by [].
        - exfalso; subst r; rewrite WA in Hcap; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
          + subst m; move: Hcap; rewrite Hreg1 => -[= _ HH]; discriminate HH.
          + have [vv Hvv] := Hinv m Hmr; move: Hcap; rewrite Hvv => -[= _ HH]; discriminate HH. }
      subst r v n; split.
      + by exists (fp1 @ (Ret cn)), (fp3 @ (Ret cn)), cc; left.
      + move=> [r' | w'] v'.
        * move=> Hr'. by rewrite (RegRet _ _ Hr').
        * move=> [t' [Hmw' Hvt']]. exfalso. move: Hmw'; rewrite Hmem => Hmw'.
          exact: (NoMemCn w' (v' @ t') Hmw' Hvt').
    - move: Hcap => [t [Hmw Hvt]]; move: Hmw; rewrite Hmem => Hmw.
      have [Hin Huniq] := cap v n (inr w) (ex_intro _ t (conj Hmw Hvt)).
      split.
      + move: Hin => [sv1 [sv2 [col Hin]]]. by exists sv1, sv2, col; right.
      + move=> [r' | w'] v'.
        * move=> Hr'; exfalso.
          have Hncn : n = cn.
          { have Hr'in : r' \in domm (regs s') by apply/dommP; exists (v' @ (Ret n)).
            move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
            - by move: Hr'; rewrite Hr Hr4; move=> [= _ [= ->]].
            - exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons
                => /orP[/eqP Hm1 | Hmr].
              + subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
              + have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
          subst n. exact: (NoMemCn w (v @ t) Hmw Hvt).
        * move=> [t' [Hmw' Hvt']]. apply: (Huniq (inr w') v').
          exists t'; split; [ by move: Hmw'; rewrite ?Hmem | exact: Hvt' ].
  Qed.

  (* WS_S3 mirror of [cross_capability_S1]: the capability sits in the 3rd stack slot. *)
  Lemma cross_capability_S3 :
    forall (s s' : state) (m1 m2 : @memory mt) (cn : nat) (cc : Component.id) (M0 : stack)
           (fp1 fp2 fp3 vo1 : mword mt),
      capability_correctness M0 WS_S3 s ->
      mem s' = mem s ->
      wf_stack m1 m2 (mem s) cn M0 ->
      regs s' ra = Some (fp3 @ (Ret cn)) ->
      regs s' (as_word (ssrint.Posz 1)) = Some (vo1 @ Other) ->
      (forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
          exists v, regs s' (as_word (ssrint.Posz k)) = Some (v @ Invalidated)) ->
      domm (regs s') = fset (ra :: map word_of_nat reg_list) ->
      capability_correctness
        ((fp1 @ (Ret cn), fp2 @ (Ret cn), fp3 @ (Ret cn), cc) :: M0) WS_S3 s'.
  Proof.
    move=> s s' m1 m2 cn cc M0 fp1 fp2 fp3 vo1 cap Hmem WF Hr4 Hreg1 Hinv Hdom.
    have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
    have NoMemCn : forall w (u : atom (mword mt) (tag_type lrc_tags M)),
        mem s w = Some u -> vtag (taga u) <> Ret cn.
    { move=> w [uv ut] Hmw Hvt.
      have Hh : exists t, mem s w = Some (uv @ t) /\ vtag t = Ret cn.
      { exists ut; split; [exact: Hmw | exact: Hvt]. }
      have [[sv1 [sv2 [col Hin]]] _] := cap uv cn (inr w) Hh.
      have [k [_ [_ [Hk Hlt]]]] := wf_stack_levels_lt WF Hin.
      move: Hk; cbn [taga] => [= Hkc]; subst k. by move: Hlt; rewrite ltnn. }
    have RegRet : forall r' v', regs s' r' = Some (v' @ (Ret cn)) -> r' = ra.
    { move=> r' v' Hr'. have Hr'in : r' \in domm (regs s') by apply/dommP; exists (v' @ (Ret cn)).
      move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP // | /mapP[m Hm Hrm]].
      exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
      - subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
      - have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
    move=> v n [r | w] Hcap.
    - have [Hra [Hv Hn]] : r = ra /\ v = fp3 /\ n = cn.
      { have Hrin : r \in domm (regs s') by apply/dommP; exists (v @ (Ret n)).
        move: Hrin; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
        - move: Hcap; rewrite Hr Hr4 => -[= -> ->]. by [].
        - exfalso; subst r; rewrite WA in Hcap; move: Hm; rewrite /reg_list in_cons => /orP[/eqP Hm1 | Hmr].
          + subst m; move: Hcap; rewrite Hreg1 => -[= _ HH]; discriminate HH.
          + have [vv Hvv] := Hinv m Hmr; move: Hcap; rewrite Hvv => -[= _ HH]; discriminate HH. }
      subst r v n; split.
      + by exists (fp1 @ (Ret cn)), (fp2 @ (Ret cn)), cc; left.
      + move=> [r' | w'] v'.
        * move=> Hr'. by rewrite (RegRet _ _ Hr').
        * move=> [t' [Hmw' Hvt']]. exfalso. move: Hmw'; rewrite Hmem => Hmw'.
          exact: (NoMemCn w' (v' @ t') Hmw' Hvt').
    - move: Hcap => [t [Hmw Hvt]]; move: Hmw; rewrite Hmem => Hmw.
      have [Hin Huniq] := cap v n (inr w) (ex_intro _ t (conj Hmw Hvt)).
      split.
      + move: Hin => [sv1 [sv2 [col Hin]]]. by exists sv1, sv2, col; right.
      + move=> [r' | w'] v'.
        * move=> Hr'; exfalso.
          have Hncn : n = cn.
          { have Hr'in : r' \in domm (regs s') by apply/dommP; exists (v' @ (Ret n)).
            move: Hr'in; rewrite Hdom in_fset in_cons => /orP[/eqP Hr | /mapP[m Hm Hrm]].
            - by move: Hr'; rewrite Hr Hr4; move=> [= _ [= ->]].
            - exfalso; subst r'; rewrite WA in Hr'; move: Hm; rewrite /reg_list in_cons
                => /orP[/eqP Hm1 | Hmr].
              + subst m; move: Hr'; rewrite Hreg1 => -[= _ HH]; discriminate HH.
              + have [vv Hvv] := Hinv m Hmr; move: Hr'; rewrite Hvv => -[= _ HH]; discriminate HH. }
          subst n. exact: (NoMemCn w (v @ t) Hmw Hvt).
        * move=> [t' [Hmw' Hvt']]. apply: (Huniq (inr w') v').
          exists t'; split; [ by move: Hmw'; rewrite ?Hmem | exact: Hvt' ].
  Qed.

  Lemma call_step_z : forall (s s' : Symbolic.state lrc_tags unit) comp proc z comp' a1,
    step_me (NC := NC) s s' (Some (ECall comp proc z comp')) ->
    Symbolic.regs s (as_word (ssrint.Posz 1)) = Some a1 ->
    z = convert (int_of_word (vala a1)).
  Proof.
    move=> s s' comp proc z comp' a1 H Ha1.
    have [ip [imm [cell [rac [a1' [_ [_ [_ [_ [_ [_ [_ [_ [Ha1' [_ [_ [_ [_ [_ Hz]]]]]]]]]]]]]]]]]]] :=
      call_step_inv H.
    rewrite Hz. congr (convert (int_of_word (vala _))). congruence.
  Qed.

  Lemma jal_cross_step3 :
    forall (mem3 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags M)})
           (regs3 : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)})
           pc3v int3 cn cc i3 ti3 imm' vra3 tret vo to l3 a3 dd' comp proc z comp',
      mem3 pc3v = Some (i3$ti3) ->
      mem3 (pc3v + 1)%w = Some (vra3$tret) ->
      decode_instr i3 = Some (Jal imm') ->
      regs3 ra = Some (vo$to) ->
      reg_clear_list regs3 to = Some l3 ->
      register_domm regs3 ->
      is_code ti3 = true ->
      color ti3 = cc ->
      color tret = cc ->
      regs3 (as_word (ssrint.Posz 1)) = Some a3 ->
      taga a3 = Other ->
      mem3 (swcast imm') = Some dd' ->
      belong cc (Some (taga dd')) = false ->
      get_tni_color (Some (taga dd')) = Some comp' ->
      check_entry cc (Some (taga dd')) = Some tt ->
      get_proc_name (Some (taga dd')) = Some proc ->
      z = convert (int_of_word (vala a3)) ->
      comp = cc ->
      step_me (NC := NC) {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
        {| mem := mem (odflt {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                          (next_state_do_updates
                             {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                             ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
                              : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
                             (MemRead (pc3v + 1)%w :: RegWrite (as_word (ssrint.Posz 4)) (pc3v + 1)%w
                              :: reg_clear_read)));
           regs := regs (odflt {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                          (next_state_do_updates
                             {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                             ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
                              : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
                             (MemRead (pc3v + 1)%w :: RegWrite (as_word (ssrint.Posz 4)) (pc3v + 1)%w
                              :: reg_clear_read)));
           pc := (swcast imm')$(build_tpc cn.+1 comp');
           internal := internal (odflt {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                          (next_state_do_updates
                             {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
                             ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
                              : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
                             (MemRead (pc3v + 1)%w :: RegWrite (as_word (ssrint.Posz 4)) (pc3v + 1)%w
                              :: reg_clear_read))) |}
        (Some (ECall comp proc z comp')).
  Proof.
    move=> mem3 regs3 pc3v int3 cn cc i3 ti3 imm' vra3 tret vo to l3 a3 dd' comp proc z comp'
           Hpc3 Hra3 Hdec3 Hold3 Hl3 rd3 Hic Hcolor Hcolor_ra Ha3 Hta3 Hdd' Hbelf Htc Hce Hpn Hz Hcomp.
    subst comp.
    eapply step_jal.
    - reflexivity.
    - exact Hpc3.
    - exact Hra3.
    - exact Hdec3.
    - exact Hold3.
    - exact Hl3.
    - unfold next_state_updates_and_pc.
      rewrite Hdd'.
      unfold next_state. cbn [op].
      unfold evi, transfer, instr_rules, LRC.instr_rules.
      cbn -[obind belong is_other get_tni_color get_proc_name check_belong
            check_entry reg_invalidate_hseq next_state_do_updates getm setm
            build_tpc rcom_value reg_clear_read hsbehead hshead].
      rewrite Ha3 !obindE; cbn beta.
      rewrite Hic !obindE; cbn beta.
      have Hcolor' : (match ti3 with {| color := cx |} => cx end) = cc by exact Hcolor.
      rewrite Hcolor' (_ : eqn cc cc = true); last by apply/eqnP.
      cbn beta iota.
      rewrite obindE.
      have [a0' Ha0'] : exists a0', regs3 (as_word (ssrint.Posz 0)) = Some a0'.
      { move: Hl3; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha3 obindE
          reg_clear_list_aux_cons;
        case: (regs3 (as_word (ssrint.Posz 0))) => [a0'|] //= _; by exists a0'. }
      have [t0 [rest3 El3]] : exists t0 rest, l3 = HSeqCons t0 (HSeqCons (taga a3) rest).
      { move: Hl3; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha3 obindE
          reg_clear_list_aux_cons Ha0' obindE;
        case: (reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19] regs3 (taga a0'))
          => [rest|] //= [= <-]; by do 2 eexists. }
      rewrite El3; cbn beta iota.
      have COMM : forall (t : tag_type lrc_tags M) (d : Component.id),
          (match t with {| color := cx |} => d == cx end) = (d == color t)
        by move=> t d; case: t.
      rewrite (_ : check_belong cc (Some tret) = Some tt);
        last by rewrite /check_belong /belong COMM Hcolor_ra eqxx.
      cbn beta iota. rewrite obindE.
      rewrite Hbelf; cbn beta iota.
      rewrite (_ : is_other (taga a3) = Some tt); last by rewrite /is_other Hta3.
      cbn beta iota. rewrite obindE.
      rewrite Htc. cbn beta iota. rewrite obindE.
      rewrite (_ : check_entry cc (Some (taga dd')) = Some tt); last by exact Hce.
      cbn beta iota. rewrite Hpn.
      rewrite !obindE. cbn beta iota. cbn [tr trpc].
      have Hmemra : mem3 (pc3v + 1)%w <> None by rewrite Hra3.
      have Hreg4 : regs3 (as_word (ssrint.Posz 4)) <> None.
      { by rewrite (_ : regs3 (as_word (ssrint.Posz 4)) = Some (vo$to)); [|exact: Hold3]. }
      have [stf Hstf] : exists stf, next_state_do_updates
          {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
          ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
          (MemRead (pc3v + 1)%w :: RegWrite (as_word (ssrint.Posz 4)) (pc3v + 1)%w
           :: reg_clear_read) = Some stf.
      { apply: cross_do_updates_exists.
        - exact: Hmemra.
        - exact: Hreg4.
        - move=> n Hn.
          have Hin : as_word (ssrint.Posz n) \in domm regs3.
          { rewrite rd3 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
            by rewrite /word_of_nat. }
          have Hnn : regs3 (as_word (ssrint.Posz n)) <> None.
          { by move/dommP: Hin => [v ->]. }
          exact: Hnn. }
      rewrite Hstf obindE.
      cbn [snd]. rewrite Hz. cbn [rcom_value].
      have Hstf2 : odflt {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
          (next_state_do_updates
             {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |}
             ((tret :: Ret cn :: Other :: reg_invalidate_hseq)%hseq
              : hseq (tag_type lrc_tags) (M :: R :: nseq (size reg_list) R))
             (MemRead (pc3v + 1)%w :: RegWrite (as_word (ssrint.Posz 4)) (pc3v + 1)%w
              :: reg_clear_read)) = stf
        by rewrite Hstf.
      rewrite -Hstf2. reflexivity.
  Qed.

  Lemma secmr :
    forall s1 comp proc z comp' s1',
      step2 tt s1 ((ECall comp proc z comp') :: nil) s1' ->
    forall s2 s2',
      Step sem' s2 ((ECall comp proc z comp') :: nil) s2' ->
    forall s3 M0,
      common_equiv M0 s1 s2 s3 ->
      weak_equiv Left M0 s1 s3 ->
      strong_equiv Right M0 s2 s3 ->
      exists s3' M', Plus sem'' s3 ((ECall comp proc z comp') :: nil) s3' /\ match_states M' s1' s2' s3'.
  Proof.
    import_context.
    intros s1 comp proc z comp' s1' sme1 s2 s2' step_s2 s3 M0 common weak strong.
    simpl in step_s2.
    pose proof (call_step_inv step_s2) as Hs2.
    destruct Hs2 as (ip2 & imm2 & cell2 & Jracv2 & Ja1_2 & Hpc2 & Hdec2 & Hcell2 & Hpn2 & Htc2 & Hbel2 & Hcur2
         & Jrac2 & Jr1_2 & Jic_2 & Jcol_2 & Jcolra_2 & Joth_2 & Jce_2 & _).
    subst comp.
    cbn [step2] in sme1.
    pose proof (call_step_inv_mp sme1) as Hs1.
    destruct Hs1 as (ip1 & imm1 & cell1 & Hpc1 & Hdec1 & Hcell1 & Hpn1 & Htc1 & Hbel1 & Hcur1).
        cbn [step1] in step_s2.
        inversion step_s2; subst s2; simpl in Hpc2.
        all: rewrite Hpc2 in PC.
        all: try discriminate.   (* refutes syscall: Some ip2 = None *)
        all: injection PC as PCeq2.
        all: assert (Hvi2 : vala ip2 = i) by (rewrite PCeq2; reflexivity).
        all: rewrite Hvi2 in Hdec2.
        all: try (rewrite Hdec2 in INST; discriminate).  (* refutes the 8 non-JAL opcodes *)
        (* only the JAL case remains *)
        inversion strong as
          [ms2 ? ? same_pc2 color_eq2 side_eq2 s_mem2 s'_mem2 entry_off2 s_reg2 s'_reg2 mem_match2 reg_match2].
        inversion common as
          [mc ? ? ? cn cc tag_pc1 tag_pc2 tag_pc3 wfst rd1 rd2 rd3 gmc1 gmc2 gmc3 cap1 cap2 cap3 codeL codeR].
        destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
        destruct gmc2 as [mp2 [mp2' [cp2 [ae2 [bnz2 [end2 [col_mem2 [ecode2 cvo2]]]]]]]].
        inversion same_pc2 as [? ? Hpcv Hnone | ? ? vsp off_sp Hmem_sp eq_off Hpc_sp].
        { exfalso. case: Hnone => Hnone _. simpl in Hnone. rewrite Hpc2 in Hnone. discriminate. }
        (* extract s3's register facts into OUTER hypotheses (shared evars need outer terms) *)
        destruct (proj2 (reg_match2 ra (old$told)) OLD) as [[vo to] [Hdm3 Hold3]].
        destruct (reg_clear_list_total to rd3) as [l3 Hl3].
        (* derive s3's instruction at pc3v via codeR (combined_codes) *)
        simpl in tag_pc2; subst tpc0.    (* pc tag = Level cn cc, so pc color = cc *)
        rewrite PCeq2 in Hpc2.            (* Hpc2 : mem0 pc0 = Some (i$ti0) *)
        have Himm : imm2 = imm by congruence.
        have Hcelli : mem {| mem := mem0; regs := reg; pc := pc0$(Level cn cc); internal := extra |} pc'
                      = Some cell2.
        { rewrite Himm in Hcell2. exact Hcell2. }
        have [a1 Ha1] : exists a1, reg (as_word (ssrint.Posz 1)) = Some a1.
        { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons;
          case: (reg (as_word (ssrint.Posz 1))) => [a1|] //= _; by exists a1. }
        have Hic : is_code ti0 by move: Jic_2; rewrite PCeq2.
        have Hcolor : color ti0 = cc by move: Jcol_2; rewrite PCeq2.
        edestruct (codeR pc0 i ti0 off_sp cc) as [Xpc _].
        { rewrite /is_relevant_comp.
          have HCm := col_mem2 pc0 (i$ti0) Hpc2; cbn [taga] in HCm; rewrite Hcolor in HCm.
          case: HCm => [/In_in HCm | /In_in HCm];
            [ exfalso; move: side_eq2; rewrite /side_of HCm; by [] | exact: HCm ]. }
        { exact eq_off. }
        { exact Hic. }
        { exact Hcolor. }
        specialize (Xpc Hpc2) as [vpc3 [match_dec_pc mem_s3_pc]].
        (* decode_match: refute no-JAL (Hdec2) + alloc (Hcell2 vs ae1); keep the genuine JAL case *)
        inversion match_dec_pc as
          [Hnoj ? ? | Haj1 Haj2 | imm0 imm' dd dd' Hjd1 Hjd2 Hdd Hdd' Hcode_dd Htag_dd Hoff_dd].
        { exfalso; exact (Hnoj imm2 Hdec2). }
        { exfalso.
          have Himm2 : imm2 = word_of_nat alloc_label by congruence.
          move: Hcell2; rewrite Himm2 swcast_word_of_nat_alloc_label ae2; discriminate. }
        (* derive s3's next cell (RA) via a second code_left at pc0+1 *)
        assert (Hic_ra : is_code tret).
        { case: (end2 pc0 (i$ti0) Hpc2 Hic) => [Hhalt | [v' [Hmv' Hicv']]].
          - exfalso; move: Hhalt; have -> : vala (i$ti0) = i by []; rewrite INST; done.
          - have Hmv2 : mem0 (pc0 + 1)%w = Some v' by exact Hmv'.
            have Hv : v' = vret$tret by congruence.
            subst v'; exact Hicv'. }
        have Ejr : Jracv2 = vret$tret by have E := etrans (esym Jrac2) RA; case: E.
        have Hcolor_ra : color tret = cc.
        { move: Jcolra_2; rewrite Ejr PCeq2 /= => ->; exact Hcolor. }
        edestruct (codeR (pc0 + 1)%w vret tret off_sp cc) as [Xra _].
        { rewrite /is_relevant_comp.
          have HCm := col_mem2 (pc0 + 1)%w (vret$tret) RA; cbn [taga] in HCm; rewrite Hcolor_ra in HCm.
          case: HCm => [/In_in HCm | /In_in HCm];
            [ exfalso; move: side_eq2; rewrite /side_of HCm; by [] | exact: HCm ]. }
        { exact eq_off. }
        { exact Hic_ra. }
        { exact Hcolor_ra. }
        specialize (Xra RA) as [vra3 [match_dec_ra mem_s3_ra]].
        simpl in Hpc_sp.
        (* subst pc3t BEFORE eexists so [cc] (from [Level cn cc]) is in the [s3'] evar's scope. *)
        simpl in tag_pc3; subst pc3t.
        do 2 eexists. split.
        * have COLPROJ : forall (t : tag_type lrc_tags M),
              (match t with {| color := c |} => c end) = color t by move=> t; case: t.
          have Hcc2 : (let '_${| color := c |} := ip2 in c) = cc.
          { rewrite PCeq2; cbn iota; rewrite COLPROJ; exact Hcolor. }
          have Himm20 : imm2 = imm0 by congruence.
          have Hdd2 : mem0 (swcast imm0) = Some dd by exact Hdd.
          have Hc1d : cell2 = dd.
          { move: Hcell2 Hdd2; rewrite Himm20 => Hcc1 Hcc2'; congruence. }
          have Hcd : taga cell2 = taga dd' by rewrite Hc1d; exact Htag_dd.
          have Ea1 : Ja1_2 = a1 by have E := etrans (esym Jr1_2) Ha1; case: E.
          destruct (proj2 (reg_match2 (as_word (ssrint.Posz 1)) a1) Ha1) as [a3d [Hdm Hr3]].
          have Hoth2 : taga a1 = Other by rewrite -Ea1.
          have Hta3 : taga a3d = Other by rewrite -(data_match_taga Hdm); exact Hoth2.
          have Hva3 : vala a3d = vala a1 by rewrite (data_match_other_val Hoth2 Hdm).
          have Hz : z = convert (int_of_word (vala a3d)).
          { rewrite Hva3. exact: (call_step_z step_s2 Ha1). }
          eapply plus_one.
          eapply jal_cross_step3;
            [ rewrite Hpc_sp; exact mem_s3_pc
            | rewrite Hpc_sp;
              rewrite (eq_trans (esym (addwA pc0 (as_word off_sp) 1%w))
                        (eq_trans (f_equal (addw pc0) (addwC (as_word off_sp) 1%w))
                           (addwA pc0 1%w (as_word off_sp))));
              exact mem_s3_ra
            | exact Hjd2 | exact Hold3 | exact Hl3 | exact rd3 | exact Hic | exact Hcolor
            | exact Hcolor_ra | exact Hr3 | exact Hta3 | exact Hdd'
            | rewrite -Hcd -Hcc2; exact Hbel2 | rewrite -Hcd; exact Htc2
            | rewrite -Hcd -Hcc2; exact Jce_2 | rewrite -Hcd; exact Hpn2
            | exact Hz | exact Hcc2 ].
        * (* preserve the three-way match *)
          match goal with |- match_states ?M _ _ _ =>
            unify M (((vala (pc s1) + 1)%w$(Ret cn), (pc0 + 1)%w$(Ret cn),
                      (pc3v + 1)%w$(Ret cn), cc) :: M0) end.
          have Hcc : (let '_${| color := c0 |} := ip2 in c0) = cc.
          { rewrite PCeq2; exact: Hcolor. }
          rewrite ?Hcc.
          have Hcell3 : mem3 (pc3v + 1)%w = Some vra3$tret.
          { rewrite Hpc_sp (eq_trans (esym (addwA pc0 (as_word off_sp) 1%w))
              (eq_trans (f_equal (addw pc0) (addwC (as_word off_sp) 1%w))
                 (addwA pc0 1%w (as_word off_sp)))); exact: mem_s3_ra. }
          have Hreg4 : regs3 (as_word (ssrint.Posz 4)) <> None.
          { by rewrite (_ : regs3 (as_word (ssrint.Posz 4)) = Some (vo$to)); [|exact: Hold3]. }
          have [a3 Ha3] : exists a3, regs3 (as_word (ssrint.Posz 1)) = Some a3.
          { move: Hl3; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons;
            case: (regs3 (as_word (ssrint.Posz 1))) => [a3|] //= _; by exists a3. }
          have Hex3 : forall n, n \in reg_list -> regs3 (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm regs3.
            { rewrite rd3 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [rs3 [Hdu3 [Hr4_3 [Hr1_3 Hinv3]]]] :=
            cross_do_updates_props
              (st := {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |})
              (w := (pc3v + 1)%w) tret cn Hcell3 Ha3 Hreg4 Hex3.
          rewrite Hdu3 /=.
          (* --- now characterise s1' the same way, by reducing NEXT --- *)
          have COMM : forall (t : tag_type lrc_tags M) (d : Component.id),
              (match t with {| color := cx |} => d == cx end) = (d == color t)
            by move=> t d; case: t.
          have Hcolor'' : (match ti0 with {| color := cx |} => cx end) = cc by exact Hcolor.
          have [a0 Ha0] : exists a0, reg (as_word (ssrint.Posz 0)) = Some a0.
          { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha1 obindE
              reg_clear_list_aux_cons;
            case: (reg (as_word (ssrint.Posz 0))) => [a0|] //= _; by exists a0. }
          have [t0s [rests Els]] : exists t0 rest, l = HSeqCons t0 (HSeqCons (taga a1) rest).
          { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha1 obindE
              reg_clear_list_aux_cons Ha0 obindE;
            case: (reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19] reg (taga a0))
              => [rest|] //= [= <-]; by do 2 eexists. }
          have Hoth2 : taga a1 = Other.
          { have E := etrans (esym Jr1_2) Ha1. case: E => <-. exact Joth_2. }
          have Hce2 : check_entry cc (Some (taga cell2)) = Some tt by rewrite -Hcc; exact Jce_2.
          have HmemS2 : mem0 (pc0 + 1)%w = Some vret$tret by exact RA.
          have Hreg4S2 : reg (as_word (ssrint.Posz 4)) <> None.
          { by rewrite (_ : reg (as_word (ssrint.Posz 4)) = Some (old$told)); [|exact: OLD]. }
          have Hex2 : forall n, n \in reg_list -> reg (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm reg.
            { rewrite rd2 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [rs2 [Hdu2 [Hr4_2 [Hr1_2 Hinv2]]]] :=
            cross_do_updates_props
              (st := {| mem := mem0; regs := reg; pc := pc0$(Level cn cc); internal := extra |})
              (w := (pc0 + 1)%w) tret cn HmemS2 Ha1 Hreg4S2 Hex2.
          move: NEXT.
          rewrite /next_state_updates_and_pc Hcelli /next_state. cbn [op].
          unfold evi, transfer, instr_rules, LRC.instr_rules.
          cbn -[obind belong is_other get_tni_color get_proc_name check_belong check_entry
                reg_invalidate_hseq next_state_do_updates getm setm build_tpc rcom_value
                reg_clear_read hsbehead hshead].
          rewrite Ha1 !obindE. cbn beta. rewrite Hic !obindE. cbn beta.
          rewrite Hcolor'' (_ : eqn cc cc = true); last by apply/eqnP. cbn beta iota.
          rewrite obindE Els. cbn beta iota.
          rewrite (_ : check_belong cc (Some tret) = Some tt);
            last by rewrite /check_belong /belong COMM Hcolor_ra eqxx.
          cbn beta iota. rewrite obindE.
          rewrite (_ : belong cc (Some (taga cell2)) = false); last by rewrite -Hcc; exact Hbel2.
          cbn beta iota.
          rewrite (_ : is_other (taga a1) = Some tt); last by rewrite /is_other Hoth2.
          cbn beta iota. rewrite obindE. rewrite Htc2 obindE.
          rewrite (_ : check_entry cc (Some (taga cell2)) = Some tt); last by exact Hce2.
          cbn beta iota. rewrite Hpn2.
          rewrite !obindE. cbn beta iota. cbn [tr trpc].
          rewrite Hdu2 obindE. cbn [snd mem regs internal pc].
          move=> Hprem. injection Hprem as Hs2eq Hev2c Hev2z. rewrite -Hs2eq.
          (* both s1' and s3' are now explicit cross-updated states. *)
          (* --- reduce s2' from the raw step --- *)
          apply stepP in sme1.
          destruct s1 as [mem2 regs2 [pc2v pc2t] int2].
          destruct ip1 as [vip1 tip1].
          have Hdec1' : decode_instr vip1 = Some (Jal imm1) by exact: Hdec1.
          move: sme1. rewrite /stepf.
          cbn -[obind decode_instr next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          rewrite Hpc1.
          cbn -[obind decode_instr next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          rewrite Hdec1' obindE.
          cbn -[obind next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          move=> Hsf2.
          apply obind_inv in Hsf2 as [oldtold [Hold2 Hsf2]].
          destruct oldtold as [oldv2 told2].
          apply obind_inv in Hsf2 as [ret [Hret Hsf2]].
          apply obind_inv in Hsf2 as [l0 [Hl0 Hsf2]].
          (* Hsf2 = the NEXT-form for s2. *)
          have Hex1 : forall n, n \in reg_list -> regs2 (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm regs2.
            { rewrite rd1 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [a2 Ha2] : exists a, regs2 (as_word (ssrint.Posz 1)) = Some a.
          { case E: (regs2 (as_word (ssrint.Posz 1))) => [a|];
              [by exists a | by exfalso; apply: (Hex1 1%N)]. }
          have Hreg4S1 : regs2 (as_word (ssrint.Posz 4)) <> None by rewrite Hold2.
          have [rs1 [Hdu1 [Hr4_1 [Hr1_1 Hinv1]]]] :=
            cross_do_updates_props
              (st := {| mem := mem2; regs := regs2; pc := pc2v$pc2t; internal := int2 |})
              (w := (pc2v + 1)%w) (taga ret) cn Hret Ha2 Hreg4S1 Hex1.
          move: Hsf2.
          rewrite /next_state_updates_and_pc Hcell1 /next_state. cbn [op].
          unfold evi, transfer, LRC.transfer, instr_rules, LRC.instr_rules, LRC.instr_rules_mp.
          cbn -[obind belong is_other is_data get_tni_color get_proc_name check_belong check_entry
                reg_invalidate_hseq next_state_do_updates getm setm build_tpc rcom_value
                reg_clear_read hsbehead hshead].
          rewrite Ha2 !obindE. cbn beta.
          have Hpc1t : pc2t = Level cn cc by exact: tag_pc1.
          have Hcol1 : match tip1 with {| color := c |} => c end = cc by rewrite Hev2c.
          have Hbel1' : belong cc (Some (taga cell1)) = false by rewrite -Hcol1 Hcur1; exact: Hbel1.
          (* step_mp (LRC) has NO is_code gate: the first [do!] is the level check [cc == cc]. *)
          rewrite Hpc1t. cbn beta iota. rewrite Hcol1. cbn beta iota.
          rewrite (_ : eqn cc cc = true); last by apply/eqnP. cbn beta iota. rewrite obindE.
          clear Hl0. case: l0 => l0a l0rest. case: l0rest => trcom l0next. cbn beta iota.
          case Hcb1 : (check_belong cc (Some (taga ret))) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Hbel1'. cbn beta iota.
          case Hoth1 : (is_data trcom) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Htc1 obindE.
          case Hce1 : (check_entry cc (Some (taga cell1))) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Hpn1. rewrite !obindE. cbn beta iota. cbn [tr trpc].
          move: Hdu1; rewrite /reg_clear_read /reg_list Hpc1t; cbn [map]; move=> Hdu1.
          rewrite Hdu1 obindE. cbn [snd mem regs internal pc].
          move=> Hpr2. injection Hpr2 as Hs1eq Hev1c Hev1z. rewrite -Hs1eq.
          (* all three states s1'/s2'/s3' are now explicit; collapse the [setm]s via [setmI]. *)
          have ETA : forall (S : Type) (a : atom (mword mt) S), (vala a)$(taga a) = a
            by move=> S; case.
          rewrite (@setmI _ _ mem0); [|exact: RA].
          rewrite (ETA _ ret) (@setmI _ _ mem2); [|exact: Hret].
          rewrite (@setmI _ _ mem3); [|exact: Hcell3].
          (* [is_code (taga ret)] is NOT available here: in the UB case s1 (the context) runs data
             as a JAL, so the return cell need not be code.  The wf_stack push (via the LEFT branch
             of [points_to_comp_code']) and the s1 register-address-correctness (vacuous for [Left]
             since [color ret = cc \in ic]) both use [side_of cc = Right] instead of [is_code ret].
             The return cell's color is [cc] (via [Hcb1]). *)
          have Hcolret : color (taga ret) = cc.
          { move: Hcb1; rewrite /check_belong /belong.
            case: (taga ret) => vt ct et bt /=.
            case: ifP => // Hbel _. apply/eqP; rewrite eq_sym; exact: Hbel. }
          (* common_equiv is symmetric; prove it once (pinned metadata), then case on comp'. *)
          have Hic_rel : cc \in domm ic.
          { have HCm := col_mem2 pc0 (i$ti0) Hpc2; cbn [taga] in HCm; rewrite Hcolor in HCm.
            case: HCm => [/In_in HCm | /In_in HCm];
              [ exfalso; move: side_eq2; rewrite /side_of HCm; by [] | exact: HCm ]. }
          have Hsideret : side_of cc = Right.
          { rewrite /side_of; case: ifP => [Hcip|//]; exfalso.
            eapply Machine.Intermediate.fdisjoint_partition_notinboth;
              [ have [[_ fdisj] _] := Hmergeable_ifaces; exact: fdisj
              | exact: Hic_rel | exact: Hcip ]. }
          match goal with |- match_states _ ?S1 ?S2 ?S3 =>
            have HC : common_equiv
              (((pc2v + 1)%w$(Ret cn), (pc0 + 1)%w$(Ret cn), (pc3v + 1)%w$(Ret cn), cc) :: M0)
              S1 S2 S3 end.
          { eapply common_equiv_def;
              [ by rewrite /build_tpc                                  (* taga s1' *)
              | by rewrite /build_tpc                                  (* taga s2' *)
              | by rewrite /build_tpc                                  (* taga s3' *)
              | exact: (cross_wf_stack_right Hic_rel eq_off Hret RA Hcell3
                          Hcolor_ra Hic_ra Hcolret Hsideret Hpc_sp wfst) (* wf_stack *)
              | exact: (reg_domm_cross Hdu1 rd1)                       (* register_domm s1' *)
              | exact: (reg_domm_cross Hdu2 rd2)                       (* register_domm s2' *)
              | exact: (reg_domm_cross Hdu3 rd3)                       (* register_domm s3' *)
              | exact: gmc1                                            (* gmc s1' (weak, whole) *)
              | by repeat first [ exact: mp2 | exact: mp2' | exact: cp2 | exact: ae2
                  | exact: bnz2 | exact: end2 | exact: col_mem2 | exact: ecode2 | exact: cvo2 | split ]
              | exact: gmc3                                            (* gmc s3' *)
              | apply: cross_capability_S1;
                  [ exact: cap1 | exact: erefl | exact: wfst | exact: Hr4_1 | exact: Hr1_1
                  | exact: Hinv1 | exact: (reg_domm_cross Hdu1 rd1) ]    (* capability s1' *)
              | apply: cross_capability_S2;
                  [ exact: cap2 | exact: erefl | exact: wfst | exact: Hr4_2 | exact: Hr1_2
                  | exact: Hinv2 | exact: (reg_domm_cross Hdu2 rd2) ]    (* capability s2' *)
              | apply: cross_capability_S3;
                  [ exact: cap3 | exact: erefl | exact: wfst | exact: Hr4_3 | exact: Hr1_3
                  | exact: Hinv3 | exact: (reg_domm_cross Hdu3 rd3) ]    (* capability s3' *)
              | exact: codeL                                           (* combined_codes Left *)
              | exact: codeR                                           (* combined_codes Right *)
              | exact: (running_comp_valid_call col_mem2 Hcell2 Htc2) (* callee comp' valid *)
              | (match goal with |- pc_code_color ?st =>
                   apply: (pc_code_color_entry (s := st) (c := comp'));
                     [ exact: Hcell1 | exact: Htc1 | by [] ] end)
              | (match goal with |- pc_code_color ?st =>
                   apply: (pc_code_color_entry (s := st) (c := comp'));
                     [ exact: Hcelli | exact: Htc2 | by [] ] end) ]. }
          case Hside : (comp' \in domm ip).
          -- (* comp' Left → match_states_left (s1' strong: UPGRADE from weak1) *)
             eapply match_states_left.
             ++ exact: HC.
             ++ (* strong_equiv Left (s1', s3') -- UPGRADE from weak1 *)
                inversion weak as [mw sw sw' Hcolw Hsidw Hma1 Hma3 Heow Hmmw].
                have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                have Hva3 : vala a3 = vala a1.
                { destruct (proj2 (reg_match2 (as_word (ssrint.Posz 1)) a1) Ha1)
                    as [a3d [Hdm Hr3]].
                  have Hr3' : regs3 (as_word (ssrint.Posz 1)) = Some a3d by exact: Hr3.
                  have Ha3eq : a3d = a3 by move: Ha3; rewrite Hr3' => -[= ->]. subst a3d.
                  by rewrite (data_match_other_val Hoth2 Hdm). }
                have Hva23 : vala a2 = vala a3.
                { rewrite Hva3; apply: convert_int_of_word_inj.
                  move: Hev2z; cbn [rcom_value] => Hz1.
                  move: Hev1z; cbn [rcom_value] => Hz2. by rewrite Hz2 Hz1. }
                eapply strong_equiv_def.
                ** (* same_pc *)
                   have Himm0 : imm = imm0 by congruence.
                   have Hc2d : cell2 = dd.
                   { move: Hcell2 Hdd; rewrite Himm Himm0 => Hca Hcb; congruence. }
                   have Hcc2 : color (taga cell2) = comp'
                     by move: Htc2; rewrite /get_tni_color;
                        case: (taga cell2) => vt ct et bt /= [= ->].
                   have Hcdd' : color (taga dd') = comp' by rewrite -Htag_dd -Hc2d.
                   have Hcoddd' : is_code (taga dd') by rewrite -Htag_dd.
                   have [l2 He2] : exists l2, entry (taga cell2) = Some (proc, l2).
                   { move: Hpn2; rewrite /get_proc_name; case: (taga cell2) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   have He2'' : entry (taga dd') = Some (proc, l2) by rewrite -Htag_dd -Hc2d.
                   have Hcc1 : color (taga cell1) = comp'
                     by move: Htc1; rewrite /get_tni_color;
                        case: (taga cell1) => vt ct et bt /= [= ->].
                   have [l1 He1] : exists l1, entry (taga cell1) = Some (proc, l1).
                   { move: Hpn1; rewrite /get_proc_name; case: (taga cell1) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   (* the JAL target [cell1] is code via [entry_is_code] (it is a valid entry, [He1]);
                      this avoids needing [is_code (taga tip1)] (false in the UB case). *)
                   have Hcode1t : is_code (taga cell1).
                   { have ecode1 : entry_is_code mem2
                       by move: gmc1 => [_ [_ [_ [_ [_ [_ [_ [He _]]]]]]]]; exact: He.
                     exact: (ecode1 _ _ _ Hcell1 He1). }
                   have Hrel2 : comp' \in domm ip by exact: Hside.
                   have [off [Hoff Hwoff]] :=
                     Heow comp' (swcast imm1) (swcast imm') cell1 dd' proc l1 l2
                       Hrel2 Hcell1 Hdd' Hcode1t Hcoddd' Hcc1 Hcdd' He1 He2''.
                   unshelve eapply (same_pc_normal _ _ (v := cell1) (off := off));
                     cbn [color_of build_tpc];
                     first [ exact: Hoff | exact: Hwoff | (split; [exact: Hcell1 | exact: Hcode1t]) ].
                ** (* color_of *) by rewrite /color_of /build_tpc.
                ** (* side_of = Right *) by rewrite /side_of /color_of /build_tpc Hside.
                ** (* mem_addr s2' *) exact: Hma1.
                ** (* mem_addr s3' *) exact: Hma3.
                ** (* entry_offset *) exact: Heow.
                ** (* reg_addr s2' *)
                   move: (reg_domm_cross Hdu1 rd1) => Hdmm1.
                   move=> v r Hr. have Hrin : r \in domm rs1 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm1 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_1 => -[<-].
                     rewrite /address_correctness /=.
                     exists ret; split; first exact: Hret.
                     (* [color ret = cc \in ic] ⇒ [is_relevant_comp Left (color ret)] is false:
                        the [Ret]-tagged capability's address-correctness is vacuous on the [Left]. *)
                     move=> Hrel; rewrite Hcolret in Hrel; exfalso.
                     eapply Machine.Intermediate.fdisjoint_partition_notinboth;
                       [ have [[_ fdisj] _] := Hmergeable_ifaces; exact: fdisj
                       | exact: Hic_rel | exact: Hrel ]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_1 => -[<-]. by rewrite /address_correctness. }
                     { have [v2 Hv2] := Hinv1 n Hnr.
                       move: Hr; rewrite Hv2 => -[<-]. by rewrite /address_correctness. } }
                ** (* reg_addr s3' *)
                   move: (reg_domm_cross Hdu3 rd3) => Hdmm3.
                   move=> v r Hr. have Hrin : r \in domm rs3 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_3 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vra3$tret); split; [exact: Hcell3 | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_3 => -[<-]. by rewrite /address_correctness. }
                     { have [v3 Hv3] := Hinv3 n Hnr.
                       move: Hr; rewrite Hv3 => -[<-]. by rewrite /address_correctness. } }
                ** (* memory_match Right *)
                   have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                     data_match' Left M0 d1 d2 ->
                     data_match' Left (((pc2v+1)%w$(Ret cn), (pc0+1)%w$(Ret cn),
                                        (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                   { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                     move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                     by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                   move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                ** (* registers_match Right *)
                   move: (reg_domm_cross Hdu1 rd1) (reg_domm_cross Hdu3 rd3) => Hdmm1 Hdmm3.
                   move=> w d; split=> Hw.
                   { have Hwd : w \in domm rs3 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_3 => -[<-].
                       exists ((pc2v + 1)%w$(Ret cn)); split; last exact: Hr4_1.
                       rewrite /data_match; split=> //.
                       by exists ((pc0 + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_3 => -[<-].
                         exists ((vala a2)$Other); split; last exact: Hr1_1.
                         by rewrite /data_match; split=> //=; rewrite Hva23.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v2 Hv2] := Hinv1 n Hnr.
                         move: Hw; rewrite WA Hv3 => -[<-].
                         exists (v2$Invalidated); split; last exact: Hv2.
                         by rewrite /data_match; split. }
                   { have Hwd : w \in domm rs1 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm1 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_1 => -[<-].
                       exists ((pc3v + 1)%w$(Ret cn)); split; last exact: Hr4_3.
                       rewrite /data_match; split=> //.
                       by exists ((pc0 + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_1 => -[<-].
                         exists ((vala a3)$Other); split; last exact: Hr1_3.
                         by rewrite /data_match; split=> //=; rewrite Hva23.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v2 Hv2] := Hinv1 n Hnr.
                         move: Hw; rewrite WA Hv2 => -[<-].
                         exists (v3$Invalidated); split; last exact: Hv3.
                         by rewrite /data_match; split. }
             ++ (* weak_equiv Right (s2', s3') -- DOWNGRADE from strong2 *)
                have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                  data_match' Right M0 d1 d2 ->
                  data_match' Right (((pc2v+1)%w$(Ret cn), (pc0+1)%w$(Ret cn),
                                      (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                  move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                  by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                eapply weak_equiv_def.
                ** by rewrite /color_of /build_tpc.
                ** by rewrite /side_of /color_of /build_tpc Hside.
                ** exact: s_mem2.
                ** exact: s'_mem2.
                ** exact: entry_off2.
                ** move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (mem_match2 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (mem_match2 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
          -- (* comp' Right → match_states_right (s2' strong: preserve strong2) *)
             eapply match_states_right.
             ++ exact: HC.
             ++ (* weak_equiv Left (s1', s3') -- preserve weak1 *)
                have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                  data_match' Left M0 d1 d2 ->
                  data_match' Left (((pc2v+1)%w$(Ret cn), (pc0+1)%w$(Ret cn),
                                     (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                  move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                  by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                inversion weak as [mw sw sw' Hcolw Hsidw Hma1 Hma3 Heow Hmmw].
                eapply weak_equiv_def.
                ** by rewrite /color_of /build_tpc.
                ** by rewrite /side_of /color_of /build_tpc Hside.
                ** exact: Hma1.
                ** exact: Hma3.
                ** exact: Heow.
                ** move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
             ++ (* strong_equiv Right (s2', s3') -- preserve strong2 *)
                eapply strong_equiv_def.
                ** (* same_pc *)
                   have Himm0 : imm = imm0 by congruence.
                   have Hc1d : cell2 = dd.
                   { move: Hcell2 Hdd; rewrite Himm Himm0 => Hca Hcb; congruence. }
                   have Hcc2 : color (taga cell2) = comp'
                     by move: Htc2; rewrite /get_tni_color;
                        case: (taga cell2) => vt ct et bt /= [= ->].
                   have [l1 He1] : exists l1, entry (taga cell2) = Some (proc, l1).
                   { move: Hpn2; rewrite /get_proc_name; case: (taga cell2) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   have Hcdd : color (taga dd) = comp' by rewrite -Hc1d.
                   have Hcdd' : color (taga dd') = comp' by rewrite -Htag_dd.
                   have Hcoddd' : is_code (taga dd') by rewrite -Htag_dd.
                   have He1' : entry (taga dd) = Some (proc, l1) by rewrite -Hc1d.
                   have He1'' : entry (taga dd') = Some (proc, l1) by rewrite -Htag_dd.
                   have Hrel : is_relevant_comp Right comp'.
                   { rewrite /is_relevant_comp.
                     have HCm := col_mem2 _ cell2 Hcell2; rewrite Hcc2 in HCm.
                     case: HCm => [/In_in HCm | /In_in HCm];
                       [ by move: Hside; rewrite HCm | exact: HCm ]. }
                   have [off [Hoff Hwoff]] :=
                     entry_off2 comp' (swcast imm0) (swcast imm') dd dd' proc l1 l1
                       Hrel Hdd Hdd' Hcode_dd Hcoddd' Hcdd Hcdd' He1' He1''.
                   unshelve eapply (same_pc_normal _ _ (v := cell2) (off := off)); cbn [color_of build_tpc];
                     first [ exact: Hoff | (rewrite /pc' Himm0; exact: Hwoff)
                           | (split; [exact: Hcelli | rewrite Hc1d; exact: Hcode_dd]) ].
                ** (* color_of s1' = color_of s3' *) by rewrite /color_of /build_tpc.
                ** (* side_of (color_of s1') = Left *)
                   by rewrite /side_of /color_of /build_tpc Hside.
                ** (* mem_addr s1' *) exact: s_mem2.
                ** (* mem_addr s3' *) exact: s'_mem2.
                ** (* entry_offset *) exact: entry_off2.
                ** (* reg_addr s2' (the strong side) *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu2 rd2) => Hdmm2.
                   move=> v r Hr. have Hrin : r \in domm rs2 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm2 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_2 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vret$tret); split; [exact: RA | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_2 => -[<-]. by rewrite /address_correctness. }
                     { have [v1 Hv1] := Hinv2 n Hnr.
                       move: Hr; rewrite Hv1 => -[<-]. by rewrite /address_correctness. } }
                ** (* reg_addr s3' *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu3 rd3) => Hdmm3.
                   move=> v r Hr. have Hrin : r \in domm rs3 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_3 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vra3$tret); split; [exact: Hcell3 | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_3 => -[<-]. by rewrite /address_correctness. }
                     { have [v3 Hv3] := Hinv3 n Hnr.
                       move: Hr; rewrite Hv3 => -[<-]. by rewrite /address_correctness. } }
                ** (* memory_match *)
                   have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                     data_match' Right M0 d1 d2 ->
                     data_match' Right (((pc2v+1)%w$(Ret cn), (pc0+1)%w$(Ret cn),
                                        (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                   { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                     move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                     by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                   move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (mem_match2 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (mem_match2 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                ** (* registers_match *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu2 rd2) (reg_domm_cross Hdu3 rd3) => Hdmm2 Hdmm3.
                   destruct (proj2 (reg_match2 (as_word (ssrint.Posz 1)) a1) Ha1)
                     as [a3d [Hdm Hr3]].
                   have Hr3' : regs3 (as_word (ssrint.Posz 1)) = Some a3d by exact: Hr3.
                   have Ha3eq : a3d = a3 by congruence. subst a3d.
                   have Hva3 : vala a3 = vala a1 by rewrite (data_match_other_val Hoth2 Hdm).
                   move=> w d; split=> Hw.
                   { have Hwd : w \in domm rs3 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_3 => -[<-].
                       exists ((pc0 + 1)%w$(Ret cn)); split; last exact: Hr4_2.
                       rewrite /data_match; split=> //.
                       by exists ((pc2v + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_3 => -[<-].
                         exists ((vala a1)$Other); split; last exact: Hr1_2.
                         by rewrite /data_match; split=> //=; rewrite Hva3.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v1 Hv1] := Hinv2 n Hnr.
                         move: Hw; rewrite WA Hv3 => -[<-].
                         exists (v1$Invalidated); split; last exact: Hv1.
                         by rewrite /data_match; split. }
                   { have Hwd : w \in domm rs2 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm2 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_2 => -[<-].
                       exists ((pc3v + 1)%w$(Ret cn)); split; last exact: Hr4_3.
                       rewrite /data_match; split=> //.
                       by exists ((pc2v + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_2 => -[<-].
                         exists ((vala a3)$Other); split; last exact: Hr1_3.
                         by rewrite /data_match; split=> //=; rewrite Hva3.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v1 Hv1] := Hinv2 n Hnr.
                         move: Hw; rewrite WA Hv1 => -[<-].
                         exists (v3$Invalidated); split; last exact: Hv3.
                         by rewrite /data_match; split. }
  Qed.


  Lemma step_event_call:
  forall s1 comp proc z comp' s1', Step sem s1 ((ECall comp proc z comp') :: nil) s1' ->
  forall s2 s2',   Step sem' s2 ((ECall comp proc z comp') :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus sem'' s3 ((ECall comp proc z comp') :: nil) s3' /\
              match_states M' s1' s2' s3'.
  Proof.
    import_context.
    intros s1 comp proc z comp' s1' step_s1 s2 s2' step_s2 s3 M match_st.
    (* [step_s2] is raw [step_me] (sem' is unrestricted) — characterise directly. *)
    simpl in step_s2.
    pose proof (call_step_inv step_s2) as Hs2.
    destruct Hs2 as
      (ip2 & imm2 & cell2 & Jracv2 & Ja1_2 & Hpc2 & Hdec2 & Hcell2 & Hpn2 & Htc2 & Hbel2 & Hcur2
         & Jrac2 & Jr1_2 & Jic_2 & Jcol_2 & Jcolra_2 & Joth_2 & Jce_2 & _).
    (* [step_s1] is the 2-ctor UB-restricted Step; [inversion] substitutes the concrete trace
       index (so the underlying [step1] reduces to [step_me]). *)
    simpl in step_s1.
    inversion step_s1 as [? ? ? smp1 allowed1 | ? ? ? sme1 smp1]; subst.
    - (* UB-allowed: s1 (the Left/sem run) does allowed UB. *)
      unfold allowed_UB in allowed1.
      destruct match_st as [ ? ? ? ? common strong weak | ? ? ? ? common weak strong ].
      + (* match_left: s1 is strongly related (side = Left), but [allowed1] places it on the other
           side — contradicts the disjoint partition (cf. step_silent_strong1:93-99). *)
        exfalso.
        inversion strong as
          [m ? ? same_pc color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
        eapply Machine.Intermediate.fdisjoint_partition_notinboth;
          [ inversion Hmergeable_ifaces as [[_ fdisj] _]; exact fdisj
          | exact allowed1
          | unfold side_of in *; unfold_match' side_eq ].
      + (* match_right: s1 (the context) runs data as a JAL — UB-allowed, [smp1 : step_mp].  This is
           the genuine recomposition case; the LRC step feeds the SAME match_right helper [secmr] as
           the non-UB (UB-disallowed) case below (both provide a [step_mp]). *)
        apply: secmr;
          [ exact: smp1 | exact: step_s2 | exact: common | exact: weak | exact: strong ].
    - (* [sme1 : step1 tt s1 (ECall..::nil) s1' = step_me s1 s1' (Some (ECall ..))] *)
      pose proof (call_step_inv sme1) as Hs1.
      destruct Hs1 as
        (ip1 & imm1 & cell1 & Jracv1 & Ja1_1 & Hpc1 & Hdec1 & Hcell1 & Hpn1 & Htc1 & Hbel1 & Hcur1
         & Jrac1 & Jr1_1 & Jic_1 & Jcol_1 & Jcolra_1 & Joth_1 & Jce_1 & _).
      destruct match_st as [ ? ? ? ? common strong weak | ? ? ? ? common weak strong ].
      + (* match_left: s1 strongly related to s3 — build s3's JAL step and preserve. *)
        cbn [step1] in sme1.
        inversion sme1; subst s1; simpl in Hpc1.
        all: rewrite Hpc1 in PC.
        all: try discriminate.   (* refutes syscall: Some ip1 = None *)
        all: injection PC as PCeq.
        all: assert (Hvi : vala ip1 = i) by (rewrite PCeq; reflexivity).
        all: rewrite Hvi in Hdec1.
        all: try (rewrite Hdec1 in INST; discriminate).  (* refutes the 8 non-JAL opcodes *)
        (* only the JAL case remains *)
        inversion strong as
          [ms ? ? same_pc1 color_eq1 side_eq1 s_mem1 s'_mem1 entry_off1 s_reg1 s'_reg1 mem_match1 reg_match1].
        inversion common as
          [mc ? ? ? cn cc tag_pc1 tag_pc2 tag_pc3 wfst rd1 rd2 rd3 gmc1 gmc2 gmc3 cap1 cap2 cap3 codeL codeR].
        destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
        (* expose the code-structure invariants (col_mem1/end1) and the pc-offset *)
        destruct gmc1 as [mp1 [mp1' [cp1 [ae1 [bnz1 [end1 [col_mem1 [ecode1 cvo1]]]]]]]].
        inversion same_pc1 as [? ? Hpcv Hnone | ? ? vsp off_sp Hmem_sp eq_off Hpc_sp].
        { exfalso. case: Hnone => Hnone _. simpl in Hnone. rewrite Hpc1 in Hnone. discriminate. }
        (* extract s3's register facts into OUTER hypotheses (shared evars need outer terms) *)
        destruct (proj2 (reg_match1 ra (old$told)) OLD) as [[vo to] [Hdm3 Hold3]].
        destruct (reg_clear_list_total to rd3) as [l3 Hl3].
        (* derive s3's instruction at pc3v via codeL (combined_codes) *)
        simpl in tag_pc1; subst tpc0.    (* pc tag = Level cn cc, so pc color = cc *)
        rewrite PCeq in Hpc1.            (* Hpc1 : mem0 pc0 = Some (i$ti0) *)
        have Himm : imm1 = imm by congruence.
        have Hcelli : mem {| mem := mem0; regs := reg; pc := pc0$(Level cn cc); internal := extra |} pc'
                      = Some cell1.
        { rewrite Himm in Hcell1. exact Hcell1. }
        have [a1 Ha1] : exists a1, reg (as_word (ssrint.Posz 1)) = Some a1.
        { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons;
          case: (reg (as_word (ssrint.Posz 1))) => [a1|] //= _; by exists a1. }
        have Hic : is_code ti0 by move: Jic_1; rewrite PCeq.
        have Hcolor : color ti0 = cc by move: Jcol_1; rewrite PCeq.
        edestruct (codeL pc0 i ti0 off_sp cc) as [Xpc _].
        { unfold is_relevant_comp; move: side_eq1; unfold side_of; simpl;
          case: (cc \in domm ip) => //=. }
        { exact eq_off. }
        { exact Hic. }
        { exact Hcolor. }
        specialize (Xpc Hpc1) as [vpc3 [match_dec_pc mem_s3_pc]].
        (* decode_match: refute no-JAL (Hdec1) + alloc (Hcell1 vs ae1); keep the genuine JAL case *)
        inversion match_dec_pc as
          [Hnoj ? ? | Haj1 Haj2 | imm0 imm' dd dd' Hjd1 Hjd2 Hdd Hdd' Hcode_dd Htag_dd Hoff_dd].
        { exfalso; exact (Hnoj imm1 Hdec1). }
        { exfalso.
          have Himm1 : imm1 = word_of_nat alloc_label by congruence.
          move: Hcell1; rewrite Himm1 swcast_word_of_nat_alloc_label ae1; discriminate. }
        (* derive s3's next cell (RA) via a second code_left at pc0+1 *)
        assert (Hic_ra : is_code tret).
        { case: (end1 pc0 (i$ti0) Hpc1 Hic) => [Hhalt | [v' [Hmv' Hicv']]].
          - exfalso; move: Hhalt; have -> : vala (i$ti0) = i by []; rewrite INST; done.
          - have Hmv2 : mem0 (pc0 + 1)%w = Some v' by exact Hmv'.
            have Hv : v' = vret$tret by congruence.
            subst v'; exact Hicv'. }
        have Ejr : Jracv1 = vret$tret by have E := etrans (esym Jrac1) RA; case: E.
        have Hcolor_ra : color tret = cc.
        { move: Jcolra_1; rewrite Ejr -Hcur1 PCeq /= => ->; exact Hcolor. }
        edestruct (codeL (pc0 + 1)%w vret tret off_sp cc) as [Xra _].
        { unfold is_relevant_comp; move: side_eq1; unfold side_of; simpl; case: (cc \in domm ip) => //=. }
        { exact eq_off. }
        { exact Hic_ra. }
        { exact Hcolor_ra. }
        specialize (Xra RA) as [vra3 [match_dec_ra mem_s3_ra]].
        simpl in Hpc_sp.
        (* subst pc3t BEFORE eexists so [cc] (from [Level cn cc]) is in the [s3'] evar's scope. *)
        simpl in tag_pc3; subst pc3t.
        do 2 eexists. split.
        * have COLPROJ : forall (t : tag_type lrc_tags M),
              (match t with {| color := c |} => c end) = color t by move=> t; case: t.
          have Hcc2 : (let '_${| color := c |} := ip2 in c) = cc.
          { rewrite -Hcur1 PCeq; cbn iota; rewrite COLPROJ; exact Hcolor. }
          have Himm10 : imm1 = imm0 by congruence.
          have Hdd2 : mem0 (swcast imm0) = Some dd by exact Hdd.
          have Hc1d : cell1 = dd.
          { move: Hcell1 Hdd2; rewrite Himm10 => Hcc1 Hcc2'; congruence. }
          have Hcd : taga cell1 = taga dd' by rewrite Hc1d; exact Htag_dd.
          have Ea1 : Ja1_1 = a1 by have E := etrans (esym Jr1_1) Ha1; case: E.
          destruct (proj2 (reg_match1 (as_word (ssrint.Posz 1)) a1) Ha1) as [a3d [Hdm Hr3]].
          have Hoth1 : taga a1 = Other by rewrite -Ea1.
          have Hta3 : taga a3d = Other by rewrite -(data_match_taga Hdm); exact Hoth1.
          have Hva3 : vala a3d = vala a1 by rewrite (data_match_other_val Hoth1 Hdm).
          have Hz : z = convert (int_of_word (vala a3d)).
          { rewrite Hva3. exact: (call_step_z sme1 Ha1). }
          eapply plus_one.
          eapply jal_cross_step3;
            [ rewrite Hpc_sp; exact mem_s3_pc
            | rewrite Hpc_sp;
              rewrite (eq_trans (esym (addwA pc0 (as_word off_sp) 1%w))
                        (eq_trans (f_equal (addw pc0) (addwC (as_word off_sp) 1%w))
                           (addwA pc0 1%w (as_word off_sp))));
              exact mem_s3_ra
            | exact Hjd2 | exact Hold3 | exact Hl3 | exact rd3 | exact Hic | exact Hcolor
            | exact Hcolor_ra | exact Hr3 | exact Hta3 | exact Hdd'
            | rewrite -Hcd -Hcc2; exact Hbel1 | rewrite -Hcd; exact Htc1
            | rewrite -Hcd -Hcc2; exact Jce_1 | rewrite -Hcd; exact Hpn1
            | exact Hz | exact Hcc2 ].
        * (* preserve the three-way match *)
          (* Pin the metadata evar ?M' NOW, while s2 is still abstract: ?M' was created at
             [do 2 eexists] (before this bullet), so a frame mentioning [pc2v] (introduced later by
             [destruct s2]) would escape its scope.  Use [vala (pc s2)] — it becomes [pc2v] after
             the destruct, matching the wf_stack frame. *)
          match goal with |- match_states ?M _ _ _ =>
            unify M (((pc0 + 1)%w$(Ret cn), (vala (pc s2) + 1)%w$(Ret cn),
                      (pc3v + 1)%w$(Ret cn), cc) :: M0) end.
          have Hcc : (let '_${| color := c0 |} := ip2 in c0) = cc.
          { rewrite -Hcur1 PCeq; exact: Hcolor. }
          rewrite ?Hcc.
          have Hcell3 : mem3 (pc3v + 1)%w = Some vra3$tret.
          { rewrite Hpc_sp (eq_trans (esym (addwA pc0 (as_word off_sp) 1%w))
              (eq_trans (f_equal (addw pc0) (addwC (as_word off_sp) 1%w))
                 (addwA pc0 1%w (as_word off_sp)))); exact: mem_s3_ra. }
          have Hreg4 : regs3 (as_word (ssrint.Posz 4)) <> None.
          { by rewrite (_ : regs3 (as_word (ssrint.Posz 4)) = Some (vo$to)); [|exact: Hold3]. }
          have [a3 Ha3] : exists a3, regs3 (as_word (ssrint.Posz 1)) = Some a3.
          { move: Hl3; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons;
            case: (regs3 (as_word (ssrint.Posz 1))) => [a3|] //= _; by exists a3. }
          have Hex3 : forall n, n \in reg_list -> regs3 (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm regs3.
            { rewrite rd3 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [rs3 [Hdu3 [Hr4_3 [Hr1_3 Hinv3]]]] :=
            cross_do_updates_props
              (st := {| mem := mem3; regs := regs3; pc := pc3v$(Level cn cc); internal := int3 |})
              (w := (pc3v + 1)%w) tret cn Hcell3 Ha3 Hreg4 Hex3.
          rewrite Hdu3 /=.
          (* s3' is now the explicit cross-updated state; rs3 reads: r4=(pc3v+1)@Ret cn,
             r1=(vala a3)@Other (Hr4_3/Hr1_3), the rest @Invalidated (Hinv3). *)
          (* --- now characterise s1' the same way, by reducing NEXT --- *)
          have COMM : forall (t : tag_type lrc_tags M) (d : Component.id),
              (match t with {| color := cx |} => d == cx end) = (d == color t)
            by move=> t d; case: t.
          have Hcolor'' : (match ti0 with {| color := cx |} => cx end) = cc by exact Hcolor.
          have [a0 Ha0] : exists a0, reg (as_word (ssrint.Posz 0)) = Some a0.
          { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha1 obindE
              reg_clear_list_aux_cons;
            case: (reg (as_word (ssrint.Posz 0))) => [a0|] //= _; by exists a0. }
          have [t0s [rests Els]] : exists t0 rest, l = HSeqCons t0 (HSeqCons (taga a1) rest).
          { move: CLEAR; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Ha1 obindE
              reg_clear_list_aux_cons Ha0 obindE;
            case: (reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19] reg (taga a0))
              => [rest|] //= [= <-]; by do 2 eexists. }
          have Hoth1 : taga a1 = Other.
          { have E := etrans (esym Jr1_1) Ha1. case: E => <-. exact Joth_1. }
          have Hce1 : check_entry cc (Some (taga cell1)) = Some tt by rewrite -Hcc; exact Jce_1.
          have HmemS1 : mem0 (pc0 + 1)%w = Some vret$tret by exact RA.
          have Hreg4S1 : reg (as_word (ssrint.Posz 4)) <> None.
          { by rewrite (_ : reg (as_word (ssrint.Posz 4)) = Some (old$told)); [|exact: OLD]. }
          have Hex1 : forall n, n \in reg_list -> reg (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm reg.
            { rewrite rd1 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [rs1 [Hdu1 [Hr4_1 [Hr1_1 Hinv1]]]] :=
            cross_do_updates_props
              (st := {| mem := mem0; regs := reg; pc := pc0$(Level cn cc); internal := extra |})
              (w := (pc0 + 1)%w) tret cn HmemS1 Ha1 Hreg4S1 Hex1.
          move: NEXT.
          rewrite /next_state_updates_and_pc Hcelli /next_state. cbn [op].
          unfold evi, transfer, instr_rules, LRC.instr_rules.
          cbn -[obind belong is_other get_tni_color get_proc_name check_belong check_entry
                reg_invalidate_hseq next_state_do_updates getm setm build_tpc rcom_value
                reg_clear_read hsbehead hshead].
          rewrite Ha1 !obindE. cbn beta. rewrite Hic !obindE. cbn beta.
          rewrite Hcolor'' (_ : eqn cc cc = true); last by apply/eqnP. cbn beta iota.
          rewrite obindE Els. cbn beta iota.
          rewrite (_ : check_belong cc (Some tret) = Some tt);
            last by rewrite /check_belong /belong COMM Hcolor_ra eqxx.
          cbn beta iota. rewrite obindE.
          rewrite (_ : belong cc (Some (taga cell1)) = false); last by rewrite -Hcc; exact Hbel1.
          cbn beta iota.
          rewrite (_ : is_other (taga a1) = Some tt); last by rewrite /is_other Hoth1.
          cbn beta iota. rewrite obindE. rewrite Htc1 obindE.
          rewrite (_ : check_entry cc (Some (taga cell1)) = Some tt); last by exact Hce1.
          cbn beta iota. rewrite Hpn1.
          rewrite !obindE. cbn beta iota. cbn [tr trpc].
          rewrite Hdu1 obindE. cbn [snd mem regs internal pc].
          move=> Hprem. injection Hprem as Hs1eq Hev1c Hev1z. rewrite -Hs1eq.
          (* both s1' and s3' are now explicit cross-updated states. *)
          (* --- reduce s2' from the raw step --- *)
          apply stepP in step_s2.
          destruct s2 as [mem2 regs2 [pc2v pc2t] int2].
          destruct ip2 as [vip2 tip2].
          have Hdec2' : decode_instr vip2 = Some (Jal imm2) by exact: Hdec2.
          move: step_s2. rewrite /stepf.
          cbn -[obind decode_instr next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          rewrite Hpc2.
          cbn -[obind decode_instr next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          rewrite Hdec2' obindE.
          cbn -[obind next_state_updates next_state_updates_and_pc
                as_word word_of_nat setm getm].
          move=> Hsf2.
          apply obind_inv in Hsf2 as [oldtold [Hold2 Hsf2]].
          destruct oldtold as [oldv2 told2].
          apply obind_inv in Hsf2 as [ret [Hret Hsf2]].
          apply obind_inv in Hsf2 as [l0 [Hl0 Hsf2]].
          (* Hsf2 = the NEXT-form for s2. *)
          have Hex2 : forall n, n \in reg_list -> regs2 (as_word (ssrint.Posz n)) <> None.
          { move=> n Hn. have Hin : as_word (ssrint.Posz n) \in domm regs2.
            { rewrite rd2 in_fset in_cons; apply/orP; right; apply/mapP; exists n => //;
              by rewrite /word_of_nat. }
            by move/dommP: Hin => [v ->]. }
          have [a2 Ha2] : exists a, regs2 (as_word (ssrint.Posz 1)) = Some a.
          { case E: (regs2 (as_word (ssrint.Posz 1))) => [a|];
              [by exists a | by exfalso; apply: (Hex2 1%N)]. }
          have Hreg4S2 : regs2 (as_word (ssrint.Posz 4)) <> None by rewrite Hold2.
          have [rs2 [Hdu2 [Hr4_2 [Hr1_2 Hinv2]]]] :=
            cross_do_updates_props
              (st := {| mem := mem2; regs := regs2; pc := pc2v$pc2t; internal := int2 |})
              (w := (pc2v + 1)%w) (taga ret) cn Hret Ha2 Hreg4S2 Hex2.
          move: Hsf2.
          rewrite /next_state_updates_and_pc Hcell2 /next_state. cbn [op].
          unfold evi, transfer, instr_rules, LRC.instr_rules.
          cbn -[obind belong is_other get_tni_color get_proc_name check_belong check_entry
                reg_invalidate_hseq next_state_do_updates getm setm build_tpc rcom_value
                reg_clear_read hsbehead hshead].
          rewrite Ha2 !obindE. cbn beta.
          have Hpc2t : pc2t = Level cn cc by exact: tag_pc2.
          have Hcol2 : match tip2 with {| color := c |} => c end = cc by exact: Hcc.
          have Hbel2' : belong cc (Some (taga cell2)) = false by rewrite -Hcol2; exact: Hbel2.
          rewrite Hpc2t. cbn beta iota. rewrite Hcol2.
          case Hcode2 : (is_code tip2); last by [].
          cbn beta iota. rewrite obindE.
          rewrite (_ : eqn cc cc = true); last by apply/eqnP. cbn beta iota. rewrite obindE.
          clear Hl0. case: l0 => l0a l0rest. case: l0rest => trcom l0next. cbn beta iota.
          case Hcb2 : (check_belong cc (Some (taga ret))) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Hbel2'. cbn beta iota.
          case Hoth2 : (is_other trcom) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Htc2 obindE.
          case Hce2 : (check_entry cc (Some (taga cell2))) => [[]|]; last by [].
          cbn beta iota. rewrite obindE Hpn2. rewrite !obindE. cbn beta iota. cbn [tr trpc].
          move: Hdu2; rewrite /reg_clear_read /reg_list Hpc2t; cbn [map]; move=> Hdu2.
          rewrite Hdu2 obindE. cbn [snd mem regs internal pc].
          move=> Hpr2. injection Hpr2 as Hs2eq Hev2. rewrite -Hs2eq.
          (* all three states s1'/s2'/s3' are now explicit cross-updated states.
             The cross-call's MemRead writes the return cell back UNCHANGED, so the memories are
             identical to the originals: collapse the [setm]s via [setmI]. *)
          have ETA : forall (S : Type) (a : atom (mword mt) S), (vala a)$(taga a) = a
            by move=> S; case.
          rewrite (@setmI _ _ mem0); [|exact: RA].
          rewrite (ETA _ ret) (@setmI _ _ mem2); [|exact: Hret].
          rewrite (@setmI _ _ mem3); [|exact: Hcell3].
          (* the s2 return cell is code (via [end_condition]); its color is [cc] (via [Hcb2]).
             Both are needed by [wf_stack]'s PTS_CODE2 and the comp'-Right [reg_addr]. *)
          have Hcoret : is_code (taga ret).
          { have end_s2 : end_condition mem2
              by move: gmc2 => [_ [_ [_ [_ [_ [Hec _]]]]]]; exact: Hec.
            move: (end_s2 pc2v (vip2$tip2) Hpc2 Hcode2); cbn [vala]; rewrite Hdec2'.
            move=> [[] | [v' [Hv' Hcv']]].
            have Hvr : Some v' = Some ret; first (rewrite -Hv' -Hret; exact: erefl).
            move: Hvr => [= <-]; exact: Hcv'. }
          have Hcolret : color (taga ret) = cc.
          { move: Hcb2; rewrite /check_belong /belong.
            case: (taga ret) => vt ct et bt /=.
            case: ifP => // Hbel _. apply/eqP; rewrite eq_sym; exact: Hbel. }
          (* [common_equiv] is symmetric; prove it once with the (now pinned) metadata, then case
             on the called component's side for the strong/weak halves. *)
          match goal with |- match_states _ ?S1 ?S2 ?S3 =>
            have HC : common_equiv
              (((pc0 + 1)%w$(Ret cn), (pc2v + 1)%w$(Ret cn), (pc3v + 1)%w$(Ret cn), cc) :: M0)
              S1 S2 S3 end.
          { eapply common_equiv_def;
              [ by rewrite /build_tpc                                  (* taga s1' *)
              | by rewrite /build_tpc                                  (* taga s2' *)
              | by rewrite /build_tpc                                  (* taga s3' *)
              | exact: (cross_wf_stack side_eq1 eq_off RA Hret Hcell3
                          Hcolor_ra Hic_ra Hcolret Hcoret Hpc_sp wfst) (* wf_stack *)
              | exact: (reg_domm_cross Hdu1 rd1)                       (* register_domm s1' *)
              | exact: (reg_domm_cross Hdu2 rd2)                       (* register_domm s2' *)
              | exact: (reg_domm_cross Hdu3 rd3)                       (* register_domm s3' *)
              | by repeat first [ exact: mp1 | exact: mp1' | exact: cp1 | exact: ae1
                  | exact: bnz1 | exact: end1 | exact: col_mem1 | exact: ecode1 | exact: cvo1 | split ]
              | exact: gmc2                                            (* gmc s2' *)
              | exact: gmc3                                            (* gmc s3' *)
              | apply: cross_capability_S1;
                  [ exact: cap1 | exact: erefl | exact: wfst | exact: Hr4_1 | exact: Hr1_1
                  | exact: Hinv1 | exact: (reg_domm_cross Hdu1 rd1) ]    (* capability s1' *)
              | apply: cross_capability_S2;
                  [ exact: cap2 | exact: erefl | exact: wfst | exact: Hr4_2 | exact: Hr1_2
                  | exact: Hinv2 | exact: (reg_domm_cross Hdu2 rd2) ]    (* capability s2' *)
              | apply: cross_capability_S3;
                  [ exact: cap3 | exact: erefl | exact: wfst | exact: Hr4_3 | exact: Hr1_3
                  | exact: Hinv3 | exact: (reg_domm_cross Hdu3 rd3) ]    (* capability s3' *)
              | exact: codeL                                           (* combined_codes Left *)
              | exact: codeR                                           (* combined_codes Right *)
              | exact: (running_comp_valid_call col_mem1 Hcell1 Htc1) (* callee comp' valid *)
              | (match goal with |- pc_code_color ?st =>
                   apply: (pc_code_color_entry (s := st) (c := comp'));
                     [ exact: Hcelli | exact: Htc1 | by [] ] end)
              | (match goal with |- pc_code_color ?st =>
                   apply: (pc_code_color_entry (s := st) (c := comp'));
                     [ exact: Hcell2 | exact: Htc2 | by [] ] end) ]. }
          case Hside : (comp' \in domm ip).
          -- (* comp' Left → match_left (s1' strong) *)
             eapply match_states_left.
             ++ exact: HC.
             ++ (* strong_equiv Left (s1', s3') *)
                eapply strong_equiv_def.
                ** (* same_pc *)
                   have Himm0 : imm = imm0 by congruence.
                   have Hc1d : cell1 = dd.
                   { move: Hcell1 Hdd; rewrite Himm Himm0 => Hca Hcb; congruence. }
                   have Hcc1 : color (taga cell1) = comp'
                     by move: Htc1; rewrite /get_tni_color;
                        case: (taga cell1) => vt ct et bt /= [= ->].
                   have [l1 He1] : exists l1, entry (taga cell1) = Some (proc, l1).
                   { move: Hpn1; rewrite /get_proc_name; case: (taga cell1) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   have Hcdd : color (taga dd) = comp' by rewrite -Hc1d.
                   have Hcdd' : color (taga dd') = comp' by rewrite -Htag_dd.
                   have Hcoddd' : is_code (taga dd') by rewrite -Htag_dd.
                   have He1' : entry (taga dd) = Some (proc, l1) by rewrite -Hc1d.
                   have He1'' : entry (taga dd') = Some (proc, l1) by rewrite -Htag_dd.
                   have Hrel : is_relevant_comp Left comp'
                     by rewrite /is_relevant_comp; exact: Hside.
                   have [off [Hoff Hwoff]] :=
                     entry_off1 comp' (swcast imm0) (swcast imm') dd dd' proc l1 l1
                       Hrel Hdd Hdd' Hcode_dd Hcoddd' Hcdd Hcdd' He1' He1''.
                   unshelve eapply (same_pc_normal _ _ (v := cell1) (off := off)); cbn [color_of build_tpc];
                     first [ exact: Hoff | (rewrite /pc' Himm0; exact: Hwoff)
                           | (split; [exact: Hcelli | rewrite Hc1d; exact: Hcode_dd]) ].
                ** (* color_of s1' = color_of s3' *) by rewrite /color_of /build_tpc.
                ** (* side_of (color_of s1') = Left *)
                   by rewrite /side_of /color_of /build_tpc Hside.
                ** (* mem_addr s1' *) exact: s_mem1.
                ** (* mem_addr s3' *) exact: s'_mem1.
                ** (* entry_offset *) exact: entry_off1.
                ** (* reg_addr s1' *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu1 rd1) => Hdmm1.
                   move=> v r Hr. have Hrin : r \in domm rs1 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm1 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_1 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vret$tret); split; [exact: RA | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_1 => -[<-]. by rewrite /address_correctness. }
                     { have [v1 Hv1] := Hinv1 n Hnr.
                       move: Hr; rewrite Hv1 => -[<-]. by rewrite /address_correctness. } }
                ** (* reg_addr s3' *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu3 rd3) => Hdmm3.
                   move=> v r Hr. have Hrin : r \in domm rs3 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_3 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vra3$tret); split; [exact: Hcell3 | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_3 => -[<-]. by rewrite /address_correctness. }
                     { have [v3 Hv3] := Hinv3 n Hnr.
                       move: Hr; rewrite Hv3 => -[<-]. by rewrite /address_correctness. } }
                ** (* memory_match *)
                   have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                     data_match' Left M0 d1 d2 ->
                     data_match' Left (((pc0+1)%w$(Ret cn), (pc2v+1)%w$(Ret cn),
                                        (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                   { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                     move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                     by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                   move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (mem_match1 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (mem_match1 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                ** (* registers_match *)
                   have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                   move: (reg_domm_cross Hdu1 rd1) (reg_domm_cross Hdu3 rd3) => Hdmm1 Hdmm3.
                   destruct (proj2 (reg_match1 (as_word (ssrint.Posz 1)) a1) Ha1)
                     as [a3d [Hdm Hr3]].
                   have Hr3' : regs3 (as_word (ssrint.Posz 1)) = Some a3d by exact: Hr3.
                   have Ha3eq : a3d = a3 by congruence. subst a3d.
                   have Hva3 : vala a3 = vala a1 by rewrite (data_match_other_val Hoth1 Hdm).
                   move=> w d; split=> Hw.
                   { have Hwd : w \in domm rs3 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_3 => -[<-].
                       exists ((pc0 + 1)%w$(Ret cn)); split; last exact: Hr4_1.
                       rewrite /data_match; split=> //.
                       by exists ((pc2v + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_3 => -[<-].
                         exists ((vala a1)$Other); split; last exact: Hr1_1.
                         by rewrite /data_match; split=> //=; rewrite Hva3.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v1 Hv1] := Hinv1 n Hnr.
                         move: Hw; rewrite WA Hv3 => -[<-].
                         exists (v1$Invalidated); split; last exact: Hv1.
                         by rewrite /data_match; split. }
                   { have Hwd : w \in domm rs1 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm1 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_1 => -[<-].
                       exists ((pc3v + 1)%w$(Ret cn)); split; last exact: Hr4_3.
                       rewrite /data_match; split=> //.
                       by exists ((pc2v + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_1 => -[<-].
                         exists ((vala a3)$Other); split; last exact: Hr1_3.
                         by rewrite /data_match; split=> //=; rewrite Hva3.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v1 Hv1] := Hinv1 n Hnr.
                         move: Hw; rewrite WA Hv1 => -[<-].
                         exists (v3$Invalidated); split; last exact: Hv3.
                         by rewrite /data_match; split. }
             ++ (* weak_equiv Right (s2', s3') *)
                have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                  data_match' Right M0 d1 d2 ->
                  data_match' Right (((pc0+1)%w$(Ret cn), (pc2v+1)%w$(Ret cn),
                                      (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                  move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                  by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                inversion weak as [mw sw sw' Hcolw Hsidw Hma2 Hma3 Heow Hmmw].
                eapply weak_equiv_def.
                ** by rewrite /color_of /build_tpc.
                ** by rewrite /side_of /color_of /build_tpc Hside.
                ** exact: Hma2.
                ** exact: Hma3.
                ** exact: Heow.
                ** move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
          -- (* comp' Right → match_right (s2' strong) *)
             eapply match_states_right.
             ++ exact: HC.
             ++ (* weak_equiv Left (s1', s3') *)
                have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                  data_match' Left M0 d1 d2 ->
                  data_match' Left (((pc0+1)%w$(Ret cn), (pc2v+1)%w$(Ret cn),
                                     (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                  move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                  by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                eapply weak_equiv_def.
                ** by rewrite /color_of /build_tpc.
                ** by rewrite /side_of /color_of /build_tpc Hside.
                ** exact: s_mem1.
                ** exact: s'_mem1.
                ** exact: entry_off1.
                ** move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (mem_match1 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (mem_match1 w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
             ++ (* strong_equiv Right (s2', s3') *)
                inversion weak as [mw sw sw' Hcolw Hsidw Hma2 Hma3 Heow Hmmw].
                have WA : forall m : nat, word_of_nat m = as_word (ssrint.Posz m) by [].
                have Hva3 : vala a3 = vala a1.
                { destruct (proj2 (reg_match1 (as_word (ssrint.Posz 1)) a1) Ha1)
                    as [a3d [Hdm Hr3]].
                  have Hr3' : regs3 (as_word (ssrint.Posz 1)) = Some a3d by exact: Hr3.
                  have Ha3eq : a3d = a3 by move: Ha3; rewrite Hr3' => -[= ->]. subst a3d.
                  by rewrite (data_match_other_val Hoth1 Hdm). }
                have Hva23 : vala a2 = vala a3.
                { rewrite Hva3; apply: convert_int_of_word_inj.
                  move: Hev1z; cbn [rcom_value] => Hz1. by rewrite Hev2 Hz1. }
                eapply strong_equiv_def.
                ** (* same_pc *)
                   have Himm0 : imm = imm0 by congruence.
                   have Hc1d : cell1 = dd.
                   { move: Hcell1 Hdd; rewrite Himm Himm0 => Hca Hcb; congruence. }
                   have Hcc1 : color (taga cell1) = comp'
                     by move: Htc1; rewrite /get_tni_color;
                        case: (taga cell1) => vt ct et bt /= [= ->].
                   have Hcdd' : color (taga dd') = comp' by rewrite -Htag_dd -Hc1d.
                   have Hcoddd' : is_code (taga dd') by rewrite -Htag_dd.
                   have [l1 He1] : exists l1, entry (taga cell1) = Some (proc, l1).
                   { move: Hpn1; rewrite /get_proc_name; case: (taga cell1) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   have He1'' : entry (taga dd') = Some (proc, l1) by rewrite -Htag_dd -Hc1d.
                   have Hcc2 : color (taga cell2) = comp'
                     by move: Htc2; rewrite /get_tni_color;
                        case: (taga cell2) => vt ct et bt /= [= ->].
                   have [l2 He2] : exists l2, entry (taga cell2) = Some (proc, l2).
                   { move: Hpn2; rewrite /get_proc_name; case: (taga cell2) => vt ct et bt /=.
                     by case: et => [[p ll]|] //= [= <-]; exists ll. }
                   have Hcode2t : is_code (taga cell2).
                   { have bnz2 : BNZ_correctness mem2
                       by move: gmc2 => [_ [_ [_ [_ [Hb _]]]]]; exact: Hb.
                     have HB := bnz2 pc2v (vip2$tip2) Hpc2 Hcode2.
                     move: HB; cbn [vala]; rewrite Hdec2'.
                     case=> [[v' [Hv' Hcv']] | Halloc].
                     - move: Hv'; rewrite Hcell2 => -[->]; exact: Hcv'.
                     - exfalso; have ae2 : alloc_empty mem2
                         by move: gmc2 => [_ [_ [_ [Ha _]]]]; exact: Ha.
                       move: Hcell2; rewrite -Halloc swcast_word_of_nat_alloc_label ae2;
                         discriminate. }
                   have Hrel2 : comp' \in domm ic.
                   { have col_mem2 : color_in_memory mem2
                       by move: gmc2 => [_ [_ [_ [_ [_ [_ [Hcol _]]]]]]]; exact: Hcol.
                     have HCm := col_mem2 (swcast imm2) cell2 Hcell2. rewrite Hcc2 in HCm.
                     case: HCm => [/In_in HCm | /In_in HCm];
                       [ by move: Hside; rewrite HCm | exact: HCm ]. }
                   have [off [Hoff Hwoff]] :=
                     Heow comp' (swcast imm2) (swcast imm') cell2 dd' proc l2 l1
                       Hrel2 Hcell2 Hdd' Hcode2t Hcoddd' Hcc2 Hcdd' He2 He1''.
                   unshelve eapply (same_pc_normal _ _ (v := cell2) (off := off));
                     cbn [color_of build_tpc];
                     first [ exact: Hoff | exact: Hwoff | (split; [exact: Hcell2 | exact: Hcode2t]) ].
                ** (* color_of *) by rewrite /color_of /build_tpc.
                ** (* side_of = Right *) by rewrite /side_of /color_of /build_tpc Hside.
                ** (* mem_addr s2' *) exact: Hma2.
                ** (* mem_addr s3' *) exact: Hma3.
                ** (* entry_offset *) exact: Heow.
                ** (* reg_addr s2' *)
                   move: (reg_domm_cross Hdu2 rd2) => Hdmm2.
                   move=> v r Hr. have Hrin : r \in domm rs2 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm2 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_2 => -[<-].
                     by rewrite /address_correctness /=;
                        exists ret; split; [exact: Hret | move=> _; exact: Hcoret]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_2 => -[<-]. by rewrite /address_correctness. }
                     { have [v2 Hv2] := Hinv2 n Hnr.
                       move: Hr; rewrite Hv2 => -[<-]. by rewrite /address_correctness. } }
                ** (* reg_addr s3' *)
                   move: (reg_domm_cross Hdu3 rd3) => Hdmm3.
                   move=> v r Hr. have Hrin : r \in domm rs3 by apply/dommP; exists v.
                   move: Hrin Hr; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hr4 | /mapP[n Hn Hrn]].
                   { subst r => Hr; move: Hr; rewrite Hr4_3 => -[<-].
                     by rewrite /address_correctness /=;
                        exists (vra3$tret); split; [exact: Hcell3 | move=> _; exact: Hic_ra]. }
                   { subst r => Hr; rewrite WA in Hr.
                     move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                     { subst n; move: Hr; rewrite Hr1_3 => -[<-]. by rewrite /address_correctness. }
                     { have [v3 Hv3] := Hinv3 n Hnr.
                       move: Hr; rewrite Hv3 => -[<-]. by rewrite /address_correctness. } }
                ** (* memory_match Right *)
                   have INC : forall (d1 d2 : atom (mword mt) (tag_type lrc_tags M)),
                     data_match' Right M0 d1 d2 ->
                     data_match' Right (((pc0+1)%w$(Ret cn), (pc2v+1)%w$(Ret cn),
                                        (pc3v+1)%w$(Ret cn), cc) :: M0) d1 d2.
                   { move=> [v1 t1] [v2 t2] [Ht Hd]; split=> //; move: Hd; rewrite /data_match.
                     move=> [Hvt Hc]; split=> //; move: Hc; case: (vtag t1) => [n0| | |] //=.
                     by move=> [sv' [c' Hin]]; exists sv', c'; right. }
                   move=> w d Hcode Hrel; split=> Hw.
                   { have [d' [Hdm' Hw']] := proj1 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                   { have [d' [Hdm' Hw']] := proj2 (Hmmw w d Hcode Hrel) Hw.
                     by exists d'; split; [apply: INC | exact: Hw']. }
                ** (* registers_match Right *)
                   move: (reg_domm_cross Hdu2 rd2) (reg_domm_cross Hdu3 rd3) => Hdmm2 Hdmm3.
                   move=> w d; split=> Hw.
                   { have Hwd : w \in domm rs3 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm3 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_3 => -[<-].
                       exists ((pc2v + 1)%w$(Ret cn)); split; last exact: Hr4_2.
                       rewrite /data_match; split=> //.
                       by exists ((pc0 + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_3 => -[<-].
                         exists ((vala a2)$Other); split; last exact: Hr1_2.
                         by rewrite /data_match; split=> //=; rewrite Hva23.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v2 Hv2] := Hinv2 n Hnr.
                         move: Hw; rewrite WA Hv3 => -[<-].
                         exists (v2$Invalidated); split; last exact: Hv2.
                         by rewrite /data_match; split. }
                   { have Hwd : w \in domm rs2 by apply/dommP; exists d.
                     move: Hwd; rewrite Hdmm2 in_fset in_cons => /orP[/eqP Hw4 | /mapP[n Hn Hwn]].
                     - subst w. move: Hw; rewrite Hr4_2 => -[<-].
                       exists ((pc3v + 1)%w$(Ret cn)); split; last exact: Hr4_3.
                       rewrite /data_match; split=> //.
                       by exists ((pc0 + 1)%w$(Ret cn)), cc; left.
                     - subst w; rewrite WA.  move: Hn; rewrite /reg_list in_cons => /orP[/eqP Hn1 | Hnr].
                       + subst n. move: Hw; rewrite WA Hr1_2 => -[<-].
                         exists ((vala a3)$Other); split; last exact: Hr1_3.
                         by rewrite /data_match; split=> //=; rewrite Hva23.
                       + have [v3 Hv3] := Hinv3 n Hnr. have [v2 Hv2] := Hinv2 n Hnr.
                         move: Hw; rewrite WA Hv2 => -[<-].
                         exists (v3$Invalidated); split; last exact: Hv3.
                         by rewrite /data_match; split. }
      + (* match_right: extracted to lemma [secmr] (fed the [step_mp] [smp1] from this UB-disallowed
           step — [secmr] reduces s1 uniformly via LRC for both UB sub-cases).  Use [apply:] not
           [exact:] — secmr's s1/s2/M0 don't appear in its conclusion, so [exact:] can't infer them. *)
        apply: secmr;
          [ exact: smp1 | exact: step_s2 | exact: common | exact: weak | exact: strong ].
  (* DONE — [step_event_call] is proven to [Qed] (NOT Admitted), UB-match_right admit eliminated, all
     4 cases discharged, 0 [admit].  Whole file compiles in ~30s (was >45min / never-completing).
     ROOT CAUSE of the historical ~9.4MB-term / impractical-Qed (this lemma was [Admitted] in every
     prior rev to skip it): `col_mem2 (swcast imm0) cell2 Hcell2` in secmr's comp'-Right same_pc (and
     the match_left mirror) forced a `swcast imm0 ≡ swcast imm2` word/fmap CONVERSION whose giant
     eq-proof bloated the term AND cost ~275s CPU per occurrence — in step1 imm0 was syntactically
     imm2 (free), step_mp made them distinct.  FIX: `col_mem2 _ cell2 Hcell2` (infer the word from the
     proof, no conversion).  Two more masked bugs this exposed (the col_mem2 wall had hidden them, and
     the Qed never ran): (a) comp'-Right's reg_addr/registers_match had stale `rs1`/`a2` copy-pasted
     from comp'-Left — should be `rs2`/`a1` (the strong side is s2'); (b) `eapply same_pc_normal`
     shelves its state-dependent premises so the trailing `first[...]` never closed them → use
     `unshelve eapply`.  Also: both [secmr] call-sites use `apply: secmr; [..5 hyps..]` not [exact:]
     (secmr's s1/s2/M0 are not in its conclusion, so [exact:] cannot infer them). *)
  Qed.

End StepEventCall.

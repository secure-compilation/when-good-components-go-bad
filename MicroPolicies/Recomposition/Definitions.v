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
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Record program :=
  { prog_interface: Program.interface;
    code: @Merged.code concrete_int_32_mt;
    prog_buffers: NMap {fmap Block.id -> (nat + seq value)};
    prog_main: bool;
  }.

Definition program_link p c :=
  {| prog_interface := unionm (prog_interface p) (prog_interface c);
    code := code p ++ code c;
    prog_buffers := unionm (prog_buffers p) (prog_buffers c);
    prog_main := prog_main p || prog_main c;
  |}.

(* definition taken from Source/Language.v *)

Record closed_program (p: program) := {
    (* the interface must be closed (and consequently sound) *)
    cprog_closed_interface:
    closed_interface (prog_interface p);
    (* the main procedure must exist *)
    cprog_main_existence: prog_main p
  }.


(* Component C has a buffer of size at least one *)
Definition has_required_local_buffers (p: program) (C: Component.id) : Prop :=
  exists (b: nat),
    match (Option.bind (fun (r: {fmap Block.id -> nat + seq value}) => r b ) (prog_buffers p C)) with
    | None => False
    | Some buf =>
        match buf with
        | inl size   => size > 0
        | inr values => length values > 0
        end%nat
    end.

Definition get_procedures p :=
  fset (map (fun '(_, tag) => color tag) (code p)).

(* TODO: don't we want a condition on lc as well? (allowed components) *)
Definition find_procedure p comp proc :=
  Exists (fun '(_, tag) =>
            match (entry tag) with
            | None => False
            | Some (proc', lc) => (proc = proc') /\ (comp = color tag)
            end) (code p).

Definition unique_entry_points (cde: @Merged.code mt) :=
  forall c e n m i i' t t',
    color t  = c ->
    color t' = c ->
    entry t  = Some e ->
    entry t' = Some e ->
    nth_error cde n = Some (i, t ) ->
    nth_error cde m = Some (i',t') ->
    n = m.

Record well_formed_program (p: program) := {
    (* the interface is sound (but maybe not closed) *)
    wfprog_interface_soundness:
    sound_interface (prog_interface p);
    (* there are procedures only for the declared components *)
    wfprog_defined_procedures: domm (prog_interface p) = get_procedures p;
    (* each exported procedure is actually defined *)
    wfprog_exported_procedures_existence:
    forall C P, exported_procedure (prog_interface p) C P ->
           find_procedure p C P;
    (* there are no duplicate entry points *)
    wfprog_unique_entry_points:
    unique_entry_points (code p);
    (* each declared component has the required static buffers *)
    wfprog_defined_buffers: domm (prog_interface p) = domm (prog_buffers p);
    (* each component's buffer is well formed *)
    wfprog_well_formed_buffers:
    forall C, prog_interface p C ->
         has_required_local_buffers p C;
    (* iff the main component is defined, so is the main procedure *)
    wfprog_main_existence:
    Component.main \in domm (prog_interface p) <-> prog_main p;
    (*wfprog_main_start:
    Component.main \in domm (prog_interface p) <->
                         exists v, nth_error (code p) 0 = Some v /\ color (snd v) = Component.main *)
  }.

Module Type RecompositionContext.
  Parameters p c p' c' : program.

  Parameter NC: nat.

  Axiom Hwfp  : well_formed_program p.
  Axiom Hwfc  : well_formed_program c.
  Axiom Hwfp' : well_formed_program p'.
  Axiom Hwfc' : well_formed_program c'.

  Axiom Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Axiom Hifacep  : prog_interface p  = prog_interface p'.
  Axiom Hifacec  : prog_interface c  = prog_interface c'.

  Axiom Hprog_is_closed  : closed_program (program_link p  c ).
  Axiom Hprog_is_closed' : closed_program (program_link p' c').

End RecompositionContext.

(* Main simulation theorem. *)
Module RecompositionDefinitions (S: RecompositionContext).

  Export S.

  (* Variables p c p' c' : program. *)

  (* Hypothesis Hwfp  : well_formed_program p. *)
  (* Hypothesis Hwfc  : well_formed_program c. *)
  (* Hypothesis Hwfp' : well_formed_program p'. *)
  (* Hypothesis Hwfc' : well_formed_program c'. *)

  (* Hypothesis Hmergeable_ifaces : *)
  (*   mergeable_interfaces (prog_interface p) (prog_interface c). *)

  (* Hypothesis Hifacep  : prog_interface p  = prog_interface p'. *)
  (* Hypothesis Hifacec  : prog_interface c  = prog_interface c'. *)

  (* Hypothesis Hprog_is_closed  : closed_program (program_link p  c ). *)
  (* Hypothesis Hprog_is_closed' : closed_program (program_link p' c'). *)

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p'  c'.
  Let prog'' := program_link p c'.

  Let state := @Symbolic.state mt LRC.lrc_tags [eqType of unit].
  Let genvtype := unit.
  Let step1 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_me s s' None (NC := NC)
                                       | e :: [::] => step_me s s' (Some e) (NC := NC)
                                       | _ => False
                                       end).
  Let step2 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_mp s s' None (NC := NC)
                                       | e :: [::] => step_mp s s' (Some e) (NC := NC)
                                       | _ => False
                                       end).
  Definition initial_state1: state -> Prop :=
    fun s => s = initial_state (code prog  ) (prog_buffers prog  ) (prog_interface prog  ).

  Definition initial_state2: state -> Prop :=
    fun s => s = initial_state (code prog' ) (prog_buffers prog' ) (prog_interface prog' ).

  Definition initial_state3: state -> Prop :=
    fun s => s = initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'').

  Definition color_of: state -> Component.id :=
    fun '(Symbolic.State m r (Types.Atom _ tpc) _) =>
      match (tpc) with
      | Level _ c => c
      end.

  Definition allowed_UB: state -> Prop :=
    fun s => (color_of s) \in (domm ic).

  Definition final_state_me: state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc _) _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) =>
          ((Types.decode_instr i) = Some (Types.Halt _)) /\ (is_code tag = true)
      end.

  Definition final_state_rUB: state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc tpc) _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) =>
          ((Types.decode_instr i) = Some (Types.Halt _)) /\ ((color tag) \in (domm ip) -> (is_code tag = true))
      end.

  Let sem   :=
        L_restricted_UB step1 step2 initial_state1 final_state_rUB tt allowed_UB.

  Let sem'  :=
        {| Smallstep.state := state;
          Smallstep.genvtype := genvtype;
          Smallstep.step := step1;
          Smallstep.initial_state := initial_state2;
          Smallstep.final_state := final_state_me;
          Smallstep.globalenv := tt |}.
  Let sem'' :=

        {| Smallstep.state := state;
          Smallstep.genvtype := genvtype;
          Smallstep.step := step1;
          Smallstep.initial_state := initial_state3;
          Smallstep.final_state := final_state_me;
          Smallstep.globalenv := tt |}.

  Lemma det_sem' : determinate sem'.
  Proof.
    econstructor; intros; unfold sem'  in *.
    - simpl in *. unfold step1, step_me in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold initial_state2 in *. subst. done.
    - simpl in *. intros t s' step. unfold step1, step_me in step.
      destruct t; try destruct t; try contradiction;
        setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step;
        destruct s, pc0; unfold final_state_me in H; destruct (mem0 vala); try auto; destruct a;
        destruct H as [eq ?]; rewrite eq in step; simpl in step; inversion step.
  Qed.

  Lemma det_sem'' : determinate sem''.
  Proof.
    econstructor; intros; unfold sem'  in *.
    - simpl in *. unfold step1, step_me in *.
      destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
        setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
        rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor|done]).
    - unfold single_events. intros.
      destruct t; try destruct t; try contradiction; simpl; lia.
    - simpl in *. unfold initial_state3 in *. subst. done.
    - simpl in *. intros t s' step. unfold step1, step_me in step. destruct t; try destruct t; try contradiction;
        setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step;
        destruct s, pc0; unfold final_state_me in H; destruct (mem0 vala); try auto; destruct a;
        destruct H as [eq ?]; rewrite eq in step; simpl in step; inversion step.
  Qed.

  Lemma det_sem : determinate sem.
  Proof.
   econstructor; intros; unfold sem'  in *.
    - simpl in *. (*unfold step1, step2, step_mp, step_me in *. *)
      destruct H, H0 ; [|clear H0| clear H| clear H1 H2];
        unfold step1, step2, step_mp, step_me in *;
        destruct t, t0; try destruct t; try destruct t0; try contradiction;
        (do 2 (match goal with | H : step _ _ _ _ |- _ => setoid_rewrite <- Exec.stepP in H end));
        (match goal with | H : ?a = ?b, H0 : ?a = ?c |- _  => try (rewrite H0 in H; inv H) end);
        try (split; [try destruct e; try econstructor|try done]).
    - unfold single_events. intros.
      destruct H; unfold step1, step2, step_mp, step_me in *;
        destruct t; try destruct t; try contradiction;
        (match goal with | H : step _ _ _ _ |- _ => setoid_rewrite <- Exec.stepP in H end); simpl; lia.
    - simpl in *. unfold initial_state1 in *. subst. done.
    - simpl in *. intros t s' step. destruct step; rename H0 into step; unfold step1, step2, step_mp, step_me in step;
        destruct t; try destruct t; try contradiction;
        setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step; unfold final_state_me in H;
        destruct s; unfold final_state_me in H ; simpl in H; destruct pc0;
        remember (mem0 vala) as mv; unfold getm in H;
        assert (eqmv: getm_def mem0 vala = mv) by ( clear - Heqmv; unfold getm in Heqmv; auto); rewrite eqmv in H;
        destruct mv; try auto; try destruct a;
        destruct H as [eq ?]; unfold Types.decode_instr in step; simpl in step; rewrite eq in step; simpl in step; inversion step.
  Qed.

  (*** Equivalence Relations ***)

  Section SimulationRelations.

    Variant side := Left | Right.

    Definition other_side s :=
      match s with Left => Right | Right => Left end.

    Definition side_of c: side :=
      if c \in domm ip then Left else Right.

    Definition is_relevant_comp i c : Prop :=
      match i with
      | Left => c \in domm ip
      | Right => c \in domm ic
      end.

    Definition stack_value := Types.atom (Types.mword mt) value_tag.

    Fixpoint find_rank' {T} (f: pred T) (l: seq T) (n: nat) : option nat :=
      match l with
      | [] => None
      | e :: l => if (f e) then Some n else find_rank' f l (S n)
      end.

    (* [find_rank f l] finds the location of the first element
     that satisfies [f] in list [l] *)
    Definition find_rank {T} (f: pred T) (l: seq T): option nat :=
      find_rank' f l 0.
    (* Todo: write a lemma (about find_rank) usable
       along get_procedures and well_formed_program *)


    (* [p0 prog C] finds the first location of
       [C]'s code in the code of the program *)
    Definition p0 (prog: program) (comp: Component.id): option nat :=
      do! start <- find_rank (fun '(_,tag) => color tag == comp) (code prog);
      Some (start + size (domm (@initial_memory mt (prog_buffers prog)))).

    Definition offset1: NMap ssrint.int :=
      mkfmapfp (fun comp =>
                  do! p_s3 <- p0 prog'' comp;
                  do! p_s1 <- p0 prog comp;
                  Some (encode_int (Z.of_nat p_s3 - Z.of_nat p_s1)))
        (domm ip).

    Definition offset2: NMap ssrint.int :=
      mkfmapfp (fun comp =>
                  do! p_s3 <- p0 prog'' comp;
                  do! p_s2 <- p0 prog' comp;
                  Some (encode_int (Z.of_nat p_s3 - Z.of_nat p_s2)))
        (domm ic).

    Lemma offset1_domm : domm offset1 = domm ip.
    Proof.
      unfold offset1. clear. rewrite domm_mkfmapfp. simpl.
    Admitted.

    Lemma offset2_domm : domm offset2 = domm ic.
    Proof.
    Admitted.

    Definition stack: Type := seq (stack_value * stack_value * stack_value * Component.id).
    Definition metadata: Type := stack.

    Definition get_offset i comp :=
      match i with
      | Left => offset1 comp
      | Right => offset2 comp
      end.

    Definition points_to_comp_code (m: memory) (v: Types.mword mt) (comp : Component.id) : Prop :=
      Option.apply (fun memval => color (Types.taga (memval)) = comp /\ is_code (taga memval)) False (m v).

    Definition points_to_comp_code' i j (m: memory) (v: Types.mword mt) (comp : Component.id) : Prop :=
      Option.apply (fun memval => color (Types.taga (memval)) = comp /\ ((i = Right /\ j = Right) \/ is_code (taga memval))) False (m v).
    (* unless we are in the 'Right' state, running the 'Right' side (c), we should point to code only *)

    Inductive wf_stack (m1 m2 m3: memory): nat -> stack -> Prop :=
    | wf_stack_empty:
        wf_stack m1 m2 m3 0 []
    | wf_stack_cons_left: forall n st v1 v2 v3 C off,
      forall (SIDE: is_relevant_comp Left C)
        (OFF_C: get_offset Left C = Some off)
        (PTS_CODE1: points_to_comp_code' Right (side_of C) m1 v1 C)
        (PTS_CODE2: points_to_comp_code m2 v2 C)
        (PTS_CODE3: points_to_comp_code m3 v3 C)
        (VALA_OFF: v3 = addw v1 (as_word off))
        (WF_ST: wf_stack m1 m2 m3 n st),
        wf_stack m1 m2 m3 (n+1)
          ((Types.Atom v1 (Ret n), Types.Atom v2 (Ret n), Types.Atom v3 (Ret n), C) :: st)
    | wf_stack_cons_right: forall n st v1 v2 v3 C off,
      forall (SIDE: is_relevant_comp Right C)
        (OFF_C: get_offset Right C = Some off)
        (PTS_CODE1: points_to_comp_code' Right (side_of C) m1 v1 C)
        (PTS_CODE2: points_to_comp_code m2 v2 C)
        (PTS_CODE3: points_to_comp_code m3 v3 C)
        (VALA_OFF: v3 = addw v2 (as_word off))
        (WF_ST: wf_stack m1 m2 m3 n st),
        wf_stack m1 m2 m3 (n+1)
          ((Types.Atom v1 (Ret n), Types.Atom v2 (Ret n), Types.Atom v3 (Ret n), C) :: st)
    .

    (* This property states that all capabilities are stored in our metadata *)
    (* And that they are unique in our *)
    Variant which_state := WS_S1 | WS_S2 | WS_S3.
    Definition in_stack (m:stack) ws v n :=
      (exists sv1 sv2 col,
          match ws with
          | WS_S1 => In (v @ (Ret n), sv1, sv2, col) m
          | WS_S2 => In (sv1, v @ (Ret n), sv2, col) m
          | WS_S3 => In (sv1, sv2, v @ (Ret n), col) m
          end)
    .
    Definition capability_correctness (m: metadata) (ws: which_state) (s: state) :=
      forall v n p,
        match p with
        | inr w => exists t, (mem s) w = Some (v @ t) /\ vtag t = Ret n
        | inl r => (regs s) r = Some (v @ (Ret n))
        end ->
        in_stack m ws v n
        /\ forall p' v',
            (match p, p' with
             | inr w, inr w' => (exists t', (mem s) w' = Some (v' @ t') /\ vtag t' = Ret n) -> w = w'
             | inl r, inl r' => (regs s) r' = Some (v' @ (Ret n)) -> r = r'
             (* The capability can't be both in our registers and in memoryD *)
             | inl _, inr w' => (exists t', (mem s) w' = Some (v' @ t') /\ vtag t' = Ret n) -> False
             | inr _, inl r' => (regs s) r' = Some (v' @ (Ret n)) -> False
             end)
    .

    #[export] Notation data := (Types.atom (Types.mword mt) mem_tag).

    Variant data_match_variant (i: side) (comp: Component.id) (m: metadata): stack_value -> stack_value -> Prop :=
      | data_match_variant_invalidated: forall v1 v2,
          data_match_variant i comp m (Types.Atom v1 Invalidated) (Types.Atom v2 Invalidated)
      | data_match_variant_other: forall v,
          data_match_variant i comp m (Types.Atom v Other) (Types.Atom v Other)
      | data_match_variant_internal_jump: forall v1 v2 off,
          get_offset i comp = Some off ->
          v2 = addw v1 (as_word off) ->
          data_match_variant i comp m (Types.Atom v1 InternalJump) (Types.Atom v2 InternalJump)
      | data_match_variant_ret: forall v1 t1 v2 t2 n sv' comp',
        t1 = Ret n ->
        t2 = Ret n ->
        (i = Left -> In (Types.Atom v1 t1, sv', Types.Atom v2 t2, comp') m) ->
        (i = Right -> In (sv', Types.Atom v1 t1, Types.Atom v2 t2, comp') m) ->
        data_match_variant i comp m (Types.Atom v1 t1) (Types.Atom v2 t2)
    .

    Definition data_match (i: side) (comp: Component.id) (m: metadata) (d: stack_value) (d': stack_value) : Prop :=
      match d, d' with
      | Types.Atom v1 t1, Types.Atom v2 t2 =>
          t1 = t2 /\
            match t1 with
            | Invalidated => True
            | Other => v1 = v2
            | InternalJump => Option.apply (fun off => v2 = addw v1 (as_word off)) False (get_offset i comp)
            | Ret _ =>
                match i with
                | Left  => exists sv' comp', In (d, sv', d', comp') m
                | Right => exists sv' comp', In (sv', d, d', comp') m
                end
            end
      end.

    Lemma data_match_eq: forall i comp m d d',
        data_match_variant i comp m d d' <-> data_match i comp m d d'.
    Proof.
      intros; split.
      - intros H; inv H.
        + simpl; auto.
        + simpl; auto.
        + simpl. rewrite H0. simpl; auto.
        + simpl; auto. destruct i; eauto.
      - destruct d as [v1 []], d' as [v2 []]; simpl; try now auto.
        + move=> [] [] <-; case: i => [] [] sv' [] comp' H; econstructor; eauto; congruence.
        + move=> [] _ <-; constructor.
        + move=> [] _; case eq_offset: (get_offset i comp) => //=; econstructor; eauto.
        + move=> _; constructor.
    Qed.

    Definition data_match' (i: side) (m: metadata) (d: data) (d': data) : Prop :=
      match d, d' with
      | Types.Atom v1 t1, Types.Atom v2 t2 =>
          t1 = t2 /\
            let comp := (color t1) in
            (data_match i comp m (Types.Atom v1 (vtag t1)) (Types.Atom v2 (vtag t2)))
      end.

    Definition memory_match (i: side) (m: metadata) (s: state) (s': state) : Prop :=
      forall w d,
        not (is_code (Types.taga d)) ->
        is_relevant_comp i (color (Types.taga d)) ->
        ((mem s' w) = Some d -> exists d', data_match' i m d' d /\ (mem s  w) = Some d') /\
          ((mem s  w) = Some d -> exists d', data_match' i m d d' /\ (mem s' w) = Some d').

    Definition registers_match (i: side) (m: metadata) (s: state) (s': state) : Prop :=
      forall w d,
        ((regs s' w) = Some d -> exists d', data_match i (color_of s) m d' d /\ (regs s  w) = Some d') /\
          ((regs s  w) = Some d -> exists d', data_match i (color_of s) m d d' /\ (regs s' w) = Some d').

    Variant same_pc (i: side): state -> state -> Prop :=
      | same_pc_alloc: forall s s',
          vala (pc s) = vala (pc s') ->
          mem s (vala (pc s)) = None ->
          same_pc i s s'
      | same_pc_normal: forall s s' v off,
          mem s (vala (pc s)) = Some v ->
          get_offset i (color_of s) = Some off ->
          vala (pc s') = addw (Types.vala (pc s)) (as_word off) ->
          same_pc i s s'
    .

    Variant decode_match (mem: @memory mt) (mem': @memory mt) v v': Prop :=
      | decode_match_no_JAL:
        (forall imm, decode_instr v <> Some (Jal imm)) ->
        (forall imm', decode_instr v' <> Some (Jal imm')) ->
        v = v' ->
        decode_match mem mem' v v'
      | decode_match_alloc_JAL:
        decode_instr v  = Some (Jal (word_of_nat alloc_label) ) ->
        decode_instr v' = Some (Jal (word_of_nat alloc_label) ) ->
        decode_match mem mem' v v'
      | decode_match_JAL: forall imm imm' d d',
          decode_instr v  = Some (Jal imm ) ->
          decode_instr v' = Some (Jal imm') ->
          mem (swcast imm) = Some d ->
          mem' (swcast imm') = Some d' ->
          is_code (taga d) ->
          taga d = taga d' -> (* exact same tag, so same entry point if there is one *)
          (forall off, (get_offset (side_of (color (taga d))) (color (taga d)) = Some off) -> imm' = addw imm (as_word off)) ->
          decode_match mem mem' v v'
    .

    Definition combined_codes (i: side) (s: state) (s': state) : Prop :=
      forall w v t off c,
        is_relevant_comp i c ->
        get_offset i c = Some off ->
        is_code (t) ->
        color (t) = c ->
        ((mem s w = Some v@t -> exists v',
             decode_match (mem s) (mem s') v v' /\
               (mem s' (addw w (as_word off)) = Some v'@t))
         /\ ((mem s' (addw w (as_word off)) = Some (v@t)) -> exists v',
               decode_match (mem s) (mem s') v' v /\
                 (mem s w = Some (v'@t))))
    .

    Definition end_condition (mem: memory) : Prop :=
      forall w v,
        mem w = Some v ->
        is_code (taga v) ->
        (match (decode_instr (vala v)) with Some Halt => True | _ => False end)
        \/ exists v', (mem (addw w onew) = Some v' /\ is_code (taga v'))
    .

    (* necessary invariants for the allocation case *)
    Definition memory_prefix_condition (mem:memory) :=
      forall current_c,
        let prefix := (@component_memory_prefix mt NC (ssrint.Posz(1 + current_c))) in
        (* let mask := (@component_memory_prefix mt (ssrint.Posz((2 ^ nc)-1)) nc) in *)
        let prefix_filter := (fun mw => ((word.andw mw (mask (NC := NC))) == prefix) ) in
        let comp_filter := (fun w v => andb (color (taga v) == current_c) (negb (is_code (taga v)))) in
        filter prefix_filter (domm (mem)) =
          fsetD (domm (filterm comp_filter (mem))) (domm (initial_memory (prog_buffers prog))).

    Definition code_prefix_condition (mem:memory) :=
      forall w v,
        mem w = Some v ->
        is_code (taga v) ->
        let prefix := (@component_memory_prefix mt NC (ssrint.Posz(0))) in
        (* let mask := (@component_memory_prefix mt (ssrint.Posz((2 ^ nc)-1)) nc) in *)
        ((word.andw w (mask (NC := NC))) == prefix).

    Definition alloc_empty (mem: @memory mt) :=
      mem (word_of_nat alloc_label) = None.

    (* necessary invariants for the JMP and JAL cases *)
    Definition address_correctness i w t (mem: memory) :=
      match t with
      | Ret _ | InternalJump => exists (v: atom (mword mt) _),
                  mem w = Some v /\ (is_relevant_comp i (color (taga v)) -> is_code (taga v))
      | Other | Invalidated => True
      end.

    Definition memory_address_correctness (i: side) (s: state) :=
      forall v w,
        is_relevant_comp i (color (taga v)) ->
         mem s w = Some v ->
         address_correctness i (vala v) (vtag (taga v)) (mem s).

    Definition register_address_correctness i (s: state) :=
      forall v r,
         regs s r = Some v ->
         address_correctness i (vala v) (taga v) (mem s).

    (* necessary invariant for the BNZ/JAL cases *)
    Definition BNZ_correctness (mem: memory) : Prop :=
      forall w, forall v: atom (mword mt) _,
        mem w = Some v ->
        is_code (taga v) ->
        (match (decode_instr (vala v)) with
         | Some (Bnz _ n) =>
             exists (v': atom (mword mt) _),
             mem (addw w (swcast n)) = Some v' /\ is_code (taga v')
         | Some (Jal n)=>
             (exists (v': atom (mword mt) _),
                 mem (swcast n) = Some v' /\ is_code (taga v')) \/ (word_of_nat alloc_label = n)
         | _ => True
         end).

    Definition color_in_memory (mem: @memory mt) :=
      forall w d, mem w = Some d -> In (color (taga d)) (domm ip) \/ In (color (taga d)) (domm ic).

    Definition entry_is_code (mem: @memory mt) :=
      forall w d e,
        mem w = Some d ->
        entry (taga d) = Some e ->
        is_code (taga d)
    .

    (* necessary invariant to prove that registers are properly cleared on call/return *)
    Definition register_domm (regs: {fmap reg mt -> atom (mword mt) value_tag} ) : Prop :=
      domm regs =
        fset (ra :: (map (word_of_nat) reg_list)).

    (* necessary invariant on calls that change which state is weakly/strongly related *)
    Definition entry_points_offset i (mem: @memory mt) (mem': @memory mt) : Prop :=
      forall c w w' d d' proc l l',
        is_relevant_comp i c ->
        mem  w  = Some d ->
        mem' w' = Some d' ->
        is_code (taga d ) ->
        is_code (taga d') ->
        color (taga d ) = c ->
        color (taga d') = c ->
        entry (taga d ) = Some (proc, l ) ->
        entry (taga d') = Some (proc, l') ->
        (exists off,
            get_offset i c = Some off
            /\  w' = addw w (as_word off)).

    Definition general_memory_correctness (mem: memory) : Prop :=
      memory_prefix_condition mem
      /\ code_prefix_condition mem
      /\ alloc_empty mem
      /\ BNZ_correctness mem
      /\ end_condition mem
      /\ color_in_memory mem
      /\ entry_is_code mem.

    Definition compatible {A} (col_opt: option A) (col: A) :=
      match col_opt with
      | Some c => col = c
      | None => True
      end.

    Variant common_equiv: metadata -> state -> state -> state -> Prop :=
      common_equiv_def : forall m s1 s2 s3 n c,
          taga (@pc _ lrc_tags _ s1) = Level n c ->
          taga (@pc _ lrc_tags _ s2) = Level n c ->
          taga (@pc _ lrc_tags _ s3) = Level n c ->
          wf_stack (mem s1) (mem s2) (mem s3) n m ->
          register_domm (regs s1) ->
          register_domm (regs s2) ->
          register_domm (regs s3) ->
          general_memory_correctness (mem s1) ->
          general_memory_correctness (mem s2) ->
          general_memory_correctness (mem s3) ->
          capability_correctness m WS_S1 s1 ->
          capability_correctness m WS_S2 s2 ->
          capability_correctness m WS_S3 s3 ->
          combined_codes Left  s1 s3 ->
          combined_codes Right s2 s3 ->
          common_equiv m s1 s2 s3
    .
    Variant strong_equiv (i: side): metadata -> state -> state -> Prop :=
      strong_equiv_def : forall m s s',
          same_pc i s s' ->
          color_of s = color_of s' ->
          side_of (color_of s) = i ->
          memory_address_correctness i s ->
          memory_address_correctness i s' ->
          entry_points_offset i (mem s) (mem s') ->
          register_address_correctness i s ->
          register_address_correctness i s' ->
          memory_match i m s s' ->
          registers_match i m s s' ->
          strong_equiv i m s s'
    .

    Variant weak_equiv (i: side): metadata -> state -> state -> Prop :=
      weak_equiv_def : forall m s s',
          color_of s = color_of s' ->
          side_of (color_of s) = other_side i ->
          memory_address_correctness i s ->
          memory_address_correctness i s' ->
          entry_points_offset i (mem s) (mem s') ->
          register_address_correctness i s' ->
          memory_match i m s s' ->
          weak_equiv i m s s'
    .


  End SimulationRelations.

  #[export] Notation match_states := (match_states sem sem' sem'' (common_equiv)
    (strong_equiv Left) (strong_equiv Right) (weak_equiv Left) (weak_equiv Right)).

  (*** Tactics ***)


  #[export] Ltac eq_op_to_eq :=
    let ineq := fresh in
    match goal with
      | H: (true = (?a == ?b)) |- ?a = ?b =>
    eapply (@contraNeq (Ord.eqType _) false); auto; intro ineq; exfalso; try destruct ineq; eapply no_fixpoint_negb; eauto
    end.

  #[export] Ltac convert_eq_op :=
    repeat
    match goal with
    | H: (true = (?a == ?b)) |- _ => assert (a = b) by eq_op_to_eq; (subst a || subst b); clear H
    end.

  #[export] Ltac decode_instr_eq :=
    (match goal with
     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
       => simpl; rewrite <- op; simpl; rewrite inst; try done
     end).

  #[export] Ltac oapp_False :=
    let b := fresh in
    match goal with | H: oapp _ False ?v |- _ => remember v as b; destruct b; try contradiction; simpl in H; try subst b end.

  #[export] Ltac unfold_match :=
    let a := fresh "a" in
    match goal with
    | H : (match ?cond as _ return _ with _ => _ end) = Some _  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : Some _ = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = None  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : None = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = true  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : true = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = false  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : false = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = Left  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : Left = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = Right  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : Right = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    end.
  #[export] Ltac unfold_match' H :=
    let a := fresh "a" in
    match (type of H) with
    | (match ?cond as _ return _ with _ => _ end) = _ => try(remember cond as a; destruct a);
                                                       simpl in H; try (inversion H; done)
    | _ = (match ?cond as _ return _ with _ => _ end) => try(remember cond as a; destruct a);
                                                       simpl in H; try (inversion H; done)
    end.
  #[export] Ltac unfold_match_misc :=
    let a := fresh "a" in
    match goal with
    | H : _ = (match ?cond as _ return _ with _ => _ end) _  |- _ => try(remember cond as a; destruct a);
                                                                  simpl in H; try (inversion H; done)
    | H : _ = (match ?cond as _ return _ with _ => _ end) _ _  |- _ => try(remember cond as a; destruct a);
                                                                    simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) _ = _  |- _ => try(remember cond as a; destruct a);
                                                                  simpl in H; try (inversion H; done)
    | H : _ = ((match ?cond as _ return _ with _ => _ end) == _)  |- _ => try(remember cond as a; destruct a);
                                                                       simpl in H; try (inversion H; done)
    end.
  #[export] Ltac unfold_bind :=
    let a := fresh "a" in
    match goal with
    | H : _ = (Option.bind ?f ?v) |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : (Option.bind ?f ?v) = _ |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : match (Option.bind ?f ?v) with _ => _ end |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    end.

  #[export] Ltac simplify_some :=
    match goal with
    | H : Some ?a = Some _ |- _ => inversion H; clear H; subst a
    | H : Some (?a, ?b) = Some _ |- _ => inversion H; clear H; try subst a; try subst b
    | H : (?a, ?b) = (_, _) |- _ => inversion H; clear H; try subst a; try subst b
    | H : Some _ = Some ?a |- _ => inversion H; clear H; try subst a
    | H : Some _ = Some (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    | H : (_, _) = (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    end.

  #[export] Ltac destruct_unit :=
    match goal with
    | u: unit |- _ => destruct u
    end.

  #[export] Ltac updm_to_setm :=
    repeat (match goal with | H: Some ?f = updm _ _ _ |- _ => pose proof (updm_set (esym H)); clear H; subst f end).

  #[export] Ltac unfold_all :=
    repeat (simpl in *;(simplify_some || unfold_bind || destruct_unit || unfold_match_misc || updm_to_setm)).

  #[export] Ltac goal_match_bind_step :=
    let a := fresh "a" in
    match goal with
    | |- _ = (Option.bind ?f ?v) => remember v as a; destruct a
    | |- (Option.bind ?f ?v) = _ => remember v as a; destruct a
    | |- (match ?cond as _ return _ with _ => _ end) = _ => remember cond as a; destruct a
    | |- _ = (match ?cond as _ return _ with _ => _ end) => remember cond as a; destruct a
    | |- (match ?cond as _ return _ with _ => _ end) _ = _ => remember cond as a; destruct a
    | |- _ = (match ?cond as _ return _ with _ => _ end) _  => remember cond as a; destruct a
    | |- (match ?cond as _ return _ with _ => _ end) _ _ = _ => remember cond as a; destruct a
    | |- _ = (match ?cond as _ return _ with _ => _ end) _ _ => remember cond as a; destruct a
    | |- (match ?cond as _ return _ with _ => _ end) => remember cond as a; destruct a
    end.

  #[export] Ltac deduce_reg reg_match :=
    let impl := fresh "impl" in
    let d_eq := fresh "d_eq" in
    match goal with
    | H: (getm ?m' ?w = Some ?v) |- context[(getm ?m ?w) = _] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl H) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (Some ?v = getm ?m' ?w) |- context[(getm ?m ?w) = _] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl (esym H)) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (getm ?m' ?w = Some ?v) |- context[Option.bind _ (getm ?m ?w)] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl H) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (Some ?v = getm ?m' ?w) |- context[Option.bind _ (getm ?m ?w)] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl (esym H)) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (Some ?v = getm ?m' ?w) |- context[match (getm ?m ?w) with _ => _ end] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl H) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (getm ?m' ?w = Some ?v) |- context[match (getm ?m ?w) with _ => _ end] =>
        pose proof (reg_match w v) as [_ impl];
        destruct (impl (esym H)) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (Some ?v = getm ?m' ?w) |- context[isSome (getm ?m ?w)] =>
        pose proof (reg_match w v) as [_ impl]; simpl in impl;
        destruct (impl (esym H)) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    | H: (getm ?m' ?w = Some ?v) |- context[isSome (getm ?m ?w)] =>
        pose proof (reg_match w v) as [_ impl]; simpl in impl;
        destruct (impl H) as [? [? d_eq]]; rewrite d_eq; simpl; clear impl
    end.


  #[export] Ltac deduce_equality s_eq :=
    let v := fresh "v" in
    let t := fresh "t" in
    let vt_match := fresh "vt_match" in
    let vt_eq := fresh "vt_eq" in
    (match goal with
     | reg_match: (registers_match _ _ ?s ?s'), ST: ?s = _ |- _
       =>( match (type of s_eq) with
          | (?m ?r) = Some ?old_v => destruct (reg_match r old_v) as [_ impl]; rewrite ST in impl;
                                    destruct (impl s_eq) as [[v t] [vt_match vt_eq]]; clear impl
          end)
     end) ||
      (match goal with
       | mem_match: (memory_match _ _ ?s ?s'), side_eq : side_of _ = _, ST: ?s = _ |- _ =>
           ( match (type of s_eq) with
             | (?m ?w) = Some ?old_v =>
                 pose proof (mem_match w old_v) as [_ impl]; simpl;
                 [auto | rewrite ST in side_eq; unfold side_of, color_of in side_eq; unfold_all; repeat unfold_match
                 | rewrite ST in impl; destruct (impl s_eq) as [[v t] [vt_match vt_eq]]; clear impl]
             end)
       end) ||
      (let comp_in := fresh "comp_in" in
       let t_color := fresh "t_color" in
       let t_code  := fresh "t_code" in
       let impl  := fresh "impl" in
       (match (type of s_eq) with
        | (?m ?w) = Some ?ov@?ot =>
            (match goal with
             | eq_off: (_ _ = Some ?off), pc_s1_s3: _ = (addw _ (as_word ?off)),
                     code_left: combined_codes _ _ _, code: is_true ?isc |- _  =>
                 match goal with
                 | H : true = (@in_mem ?T ?comp ?s) |- _ =>
                     assert (comp_in: @in_mem T comp s) by (rewrite <- H; done);
                     assert (t_color: LRC.color ot = comp) by (subst; auto);
                     assert (t_code : LRC.is_code ot) by (subst; done);
                     destruct (code_left w ov ot off comp comp_in eq_off t_code t_color) as [impl _];
                     try (rewrite (addwC _ onew) in impl; rewrite <- (addwA _ _ _) in impl);
                     simpl in impl; rewrite <- pc_s1_s3 in impl;
                     repeat (rewrite (addwC onew _) in impl);
                     pose proof (impl s_eq) as [v [vt_match vt_eq]]; clear impl
                 end
             end)
        end)).

End RecompositionDefinitions.
